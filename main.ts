// png-squeeze-01-run-20261127 entry: "Squeeze" — an adaptive lossless PNG
// encoder for 1280x720 RGBA screenshots, written for make.fun's png-squeeze
// bounty. It reads each /input/<id>/image.png, re-encodes it losslessly in
// as few bytes as it can, and writes /output/<id>/image.png.
//
// How it works, per image:
//   1. Decode the input PNG to RGBA (its own decoder; bit depth 8, colour
//      types 0/2/3/4/6, only IHDR/PLTE/tRNS/IDAT/IEND).
//   2. Choose a form: a palette (type 3) when the image holds at most 256
//      colours, in count order and in luminance order; grey (type 0) or
//      grey+alpha (type 4) when every pixel is grey; RGB (type 2) or RGBA
//      (type 6) otherwise; a single fully transparent value, when no opaque
//      pixel shares it, is carried by a tRNS key instead of an alpha channel.
//   3. Filter each row: fixed filter 0, and per-row choices by the
//      minimum-sum heuristic (PNG spec 12.8), fewest distinct byte pairs,
//      and brute force (each filter tried through zlib at level 4 after the
//      32 KiB written before it). The winner is screened by zlib at level
//      6: the cheap proxies mislead, because the signed sum and a level-1
//      deflate both favour small filtered values over the exact repetition
//      an unfiltered row keeps and level 6 squeezes hardest.
//   4. Deflate the winner with an optimal-parsing DEFLATE encoder written
//      from RFC 1951 (hash-chain longest-match search, a Pareto frontier of
//      (length, distance) records per position, and a shortest-path parse
//      under iterated dynamic Huffman lengths), with the work budgeted by
//      the filtered stream's size so the whole set fits the 60 s wall; a
//      zlib level-9 stream is kept whenever it is smaller. Everything is
//      deterministic: no clock, no environment, no randomness.
//
// Written from the DEFLATE (RFC 1951) and PNG specifications and the
// standard techniques behind optimal-parsing compressors. No code is copied
// from any existing compressor or from the kit; the tables are the ones
// RFC 1951 publishes, and the filter heuristics are the ones the PNG
// specification describes.
import { readFileSync, writeFileSync, mkdirSync, readdirSync, existsSync, copyFileSync } from 'node:fs';
import { join } from 'node:path';
import { deflateSync, inflateSync, constants } from 'node:zlib';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// ---------- CRC-32 (PNG) and Adler-32 (zlib) ----------
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();
function crc32(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}
function adler32(data) {
  let a = 1;
  let b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) {
      a += data[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

// ---------- PNG decode (to RGBA) ----------
const PNG_SIG = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}
// Decode a PNG file's bytes to { width, height, rgba }. Throws on anything
// the contest's own decoder would not read.
function decodePng(bytes) {
  if (bytes.length < 8 || PNG_SIG.some((b, i) => bytes[i] !== b)) throw new Error('not a PNG');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  let ended = false;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    if (at + 12 > bytes.length) throw new Error('short chunk');
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) throw new Error('chunk overruns file');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error(type + ' CRC');
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      if (header !== null || len !== 13) throw new Error('bad IHDR');
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9], interlace: data[12] };
      if (header.depth !== 8 || !Object.hasOwn(CHANNELS, header.colourType) || header.interlace !== 0) throw new Error('unsupported IHDR');
    } else if (type === 'PLTE') {
      if (palette !== null || header.colourType !== 3 || idat.length > 0 || len === 0 || len % 3 !== 0 || len > 768) throw new Error('bad PLTE');
      palette = data;
    } else if (type === 'tRNS') {
      if (trns !== null || idat.length > 0) throw new Error('bad tRNS');
      const ct = header.colourType;
      if (ct === 3) {
        if (palette === null || len > palette.length / 3) throw new Error('bad tRNS for palette');
      } else if (ct === 0 || ct === 2) {
        if (len !== (ct === 0 ? 2 : 6)) throw new Error('bad tRNS length');
        for (let i = 0; i < len; i += 2) if (data[i] !== 0) throw new Error('tRNS sample over 255');
      } else throw new Error('tRNS with colour type ' + ct);
      trns = data;
    } else if (type === 'IDAT') {
      if (header.colourType === 3 && palette === null) throw new Error('IDAT before PLTE');
      idat.push(data);
    } else if (type === 'IEND') {
      if (len !== 0) throw new Error('bad IEND');
      ended = true;
    } else throw new Error('unread chunk ' + type);
  }
  if (!ended || idat.length === 0) throw new Error('no IEND or IDAT');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  if (raw.length !== expected) throw new Error('IDAT inflates to the wrong length');
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    if (ft > 4) throw new Error('bad filter type');
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3];
      lut[e * 4 + 1] = palette[e * 3 + 1];
      lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      if (e >= entries) throw new Error('palette index out of range');
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { width, height, rgba };
}

// ---------- image analysis ----------
function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = rgba.byteOffset % 4 === 0
    ? new Uint32Array(rgba.buffer, rgba.byteOffset, n)
    : new Uint32Array(rgba.slice().buffer, 0, n);
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  let colours = null;
  if (!many) {
    colours = [...counts.keys()].map((c) => {
      const b = new Uint8Array(Uint32Array.of(c).buffer);
      return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
    });
  }
  return { opaque, grey, colours };
}
// The one fully transparent value (grey or RGB) the image may key by tRNS
// instead of an alpha channel: every pixel opaque or that exact value at
// alpha 0, and no opaque pixel of the same value. Null when there is none.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}
function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}
function paletteForm(rgba, colours, order) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  const entries = [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0];
    plte[i * 3 + 1] = c.rgba[1];
    plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = rgba.byteOffset % 4 === 0
    ? new Uint32Array(rgba.buffer, rgba.byteOffset, n)
    : new Uint32Array(rgba.slice().buffer, 0, n);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { plte, trns, indices };
}
// The forms an image can be written in: each { colourType, bpp, samples,
// plte, trns, filters }. A palette image is tried as a palette only (a
// palette holds it in a third of the bytes of RGB or less), unless it is
// also grey, in which case grey is tried too.
function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const [order, filters] of [
      ['count', [0]],
      ['luminance', [0, 'minsum', 'brute']],
    ]) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: [0, 'minsum', 'pairs', 'brute'] });
  return forms;
}

// ---------- PNG row filters ----------
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}
// The minimum-sum heuristic's cost: the sum of a filtered row's bytes read
// as signed (-128 to 127), absolute.
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}
function pairsOf(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) {
      seen[pair] = stamp;
      n++;
    }
  }
  return n;
}
// The filtered data of an image's samples by `choice`: a filter type (0-4)
// for every row, or 'minsum', 'pairs' or 'brute' per row (the lower type on
// a tie). Brute force tries each filter through zlib at level 4 after the
// 32 KiB written before the row.
function filtered(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, () => new Uint8Array(stride + 1));
  for (let t = 0; t < 5; t++) trial[t][0] = t;
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - 32768), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else cost = deflateSync(trial[t], before.length === 0 ? { level: 4, memLevel: 9 } : { level: 4, memLevel: 9, dictionary: before }).length;
      if (cost < best) {
        best = cost;
        type = t;
      }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// ---------- optimal-parsing DEFLATE (from RFC 1951) ----------
// Hash-chain longest-match search, a Pareto frontier of (length, distance)
// records per position, and a shortest-path parse under iterated dynamic
// Huffman code lengths. Deterministic: no clock, no randomness.
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const LEN_SYM = new Uint8Array(259);
for (let s = 0; s < 29; s++) for (let l = LEN_BASE[s]; l < (s === 28 ? 259 : LEN_BASE[s + 1]); l++) LEN_SYM[l] = s;
const DIST_SYM = new Uint8Array(32769);
for (let s = 0; s < 30; s++) for (let d = DIST_BASE[s]; d < (s === 29 ? 32769 : DIST_BASE[s + 1]); d++) DIST_SYM[d] = s;
const LEN_MAX = LEN_BASE.map((b, s) => (s === 28 ? 258 : LEN_BASE[s + 1] - 1));
const FIXED_LIT = new Uint8Array(288);
for (let i = 0; i < 288; i++) FIXED_LIT[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;
const FIXED_DIST = new Uint8Array(30).fill(5);
const WSIZE = 32768;
const MIN_MATCH = 3;
const MAX_MATCH = 258;
const BLOCK = 100000;
// A symbol the current table gives length 0 is not free: it will cost real
// bits once the table is rebuilt from this parse. Charge a penalty instead,
// so the parse never chases symbols the table cannot code.
const PENALTY = 12;

class BitWriter {
  constructor(cap) {
    this.buf = new Uint8Array(cap);
    this.pos = 0;
    this.bitbuf = 0;
    this.bitcnt = 0;
  }
  bits(value, len) {
    if (len === 0) return;
    this.bitbuf |= (value & ((1 << len) - 1)) << this.bitcnt;
    this.bitcnt += len;
    while (this.bitcnt >= 8) {
      if (this.pos >= this.buf.length) this.grow();
      this.buf[this.pos++] = this.bitbuf & 0xff;
      this.bitbuf >>>= 8;
      this.bitcnt -= 8;
    }
  }
  grow() {
    const nb = new Uint8Array(this.buf.length * 2);
    nb.set(this.buf);
    this.buf = nb;
  }
  align() {
    if (this.bitcnt > 0) {
      if (this.pos >= this.buf.length) this.grow();
      this.buf[this.pos++] = this.bitbuf & 0xff;
      this.bitbuf = 0;
      this.bitcnt = 0;
    }
  }
}

// Huffman code lengths from frequencies, capped at maxLen. Builds a Huffman
// tree, then repairs any overflow past maxLen the way zlib's gen_bitlen
// does (move a leaf down a level, two leaves up).
function buildLengths(freq, maxLen) {
  const n = freq.length;
  const len = new Uint8Array(n);
  const blCount = new Uint32Array(maxLen + 1);
  let nodes = 0;
  let only = -1;
  for (let s = 0; s < n; s++) if (freq[s] > 0) { nodes++; only = s; }
  if (nodes === 0) return len;
  if (nodes === 1) { len[only] = 1; return len; }
  const treeFreq = new Float64Array(2 * n);
  const treeLeft = new Int32Array(2 * n).fill(-1);
  const treeRight = new Int32Array(2 * n).fill(-1);
  const treeSym = new Int32Array(2 * n).fill(-1);
  for (let s = 0; s < n; s++) if (freq[s] > 0) { treeFreq[s] = freq[s]; treeSym[s] = s; }
  let list = [];
  for (let s = 0; s < n; s++) if (freq[s] > 0) list.push(s);
  let next = n;
  while (list.length > 1) {
    list.sort((a, b) => treeFreq[a] - treeFreq[b]);
    const a = list.shift();
    const b = list.shift();
    treeFreq[next] = treeFreq[a] + treeFreq[b];
    treeLeft[next] = a;
    treeRight[next] = b;
    list.push(next);
    next++;
  }
  const root = list[0];
  let overflow = 0;
  const stack = [[root, 0]];
  while (stack.length) {
    const [node, d] = stack.pop();
    if (treeSym[node] >= 0) {
      let dd = d;
      if (dd > maxLen) { dd = maxLen; overflow++; }
      len[treeSym[node]] = dd;
      blCount[dd]++;
    } else {
      stack.push([treeLeft[node], d + 1]);
      stack.push([treeRight[node], d + 1]);
    }
  }
  if (overflow > 0) {
    let m = maxLen - 1;
    while (overflow > 0) {
      while (blCount[m] === 0) m--;
      blCount[m] -= 1;
      blCount[m + 1] += 2;
      blCount[maxLen] -= 1;
      overflow -= 2;
    }
    const syms = [];
    for (let s = 0; s < n; s++) if (freq[s] > 0) syms.push(s);
    syms.sort((a, b) => freq[b] - freq[a] || a - b);
    let idx = 0;
    for (let l = 1; l <= maxLen; l++) {
      for (let k = 0; k < blCount[l]; k++) len[syms[idx++]] = l;
    }
  }
  return len;
}
function canonicalCodes(len) {
  const maxLen = Math.max(0, ...len);
  const blCount = new Uint32Array(maxLen + 1);
  for (const l of len) if (l) blCount[l]++;
  const nextCode = new Uint32Array(maxLen + 1);
  let code = 0;
  for (let l = 1; l <= maxLen; l++) {
    code = (code + blCount[l - 1]) << 1;
    nextCode[l] = code;
  }
  const codes = new Uint32Array(len.length);
  for (let s = 0; s < len.length; s++) if (len[s]) codes[s] = nextCode[len[s]]++;
  return { codes, maxLen };
}
function revBits(code, len) {
  let r = 0;
  for (let i = 0; i < len; i++) r = (r << 1) | ((code >> i) & 1);
  return r;
}

// Longest-match search: for every position, the Pareto frontier of (length,
// distance) records — each record the smallest distance seen achieving its
// length. Candidates arrive in increasing-distance order, so a record is
// useful exactly when its length beats every length seen so far: O(1) per
// candidate, and the frontier stays ordered by increasing length and
// distance, which the parse relies on.
function findMatches(data, chain) {
  const n = data.length;
  const P = 6;
  const pairLen = new Uint16Array(P * n);
  const pairDist = new Uint16Array(P * n);
  const head = new Int32Array(65536).fill(-1);
  const prev = new Int32Array(n);
  const hash = (i) => (((data[i] * 257 + data[i + 1]) * 257 + data[i + 2]) & 0xffff);
  const limit = n - MIN_MATCH;
  const recL = new Int16Array(P);
  const recD = new Int16Array(P);
  for (let i = 0; i <= limit; i++) {
    const h = hash(i);
    let cand = head[h];
    prev[i] = cand;
    head[h] = i;
    const maxL = Math.min(MAX_MATCH, n - i);
    let recN = 0;
    let maxRec = 0;
    const addRec = (l, d) => {
      if (l <= maxRec || l < MIN_MATCH) return;
      maxRec = l;
      if (recN < P) {
        recL[recN] = l;
        recD[recN] = d;
        recN++;
      } else {
        // Full: drop a middle record, keeping the nearest and the longest.
        recL[2] = recL[3]; recD[2] = recD[3];
        recL[3] = recL[4]; recD[3] = recD[4];
        recL[4] = recL[5]; recD[4] = recD[5];
        recL[5] = l; recD[5] = d;
      }
    };
    let bl = 0;
    let steps = 0;
    const maxDist = i < WSIZE ? i : WSIZE;
    while (cand >= 0) {
      const dist = i - cand;
      if (dist > maxDist) break;
      if (data[cand + bl] === data[i + bl]) {
        let l = 0;
        while (l < maxL && data[cand + l] === data[i + l]) l++;
        if (l >= MIN_MATCH) addRec(l, dist);
        if (l > bl) {
          bl = l;
          if (l >= MAX_MATCH) break;
        }
      }
      cand = prev[cand];
      steps++;
      if (steps >= chain) break;
    }
    for (let p = 0; p < recN; p++) {
      pairLen[p * n + i] = recL[p];
      pairDist[p * n + i] = recD[p];
    }
  }
  return { pairLen, pairDist, pairs: P, n };
}

// Optimal parse (shortest path) for one block. cost[i] is the cheapest bit
// cost to encode data[bs..i). At each position the parse may take a literal,
// or any frontier match at its length-symbol boundaries (plus its exact
// length). The block's cut is the cheapest reachable position at or past its
// end, so a match may overshoot the block.
function parseBlock(data, bs, be, matches, litLen, distLen, cost, choiceLen, choiceDist) {
  const { pairLen, pairDist, pairs: P, n } = matches;
  const end = Math.min(be + MAX_MATCH, n);
  cost.fill(Infinity, bs, end + 1);
  cost[bs] = 0;
  const litCost = new Uint8Array(288);
  const distCost = new Uint8Array(30);
  for (let s = 0; s < 288; s++) litCost[s] = litLen[s] || PENALTY;
  for (let s = 0; s < 30; s++) distCost[s] = distLen[s] || PENALTY;
  const lenSymCost = new Uint8Array(29);
  for (let s = 0; s < 29; s++) lenSymCost[s] = litCost[257 + s] + LEN_EXTRA[s];
  for (let i = bs; i < be; i++) {
    const c0 = cost[i];
    if (c0 === Infinity) continue;
    const lc = c0 + litCost[data[i]];
    if (lc < cost[i + 1]) {
      cost[i + 1] = lc;
      choiceLen[i + 1] = 0;
    }
    // Pairs are ordered by increasing (length, distance), so for each length
    // symbol the first pair long enough for it has the smallest distance and
    // therefore the cheapest cost: one candidate per symbol, not pairs x 29.
    let p = 0;
    for (let s = 0; s < 29; s++) {
      const L = LEN_MAX[s];
      if (L < MIN_MATCH) continue;
      while (p < P && pairLen[p * n + i] < L) p++;
      if (p >= P) break;
      const dist = pairDist[p * n + i];
      const c = c0 + lenSymCost[s] + distCost[DIST_SYM[dist]] + DIST_EXTRA[DIST_SYM[dist]];
      const j = i + L;
      if (c < cost[j]) {
        cost[j] = c;
        choiceLen[j] = L;
        choiceDist[j] = dist;
      }
    }
    // Each pair's exact length is a candidate too (it can sit inside a symbol
    // whose maximum no pair reaches).
    for (let q = 0; q < P; q++) {
      const ml = pairLen[q * n + i];
      if (ml < MIN_MATCH || ml >= 258) continue;
      const dist = pairDist[q * n + i];
      const s = LEN_SYM[ml];
      const c = c0 + lenSymCost[s] + distCost[DIST_SYM[dist]] + DIST_EXTRA[DIST_SYM[dist]];
      const j = i + ml;
      if (c < cost[j]) {
        cost[j] = c;
        choiceLen[j] = ml;
        choiceDist[j] = dist;
      }
    }
  }
  let cut = be;
  let bc = cost[be];
  for (let j = be + 1; j <= end; j++) {
    if (cost[j] < bc) {
      bc = cost[j];
      cut = j;
    }
  }
  const syms = [];
  let j = cut;
  while (j > bs) {
    const L = choiceLen[j];
    if (L === 0) {
      syms.push({ lit: data[j - 1] });
      j -= 1;
    } else {
      syms.push({ len: L, dist: choiceDist[j] });
      j -= L;
    }
  }
  syms.reverse();
  return { syms, cut, cost: bc };
}
function countFreqs(syms) {
  const lf = new Uint32Array(288);
  const df = new Uint32Array(30);
  for (const s of syms) {
    if (s.lit !== undefined) lf[s.lit]++;
    else {
      lf[257 + LEN_SYM[s.len]]++;
      df[DIST_SYM[s.dist]]++;
    }
  }
  lf[256] = 1;
  return { lf, df };
}
function writeDynamicBlock(bw, syms, litLen, distLen) {
  const { codes: litCodes } = canonicalCodes(litLen);
  const { codes: distCodes } = canonicalCodes(distLen);
  let hlit = 288;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const seq = new Uint8Array(hlit + hdist);
  for (let i = 0; i < hlit; i++) seq[i] = litLen[i];
  for (let i = 0; i < hdist; i++) seq[hlit + i] = distLen[i];
  const items = [];
  let i = 0;
  while (i < seq.length) {
    const v = seq[i];
    if (v === 0) {
      let run = 0;
      while (i + run < seq.length && seq[i + run] === 0 && run < 138) run++;
      if (run >= 3) {
        if (run <= 10) items.push([17, 3, run - 3]);
        else items.push([18, 7, run - 11]);
        i += run;
      } else {
        for (let k = 0; k < run; k++) items.push([0, 0, 0]);
        i += run;
      }
    } else {
      items.push([v, 0, 0]);
      i++;
      let run = 0;
      while (i + run < seq.length && seq[i + run] === v && run < 6) run++;
      if (run >= 3) {
        items.push([16, 2, run - 3]);
        i += run;
      }
    }
  }
  const clFreq = new Uint32Array(19);
  for (const [s] of items) clFreq[s]++;
  const clLen = buildLengths(clFreq, 7);
  const { codes: clCodes } = canonicalCodes(clLen);
  const ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let hclen = 19;
  while (hclen > 4 && clLen[ORDER[hclen - 1]] === 0) hclen--;
  bw.bits(hlit - 257, 5);
  bw.bits(hdist - 1, 5);
  bw.bits(hclen - 4, 4);
  for (let k = 0; k < hclen; k++) bw.bits(clLen[ORDER[k]], 3);
  for (const [s, eb, ev] of items) {
    bw.bits(revBits(clCodes[s], clLen[s]), clLen[s]);
    if (eb) bw.bits(ev, eb);
  }
  for (const s of syms) {
    if (s.lit !== undefined) {
      bw.bits(revBits(litCodes[s.lit], litLen[s.lit]), litLen[s.lit]);
    } else {
      const ls = LEN_SYM[s.len];
      bw.bits(revBits(litCodes[257 + ls], litLen[257 + ls]), litLen[257 + ls]);
      if (LEN_EXTRA[ls]) bw.bits(s.len - LEN_BASE[ls], LEN_EXTRA[ls]);
      const ds = DIST_SYM[s.dist];
      bw.bits(revBits(distCodes[ds], distLen[ds]), distLen[ds]);
      if (DIST_EXTRA[ds]) bw.bits(s.dist - DIST_BASE[ds], DIST_EXTRA[ds]);
    }
  }
  bw.bits(revBits(litCodes[256], litLen[256]), litLen[256]);
}
// A zlib stream of `data`: the match frontier is computed once and reused by
// every parse iteration; lengths are rebuilt from each parse's frequencies,
// and the final block is written with lengths rebuilt from the final parse,
// so every symbol the stream uses has a code in the table it is written with.
function zliteDeflate(data, { chain = 512, iterations = 1 } = {}) {
  const n = data.length;
  const matches = findMatches(data, chain);
  const bw = new BitWriter(n + 65536);
  bw.buf[bw.pos++] = 0x78;
  bw.buf[bw.pos++] = 0x9c;
  const cost = new Float64Array(n + MAX_MATCH + 1);
  const choiceLen = new Uint16Array(n + MAX_MATCH + 1);
  const choiceDist = new Uint16Array(n + MAX_MATCH + 1);
  let pos = 0;
  while (pos < n) {
    const bs = pos;
    const be = Math.min(n, bs + BLOCK);
    let { syms, cut } = parseBlock(data, bs, be, matches, FIXED_LIT, FIXED_DIST, cost, choiceLen, choiceDist);
    let litLen;
    let distLen;
    for (let it = 0; it < iterations; it++) {
      const { lf, df } = countFreqs(syms);
      litLen = buildLengths(lf, 15);
      distLen = buildLengths(df, 15);
      if (litLen[256] === 0) litLen[256] = 1;
      const r = parseBlock(data, bs, be, matches, litLen, distLen, cost, choiceLen, choiceDist);
      syms = r.syms;
      cut = r.cut;
    }
    const fin = countFreqs(syms);
    litLen = buildLengths(fin.lf, 15);
    distLen = buildLengths(fin.df, 15);
    if (litLen[256] === 0) litLen[256] = 1;
    if (distLen.every((v) => v === 0)) distLen[0] = 1;
    const last = cut >= n;
    bw.bits(last ? 1 : 0, 1);
    bw.bits(2, 2);
    writeDynamicBlock(bw, syms, litLen, distLen);
    pos = cut;
  }
  bw.align();
  const ad = adler32(data);
  bw.buf[bw.pos++] = (ad >>> 24) & 0xff;
  bw.buf[bw.pos++] = (ad >>> 16) & 0xff;
  bw.buf[bw.pos++] = (ad >>> 8) & 0xff;
  bw.buf[bw.pos++] = ad & 0xff;
  return bw.buf.subarray(0, bw.pos);
}

// ---------- PNG writer ----------
function pngOf(chunks) {
  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(PNG_SIG, 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    for (let k = 0; k < 4; k++) out[at + 4 + k] = type.charCodeAt(k);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}
function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}
function pngOfForm(width, height, form, idat) {
  const chunks = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}
const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

// ---------- final deflate ----------
// zlib's best of a few level-9 settings (the safety net and the large-image
// default). Deterministic for the same input and settings.
function zlibBest(data) {
  let best = null;
  for (const [level, memLevel, strategy] of [[9, 8, 0], [9, 9, 0]]) {
    const z = deflateSync(data, { level, memLevel, strategy });
    if (best === null || z.length < best.length) best = z;
  }
  return best;
}
// The work is budgeted by the filtered stream's size, so the whole set fits
// the wall: small streams get the deep chain, medium ones a shallow chain,
// and the largest streams get zlib-9 first — optimal parsing only when the
// stream still holds enough redundancy for it to pay (a large stream zlib-9
// already squeezes hard has little left for it). The smaller of the two
// streams is always kept.
function finalDeflate(data) {
  const z9 = zlibBest(data);
  const n = data.length;
  if (n <= 1048576) {
    const zl = zliteDeflate(data, { chain: 512, iterations: 2 });
    return zl.length < z9.length ? zl : z9;
  }
  if (n <= 3145728) {
    const zl = zliteDeflate(data, { chain: 256, iterations: 1 });
    return zl.length < z9.length ? zl : z9;
  }
  if (z9.length / n < 0.02) return z9;
  const zl = zliteDeflate(data, { chain: 256, iterations: 1 });
  return zl.length < z9.length ? zl : z9;
}

// The screen: each form's filter choices are weighed by zlib at level 6,
// the smallest the winner (the first on a tie), each weighed with its
// PLTE and tRNS chunks. Level 6 is the screen because the cheap proxies
// mislead: the signed sum and a level-1 deflate both favour small filtered
// values over exact repetition, while an unfiltered row of a transparent
// background repeats exactly and is the one zlib at level 6 and above
// squeezes hardest. Fixed filter 0 is always screened: it is the
// repetition-preserving baseline the adaptive choices are judged against.
const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };
function encodeImage(rgba, width, height) {
  let best = null;
  for (const form of formsOf(rgba)) {
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const bytes = deflateSync(data, SCREEN).length + chunks;
      if (best === null || bytes < best.bytes) best = { form, data, bytes };
    }
  }
  const idat = finalDeflate(best.data);
  return pngOfForm(width, height, best.form, idat);
}

// ---------- main ----------
// One run over the whole set. An instance that fails to encode is answered
// with an exact copy of its input (a valid stored PNG in the stated format),
// so every instance is always answered.
for (const id of readdirSync(INPUT_DIR).sort()) {
  const inPath = join(INPUT_DIR, id, 'image.png');
  if (!existsSync(inPath)) continue;
  const outDir = join(OUTPUT_DIR, id);
  mkdirSync(outDir, { recursive: true });
  const outPath = join(outDir, 'image.png');
  try {
    const { width, height, rgba } = decodePng(new Uint8Array(readFileSync(inPath)));
    writeFileSync(outPath, encodeImage(rgba, width, height));
  } catch {
    copyFileSync(inPath, outPath);
  }
}
