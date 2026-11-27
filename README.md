# Squeeze — a lossless PNG encoder for make.fun's png-squeeze-01

An entry for the make.fun bounty
[png-squeeze-01-run-20261127](https://make.fun/bounty/png-squeeze-01-run-20261127):
one program (`main.ts`, run as `node /bot/main.ts` on Node 22) that answers
every instance of a set of eight 1280×720 RGBA screenshots, writing each one
losslessly as a PNG in as few bytes as it can.

## How it works

Per image:

1. **Decode** the input PNG to RGBA with its own decoder (bit depth 8,
   colour types 0/2/3/4/6, only IHDR/PLTE/tRNS/IDAT/IEND).
2. **Choose a form**: a palette (type 3) when the image holds at most 256
   colours, in count order and in luminance order; grey (type 0) or
   grey+alpha (type 4) when every pixel is grey; RGB (type 2) or RGBA
   (type 6) otherwise. A single fully transparent value, when no opaque
   pixel shares it, is carried by a tRNS key instead of an alpha channel.
3. **Filter** each row: fixed filter 0, and per-row choices by the
   minimum-sum heuristic (PNG spec 12.8), fewest distinct byte pairs, and
   brute force (each filter tried through zlib at level 4 after the 32 KiB
   written before it). The winner is screened by zlib at level 6 — the
   cheap proxies mislead, because the signed sum and a level-1 deflate both
   favour small filtered values over the exact repetition an unfiltered row
   keeps and level 6 squeezes hardest.
4. **Deflate** the winner with an optimal-parsing DEFLATE encoder written
   from RFC 1951: a hash-chain longest-match search, a Pareto frontier of
   (length, distance) records per position, and a shortest-path parse under
   iterated dynamic Huffman lengths. The work is budgeted by the filtered
   stream's size so the whole set fits the 60 s wall (deep chains on small
   streams, shallow chains on large ones, zlib level 9 where a stream
   already squeezes hard), and the smaller of the optimal parse and a zlib
   level-9 stream is always kept.

Everything is deterministic — no clock, no environment, no randomness — so
two executions write identical bytes. An instance that fails to encode is
answered with an exact copy of its input, so every instance is always
answered in the stated format.

## Measured results

Practice set (kit): **740,955** / 1,000,000, all 8 instances answered
exactly, in ~45 s of the 60 s wall. A second set drawn with the kit
generator scores 751,387. The house baseline (fixed-paeth 1.0.0) scores
420,399 on the practice set.

## License

MIT — see `LICENSE`.
