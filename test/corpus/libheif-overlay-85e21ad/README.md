# libheif overlay heap overflow (pre commit 85e21ad)

**Real function:** `HeifPixelImage::overlay(std::shared_ptr<HeifPixelImage>&, int32_t dx, int32_t dy)`
in `libheif/pixelimage.cc`. **Bug class:** signed/unsigned integer mixing in
bounds-clipping arithmetic (CWE-190 integer overflow/wraparound leading to
CWE-787/CWE-125 out-of-bounds write/read). Fixed upstream by commit
[`85e21ad44eba931314337300a2376b8d28f085ae`](https://github.com/strukturag/libheif/commit/85e21ad44eba931314337300a2376b8d28f085ae)
("simplify overlay overlap area computation"), which is also the fix for the
libheif 1.19.7/1.19.8 heap overflow exploited via Discourse -> ImageMagick ->
HEIC decode as described in the [hacktron.ai "Hacking OpenAI"](https://www.hacktron.ai/blog/hacking-openai)
report. An HEIF `iovl` (image overlay) box supplies attacker-controlled
signed offsets `(dx, dy)` placing an overlay image onto a canvas; the pre-fix
code computes the visible width/height of the overlay by casting a possibly
negative `dx`/`dy` to `uint32_t` inside a stale "we know dx >= 0" assumption,
which wraps around and replaces the already-correctly-clipped width with a
value larger than the canvas, so the copy loop that follows reads/writes past
the overlay and canvas plane buffers. `vulnerable.c` and `fixed.c` port the
per-channel, non-alpha branch of the real function to plain C (flat
`(buffer, stride, width, height)` tuples instead of `HeifPixelImage`
accessors); see the comment headers in each file for the full C++ -> C
translation notes and a line-by-line explanation of the bug.
