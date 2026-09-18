/*
 * vulnerable.c — pre-fix HeifPixelImage::overlay (libheif < 1.19.8 / commit 85e21ad^)
 *
 * Ported from libheif/pixelimage.cc, function HeifPixelImage::overlay(), as it
 * existed before commit 85e21ad44eba931314337300a2376b8d28f085ae ("simplify
 * overlay overlap area computation"). This is the bug the hacktron.ai
 * "Hacking OpenAI" report exploited (heap overflow in libheif 1.19.7/1.19.8,
 * reached through Discourse -> ImageMagick -> HEIC decode).
 *
 * C++ -> C translation notes:
 *   - HeifPixelImage becomes two flat (buffer, stride, width, height) tuples:
 *     the destination "canvas" plane and the source "overlay" plane. Real
 *     libheif gets these via get_plane()/get_width()/get_height() accessors
 *     on shared_ptr<HeifPixelImage>; here they're plain function parameters.
 *   - Error return type becomes int (0 = Error::Ok).
 *   - The has_alpha per-pixel blend branch is dropped; only the plain
 *     (!has_alpha) copy branch is ported, since that's where the byte-count
 *     bug lives. The copy loop itself is written as a clean two-index
 *     nested loop (count-based: in_w/in_h are "how many columns/rows to
 *     copy, starting at in_x0/in_y0") rather than reproducing the original's
 *     memcpy call verbatim, to keep source/destination indexing unambiguous.
 *   - negate_negative_int32() is copied verbatim (handles INT32_MIN specially
 *     to avoid UB on negation).
 *
 * THE BUG (unchanged from upstream, this is the whole point of this file):
 * after computing in_x0/out_x0 for a left-clipped overlay (dx < 0), the code
 * still believes "we know that dx >= 0" (see the comment reproduced below)
 * and does `static_cast<uint32_t>(dx) > UINT32_MAX - in_w || dx + in_w > out_w`.
 * When dx is negative, casting it to uint32_t wraps it to a huge value, so
 * `dx + in_w` (usual arithmetic conversions -> unsigned) is *also* huge, and
 * `dx + in_w > out_w` is true essentially whenever dx < 0. The "fix-up" that
 * follows, `in_w = out_w - (uint32_t)dx`, then evaluates to `out_w + |dx|`
 * (mod 2^32) -- i.e. in_w is *replaced* with a value larger than out_w by
 * exactly the amount that was just clipped off the left, instead of staying
 * clipped. The copy loop that follows is bounded by this corrupted in_w and
 * reads/writes past both the source (overlay) and destination (canvas)
 * plane buffers.
 *
 * See libheif/pixelimage.cc:85e21ad44eba931314337300a2376b8d28f085ae^
 * https://github.com/strukturag/libheif/commit/85e21ad44eba931314337300a2376b8d28f085ae
 */

typedef unsigned long size_t;
typedef unsigned char uint8_t;
typedef unsigned int uint32_t;
typedef int int32_t;

void *malloc(size_t size);
/* NOTE: no free() declared/called in main() below -- see the comment there. */

/* Verbatim port of libheif's negate_negative_int32 (pixelimage.cc). */
uint32_t negate_negative_int32(int32_t x) {
    if (x == -2147483647 - 1) {
        /* INT32_MIN: -x is UB, so special-case it like upstream does. */
        return 2147483648u;
    }
    return (uint32_t)(-x);
}

/*
 * Pre-fix HeifPixelImage::overlay, single channel, no alpha.
 * out_p/out_w/out_h: destination canvas plane (stride == out_w -- tightly
 *                     packed; real libheif planes can be padded and carry
 *                     a separate stride, but CCC's AArch64 backend caps
 *                     calls at 8 arguments (no stack-passed args yet), so
 *                     this repro folds stride into width to stay portable
 *                     across CCC's current pipeline; the bug is identical
 *                     either way since stride never participates in it).
 * in_p/in_w/in_h:     source overlay plane (stride == in_w, same reason).
 * dx, dy: attacker-controlled offsets from the HEIF 'iovl' (image overlay)
 *         box, telling the decoder where to place the overlay on the canvas.
 * Returns 0 on success (Error::Ok in the original).
 */
int overlay_vulnerable(uint8_t *out_p, uint32_t out_w, uint32_t out_h,
                        const uint8_t *in_p, uint32_t in_w, uint32_t in_h,
                        int32_t dx, int32_t dy) {
    uint32_t in_x0;
    uint32_t in_y0;
    uint32_t out_x0;
    uint32_t out_y0;

    if (dx > 0 && (uint32_t)dx >= out_w) {
        /* the overlay image is completely outside the right border -> skip overlaying */
        return 0;
    } else if (dx < 0 && in_w <= negate_negative_int32(dx)) {
        /* the overlay image is completely outside the left border -> skip overlaying */
        return 0;
    }

    if (dx < 0) {
        /* overlay image started partially outside of left border */
        in_x0 = negate_negative_int32(dx);
        out_x0 = 0;
        in_w = in_w - in_x0; /* in_x0 < in_w because in_w > -dx = in_x0 */
    } else {
        in_x0 = 0;
        out_x0 = (uint32_t)dx;
    }

    /* we know that dx >= 0 && dx < out_w   <-- WRONG when the dx<0 branch above ran */
    if ((uint32_t)dx > (4294967295u - in_w) || dx + in_w > out_w) {
        /* overlay image extends partially outside of right border */
        in_w = out_w - (uint32_t)dx; /* we know that dx < out_w from first condition */
    }

    if (dy > 0 && (uint32_t)dy >= out_h) {
        /* the overlay image is completely outside the bottom border -> skip overlaying */
        return 0;
    } else if (dy < 0 && in_h <= negate_negative_int32(dy)) {
        /* the overlay image is completely outside the top border -> skip overlaying */
        return 0;
    }

    if (dy < 0) {
        /* overlay image started partially outside of top border */
        in_y0 = negate_negative_int32(dy);
        out_y0 = 0;
        in_h = in_h - in_y0; /* in_y0 < in_h because in_h > -dy = in_y0 */
    } else {
        in_y0 = 0;
        out_y0 = (uint32_t)dy;
    }

    /* we know that dy >= 0 && dy < out_h   <-- same trap as the dx case above */
    if ((uint32_t)dy > (4294967295u - in_h) || dy + in_h > out_h) {
        /* overlay image extends partially outside of bottom border */
        in_h = out_h - (uint32_t)dy; /* we know that dy < out_h from first condition */
    }

    /* copy loop: in_w/in_h are now "number of columns/rows to copy", starting
       at source (in_x0, in_y0) and destination (out_x0, out_y0). When the
       bug above fired, in_w/in_h can exceed the real remaining space in
       both the source and destination planes. */
    uint32_t row = 0;
    while (row < in_h) {
        uint32_t col = 0;
        while (col < in_w) {
            out_p[(out_y0 + row) * out_w + out_x0 + col] =
                in_p[(in_y0 + row) * in_w + in_x0 + col];
            col = col + 1;
        }
        row = row + 1;
    }

    return 0;
}

int main() {
    /* Canvas plane (the base HEIC image being composited onto). */
    uint32_t out_w = 20;
    uint32_t out_h = 16;

    /* Overlay plane (a derived image referenced by the 'iovl' box). */
    uint32_t in_w = 16;
    uint32_t in_h = 16;

    uint8_t *out_p = malloc(out_w * out_h);
    uint8_t *in_p = malloc(in_w * in_h);

    uint32_t i = 0;
    while (i < out_w * out_h) {
        out_p[i] = 0;
        i = i + 1;
    }
    i = 0;
    while (i < in_w * in_h) {
        in_p[i] = 1;
        i = i + 1;
    }

    /* Attacker-controlled iovl offsets: overlay placed 10px past the left
       edge of the canvas. dy = 0 (vertical offset unused for this trigger;
       the dy path has the exact same bug shape). */
    int32_t dx = -10;
    int32_t dy = 0;

    overlay_vulnerable(out_p, out_w, out_h, in_p, in_w, in_h, dx, dy);

    /* Deliberately not free()'d: CCC's verifier cannot yet relate a
       non-constant malloc() size (out_w*out_h / in_w*in_h here) to pointer
       liveness (tracked separately as FEL-47), so free() on either buffer
       is currently rejected as "not known to be heap-live" regardless of
       this file's actual bug. Calling free() here would make this entry's
       scoreboard verdict about that unrelated, already-known gap instead of
       about the overlay bounds bug this entry exists to exercise -- see
       docs/corpus-results.md. */
    return 0;
}
