/*
 * fixed.c — post-fix HeifPixelImage::overlay (libheif >= 1.19.8, commit 85e21ad)
 *
 * Same port as vulnerable.c (see that file's header comment for the full
 * C++ -> C translation notes), but with the clipping logic reordered exactly
 * as commit 85e21ad44eba931314337300a2376b8d28f085ae ("simplify overlay
 * overlap area computation") reorders it in libheif/pixelimage.cc:
 *
 *   1. Check complete non-overlap for BOTH axes first (return early).
 *   2. Clip the right and bottom borders using int64_t arithmetic on the
 *      *original*, unclipped in_w/in_h (`dx + (int64_t)in_w > out_w`),
 *      instead of casting the possibly-negative dx/dy to uint32_t.
 *   3. Only then clip the left and top borders (in_x0/out_x0/in_y0/out_y0),
 *      each exactly once.
 *
 * Because the right/bottom clip no longer reads a wrapped-around dx/dy, and
 * because in_x0/in_y0/out_x0/out_y0 are computed after (not interleaved
 * with) the right/bottom clip, in_w/in_h can no longer end up larger than
 * the real overlap area. See:
 * https://github.com/strukturag/libheif/commit/85e21ad44eba931314337300a2376b8d28f085ae
 */

typedef unsigned long size_t;
typedef unsigned char uint8_t;
typedef unsigned int uint32_t;
typedef int int32_t;
typedef long int64_t;

void *malloc(size_t size);
/* NOTE: no free() declared/called in main() below -- see the comment there. */

uint32_t negate_negative_int32(int32_t x) {
    if (x == -2147483647 - 1) {
        return 2147483648u;
    }
    return (uint32_t)(-x);
}

/* out_p/out_w/out_h, in_p/in_w/in_h: stride == width (tightly packed) --
   see the matching note on overlay_vulnerable() in vulnerable.c for why
   this repro folds stride into width (CCC's AArch64 backend caps calls
   at 8 arguments). */
int overlay_fixed(uint8_t *out_p, uint32_t out_w, uint32_t out_h,
                   const uint8_t *in_p, uint32_t in_w, uint32_t in_h,
                   int32_t dx, int32_t dy) {
    /* --- check whether overlay image overlaps with current image */

    if (dx > 0 && (uint32_t)dx >= out_w) {
        /* the overlay image is completely outside the right border -> skip overlaying */
        return 0;
    } else if (dx < 0 && in_w <= negate_negative_int32(dx)) {
        /* the overlay image is completely outside the left border -> skip overlaying */
        return 0;
    }

    if (dy > 0 && (uint32_t)dy >= out_h) {
        /* the overlay image is completely outside the bottom border -> skip overlaying */
        return 0;
    } else if (dy < 0 && in_h <= negate_negative_int32(dy)) {
        /* the overlay image is completely outside the top border -> skip overlaying */
        return 0;
    }

    /* --- compute overlapping area */

    uint32_t in_x0;
    uint32_t in_y0;
    uint32_t out_x0;
    uint32_t out_y0;

    /* right border */
    if (dx + (int64_t)in_w > out_w) {
        /* overlay image extends partially outside of right border */
        in_w = (uint32_t)((int64_t)out_w - dx);
    }

    /* bottom border */
    if (dy + (int64_t)in_h > out_h) {
        /* overlay image extends partially outside of bottom border */
        in_h = (uint32_t)((int64_t)out_h - dy);
    }

    /* left border */
    if (dx < 0) {
        /* overlay image starts partially outside of left border */
        in_x0 = negate_negative_int32(dx);
        out_x0 = 0;
        in_w = in_w - in_x0; /* in_x0 < in_w because in_w > -dx = in_x0 */
    } else {
        in_x0 = 0;
        out_x0 = (uint32_t)dx;
    }

    /* top border */
    if (dy < 0) {
        /* overlay image started partially outside of top border */
        in_y0 = negate_negative_int32(dy);
        out_y0 = 0;
        in_h = in_h - in_y0;
    } else {
        in_y0 = 0;
        out_y0 = (uint32_t)dy;
    }

    /* --- copy overlay into overlapping area */
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
    uint32_t out_w = 20;
    uint32_t out_h = 16;

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

    int32_t dx = -10;
    int32_t dy = 0;

    overlay_fixed(out_p, out_w, out_h, in_p, in_w, in_h, dx, dy);

    /* Deliberately not free()'d -- see the matching note in vulnerable.c
       (FEL-47: non-constant malloc() size isn't yet related to pointer
       liveness, so free() here would be rejected for an unrelated reason
       regardless of this file's actual, fixed safety). */
    return 0;
}
