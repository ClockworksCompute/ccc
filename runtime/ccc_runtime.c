#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/*
 * FEL-59 (--harden, prototype): a tiny allocation-size registry so
 * `ccc_check_index` (called by the emitter, only when --harden is passed,
 * before every array/pointer subscript through a POINTER-typed base) can
 * catch at runtime what the static verifier couldn't prove at compile
 * time. Linear scan over a small fixed table -- deliberately simple and
 * obviously correct rather than fast; this is a correctness prototype, not
 * a production allocator shim. If the table fills up, further allocations
 * are silently left unregistered (their accesses go unchecked, exactly
 * like today's behavior without --harden) rather than doing anything that
 * could itself misbehave.
 */
#define CCC_MAX_TRACKED_ALLOCS 65536
static void *ccc_alloc_ptrs[CCC_MAX_TRACKED_ALLOCS];
static long ccc_alloc_sizes[CCC_MAX_TRACKED_ALLOCS];
static int ccc_alloc_count = 0;

static void ccc_register_alloc(void *ptr, long size) {
    if (!ptr) return;
    if (ccc_alloc_count < CCC_MAX_TRACKED_ALLOCS) {
        ccc_alloc_ptrs[ccc_alloc_count] = ptr;
        ccc_alloc_sizes[ccc_alloc_count] = size;
        ccc_alloc_count++;
    }
}

static void ccc_unregister_alloc(void *ptr) {
    if (!ptr) return;
    for (int i = 0; i < ccc_alloc_count; i++) {
        if (ccc_alloc_ptrs[i] == ptr) {
            ccc_alloc_ptrs[i] = 0;
            ccc_alloc_sizes[i] = -1;
            return;
        }
    }
}

/*
 * FEL-59 follow-up: an INTERIOR pointer (`row = p + 3*stride; row[i];`)
 * used to go completely unchecked -- the previous version of this
 * function only matched `ptr` against a registered allocation's OWN
 * starting address exactly, and `row`'s address is never itself
 * registered anywhere (only `p`'s is), so the lookup silently missed
 * and `ccc_check_index` no-opped, exactly as if --harden had not been
 * passed. Confirmed by ASan: this shape genuinely overflows and this
 * exact-match registry genuinely let it through.
 *
 * Finds the tracked allocation whose byte range [base, base+size)
 * CONTAINS `addr` (not just an exact match on `base` itself), and
 * returns the number of bytes remaining from `addr` to the end of
 * that allocation -- what `ccc_check_index` actually needs to bounds-
 * check an access through `addr`, whatever pointer arithmetic produced
 * it. Most recent registration wins on ties, same as before (a freed
 * then reused address correctly picks up the new size). Returns -1 if
 * `addr` falls inside no tracked allocation at all.
 */
static long ccc_lookup_remaining(void *addr) {
    char *a = (char *)addr;
    for (int i = ccc_alloc_count - 1; i >= 0; i--) {
        void *base = ccc_alloc_ptrs[i];
        long size = ccc_alloc_sizes[i];
        if (!base || size < 0) continue;
        char *lo = (char *)base;
        char *hi = lo + size;
        if (a >= lo && a < hi) {
            return (long)(hi - a);
        }
    }
    return -1;
}

void *ccc_malloc(long size) {
    void *p = malloc((size_t)size);
    ccc_register_alloc(p, size);
    return p;
}

void ccc_free(void *ptr) {
    ccc_unregister_alloc(ptr);
    free(ptr);
}

void ccc_memcpy(void *dst, void *src, long n) { memcpy(dst, src, (size_t)n); }

/*
 * Called (only in --harden-emitted code) immediately before every
 * `base[index]` access through a pointer-typed base, with the element
 * size in bytes. `base` is whatever address the expression evaluates to
 * at the access site -- the start of a `malloc`/`ccc_malloc` allocation,
 * OR an interior pointer somewhere inside one (`row = p + 3*stride`) --
 * `ccc_lookup_remaining` finds the tracked allocation containing it
 * either way. Aborts with a diagnostic on an out-of-bounds or negative
 * index. An untracked base (a stack local, a pointer parameter whose
 * origin allocation this table never saw, e.g. because it came from
 * something other than ccc_malloc, or a table that's full) is not an
 * error here -- it just means this specific access couldn't be checked,
 * exactly as if --harden had not been passed for it.
 *
 * Known limitation, not addressed by the interior-pointer fix above: a
 * NEGATIVE index is always rejected, even through an interior pointer
 * where a small negative index would still land inside the SAME tracked
 * allocation (e.g. `row = p + 5; row[-2];` legitimately reaches `p[3]`).
 * Catching that needs `addr - lo` (the offset already consumed) tracked
 * alongside the remaining-bytes count computed here; deferred as a
 * smaller, separate follow-up rather than folded into this fix.
 */
void ccc_check_index(void *base, long index, long elem_size) {
    long remaining = ccc_lookup_remaining(base);
    if (remaining < 0) return;
    if (index < 0 || elem_size <= 0 || (index + 1) * elem_size > remaining) {
        fprintf(stderr,
                "ccc --harden: bounds check failed (base=%p index=%ld elem_size=%ld "
                "remaining_bytes_from_base=%ld) -- aborting instead of corrupting memory\n",
                base, index, elem_size, remaining);
        abort();
    }
}
