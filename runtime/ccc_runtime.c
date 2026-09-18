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

/* Most recent registration wins on an exact-address match (a freed then
   reused address correctly picks up the new size). */
static long ccc_lookup_size(void *ptr) {
    for (int i = ccc_alloc_count - 1; i >= 0; i--) {
        if (ccc_alloc_ptrs[i] == ptr) return ccc_alloc_sizes[i];
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
 * size in bytes. Aborts with a diagnostic on an out-of-bounds or negative
 * index into a TRACKED allocation. An untracked base (a stack local, a
 * pointer parameter whose origin allocation this table never saw, e.g.
 * because it came from something other than ccc_malloc, or a table
 * that's full) is not an error here -- it just means this specific access
 * couldn't be checked, exactly as if --harden had not been passed for it.
 */
void ccc_check_index(void *base, long index, long elem_size) {
    long sz = ccc_lookup_size(base);
    if (sz < 0) return;
    if (index < 0 || elem_size <= 0 || (index + 1) * elem_size > sz) {
        fprintf(stderr,
                "ccc --harden: bounds check failed (base=%p index=%ld elem_size=%ld "
                "tracked_alloc_size=%ld) -- aborting instead of corrupting memory\n",
                base, index, elem_size, sz);
        abort();
    }
}
