#include <stdlib.h>
#include <string.h>

void *ccc_malloc(long size) { return malloc((size_t)size); }
void ccc_free(void *ptr) { free(ptr); }
void ccc_memcpy(void *dst, void *src, long n) { memcpy(dst, src, (size_t)n); }
