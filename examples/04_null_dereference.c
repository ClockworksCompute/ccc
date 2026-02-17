/*
 * 04_null_dereference.c — BUG: uses a pointer without checking for null.
 *
 * malloc can return null if out of memory. Dereferencing null = crash.
 * CCC requires a null check before any dereference.
 * Run: ccc examples/04_null_dereference.c
 */
int main() {
    int *p = malloc(sizeof(int));

    /* BUG: no null check — p could be 0 */
    *p = 42;

    free(p);
    return 0;
}
