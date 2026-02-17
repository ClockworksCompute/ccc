/*
 * 05_double_free.c — BUG: frees the same memory twice.
 *
 * Double free corrupts the heap allocator. Exploitable in real programs.
 * CCC tracks every pointer's state and catches the second free.
 * Run: ccc examples/05_double_free.c
 */
int main() {
    int *p = malloc(sizeof(int));
    if (p == 0) { return -1; }

    *p = 7;
    free(p);

    /* BUG: p was already freed above */
    free(p);

    return 0;
}
