/*
 * 02_use_after_free.c — BUG: reads memory after freeing it.
 *
 * CCC catches this at compile time. A regular C compiler won't.
 * Run: ccc examples/02_use_after_free.c
 */
int main() {
    int *score = malloc(sizeof(int));
    if (score == 0) { return -1; }

    *score = 100;
    free(score);

    /* BUG: score was freed on the line above */
    int result = *score;

    return result;
}
