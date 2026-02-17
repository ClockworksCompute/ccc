/*
 * 01_safe_program.c — A correct program. CCC accepts this.
 *
 * Allocates a struct, null-checks, uses it, frees it.
 * Run: ccc examples/01_safe_program.c
 */
struct Point {
    int x;
    int y;
};

int distance_squared(struct Point *a, struct Point *b) {
    int dx = a->x - b->x;
    int dy = a->y - b->y;
    return dx * dx + dy * dy;
}

int main() {
    struct Point *p1 = malloc(sizeof(struct Point));
    if (p1 == 0) { return -1; }
    struct Point *p2 = malloc(sizeof(struct Point));
    if (p2 == 0) { free(p1); return -1; }

    p1->x = 3;
    p1->y = 0;
    p2->x = 0;
    p2->y = 4;

    int d2 = distance_squared(p1, p2);

    free(p1);
    free(p2);
    return d2;   /* exits 25 (= 3² + 4²) */
}
