/*
 * buffer_overflow.c — Stack buffer overflow (CWE-121, CWE-787)
 * Morris Worm (1988), Code Red (2001), Slammer (2003).
 */

int main() {
    int scores[5];

    scores[0] = 95;
    scores[1] = 87;
    scores[2] = 92;
    scores[3] = 78;
    scores[4] = 88;

    scores[5] = 100;    /* ← OUT OF BOUNDS */

    int sum = 0;
    int i = 0;
    while (i < 5) {
        sum = sum + scores[i];
        i = i + 1;
    }
    return sum;
}
