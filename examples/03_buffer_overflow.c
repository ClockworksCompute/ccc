/*
 * 03_buffer_overflow.c — BUG: writes past the end of an array.
 *
 * This is the #1 cause of security vulnerabilities in C.
 * CCC catches it at compile time.
 * Run: ccc examples/03_buffer_overflow.c
 */
int main() {
    int data[4];
    data[0] = 10;
    data[1] = 20;
    data[2] = 30;
    data[3] = 40;

    /* BUG: index 4 is out of bounds (array has 4 elements: 0..3) */
    data[4] = 50;

    return data[0];
}
