/*
 * double_free.c — CWE-415
 * CVE-2023-25136 (OpenSSH), CVE-2021-21220 (Chrome V8).
 */

int main() {
    int *data = malloc(10 * sizeof(int));
    if (data == 0) { return -1; }

    data[0] = 42;
    data[9] = 99;

    free(data);
    free(data);    /* ← DOUBLE FREE */

    return 0;
}
