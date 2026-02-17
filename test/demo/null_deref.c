/*
 * null_deref.c — CWE-476
 * CVE-2019-9213 (Linux kernel): null deref → root.
 */

struct Config {
    int max_connections;
    int timeout_ms;
    int buffer_size;
};

int main() {
    struct Config *config = malloc(sizeof(struct Config));

    /* BUG: no null check */
    config->max_connections = 100;    /* ← NULL DEREF */

    return config->max_connections;
}
