/*
 * use_after_free.c — CWE-416
 * Chrome fixed 130+ of these in 2023 alone.
 */

struct User {
    int id;
    int permissions;
};

int main() {
    struct User *alice = malloc(sizeof(struct User));
    if (alice == 0) { return -1; }

    alice->id = 42;
    alice->permissions = 1;

    free(alice);

    int id = alice->id;    /* ← USE AFTER FREE */

    return id;
}
