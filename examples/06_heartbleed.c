/*
 * 06_heartbleed.c — The Heartbleed pattern: memcpy with unchecked length.
 *
 * This is the exact class of bug that caused the Heartbleed vulnerability
 * (CVE-2014-0160), which leaked passwords, private keys, and session tokens
 * from ~17% of the internet's servers.
 *
 * The bug: the server trusts the client's claimed payload_length without
 * checking it against the actual buffer size. An attacker sends length=64000
 * with a tiny payload, and memcpy reads past the buffer into adjacent memory.
 *
 * CCC catches this at compile time.
 * Run: ccc examples/06_heartbleed.c
 */
struct Request {
    int payload_length;
    char payload[64];
};

int main() {
    struct Request *req = malloc(sizeof(struct Request));
    if (req == 0) { return -1; }

    char response[64];

    req->payload_length = 9999;   /* attacker sends huge length */

    /* BUG: req->payload_length is attacker-controlled, never bounds-checked.
       If payload_length > 64, this reads past req->payload into other memory. */
    memcpy(response, req->payload, req->payload_length);

    free(req);
    return response[0];
}
