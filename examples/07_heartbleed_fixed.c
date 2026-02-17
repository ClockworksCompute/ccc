/*
 * 07_heartbleed_fixed.c — The Heartbleed pattern, FIXED.
 *
 * Same structure as 06_heartbleed.c, but with a bounds check before memcpy.
 * CCC accepts this because the length is provably within both buffer sizes.
 *
 * Compare with 06_heartbleed.c to see the one-line difference.
 * Run: ccc examples/07_heartbleed_fixed.c
 */
struct Request {
    int payload_length;
    char payload[64];
};

int main() {
    struct Request *req = malloc(sizeof(struct Request));
    if (req == 0) { return -1; }

    char response[64];

    req->payload_length = 13;
    req->payload[0] = 72;
    req->payload[1] = 101;
    req->payload[2] = 108;
    req->payload[3] = 108;
    req->payload[4] = 111;

    /* FIX: bounds check before memcpy — this is what Heartbleed was missing */
    if (req->payload_length < 0) { free(req); return -1; }
    if (req->payload_length > 64) { free(req); return -1; }

    memcpy(response, req->payload, req->payload_length);

    free(req);
    return response[0];   /* exits 72 ('H') */
}
