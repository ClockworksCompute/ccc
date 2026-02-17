/*
 * heartbleed_fixed.c — Heartbleed with bounds check.
 * The one-line fix that would have prevented CVE-2014-0160.
 */

struct HeartbeatRequest {
    int payload_length;
    char payload[64];
};

struct HeartbeatResponse {
    int payload_length;
    char payload[64];
};

int process_heartbeat(struct HeartbeatRequest *request,
                      struct HeartbeatResponse *response) {

    /* THE FIX */
    if (request->payload_length < 0 || request->payload_length > 64) {
        return -1;
    }

    response->payload_length = request->payload_length;

    /* SAFE: compiler has proof that payload_length ≤ 64 */
    memcpy(response->payload,
           request->payload,
           request->payload_length);

    return 0;
}

int main() {
    struct HeartbeatRequest req;
    struct HeartbeatResponse resp;

    req.payload_length = 13;
    req.payload[0] = 72;
    req.payload[1] = 101;
    req.payload[2] = 108;
    req.payload[3] = 108;
    req.payload[4] = 111;
    req.payload[5] = 44;
    req.payload[6] = 32;
    req.payload[7] = 119;
    req.payload[8] = 111;
    req.payload[9] = 114;
    req.payload[10] = 108;
    req.payload[11] = 100;
    req.payload[12] = 33;

    int result = process_heartbeat(&req, &resp);
    if (result == 0) {
        return resp.payload_length;
    }
    return -1;
}
