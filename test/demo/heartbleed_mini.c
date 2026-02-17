/*
 * heartbleed_mini.c — Simplified Heartbleed (CVE-2014-0160)
 *
 * The real Heartbleed: OpenSSL's TLS heartbeat extension read
 * payload_length bytes from a buffer without checking if the
 * buffer actually contained that many bytes. Attackers sent
 * length=65535 with a tiny payload, reading private keys,
 * passwords, and session tokens from server memory.
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

    response->payload_length = request->payload_length;

    /* BUG: payload_length could be > 64. Reads out of bounds. */
    memcpy(response->payload,
           request->payload,
           request->payload_length);    /* ← MEMORY SAFETY VIOLATION */

    return 0;
}
