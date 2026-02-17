/*
 * safe_server.c — Fully verified message handler.
 */

struct Message {
    int type;
    int length;
    char data[256];
};

struct Response {
    int status;
    int length;
    char data[256];
};

int handle_message(struct Message *msg, struct Response *resp) {
    if (msg->length < 0 || msg->length > 256) {
        resp->status = -1;
        resp->length = 0;
        return -1;
    }

    resp->status = 0;
    resp->length = msg->length;
    memcpy(resp->data, msg->data, msg->length);
    return 0;
}

int count_bytes(char *buf, int size, char target) {
    int count = 0;
    int i = 0;
    while (i < size) {
        if (buf[i] == target) {
            count = count + 1;
        }
        i = i + 1;
    }
    return count;
}

int main() {
    struct Message msg;
    struct Response resp;

    msg.type = 1;
    msg.length = 5;
    msg.data[0] = 72;
    msg.data[1] = 101;
    msg.data[2] = 108;
    msg.data[3] = 108;
    msg.data[4] = 111;

    int result = handle_message(&msg, &resp);
    if (result != 0) { return 1; }

    int *counters = malloc(4 * sizeof(int));
    if (counters == 0) { return 1; }

    counters[0] = count_bytes(resp.data, resp.length, 108);
    counters[1] = resp.length;
    counters[2] = resp.status;
    counters[3] = 0;

    int l_count = counters[0];
    free(counters);

    return l_count;  /* returns 2 */
}
