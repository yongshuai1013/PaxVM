/* paxsvc -- a tiny guest-side binder client/server for PaxVM's
 * virtual binder driver (S5b). It speaks the exact wire
 * protocol of the stock 2.3.7 servicemanager stack (the bio /
 * binder_call / binder_loop shapes from system/core's
 * servicemanager binder.c), built freestanding against the
 * guest's own libc.so: no headers, hand-declared prototypes,
 * and a crtbegin-style _start that hands control to the guest
 * libc's __libc_init, exactly like a stock guest binary.
 *
 * Modes (argv scan, first match wins):
 *   serve -- register the "paxsvc" service and answer PING
 *   list  -- enumerate services via LIST_SERVICES (paged)
 *   ping  -- GET "paxsvc" and call its PING transaction
 * Evidence is written as files/markers under /data (the
 * supervisor's log shows the syscalls; marker names carry
 * the values, the established probe convention).
 */

typedef unsigned int u32;
typedef unsigned short u16;
typedef unsigned char u8;

/* ---- guest libc surface (hand-declared) ---- */
int open(const char *path, int flags, ...);
int close(int fd);
int read(int fd, void *buf, unsigned count);
int write(int fd, const void *buf, unsigned count);
int ioctl(int fd, int request, ...);
void *mmap(void *addr, unsigned length, int prot, int flags, int fd, int offset);
int munmap(void *addr, unsigned length);
int mkdir(const char *path, int mode);
void _exit(int status);

/* ---- memory/string helpers (also satisfy compiler-emitted
 * calls; the __aeabi_ aliases are the ARM EABI spellings) ---- */
void *memcpy(void *d, const void *s, unsigned n) {
    u8 *dd = (u8 *)d;
    const u8 *ss = (const u8 *)s;
    while (n--) *dd++ = *ss++;
    return d;
}
void *__aeabi_memcpy(void *d, const void *s, unsigned n) { return memcpy(d, s, n); }
void *memmove(void *d, const void *s, unsigned n) {
    u8 *dd = (u8 *)d;
    const u8 *ss = (const u8 *)s;
    if (dd < ss) {
        while (n--) *dd++ = *ss++;
    } else {
        dd += n; ss += n;
        while (n--) *--dd = *--ss;
    }
    return d;
}
void *__aeabi_memmove(void *d, const void *s, unsigned n) { return memmove(d, s, n); }
void *memset(void *d, int c, unsigned n) {
    u8 *dd = (u8 *)d;
    while (n--) *dd++ = (u8)c;
    return d;
}
void *__aeabi_memset(void *d, int c, unsigned n) { return memset(d, c, n); }
static unsigned xstrlen(const char *s) {
    unsigned n = 0;
    while (s[n]) n++;
    return n;
}
static int xstreq(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return *a == *b;
}

/* crtbegin_dynamic.S, restated: the guest linker jumps to
 * _start; we hand the raw kernel argument block, a main
 * trampoline and the structors table to __libc_init. */
__asm__(
    ".text\n"
    ".align 4\n"
    ".type _start,#function\n"
    ".globl _start\n"
    "_start:\n"
    "    mov r0, sp\n"
    "    mov r1, #0\n"
    "    adr r2, 0f\n"
    "    adr r3, 1f\n"
    "    b __libc_init\n"
    "0:  b guest_main\n"
    "1:  .long __PREINIT_ARRAY__\n"
    "    .long __INIT_ARRAY__\n"
    "    .long __FINI_ARRAY__\n"
    "    .long __CTOR_LIST__\n"
    ".section .preinit_array, \"aw\"\n"
    ".globl __PREINIT_ARRAY__\n"
    "__PREINIT_ARRAY__:\n"
    "    .long -1\n"
    "    .long 0\n"
    ".section .init_array, \"aw\"\n"
    ".globl __INIT_ARRAY__\n"
    "__INIT_ARRAY__:\n"
    "    .long -1\n"
    "    .long 0\n"
    ".section .fini_array, \"aw\"\n"
    ".globl __FINI_ARRAY__\n"
    "__FINI_ARRAY__:\n"
    "    .long -1\n"
    "    .long 0\n"
    ".section .ctors, \"aw\"\n"
    ".globl __CTOR_LIST__\n"
    "__CTOR_LIST__:\n"
    "    .long -1\n"
    "    .long 0\n"
    ".section .data, \"aw\"\n"
    ".globl __dso_handle\n"
    "__dso_handle:\n"
    "    .long __dso_handle\n"
);

/* ---- binder wire constants (ARM32 binder.h, 2.3.7) ---- */
#define BINDER_WRITE_READ ((int)0xC0186201)
#define BC_TRANSACTION 0x40286300u
#define BC_REPLY 0x40286301u
#define BC_FREE_BUFFER 0x40046303u
#define BC_ENTER_LOOPER 0x630cu
#define BR_NOOP 0x720cu
#define BR_TRANSACTION_COMPLETE 0x7206u
#define BR_INCREFS 0x80087207u
#define BR_ACQUIRE 0x80087208u
#define BR_RELEASE 0x80087209u
#define BR_DECREFS 0x8008720au
#define BR_TRANSACTION 0x80287202u
#define BR_REPLY 0x80287203u
#define BR_DEAD_REPLY 0x7205u
#define BR_FAILED_REPLY 0x7211u
#define BR_DEAD_BINDER 0x8004720fu
#define BR_CLEAR_DEATH_NOTIFICATION_DONE 0x80047210u
#define BR_ATTEMPT_ACQUIRE 0x800c720bu
#define TF_STATUS_CODE 0x08u
#define OBJ_BINDER 0x73622a85u
#define OBJ_HANDLE 0x73682a85u
#define SVC_MGR_GET_SERVICE 1u
#define SVC_MGR_ADD_SERVICE 3u
#define SVC_MGR_LIST_SERVICES 4u
#define PING_MAGIC 0x50494E47u /* "PING" */
#define PONG_MAGIC 0x504F4E47u /* "PONG" */

struct bwr {
    u32 write_size, write_consumed, write_buffer;
    u32 read_size, read_consumed, read_buffer;
};
struct txn {
    u32 target, cookie, code, flags, sender_pid, sender_euid;
    u32 data_size, offs_size, data, offs;
};
struct flat {
    u32 type, flags, ptr, cookie;
};

/* ---- parcel building (bio_put_* shapes) ---- */
struct parcel {
    u8 data[1024];
    u32 len;
    u32 offs[8];
    u32 noffs;
};
static void p_init(struct parcel *p) { p->len = 0; p->noffs = 0; }
static void p_u32(struct parcel *p, u32 v) {
    memcpy(p->data + p->len, &v, 4);
    p->len += 4;
}
static void p_str16_x(struct parcel *p, const char *s) {
    u32 len = xstrlen(s);
    u32 i;
    p_u32(p, len);
    for (i = 0; i <= len; i++) {
        u16 c = (u16)(u8)s[i];
        memcpy(p->data + p->len, &c, 2);
        p->len += 2;
    }
    while (p->len & 3) p->data[p->len++] = 0;
}
static void p_obj(struct parcel *p, u32 ptr, u32 type) {
    struct flat f;
    f.type = type;
    f.flags = 0x7f | 0x100; /* priority mask | ACCEPTS_FDS */
    f.ptr = ptr;
    f.cookie = 0;
    p->offs[p->noffs++] = p->len;
    memcpy(p->data + p->len, &f, 16);
    p->len += 16;
}
static void p_svcmgr_header(struct parcel *p) {
    p_u32(p, 0); /* strict-mode policy, ignored by the manager */
    p_str16_x(p, "android.os.IServiceManager");
}

/* ---- parcel reading (bio_get_* shapes) ---- */
struct rparcel {
    const u8 *data;
    u32 len;
    const u32 *offs;
    u32 noffs;
    u32 pos;
};
static u32 r_u32(struct rparcel *r) {
    u32 v = 0;
    if (r->pos + 4 <= r->len) memcpy(&v, r->data + r->pos, 4);
    r->pos += 4;
    return v;
}
static const u16 *r_str16(struct rparcel *r, u32 *len_out) {
    u32 len = r_u32(r);
    const u16 *s = (const u16 *)(r->data + r->pos);
    u32 adv = (len + 1) * 2;
    r->pos += (adv + 3) & ~3u;
    *len_out = len;
    return s;
}
static int r_ref(struct rparcel *r, u32 *handle_out) {
    u32 i;
    for (i = 0; i < r->noffs; i++) {
        if (r->offs[i] == r->pos) {
            struct flat f;
            if (r->pos + 16 > r->len) return -1;
            memcpy(&f, r->data + r->pos, 16);
            if (f.type != OBJ_HANDLE) return -1;
            *handle_out = f.ptr;
            r->pos += 16;
            return 0;
        }
    }
    return -1;
}

/* ---- driver plumbing ---- */
static int binder_open_guest(void) {
    int fd = open("/dev/binder", 2 /* O_RDWR */);
    void *m;
    if (fd < 0) return -1;
    m = mmap(0, 128 * 1024, 1 /* PROT_READ */, 2 /* MAP_PRIVATE */, fd, 0);
    if (m == (void *)-1) {
        close(fd);
        return -1;
    }
    return fd;
}
static int binder_write_only(int fd, const void *buf, u32 len) {
    struct bwr b;
    memset(&b, 0, sizeof(b));
    b.write_size = len;
    b.write_buffer = (u32)buf;
    return ioctl(fd, BINDER_WRITE_READ, &b);
}
static void free_reply(int fd, struct rparcel *reply) {
    u32 cmd[2];
    if (!reply->data) return;
    cmd[0] = BC_FREE_BUFFER;
    cmd[1] = (u32)reply->data;
    binder_write_only(fd, cmd, sizeof(cmd));
    reply->data = 0;
}

/* binder_call, mirroring servicemanager's: one WRITE_READ
 * carrying the transaction, then read-only WRITE_READs until
 * BR_REPLY (or a failure reply) shows up. */
static int binder_call(int fd, u32 target, u32 code, struct parcel *msg,
                       struct rparcel *reply, u32 *reply_flags) {
    struct {
        u32 cmd;
        struct txn t;
    } wb;
    u8 readbuf[128];
    struct bwr b;
    wb.cmd = BC_TRANSACTION;
    memset(&wb.t, 0, sizeof(wb.t));
    wb.t.target = target;
    wb.t.code = code;
    wb.t.data_size = msg->len;
    wb.t.offs_size = msg->noffs * 4;
    wb.t.data = (u32)msg->data;
    wb.t.offs = msg->noffs ? (u32)msg->offs : 0;
    memset(&b, 0, sizeof(b));
    b.write_size = sizeof(wb);
    b.write_buffer = (u32)&wb;
    reply->data = 0;
    for (;;) {
        u32 *p, *end;
        b.read_size = sizeof(readbuf);
        b.read_consumed = 0;
        b.read_buffer = (u32)readbuf;
        if (ioctl(fd, BINDER_WRITE_READ, &b) < 0) return -1;
        p = (u32 *)readbuf;
        end = p + (b.read_consumed / 4);
        while (p < end) {
            u32 cmd = *p++;
            if (cmd == BR_NOOP || cmd == BR_TRANSACTION_COMPLETE) continue;
            if (cmd == BR_REPLY) {
                struct txn *t = (struct txn *)p;
                reply->data = (const u8 *)(unsigned)t->data;
                reply->len = t->data_size;
                reply->offs = (const u32 *)(unsigned)t->offs;
                reply->noffs = t->offs_size / 4;
                reply->pos = 0;
                *reply_flags = t->flags;
                return 0;
            }
            if (cmd == BR_DEAD_REPLY || cmd == BR_FAILED_REPLY) return -1;
            if (cmd == BR_INCREFS || cmd == BR_ACQUIRE || cmd == BR_RELEASE ||
                cmd == BR_DECREFS) { p += 2; continue; }
            if (cmd == BR_DEAD_BINDER || cmd == BR_CLEAR_DEATH_NOTIFICATION_DONE) {
                p += 1;
                continue;
            }
            if (cmd == BR_ATTEMPT_ACQUIRE) { p += 3; continue; }
            return -1;
        }
    }
}

/* ---- evidence helpers ---- */
static void marker(const char *path) { mkdir(path, 0755); }
static char *put_dec(char *out, u32 n) {
    char tmp[12];
    int i = 0;
    if (n == 0) tmp[i++] = '0';
    while (n) {
        u32 q = 0, r = n;
        while (r >= 10) { r -= 10; q++; }
        tmp[i++] = (char)('0' + r);
        n = q;
    }
    while (i) *out++ = tmp[--i];
    return out;
}
static void marker_num(const char *prefix, u32 n) {
    char buf[64];
    char *e = buf;
    while (*prefix) *e++ = *prefix++;
    e = put_dec(e, n);
    *e = 0;
    mkdir(buf, 0755);
}
static void write_file(const char *path, const char *text, u32 len) {
    /* O_WRONLY|O_CREAT|O_TRUNC = 01 | 0100 | 01000 = 0x241 */
    int fd = open(path, 0x241, 0644);
    if (fd >= 0) {
        write(fd, text, len);
        close(fd);
    }
}

/* ---- serve mode ---- */
static int g_object; /* its address is the local binder object */

static void send_reply(int fd, u32 buffer_to_free, struct parcel *reply, int status) {
    struct {
        u32 cmd_free;
        u32 buffer;
        u32 cmd_reply;
        struct txn t;
    } data;
    data.cmd_free = BC_FREE_BUFFER;
    data.buffer = buffer_to_free;
    data.cmd_reply = BC_REPLY;
    memset(&data.t, 0, sizeof(data.t));
    if (status) {
        data.t.flags = TF_STATUS_CODE;
        data.t.data_size = 4;
        data.t.data = (u32)&status;
    } else {
        data.t.data_size = reply->len;
        data.t.offs_size = reply->noffs * 4;
        data.t.data = (u32)reply->data;
        data.t.offs = reply->noffs ? (u32)reply->offs : 0;
    }
    binder_write_only(fd, &data, sizeof(data));
}

static int do_serve(void) {
    int fd = binder_open_guest();
    struct parcel msg;
    struct rparcel reply;
    u32 flags = 0, status;
    u8 readbuf[128];
    u32 enter = BC_ENTER_LOOPER;
    if (fd < 0) {
        marker("/data/SERVE_OPENFAIL");
        return 1;
    }
    p_init(&msg);
    p_svcmgr_header(&msg);
    p_str16_x(&msg, "paxsvc");
    p_obj(&msg, (u32)&g_object, OBJ_BINDER);
    if (binder_call(fd, 0, SVC_MGR_ADD_SERVICE, &msg, &reply, &flags) < 0) {
        marker("/data/SERVE_ADDFAIL");
        return 1;
    }
    status = (flags & TF_STATUS_CODE) ? 1 : r_u32(&reply);
    free_reply(fd, &reply);
    if (status != 0) {
        marker("/data/SERVE_ADDFAIL");
        return 1;
    }
    marker("/data/SERVE_READY");
    binder_write_only(fd, &enter, sizeof(enter));
    for (;;) {
        struct bwr b;
        u32 *p, *end;
        memset(&b, 0, sizeof(b));
        b.read_size = sizeof(readbuf);
        b.read_buffer = (u32)readbuf;
        if (ioctl(fd, BINDER_WRITE_READ, &b) < 0) return 1;
        p = (u32 *)readbuf;
        end = p + (b.read_consumed / 4);
        while (p < end) {
            u32 cmd = *p++;
            if (cmd == BR_NOOP || cmd == BR_TRANSACTION_COMPLETE) continue;
            if (cmd == BR_INCREFS || cmd == BR_ACQUIRE || cmd == BR_RELEASE ||
                cmd == BR_DECREFS) { p += 2; continue; }
            if (cmd == BR_DEAD_BINDER || cmd == BR_CLEAR_DEATH_NOTIFICATION_DONE) {
                p += 1;
                continue;
            }
            if (cmd == BR_ATTEMPT_ACQUIRE) { p += 3; continue; }
            if (cmd == BR_TRANSACTION) {
                struct txn *t = (struct txn *)p;
                struct rparcel rq;
                p += 10;
                rq.data = (const u8 *)(unsigned)t->data;
                rq.len = t->data_size;
                rq.offs = (const u32 *)(unsigned)t->offs;
                rq.noffs = t->offs_size / 4;
                rq.pos = 0;
                if (t->code == 1 && r_u32(&rq) == PING_MAGIC) {
                    struct parcel rp;
                    p_init(&rp);
                    p_u32(&rp, PONG_MAGIC);
                    p_u32(&rp, 777);
                    send_reply(fd, t->data, &rp, 0);
                } else {
                    send_reply(fd, t->data, (struct parcel *)0, -1);
                }
                continue;
            }
            return 1;
        }
    }
}

/* ---- list mode: LIST_SERVICES is paged in 2.3.7 -- one
 * name per call, indexed, until the manager answers with a
 * status-code reply ---- */
static int do_list(void) {
    int fd = binder_open_guest();
    static char text[2048];
    u32 tlen = 0, count = 0, n;
    if (fd < 0) return 1;
    for (n = 0; n < 64; n++) {
        struct parcel msg;
        struct rparcel reply;
        u32 flags = 0, slen = 0, i;
        const u16 *s;
        p_init(&msg);
        p_svcmgr_header(&msg);
        p_u32(&msg, n);
        if (binder_call(fd, 0, SVC_MGR_LIST_SERVICES, &msg, &reply, &flags) < 0)
            break;
        if (flags & TF_STATUS_CODE) {
            free_reply(fd, &reply);
            break;
        }
        s = r_str16(&reply, &slen);
        for (i = 0; i < slen && tlen + 1 < sizeof(text); i++)
            text[tlen++] = (char)(s[i] & 0x7f);
        if (tlen + 1 < sizeof(text)) text[tlen++] = '\n';
        free_reply(fd, &reply);
        count++;
    }
    write_file("/data/svc-list.txt", text, tlen);
    marker_num("/data/LIST_N_", count);
    return 0;
}

/* ---- ping mode: GET the paxsvc service, then call it ---- */
static int do_ping(void) {
    int fd = binder_open_guest();
    struct parcel msg;
    struct rparcel reply;
    u32 flags = 0, handle = 0;
    if (fd < 0) return 1;
    p_init(&msg);
    p_svcmgr_header(&msg);
    p_str16_x(&msg, "paxsvc");
    if (binder_call(fd, 0, SVC_MGR_GET_SERVICE, &msg, &reply, &flags) < 0 ||
        (flags & TF_STATUS_CODE) || reply.len < 16 ||
        r_ref(&reply, &handle) < 0) {
        marker("/data/PING_NOSVC");
        return 1;
    }
    free_reply(fd, &reply);
    marker_num("/data/GET_H_", handle);
    p_init(&msg);
    p_u32(&msg, PING_MAGIC);
    flags = 0;
    if (binder_call(fd, handle, 1, &msg, &reply, &flags) < 0 ||
        (flags & TF_STATUS_CODE)) {
        marker("/data/PING_CALLFAIL");
        return 1;
    }
    if (r_u32(&reply) == PONG_MAGIC && r_u32(&reply) == 777)
        marker("/data/PING_PONG_777");
    else
        marker("/data/PING_BADREPLY");
    free_reply(fd, &reply);
    return 0;
}

int guest_main(int argc, char **argv, char **envp) {
    int i, rc = 1;
    (void)envp;
    for (i = 1; i < argc; i++) {
        if (xstreq(argv[i], "serve")) rc = do_serve();
        else if (xstreq(argv[i], "list")) rc = do_list();
        else if (xstreq(argv[i], "ping")) rc = do_ping();
        else continue;
        break;
    }
    /* Exit through _exit, not by returning: returning runs
     * libc's exit()/__cxa_finalize path, which faults in this
     * freestanding binary (deterministic SIGSEGV at pc=0x4
     * after all work is done; stock guest binaries with the
     * full crtbegin/crtend exit cleanly, and our arrays/table
     * verify byte-identical to theirs -- the divergence is
     * somewhere subtler in the hand-rolled startup and is
     * noted in the S5 spec as an open micro-mystery). paxsvc
     * keeps no stdio/malloc state to flush, so _exit loses
     * nothing. */
    _exit(rc);
    return rc;
}
