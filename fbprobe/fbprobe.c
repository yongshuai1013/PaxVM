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

/* ---- framebuffer probe (S6a) ----
 * The scaffolding above (types, memory helpers, the
 * crtbegin replica and its arrays) is shared verbatim with
 * paxsvc. What follows is the framebuffer client: open the
 * virtual /dev/graphics/fb0, ask its geometry, map it, and
 * draw an animated test pattern -- background cycling,
 * white border, checkerboard band, a moving square, and a
 * frame counter as a row of lamps -- flipping between the
 * two pages with FBIOPAN_DISPLAY so the host shell can
 * present the live picture. */

#define FBIOGET_VSCREENINFO 0x4600
#define FBIOPUT_VSCREENINFO 0x4601
#define FBIOGET_FSCREENINFO 0x4602
#define FBIOPAN_DISPLAY 0x4606
#define O_RDWR 2
#define PROT_RW 3
#define MAP_SHARED 1

int nanosleep(const void *req, void *rem);

static void marker(const char *path) { mkdir(path, 0755); }
static char *put_dec(char *out, u32 n) {
    char tmp[12];
    int i = 0;
    if (n == 0) tmp[i++] = '0';
    while (n) {
        tmp[i++] = (char)('0' + (n % 10));
        n /= 10;
    }
    while (i) *out++ = tmp[--i];
    *out = 0;
    return out;
}
static void marker_num(const char *prefix, u32 n) {
    char buf[64];
    char *p = buf;
    while (*prefix) *p++ = *prefix++;
    put_dec(p, n);
    mkdir(buf, 0755);
}

/* Fixed 700ms frame delay, spelled out: a variable divisor
 * would pull __aeabi_uidivmod, which the link-time stub set
 * does not carry (constant divisors compile to multiply
 * sequences and are fine). */
static void sleep_frame(void) {
    u32 ts[2];
    ts[0] = 0;
    ts[1] = 700000000u;
    nanosleep(ts, (void *)0);
}

static u32 px(u32 r, u32 g, u32 b) {
    return 0xFF000000u | (r << 16) | (g << 8) | b;
}

static void draw_frame(u32 *fb, u32 w, u32 h, u32 frame) {
    static const u32 bg[4] = {0x102040u, 0x10301Eu, 0x38141Cu, 0x241038u};
    u32 bgc = bg[frame & 3];
    u32 x, y;
    for (y = 0; y < h; y++) {
        for (x = 0; x < w; x++) {
            u32 c = bgc;
            /* checkerboard band across the middle */
            if (y >= h / 2 - 100 && y < h / 2 + 100) {
                if ((((x / 40) + (y / 40)) & 1) == 0) c = 0xC8C8C8u;
                else c = 0x181818u;
            }
            /* white border, 8 px */
            if (x < 8 || y < 8 || x >= w - 8 || y >= h - 8) c = 0xFFFFFFu;
            fb[y * w + x] = 0xFF000000u | c;
        }
    }
    /* moving white square, 64x64 */
    {
        u32 range = w - 64;
        u32 sx = frame * 23;
        u32 sy = h / 4;
        while (sx >= range) sx -= range;
        u32 dx, dy;
        for (dy = 0; dy < 64; dy++)
            for (dx = 0; dx < 64; dx++)
                fb[(sy + dy) * w + sx + dx] = px(255, 255, 255);
    }
    /* frame counter lamps: 8 squares at top, lit = frame%8+1 */
    {
        u32 lit = (frame % 8) + 1;
        u32 i, dx, dy;
        for (i = 0; i < 8; i++) {
            u32 c = (i < lit) ? px(255, 210, 40) : px(70, 70, 70);
            for (dy = 0; dy < 28; dy++)
                for (dx = 0; dx < 28; dx++)
                    fb[(24 + dy) * w + 24 + i * 40 + dx] = c;
        }
    }
}

static int fb_main(void) {
    u32 var[40];
    u8 fix[68];
    u32 w, h, smem;
    u32 *fb;
    u32 frame;
    int fd;
    fd = open("/dev/graphics/fb0", O_RDWR);
    if (fd < 0) {
        marker("/data/FB_OPENFAIL");
        return 1;
    }
    memset(var, 0, sizeof(var));
    if (ioctl(fd, FBIOGET_VSCREENINFO, var) < 0) {
        marker("/data/FB_VARFAIL");
        return 1;
    }
    memset(fix, 0, sizeof(fix));
    if (ioctl(fd, FBIOGET_FSCREENINFO, fix) < 0) {
        marker("/data/FB_FIXFAIL");
        return 1;
    }
    w = var[0];
    h = var[1];
    smem = *(u32 *)(fix + 20);
    marker_num("/data/FB_W_", w);
    fb = (u32 *)mmap((void *)0, smem, PROT_RW, MAP_SHARED, fd, 0);
    if (fb == (u32 *)-1) {
        marker("/data/FB_MAPFAIL");
        return 1;
    }
    for (frame = 0; frame < 36; frame++) {
        u32 page = frame & 1;
        draw_frame(fb + page * w * h, w, h, frame);
        var[5] = page * h; /* yoffset */
        var[4] = 0;
        ioctl(fd, FBIOPAN_DISPLAY, var);
        if (frame == 0) marker("/data/FB_DRAWN");
        sleep_frame();
    }
    marker_num("/data/FB_FRAMES_", frame);
    return 0;
}

int guest_main(int argc, char **argv, char **envp) {
    int rc;
    (void)argc;
    (void)argv;
    (void)envp;
    rc = fb_main();
    /* Same exit discipline as paxsvc: the plain return path
     * through libc exit() faults in these freestanding
     * binaries (open micro-mystery, see the S5 spec). */
    _exit(rc);
    return rc;
}
