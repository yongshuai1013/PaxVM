// gbprobe: a white-box walk through the guest's real
// graphics client stack (libsurfaceflinger_client), one
// marker directory per step, in the paxsvc/lbprobe style.
// bootanimation dies somewhere between createSurface and
// its first posted frame; this probe walks the same road
// with the lights on:
//
//   GB_CLIENT_n   SurfaceComposerClient constructed OK
//   GB_CTRL_n     createSurface returned a control
//   GB_SURF_n     control->getSurface() non-null
//   GB_LOCK_n     Surface::lock succeeded (bits in marker)
//   GB_POST_n     unlockAndPost done
//   GB_ROUND2_n   a second lock/post cycle done
//
// Modes via argv scan: "gprobe" runs the walk once for a
// 64x64 RGBA surface. Suffix n distinguishes rounds.

#include <surfaceflinger/SurfaceComposerClient.h>
#include <surfaceflinger/Surface.h>
#include <utils/String8.h>
#include <ui/PixelFormat.h>
#include <ui/DisplayInfo.h>

// The server control block layout, from
// private/surfaceflinger/SharedBufferStack.h
// (android-2.3.7_r1): a connected byte, padding, then
// one display block per display. Declared locally so
// this probe does not drag that header's whole chain
// in; only displays[0].w/h are read.
struct gb_display_cblk_t {
    uint16_t w;
    uint16_t h;
    uint8_t format;
    uint8_t orientation;
    uint8_t reserved[2];
    float fps;
    float density;
    float xdpi;
    float ydpi;
    uint32_t pad[2];
};
struct gb_cblk_t {
    uint8_t connected;
    uint8_t reserved[3];
    uint32_t pad[7];
    gb_display_cblk_t displays[4];
};

#include <fcntl.h>
#include <stdint.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>

using namespace android;

// Gun 5 test card (the user's call): stop chasing the
// dim boot wordmark -- draw one big bright circle
// instead. Transparent elsewhere, opaque white disc
// of radius min(w,h)/4 at the center: unmissable in
// the preview, and its bounding box and pixel count
// are known exactly, so the supervisor's page census
// can verdict composition without eyeballing shades
// of black.
static void paint_circle(Surface::SurfaceInfo &info) {
    uint32_t *px = (uint32_t *)info.bits;
    const int cx = (int)info.w / 2;
    const int cy = (int)info.h / 2;
    const int r = (int)(info.w < info.h ? info.w : info.h) / 4;
    for (uint32_t y = 0; y < info.h; y++) {
        for (uint32_t x = 0; x < info.w; x++) {
            const int dx = (int)x - cx;
            const int dy = (int)y - cy;
            px[y * info.s + x] = (dx * dx + dy * dy <= r * r)
                ? 0xFFFFFFFFu : 0x00000000u;
        }
    }
}

static void marker(const char *path) { mkdir(path, 0); }

static void marker_sfx(const char *base, const char *sfx) {
    char buf[96];
    int i = 0;
    while (*base) buf[i++] = *base++;
    while (*sfx) buf[i++] = *sfx++;
    buf[i] = 0;
    mkdir(buf, 0);
}

static void marker_val(const char *base, unsigned n, const char *sfx) {
    char buf[96];
    int i = 0;
    while (*base) buf[i++] = *base++;
    char dig[12];
    int d = 0;
    if (n == 0) dig[d++] = '0';
    while (n > 0) {
        dig[d++] = (char)('0' + (n % 10));
        n /= 10;
    }
    while (d > 0) buf[i++] = dig[--d];
    while (*sfx) buf[i++] = *sfx++;
    buf[i] = 0;
    mkdir(buf, 0);
}

extern "C" int guest_main(int argc, char **argv, char **envp) {
    const char *sfx = "_1";
    for (int i = 0; i < argc; i++) {
        if (argv[i][0] == 'r' && argv[i][1] >= '0' && argv[i][1] <= '9'
                && argv[i][2] == 0) {
            static char b[3] = "_1";
            b[1] = argv[i][1];
            sfx = b;
        }
    }

    sp<SurfaceComposerClient> client = new SurfaceComposerClient();
    if (client->initCheck() != NO_ERROR) {
        marker_sfx("/data/GB_NOCLIENT", sfx);
        return 1;
    }
    marker_sfx("/data/GB_CLIENT", sfx);

    // createSurface came back empty for us while the
    // animation client's first attempt in a fresh flinger
    // got a full reply. Bisect: retry the same parameters,
    // then fall back to the animation's full-screen size.
    sp<SurfaceControl> ctrl;
    int tries_small = 0;
    while (tries_small < 5) {
        ctrl = client->createSurface(
                getpid(), String8("gbprobe"), 0, 480, 800,
                PIXEL_FORMAT_RGBA_8888, 0);
        if (ctrl != NULL) break;
        tries_small++;
        sleep(1);
    }
    if (ctrl != NULL) {
        marker_sfx(tries_small == 0 ? "/data/GB_CTRL" : "/data/GB_CTRL_RETRY", sfx);
    } else {
        marker_sfx("/data/GB_NOCTRL", sfx);
        int tries_big = 0;
        while (tries_big < 5) {
            ctrl = client->createSurface(
                    getpid(), String8("gbprobe"), 0, 64, 64,
                    PIXEL_FORMAT_RGBA_8888, 0);
            if (ctrl != NULL) break;
            tries_big++;
            sleep(1);
        }
        if (ctrl == NULL) {
            marker_sfx("/data/GB_NOCTRL_BIG", sfx);
            return 1;
        }
        marker_sfx("/data/GB_CTRL_BIG", sfx);
    }

    // The library's Surface::init() reads the server
    // control block (via getDisplayInfo) as its very
    // first step; both guest graphics clients die there.
    // Inspect that pointer with our own hands first --
    // classified, never dereferenced while it looks bad:
    //   GB_CBLK_NULL   the pointer is NULL
    //   GB_CBLK_BAD    the pointer is -1 (a failed mmap
    //                  of the received heap, whose fd
    //                  never became ours)
    //   GB_CBLK_OK + GB_DW_<w> + GB_DH_<h>
    //                  a live block; the display size it
    //                  carries (expect 480x800)
    {
        volatile gb_cblk_t const *cblk =
                (volatile gb_cblk_t const *)
                        ComposerService::getControlBlock();
        if (cblk == NULL) {
            marker_sfx("/data/GB_CBLK_NULL", sfx);
            return 1;
        }
        if ((const void *)cblk == (const void *)(uintptr_t)-1) {
            marker_sfx("/data/GB_CBLK_BAD", sfx);
            return 1;
        }
        marker_sfx("/data/GB_CBLK_OK", sfx);
        marker_val("/data/GB_DW_", cblk->displays[0].w, sfx);
        marker_val("/data/GB_DH_", cblk->displays[0].h, sfx);
        DisplayInfo dinfo;
        if (SurfaceComposerClient::getDisplayInfo(0, &dinfo) == NO_ERROR) {
            marker_sfx("/data/GB_DINFO_OK", sfx);
        } else {
            marker_sfx("/data/GB_DINFO_FAIL", sfx);
        }
    }

    // Above bootanimation's 0x40000000: its opaque black
    // surface must not cover the test circle (gun 5).
    // SurfaceControl::setLayer only ACCUMULATES the state
    // into the client's batch (SurfaceComposerClient::
    // setLayer -> lockLayerState); it reaches SF solely
    // when closeTransaction() sends SET_STATE. Bare calls
    // (as here through 0.9.43) never leave the process --
    // that, not any binder fault, is why the layer stayed
    // at the default z under the animation's opaque plane.
    client->openTransaction();
    ctrl->setLayer(0x40000001);
    client->closeTransaction();
    marker_sfx("/data/GB_LAYER", sfx);

    sp<Surface> surf = ctrl->getSurface();
    if (surf == NULL) {
        marker_sfx("/data/GB_NOSURF", sfx);
        return 1;
    }
    marker_sfx("/data/GB_SURF", sfx);

    Surface::SurfaceInfo info;
    status_t st = surf->lock(&info);
    if (st != NO_ERROR || info.bits == NULL) {
        marker_sfx("/data/GB_NOLOCK", sfx);
        return 1;
    }
    marker_sfx("/data/GB_LOCK", sfx);

    paint_circle(info);
    marker_sfx("/data/GB_DRAWN", sfx);

    st = surf->unlockAndPost();
    if (st != NO_ERROR) {
        marker_sfx("/data/GB_NOPOST", sfx);
        return 1;
    }
    marker_sfx("/data/GB_POST", sfx);

    Surface::SurfaceInfo info2;
    st = surf->lock(&info2);
    if (st == NO_ERROR && info2.bits != NULL) {
        // Repaint: round 2 posts the OTHER buffer, and
        // posting it blank would erase the circle from
        // the composition for the rest of the run.
        paint_circle(info2);
        surf->unlockAndPost();
        marker_sfx("/data/GB_ROUND2", sfx);
    } else {
        marker_sfx("/data/GB_NOLOCK2", sfx);
        return 1;
    }

    // Gun 5, closing form: the two proof rounds above
    // are the verdict (GB_OK below); this loop only
    // keeps the picture on screen until the scene is
    // stopped, so it can be looked at in the shell
    // preview at leisure. (History: the 'band' of the
    // 0.9.38 run was the boot animation's own wordmark,
    // not a clipped circle; the circle was absent
    // because this layer sat under the animation's
    // opaque plane -- its setLayer had never been
    // wrapped in a transaction. 0.9.44 field run:
    // circle + wordmark composited together, 45237 px,
    // 16 consecutive censuses.)
    marker_sfx("/data/GB_OK", sfx);
    for (;;) {
        Surface::SurfaceInfo inf;
        st = surf->lock(&inf);
        if (st != NO_ERROR || inf.bits == NULL) break;
        paint_circle(inf);
        if (surf->unlockAndPost() != NO_ERROR) break;
        usleep(100 * 1000);
    }
    return 0;
}
