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
                getpid(), String8("gbprobe"), 0, 64, 64,
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
                    getpid(), String8("gbprobe"), 0, 480, 800,
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

    ctrl->setLayer(100000);
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

    // Paint a solid color over the whole 64x64 surface.
    {
        uint32_t *px = (uint32_t *)info.bits;
        for (uint32_t y = 0; y < info.h; y++) {
            for (uint32_t x = 0; x < info.w; x++) {
                px[y * info.s + x] = 0xFF00FF00u;
            }
        }
    }
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
        surf->unlockAndPost();
        marker_sfx("/data/GB_ROUND2", sfx);
    } else {
        marker_sfx("/data/GB_NOLOCK2", sfx);
        return 1;
    }

    marker_sfx("/data/GB_OK", sfx);
    return 0;
}
