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

#include <fcntl.h>
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

    sp<SurfaceControl> ctrl = client->createSurface(
            getpid(), String8("gbprobe"), 0, 64, 64,
            PIXEL_FORMAT_RGBA_8888, 0);
    if (ctrl == NULL) {
        marker_sfx("/data/GB_NOCTRL", sfx);
        return 1;
    }
    marker_sfx("/data/GB_CTRL", sfx);
    ctrl->setLayer(100000);

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
