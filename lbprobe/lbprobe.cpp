// lbprobe: a real libbinder client/server pair, linked
// against the guest's own libbinder.so/libutils.so (via
// generated symbol stubs at build time; the guest linker
// binds the real libraries at run time). It exists to prove
// the supervisor's virtual binder driver speaks the full
// protocol the stock C++ binder stack expects --
// IPCThreadState's command loop, ProcessState's driver
// session, BpServiceManager's registry calls -- not just
// the raw binder.c subset paxsvc exercises.
//
// Modes (evidence = /data marker directories, as with
// paxsvc):
//   serve  addService("lbpax") then join the thread pool
//          and answer PING transactions -> LB_READY
//   list   listServices count -> LB_LIST_N_<n>
//   ping   getService + transact(PING) -> LB_GOT,
//          LB_PING_PONG_777 on the expected reply

#include <binder/IServiceManager.h>
#include <binder/IBinder.h>
#include <binder/Binder.h>
#include <binder/Parcel.h>
#include <binder/ProcessState.h>
#include <binder/IPCThreadState.h>
#include <utils/String16.h>
#include <utils/Vector.h>

#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

using namespace android;

static const int32_t PING_MAGIC = 0x50494E47; /* "PING" */
static const int32_t PONG_MAGIC = 0x504F4E47; /* "PONG" */

static void marker(const char *path) { mkdir(path, 0); }

static void marker_num(const char *prefix, unsigned n) {
    char buf[64];
    int i = 0;
    while (*prefix) buf[i++] = *prefix++;
    char dig[12];
    int d = 0;
    if (n == 0) dig[d++] = '0';
    while (n > 0) {
        dig[d++] = (char)('0' + (n % 10));
        n /= 10;
    }
    while (d > 0) buf[i++] = dig[--d];
    buf[i] = 0;
    mkdir(buf, 0);
}

class PaxObj : public BBinder {
public:
    virtual status_t onTransact(uint32_t code, const Parcel &data,
                                Parcel *reply, uint32_t flags) {
        if (code == 1) {
            int32_t v = 0;
            if (data.readInt32(&v) == OK && v == PING_MAGIC) {
                reply->writeInt32(PONG_MAGIC);
                reply->writeInt32(777);
                return OK;
            }
            return UNKNOWN_TRANSACTION;
        }
        return BBinder::onTransact(code, data, reply, flags);
    }
};

static int do_serve(void) {
    sp<ProcessState> proc = ProcessState::self();
    sp<IServiceManager> sm = defaultServiceManager();
    if (sm == NULL) {
        marker("/data/LB_NOSM");
        return 1;
    }
    status_t st = sm->addService(String16("lbpax"), new PaxObj());
    if (st != OK) {
        marker_num("/data/LB_ADDFAIL_", (unsigned)-st);
        return 1;
    }
    marker("/data/LB_READY");
    proc->startThreadPool();
    IPCThreadState::self()->joinThreadPool();
    return 0;
}

static int do_list(void) {
    sp<IServiceManager> sm = defaultServiceManager();
    if (sm == NULL) {
        marker("/data/LB_NOSM");
        return 1;
    }
    Vector<String16> names = sm->listServices();
    marker_num("/data/LB_LIST_N_", (unsigned)names.size());
    return 0;
}

static int do_ping(void) {
    sp<IServiceManager> sm = defaultServiceManager();
    if (sm == NULL) {
        marker("/data/LB_NOSM");
        return 1;
    }
    sp<IBinder> b = sm->getService(String16("lbpax"));
    if (b == NULL) {
        marker("/data/LB_NOSVC");
        return 1;
    }
    marker("/data/LB_GOT");
    Parcel data, reply;
    data.writeInt32(PING_MAGIC);
    status_t st = b->transact(1, data, &reply);
    if (st != OK) {
        marker_num("/data/LB_CALLFAIL_", (unsigned)-st);
        return 1;
    }
    int32_t a = 0, c = 0;
    if (reply.readInt32(&a) == OK && reply.readInt32(&c) == OK &&
        a == PONG_MAGIC && c == 777) {
        marker("/data/LB_PING_PONG_777");
        return 0;
    }
    marker("/data/LB_BADREPLY");
    return 1;
}

static int xstreq(const char *a, const char *b) {
    while (*a && *a == *b) {
        a++;
        b++;
    }
    return *a == *b;
}

extern "C" int guest_main(int argc, char **argv, char **envp) {
    (void)envp;
    int rc = 1;
    for (int i = 1; i < argc; i++) {
        if (xstreq(argv[i], "serve"))
            rc = do_serve();
        else if (xstreq(argv[i], "list"))
            rc = do_list();
        else if (xstreq(argv[i], "ping"))
            rc = do_ping();
        else
            continue;
        break;
    }
    _exit(rc);
    return rc;
}
