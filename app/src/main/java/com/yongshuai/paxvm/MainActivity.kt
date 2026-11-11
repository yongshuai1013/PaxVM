package com.yongshuai.paxvm

import android.app.Activity
import android.app.ActivityManager
import android.app.ApplicationExitInfo
import android.content.ClipData
import android.content.ClipboardManager
import android.content.ContentValues
import android.content.Context
import android.graphics.Typeface
import android.os.Build
import android.os.Bundle
import android.os.Environment
import android.provider.MediaStore
import android.system.Os
import android.text.method.ScrollingMovementMethod
import android.view.Gravity
import android.widget.Button
import android.widget.LinearLayout
import android.graphics.Bitmap
import android.widget.ImageView
import android.widget.ScrollView
import android.widget.TextView
import java.io.RandomAccessFile
import java.nio.ByteBuffer
import java.io.IOException
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.io.File
import java.io.FileOutputStream
import java.io.OutputStream
import java.util.zip.ZipInputStream
import kotlin.concurrent.thread

/**
 * PaxVM M1 shell.
 *
 * Deliberately has zero JNI: the engine lives in a standalone native
 * process (libsupervisor.so, a Rust ptrace supervisor) that the shell
 * starts with ProcessBuilder and talks to only through its stdout
 * line protocol ([sup] / [sys] / [guest] lines, printed verbatim).
 *
 * M1 session: the guest root is the static busybox binary
 * (libbusybox.so) running `sh /verify.sh` inside the prepared
 * rootfs; the supervisor traces the whole process tree and rewrites
 * applet execs to the nativeLibraryDir busybox (M1 spec section 2).
 *
 * 0.2.8 adds a second entry: the same session with a 32-bit ARM
 * busybox guest (libbusybox32.so) in its own rootfs, probing the
 * supervisor's compat-personality support (gingerbread spike S2).
 *
 * 0.3.0 adds the S3a entry: Android 2.3.7's init (libgbinit.so,
 * the static init from Google's API 10 SDK system image) as the
 * guest root in its own rootfs, with a minimal init.rc and one
 * busybox service as the probe. The supervisor is told via --bb
 * that applet execs still belong to libbusybox32.so. When the
 * session ends, the shell dumps the guest's captured kernel log
 * (rootfsGB/.kmsg, fed by the supervisor's /dev/__kmsg__
 * redirection) into the log view as [init] lines.
 */
class MainActivity : Activity() {

    private lateinit var statusView: TextView
    private lateinit var logView: TextView
    private lateinit var scrollView: ScrollView
    private lateinit var fbView: ImageView

    // Session log file (0.9.23): every log line is also
    // written straight to filesDir/session-log.txt,
    // unbuffered, so a frozen or killed UI cannot take the
    // session's evidence with it. On launch, the previous
    // launch's file is rotated to previous-session-log.txt
    // and 下載日誌 serves it when this launch has not run
    // a session yet (the force-stop-and-reopen recovery).
    private var logFileOut: OutputStream? = null
    // 0.9.54 batching: pending session-log text (guarded
    // by logFileLock, flushed at 64 KB / 250 ms) and
    // pending on-screen text (same lock, flushed to the
    // TextView at most every 250 ms).
    private val pendingLogText = StringBuilder()
    private val pendingUiText = StringBuilder()
    private var uiFlushPosted = false
    private val logFileLock = Object()
    private var previousLogFile: File? = null
    private var sessionLogFileRef: File? = null
    // 0.9.78 live log locations: the session log streams
    // into Download/PaxVM-logs-<launch time>/ through the
    // MediaStore uri below (null in the private-file
    // fallback), and the supervisor's direct mirror logs
    // stream into the same-named directory under the
    // app's external files dir (Android/data), which the
    // shell passes to the supervisor as --logdir.
    @Volatile
    private var liveLogUri: android.net.Uri? = null
    @Volatile
    private var liveLogDirName: String? = null
    @Volatile
    private var mirrorLogDir: File? = null
    private var sessionRan = false

    // On-screen log flood guards (0.9.23): exact-repeat
    // lines collapse, the view is trimmed when huge (a
    // TextView append re-lays-out the whole text, so an
    // unbounded view freezes the UI under a log storm),
    // and scrolls coalesce. The file keeps everything.
    private var lastUiLine: String? = null
    private var dupLineCount = 0

    /** Rootfs of the GB session whose framebuffer is being
     * previewed, or null. The preview thread polls while its
     * captured rootfs is still the current session. */
    @Volatile
    private var fbSession: File? = null
    private var fbBitmap: Bitmap? = null
    private lateinit var startButton: Button
    private lateinit var probeButton: Button
    private lateinit var gbButton: Button
    private lateinit var stopButton: Button
    private lateinit var copyButton: Button
    private lateinit var saveButton: Button

    private var supervisor: Process? = null
    @Volatile
    private var startupDiagnostics: StartupDiagnostics.Session? = null

    // S10 I1 (s10-perf-desk section 3): the field
    // clock on the shell side -- System.nanoTime
    // (CLOCK_MONOTONIC, the supervisor's own clock
    // source) captured at each supervisor launch.
    // The heartbeat prints the elapsed as t=<ms>
    // beside the supervisor's account stamps.
    @Volatile
    private var fieldStartNanos: Long = 0

    private val rootfsDir: File
        get() = File(filesDir, "vm0/rootfs")

    /** Separate rootfs for the 32-bit probe: its /bin symlinks are
     * resolved by the supervisor to libbusybox32.so, so the two
     * guests never share a tree. */
    private val rootfs32Dir: File
        get() = File(filesDir, "vm0/rootfs32")

    /** Gingerbread guest rootfs (S3a): Android 2.3.7 init's tree. */
    private val rootfsGBDir: File
        get() = File(filesDir, "vm0/rootfsGB")

    /** Minimal init.rc for the S3a probe: no ueventd (netlink
     * coldplug is a later phase), no mounts (the supervisor
     * answers -ENOSYS and init carries on), stage markers as
     * properties, and one oneshot busybox service as the proof
     * that init's service machinery works under supervision.
     * Rewritten on every GB start, like verify.sh. */
    private val gbInitRc: String = listOf(
        // No setprop in early-init: 2.3's property_set writes
        // through pa_info_array, which is null until the
        // property_init builtin runs (queued after the
        // early-init actions) — a setprop there segfaults init
        // (proven in the 0.3.1 device run; the stock rc's
        // early-init likewise contains no setprop). The write
        // builtin is safe at any stage and leaves evidence.
        "on early-init",
        "    write /probe-early-init.txt ok",
        "",
        "on init",
        "    loglevel 7",
        "    export PATH /sbin:/bin:/system/bin",
        "    export ANDROID_ROOT /system",
        "    export ANDROID_DATA /data",
        // S7 gun 4: the missing export that killed every
        // zygote. Stock GB init.rc exports LD_LIBRARY_PATH
        // /system/lib; Dalvik derives java.library.path --
        // the System.loadLibrary search path for JNI libs
        // -- from it. Without it the path is empty and
        // preloadClasses died at android.media.AmrInputStream
        // with 'UnsatisfiedLinkError: Library media_jni not
        // found; tried [/libmedia_jni.so]' (the guest log's
        // own words, 0.9.52 field run). The native linker
        // never cared -- it has /system/lib built in --
        // which is why every .so loaded fine and only the
        // Java-side JNI loads starved.
        "    export LD_LIBRARY_PATH /system/lib",
        // S7: the stock BOOTCLASSPATH (ramdisk init.rc:20);
        // app_process starts the VM with no boot classpath
        // at all when the variable is missing.
        "    export BOOTCLASSPATH /system/framework/core.jar:/system/framework/bouncycastle.jar:/system/framework/ext.jar:/system/framework/framework.jar:/system/framework/android.policy.jar:/system/framework/services.jar:/system/framework/core-junit.jar",
        "    mkdir /data/misc",
        // S7: the /data skeleton zygote expects to exist
        // (stock init.rc creates these in `on init`).
        "    mkdir /data/dalvik-cache 0771",
        "    mkdir /data/system",
        "    mkdir /data/data",
        "    mkdir /data/app",
        "    mkdir /data/local",
        // Freeze forensics (0.9.81): Dalvik writes its
        // ANR / SIGQUIT stack traces under /data/anr
        // (the stock rc creates the directory too);
        // without it the dump the overflow menu can ask
        // for has nowhere to land.
        "    mkdir /data/anr 0771",
        "    setprop pax.stage init",
        "",
        "on fs",
        "    setprop pax.stage fs",
        "",
        "on boot",
        // S8 gun 3: the stock OOM-adjustment properties
        // (AOSP 2.3.7 rootdir/init.rc `on boot`). Our
        // trimmed rc never set them, and
        // ActivityManagerService's static initializer
        // parses every one of them as an integer --
        // SystemProperties.get returns "" for a missing
        // property, Integer.valueOf("") throws, and the
        // resulting ExceptionInInitializerError is a
        // FATAL EXCEPTION IN SYSTEM PROCESS: with the
        // capset abort fixed (0.9.79), system_server
        // entered, started its first services, and died
        // on exactly this, 19 zygote tenures in a row.
        // The stock rc sets them at `on boot` before any
        // service starts; same placement here.
        "    setprop ro.FOREGROUND_APP_ADJ 0",
        "    setprop ro.VISIBLE_APP_ADJ 1",
        "    setprop ro.PERCEPTIBLE_APP_ADJ 2",
        "    setprop ro.HEAVY_WEIGHT_APP_ADJ 3",
        "    setprop ro.SECONDARY_SERVER_ADJ 4",
        "    setprop ro.BACKUP_APP_ADJ 5",
        "    setprop ro.HOME_APP_ADJ 6",
        "    setprop ro.HIDDEN_APP_MIN_ADJ 7",
        "    setprop ro.EMPTY_APP_ADJ 15",
        "    setprop ro.FOREGROUND_APP_MEM 2048",
        "    setprop ro.VISIBLE_APP_MEM 3072",
        "    setprop ro.PERCEPTIBLE_APP_MEM 4096",
        "    setprop ro.HEAVY_WEIGHT_APP_MEM 4096",
        "    setprop ro.SECONDARY_SERVER_MEM 6144",
        "    setprop ro.BACKUP_APP_MEM 6144",
        "    setprop ro.HOME_APP_MEM 6144",
        "    setprop ro.HIDDEN_APP_MEM 7168",
        "    setprop ro.EMPTY_APP_MEM 8192",
        "    setprop pax.stage boot",
        "    start servicemanager",
        "    start vold",
        "    start netd",
        "    start installd",
        "    start media",
        "    start surfaceflinger",
        "    start zygote",
        "    start bootanimation",
        "    start gbprobe",
        "    start paxprobe",
        "",
        "service paxprobe /bin/sh /probe.sh",
        "    oneshot",
        "",
        // S5: the real servicemanager, served by the
        // supervisor's virtual binder driver. Not oneshot:
        // init restarts it if it ever exits.
        "service servicemanager /system/bin/servicemanager",
        "",
        // S6b/c: the real SurfaceFlinger. It composes
        // through the stock gralloc framebuffer HAL onto
        // the supervisor's virtual fb0; the shell presents
        // the pages. Run as root for this round (stock rc
        // drops to system/graphics; credential switching
        // is a later refinement, not this round's variable).
        "service surfaceflinger /system/bin/surfaceflinger",
        "",
        // S6 gun 4 (0.9.3): the boot animation as a real
        // init service -- the stock arrangement -- started
        // in parallel at boot instead of trailing the probe
        // sequence. A wrapper script retries while SF is
        // not yet registered (asked a moment too early, the
        // binary exits at once); once connected it stays
        // up for the whole session.
        // The stock init.rc runs the animation as the
        // graphics user, and that uid is load-bearing:
        // createSurface skips its package-manager
        // permission check only for AID_GRAPHICS callers,
        // and there is no package service in this guest to
        // answer the check.
        "service bootanimation /bin/sh /bootanim.sh",
        "    user graphics",
        "    group graphics",
        "",
        // S6 gun 4 (0.9.21): the graphics probe as its own
        // init service under the graphics identity, for the
        // same load-bearing reason as bootanimation above:
        // run from the root probe script, createSurface's
        // permission check parks SurfaceFlinger's thread in
        // libbinder's getService("permission") wait loop
        // forever -- that service never registers here.
        // The probe waits for SurfaceFlinger itself, so it
        // can start with the rest.
        "service gbprobe /system/bin/gbprobe gprobe r1",
        "    user graphics",
        "    group graphics",
        "    oneshot",
        "",
        // S7 gun 1: the real zygote, standing alone. The
        // socket line makes the stock init create
        // /dev/socket/zygote and hand app_process the fd,
        // exactly as on hardware. No user line: root, as
        // in the stock rc. The stock onrestart /sys writes
        // are omitted -- this guest has no real sysfs for
        // them to land on.
        // S8 gun 1 (2026-11-07): --start-system-server.
        // Zygote forks system_server (no exec: the child
        // stays in zygote's shard, W3); GB semantics say
        // a system_server death takes zygote down with
        // it, so zygote restart loops in the log are the
        // amplified failure signal. Spec:
        // vm-engine-research/s8-system-server-spec.md.
        "service zygote /system/bin/app_process -Xzygote /system/bin --zygote --start-system-server",
        "    socket zygote stream 666",
        "",
        // S9 (0.9.83): the stock daemons the service
        // march waits on. Their binaries have been in
        // the payload since the root tree was completed
        // (0.9.81); what was missing is these service
        // definitions -- init creates the /dev/socket
        // endpoints and hands over the listening fds.
        // Lines copied from the stock rc
        // (android-2.3.7_r1 rootdir/init.rc).
        // NetworkManagementService.create() awaits a
        // latch that only its netd connector's first
        // successful exchange counts down; with no netd
        // running, the 0.9.82 field's ServerThread
        // waited on that latch forever. MountService's
        // vold connector and the package manager's
        // installd connector are the same shape, a few
        // checkpoints further on.
        "service vold /system/bin/vold",
        "    socket vold stream 0660 root mount",
        "    ioprio be 2",
        "",
        "service netd /system/bin/netd",
        "    socket netd stream 0660 root system",
        "",
        "service installd /system/bin/installd",
        "    socket installd stream 600 system system",
        "",
        // S9 (0.9.86): mediaserver, stock lines. The
        // service march's Audio Service step blocks in
        // waitForService("media.audio_policy") until
        // mediaserver publishes the audio policy and
        // flinger services (0.9.85 field: 172 waits,
        // march parked there for the rest of the
        // session). Its ioprio line is survivable now
        // that the supervisor fakes ioprio_set.
        "service media /system/bin/mediaserver",
        "    user media",
        "    group system audio camera graphics inet net_bt net_bt_admin net_raw",
        "    ioprio rt 4",
        "",
        // Stock boot-completion trigger, adapted to
        // our animation service's name: when the
        // framework reports boot finished, init stops
        // the boot animation (on hardware the service
        // is called bootanim; ours is bootanimation).
        "on property:service.bootanim.exit=1",
        "    stop bootanimation",
        "",
    ).joinToString("\n")

    /** The probe service's script: its file write and the
     * supervisor's syscall log are the evidence (service stdio
     * goes to /dev/null under init). */
    /** S4 probe: after the static checks, exercise the dynamic
     * world — getprop/setprop are toolbox symlinks (dynamic,
     * bionic) run through the supervisor's gbloader reroute, and
     * servicemanager is started to record where the binder wall
     * is. A service's stdio is /dev/null, so values the probe
     * learns are encoded into mkdir paths, which the supervisor
     * log shows verbatim. */
    private val gbProbeScript: String = listOf(
        "echo paxprobe-begin",
        "echo paxprobe-ok > /data/probe-ok.txt",
        "cat /data/probe-ok.txt",
        "V=$(/system/bin/getprop pax.stage)",
        "mkdir /data/STAGE_IS_\$V",
        "/system/bin/setprop debug.fromprobe yes",
        "W=$(/system/bin/getprop debug.fromprobe)",
        "mkdir /data/FROMPROBE_IS_\$W",
        // S5c: death processing end to end, then the S5b
        // chain as regression. serveonce registers "paxsvc"
        // and exits at once: the manager's death watch must
        // fire, after which GET returns the null form
        // (GONE_OK) while the name stays listed (LISTD_N_1 --
        // stock 2.3 manager keeps the entry, pointer zeroed).
        // Then a resident serve revives the name and the
        // original S5b evidence must land again.
        "/system/bin/paxsvc serveonce",
        "sleep 1",
        "/system/bin/paxsvc listd",
        "/system/bin/paxsvc pinggone",
        "/system/bin/paxsvc serve &",
        "sleep 1",
        "/system/bin/paxsvc list",
        "/system/bin/paxsvc ping",
        // S5c (cont.): the same registry through the guest's
        // real C++ binder stack (libbinder/libutils): serve
        // publishes "lbpax" via addService and joins the
        // thread pool; list counts via listServices; ping
        // does getService + a raw transact and checks the
        // reply. Evidence markers carry the LB_ prefix.
        "/system/bin/lbprobe serve &",
        "sleep 1",
        "/system/bin/lbprobe list",
        "/system/bin/lbprobe ping",
        // S6a: the framebuffer probe drew an animated test
        // pattern directly into the virtual fb0. Since gun 5
        // (0.9.34) it stays OFF in this scene: the preview
        // must show only what SurfaceFlinger composes, with
        // no direct writer fighting it for the display --
        // the 0.9.33 screenshot was fbprobe's test card, not
        // a composition, and it briefly fooled us.
        // "/system/bin/fbprobe &",
        // S6b/c late census: by now SurfaceFlinger has had
        // the whole probe run to come up and register; a
        // second list (LB2 prefix, so it cannot blur the
        // S5c-era count) should see it.
        "sleep 5",
        "/system/bin/lbprobe list2",
        // S6 gun 4 white-box: gbprobe walks the real
        // graphics client stack step by step (GB_ markers)
        // as its own init service (see gbInitRc) under the
        // graphics identity, so nothing runs it from here.
        // S6 gun 4: the boot animation is SurfaceFlinger's
        // first real client; its gralloc buffers reach SF
        // inside binder parcels -- the FD-passing path
        // (field-proven 0.9.1: SF's reply fd 9 became the
        // client's fd 4). Since 0.9.3 it runs as an init
        // service (see gbInitRc), not from this probe
        // script, so nothing here waits for it.
        "ls /",
        "echo paxprobe-end",
    ).joinToString("\n", postfix = "\n")

    /** Applet names linked to busybox inside the guest rootfs. */
    private val applets = listOf(
        "sh", "ls", "cat", "wc", "echo", "pwd", "mkdir", "rmdir",
        "touch", "rm", "cp", "mv", "ln", "uname", "printf", "head",
        "tail", "grep", "sort", "uniq", "chmod", "env", "sleep",
        "id", "basename", "dirname", "readlink", "stat", "true",
        "false", "test",
    )

    /** M1 acceptance script (M1 spec section 5). Rewritten into the
     * rootfs on every start so it always matches the supervisor. */
    private val verifyScript: String = listOf(
        "echo BB_START",
        "pwd",
        "echo \"ROOTPID=\$\$\"",
        "cat /seed.txt",
        "cd /tmp",
        "pwd",
        "echo hello-busybox > out.txt",
        "cat out.txt",
        "ls /bin",
        "/bin/ls /tmp",
        "echo abcdef | wc -c",
        "mkdir -p /tmp/d1",
        "touch /tmp/d1/f.txt",
        "ls /tmp/d1",
        "rm /tmp/d1/f.txt",
        "rmdir /tmp/d1",
        "uname",
        "echo BB_DONE",
    ).joinToString("\n", postfix = "\n")

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        initLogFiles()
        installCrashRecorder()
        thread(name = "exitinfo", isDaemon = true) {
            reportPreviousExits()
        }
        buildUi()
        prepareRootfs(rootfsDir)
        statusView.text = "rootfs: ${rootfsDir.absolutePath}\n狀態：待命"
        val prev = previousLogFile
        if (prev != null && prev.exists() && prev.length() > 0) {
            appendLog("[shell] 上一場的日誌已保留（${prev.length()} 位元組）；本場未啟動前按「下載日誌」可取得")
        }
        val liveDir = liveLogDirName
        if (liveDir != null) {
            appendLog("[shell] 本場日誌即時寫入 Download/$liveDir/session-log.txt；監督器鏡像即時寫入 Android/data 的同名目錄")
        }
    }

    /** Open this launch's session log writer. Since
     * 0.9.78 the session log is written LIVE into its
     * own directory under Download
     * (Download/PaxVM-logs-<launch time>/session-log.txt,
     * through a MediaStore stream), so the record is
     * already where the user can reach it while the
     * session runs, and an app death cannot trap it
     * behind a reopened app's export step. The
     * supervisor's direct mirrors cannot use MediaStore
     * (native processes, no Java API), so they are
     * written live to the same-named directory in the
     * app's external files dir instead (Android/data;
     * see setupMirrorDir). If the Download stream
     * cannot be opened, or the device predates the
     * MediaStore Downloads collection, logging falls
     * back to the pre-0.9.78 private files with their
     * rotation, unchanged. Never throws: logging must
     * not be able to take the app down. */
    private fun initLogFiles() {
        try {
            val stamp = SimpleDateFormat(
                "yyyyMMdd-HHmmss", Locale.US,
            ).format(Date())
            val dirName = "PaxVM-logs-$stamp"
            var live = false
            if (Build.VERSION.SDK_INT >= 29) {
                try {
                    val values = ContentValues().apply {
                        put(
                            MediaStore.Downloads.DISPLAY_NAME,
                            "session-log.txt",
                        )
                        put(
                            MediaStore.Downloads.MIME_TYPE,
                            "text/plain",
                        )
                        put(
                            MediaStore.Downloads.RELATIVE_PATH,
                            Environment.DIRECTORY_DOWNLOADS +
                                "/" + dirName,
                        )
                    }
                    val uri = contentResolver.insert(
                        MediaStore.Downloads
                            .EXTERNAL_CONTENT_URI,
                        values,
                    )
                    val out = if (uri != null) {
                        contentResolver.openOutputStream(
                            uri, "w",
                        )
                    } else {
                        null
                    }
                    if (uri != null && out != null) {
                        liveLogUri = uri
                        liveLogDirName = dirName
                        logFileOut = out
                        live = true
                    }
                } catch (e: Exception) {
                    // Fall through to the private file.
                }
            }
            if (!live) {
                val cur = File(filesDir, "session-log.txt")
                val prev = File(
                    filesDir, "previous-session-log.txt",
                )
                if (cur.exists() && cur.length() > 0) {
                    if (prev.exists()) prev.delete()
                    cur.renameTo(prev)
                    previousLogFile = prev
                }
                sessionLogFileRef = cur
                logFileOut = FileOutputStream(cur, true)
            } else {
                // Freeze the legacy private logs: the old
                // rotation would overwrite the previous
                // session here, and it may still hold
                // unretrieved crash evidence. They are
                // copied into this launch's Download
                // directory instead (migrateLegacyLogs).
                val prev = File(
                    filesDir, "previous-session-log.txt",
                )
                if (prev.exists() && prev.length() > 0) {
                    previousLogFile = prev
                }
                migrateLegacyLogs(dirName)
            }
            setupMirrorDir(dirName)
            // The 0.9.54 batching flusher: lands buffered
            // session-log lines every 250 ms so the file
            // trails reality by at most a quarter second
            // even when nothing forces a flush.
            thread(name = "log-flusher", isDaemon = true) {
                var passes = 0
                while (true) {
                    try {
                        Thread.sleep(250)
                    } catch (_: InterruptedException) {
                        break
                    }
                    flushLogFile()
                    // 0.9.62 heartbeat: while a session
                    // runs, the app stamps its own life
                    // into the session file every ~10 s.
                    // Field runs keep ending mid-line
                    // with no exit record; comparing the
                    // last heartbeat against the
                    // supervisor mirror's last line tells
                    // whether the app outlived the
                    // supervisor (a supervisor-side kill)
                    // or they died together (a group
                    // kill, e.g. LMK).
                    passes++
                    if (passes % 40 == 0 && supervisor != null) {
                        // 0.9.74: the heartbeat also carries
                        // the app process's own memory, so
                        // the next death's log shows whether
                        // memory climbed steadily (a leak)
                        // or spiked (one huge allocation).
                        // The 0.9.73 death was a Java CRASH
                        // at pss 833 MB -- our own code.
                        val rt = Runtime.getRuntime()
                        val heapKb = (rt.totalMemory() - rt.freeMemory()) / 1024
                        // S10 I1: the field clock rides
                        // the heartbeat (elapsed since
                        // this session's supervisor
                        // launch, monotonic).
                        val tMs = if (fieldStartNanos != 0L) {
                            (System.nanoTime() - fieldStartNanos) / 1_000_000
                        } else {
                            -1
                        }
                        writeLogLineToFile(
                            "[shell] heartbeat (app alive) heapKB=$heapKb rssKB=${selfRssKb()} t=$tMs",
                        )
                    }
                }
            }
        } catch (e: Exception) {
            logFileOut = null
        }
    }


    /** One-time copy of the pre-0.9.78 private session
     * logs into this launch's Download log directory.
     * Live mode freezes the private files (the old
     * rotation would destroy the previous session, which
     * may still hold unretrieved crash evidence), so the
     * frozen pair travels as legacy-session-log.txt and
     * legacy-previous-session-log.txt instead. Copies
     * are streamed; a source is renamed to
     * <name>.migrated only after its copy has landed, so
     * a failed copy is retried on the next launch and
     * the original never disappears first. */
    private fun migrateLegacyLogs(dirName: String) {
        thread(name = "log-migrate", isDaemon = true) {
            val pairs = listOf(
                "legacy-session-log.txt" to
                    File(filesDir, "session-log.txt"),
                "legacy-previous-session-log.txt" to
                    File(filesDir, "previous-session-log.txt"),
            )
            for ((name, src) in pairs) {
                if (!src.exists() || src.length() == 0L) {
                    continue
                }
                try {
                    val values = ContentValues().apply {
                        put(
                            MediaStore.Downloads.DISPLAY_NAME,
                            name,
                        )
                        put(
                            MediaStore.Downloads.MIME_TYPE,
                            "text/plain",
                        )
                        put(
                            MediaStore.Downloads.RELATIVE_PATH,
                            Environment.DIRECTORY_DOWNLOADS +
                                "/" + dirName,
                        )
                    }
                    val uri = contentResolver.insert(
                        MediaStore.Downloads
                            .EXTERNAL_CONTENT_URI,
                        values,
                    ) ?: continue
                    val out = contentResolver
                        .openOutputStream(uri) ?: continue
                    out.use { o ->
                        src.inputStream().use {
                            it.copyTo(o, 64 * 1024)
                        }
                    }
                    src.renameTo(
                        File(filesDir, src.name + ".migrated"),
                    )
                } catch (e: Exception) {
                    // Retried on the next launch.
                }
            }
        }
    }

    /** The supervisor's direct mirror logs are written
     * by the native supervisor processes, which have no
     * MediaStore: their live directory is the same-named
     * folder in the app's external files dir
     * (Android/data/com.yongshuai.paxvm/files/), a real
     * path this app's processes can write natively and
     * the user can read directly. Writability is probed
     * here; when external storage is unavailable the
     * supervisor starts without --logdir and the mirrors
     * stay in the vm directory as before. */
    private fun setupMirrorDir(dirName: String) {
        try {
            val ext = getExternalFilesDir(null) ?: return
            val d = File(ext, dirName)
            d.mkdirs()
            val probe = File(d, ".probe")
            FileOutputStream(probe).use { it.write(1) }
            if (!probe.delete()) probe.deleteOnExit()
            mirrorLogDir = d
        } catch (e: Exception) {
            mirrorLogDir = null
        }
    }

    /** This process's resident size in KB, from procfs. */
    private fun selfRssKb(): Long {
        return try {
            val line = File("/proc/self/status").useLines { lines ->
                lines.firstOrNull { it.startsWith("VmRSS") }
            } ?: return -1
            line.filter { it.isDigit() }.toLong()
        } catch (e: Exception) {
            -1
        }
    }

    /**
     * Record an uncaught exception's stack into the
     * session log before the system takes the process
     * down. The 0.9.73 field death was recorded by the
     * system as CRASH (a Java exception in our own
     * code) at pss 833 MB, but the stack itself only
     * ever reached logcat, which we cannot read from
     * here; the next crash must leave its stack in the
     * downloadable log. The write bypasses the batched
     * flusher and syncs straight to disk, then the
     * previous handler still runs so the system's own
     * bookkeeping is unchanged.
     */
    private fun installCrashRecorder() {
        val previous = Thread.getDefaultUncaughtExceptionHandler()
        Thread.setDefaultUncaughtExceptionHandler { thread, error ->
            try {
                val sw = java.io.StringWriter()
                error.printStackTrace(java.io.PrintWriter(sw))
                val rt = Runtime.getRuntime()
                val heapKb = (rt.totalMemory() - rt.freeMemory()) / 1024
                val text = "[crash] uncaught in thread ${thread.name} " +
                    "heapKB=$heapKb rssKB=${selfRssKb()}:\n$sw\n"
                val uri = liveLogUri
                if (uri != null) {
                    // Live mode: append straight into the
                    // Download session log (0.9.78).
                    contentResolver.openOutputStream(
                        uri, "wa",
                    )?.use { out ->
                        out.write(text.toByteArray())
                        out.flush()
                    }
                } else {
                    val f = sessionLogFileRef
                    if (f != null) {
                        java.io.FileOutputStream(f, true)
                            .use { out ->
                                out.write(text.toByteArray())
                                out.flush()
                                out.fd.sync()
                            }
                    }
                }
            } catch (e: Exception) {
                // Nothing sensible left to do at this point.
            }
            previous?.uncaughtException(thread, error)
        }
    }

    /** Ask Android why this app's previous processes
     * died and write the answers into the session log.
     * Sessions keep ending with every record cut off
     * mid-line and no exit record anywhere: when the
     * app process dies, the system's process-group
     * cleanup takes the whole supervisor tree with it,
     * so the only witness left is the system's own
     * exit bookkeeping (ApplicationExitInfo: low-memory
     * kill vs native/Java crash vs signaled, with RSS
     * at death and, for crashes, a trace). */
    private fun reportPreviousExits() {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.R) {
            return
        }
        try {
            val am = getSystemService(ActivityManager::class.java)
            val exits =
                am.getHistoricalProcessExitReasons(packageName, 0, 5)
            if (exits.isEmpty()) {
                writeLogLineToFile("[exitinfo] (no previous exits recorded)")
            }
            for (e in exits) {
                val name = when (e.reason) {
                    ApplicationExitInfo.REASON_EXIT_SELF -> "EXIT_SELF"
                    ApplicationExitInfo.REASON_SIGNALED -> "SIGNALED"
                    ApplicationExitInfo.REASON_LOW_MEMORY -> "LOW_MEMORY"
                    ApplicationExitInfo.REASON_CRASH -> "CRASH"
                    ApplicationExitInfo.REASON_CRASH_NATIVE -> "CRASH_NATIVE"
                    ApplicationExitInfo.REASON_ANR -> "ANR"
                    ApplicationExitInfo.REASON_INITIALIZATION_FAILURE ->
                        "INITIALIZATION_FAILURE"
                    ApplicationExitInfo.REASON_EXCESSIVE_RESOURCE_USAGE ->
                        "EXCESSIVE_RESOURCE_USAGE"
                    ApplicationExitInfo.REASON_USER_REQUESTED -> "USER_REQUESTED"
                    ApplicationExitInfo.REASON_USER_STOPPED -> "USER_STOPPED"
                    ApplicationExitInfo.REASON_DEPENDENCY_DIED -> "DEPENDENCY_DIED"
                    ApplicationExitInfo.REASON_FREEZER -> "FREEZER"
                    else -> "reason#${e.reason}"
                }
                writeLogLineToFile(
                    "[exitinfo] ${java.util.Date(e.timestamp)} $name " +
                        "status=${e.status} importance=${e.importance} " +
                        "pss=${e.pss}KB rss=${e.rss}KB " +
                        "desc=${e.description}",
                )
                if (e.reason == ApplicationExitInfo.REASON_CRASH_NATIVE ||
                    e.reason == ApplicationExitInfo.REASON_CRASH
                ) {
                    try {
                        e.traceInputStream?.bufferedReader()?.useLines { seq ->
                            seq.take(40).forEach {
                                writeLogLineToFile("[exitinfo-trace] $it")
                            }
                        }
                    } catch (_: Exception) {
                    }
                }
            }
        } catch (ex: Exception) {
            writeLogLineToFile("[exitinfo] query failed: ${ex.message}")
        }
    }

    private fun writeLogLineToFile(line: String) {
        // Batched since 0.9.54: a boot flood is ~70k
        // lines, and one write syscall per line on an
        // unbuffered stream was a real share of the
        // boot-stretch interface stutter the user felt.
        // Lines accumulate and land at 64 KB or on the
        // flusher thread's 250 ms pass; content and
        // order are unchanged, and saveLog flushes
        // before it reads the file back.
        synchronized(logFileLock) {
            pendingLogText.append(line).append('\n')
            if (pendingLogText.length >= 65536) {
                flushPendingLogLocked()
            }
        }
    }

    /** Caller holds logFileLock. */
    private fun flushPendingLogLocked() {
        val out = logFileOut ?: run {
            pendingLogText.setLength(0)
            return
        }
        if (pendingLogText.isEmpty()) return
        try {
            out.write(
                pendingLogText.toString().toByteArray(Charsets.UTF_8),
            )
            out.flush()
        } catch (e: Exception) {
            // A dead log file must not break the session.
            // If the live Download stream died mid-session
            // (folder removed, provider hiccup), continue
            // the record in the private session file
            // instead of dropping lines from here on; the
            // crash recorder follows liveLogUri, so it
            // switches over with the flusher.
            if (liveLogUri != null) {
                liveLogUri = null
                try {
                    val f = File(filesDir, "session-log.txt")
                    sessionLogFileRef = f
                    val fb = FileOutputStream(f, true)
                    logFileOut = fb
                    fb.write(
                        pendingLogText.toString()
                            .toByteArray(Charsets.UTF_8),
                    )
                } catch (e2: Exception) {
                }
            }
        }
        pendingLogText.setLength(0)
    }

    /** Land every buffered line in the session file now. */
    private fun flushLogFile() {
        synchronized(logFileLock) { flushPendingLogLocked() }
    }

    private fun buildUi() {
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(24, 24, 24, 24)
        }
        statusView = TextView(this).apply {
            textSize = 13f
            typeface = Typeface.MONOSPACE
        }
        root.addView(statusView)

        val buttons = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.START
        }
        startButton = Button(this).apply {
            text = "啟動"
            setOnClickListener {
                queueStart(rootfsDir, "libbusybox.so", listOf("sh", "/verify.sh"))
            }
        }
        probeButton = Button(this).apply {
            text = "啟動32"
            setOnClickListener {
                queueStart(rootfs32Dir, "libbusybox32.so", listOf("sh", "/verify.sh"))
            }
        }
        gbButton = Button(this).apply {
            text = "啟動GB"
            setOnClickListener {
                queueStart(
                    rootfsGBDir,
                    "libgbinit.so",
                    listOf("/init"),
                    bbLib = "libbusybox32.so",
                    loaderLib = "libgbloader.so",
                    gb = true,
                )
            }
        }
        stopButton = Button(this).apply {
            text = "停止"
            isEnabled = false
            setOnClickListener { stopSupervisor() }
        }
        buttons.addView(startButton)
        buttons.addView(probeButton)
        buttons.addView(gbButton)
        buttons.addView(stopButton)
        copyButton = Button(this).apply {
            text = "複製日誌"
            setOnClickListener { copyLog() }
        }
        saveButton = Button(this).apply {
            text = "下載日誌"
            setOnClickListener { saveLog() }
        }
        val logButtons = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
        }
        logButtons.addView(copyButton)
        logButtons.addView(saveButton)
        root.addView(buttons)
        root.addView(logButtons)

        // Guest framebuffer preview (S6): hidden until a GB
        // session starts; the preview thread fills it from
        // the shared .fb0 file the guest draws into.
        fbView = ImageView(this).apply {
            visibility = android.view.View.GONE
            scaleType = ImageView.ScaleType.FIT_CENTER
            setBackgroundColor(0xFF000000.toInt())
        }
        root.addView(
            fbView,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                (430 * resources.displayMetrics.density).toInt(),
            ),
        )

        logView = TextView(this).apply {
            textSize = 12f
            typeface = Typeface.MONOSPACE
            movementMethod = ScrollingMovementMethod()
        }
        scrollView = ScrollView(this).apply {
            addView(logView)
        }
        root.addView(
            scrollView,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                0,
                1f,
            ),
        )
        setContentView(root)
    }

    // The settings entry lives in the stock action
    // bar's overflow menu (top right, beside the app
    // icon) -- an earlier build grew a second,
    // hand-rolled title row under the action bar,
    // which the user rightly called out as wrong.
    override fun onCreateOptionsMenu(menu: android.view.Menu): Boolean {
        menu.add("設定")
        menu.add("傾印客體堆疊")
        return true
    }

    override fun onOptionsItemSelected(item: android.view.MenuItem): Boolean {
        if (item.title == "設定") {
            startActivity(
                android.content.Intent(this, SettingsActivity::class.java),
            )
            return true
        }
        if (item.title == "傾印客體堆疊") {
            requestGuestStackDump()
            return true
        }
        return super.onOptionsItemSelected(item)
    }

    /** Freeze forensics (0.9.81): ask the supervisor
     * to make the guest's system_server dump all its
     * Java thread stacks. The shell cannot speak the
     * supervisor's coordinator protocol, so the
     * request rides a signal: W0 leaves its pid in
     * vm0/supervisor.pid at startup, and SIGUSR2
     * (signal 12 on Android) is its request line --
     * W0 relays it through the coordinator to the
     * worker tracing zygote, which SIGQUITs
     * system_server, and GB Dalvik's signal catcher
     * answers with the dump (guest /data/anr/traces.txt
     * and the guest log) without killing anything. The
     * dump rides the next 「下載日誌」 export like any
     * other guest evidence. A missing or stale pid
     * file means no supervisor is running to ask. */
    private fun requestGuestStackDump() {
        val pid = try {
            File(File(filesDir, "vm0"), "supervisor.pid")
                .readText().trim().toInt()
        } catch (e: Exception) {
            -1
        }
        if (pid <= 0) {
            android.widget.Toast.makeText(
                this,
                "監督器未執行或 pid 檔缺失",
                android.widget.Toast.LENGTH_LONG,
            ).show()
            return
        }
        try {
            android.os.Process.sendSignal(pid, 12)
            android.widget.Toast.makeText(
                this,
                "已請求傾印 system_server 堆疊（看 Download 日誌）",
                android.widget.Toast.LENGTH_LONG,
            ).show()
        } catch (e: Exception) {
            android.widget.Toast.makeText(
                this,
                "監督器未執行或 pid 檔缺失",
                android.widget.Toast.LENGTH_LONG,
            ).show()
        }
    }

    /** Delete-then-write for shell-owned guest files. A guest
     * can chmod a file the shell rewrites on every launch —
     * 2.3's init chmods /proc/cmdline to 0440 (through the
     * supervisor's proxy, onto the host path), and the next
     * launch's plain writeText then dies with EACCES inside the
     * click handler: the 0.3.2 field failure, where the GB
     * button killed the app before any log line (the busybox
     * buttons were unaffected — their guest never chmods).
     * Recreating the file resets its permissions. */
    private fun writeFresh(file: File, text: String) {
        if (file.exists()) {
            file.delete()
        }
        file.writeText(text)
    }

    /** Idempotent: build the rootfs tree the busybox guest expects. */
    private fun prepareRootfs(rootfs: File) {
        val bin = File(rootfs, "bin")
        bin.mkdirs()
        File(rootfs, "tmp").mkdirs()
        val seed = File(rootfs, "seed.txt")
        if (!seed.exists()) {
            seed.writeText("seed-42")
        }
        // /bin/busybox placeholder: exec of this path is intercepted
        // by the supervisor and rewritten to nativeLibraryDir, so
        // the file itself never runs; it exists so that listings
        // and the supervisor's existence check see it (spec 5).
        val bb = File(bin, "busybox")
        if (!bb.exists()) {
            bb.writeBytes(ByteArray(0))
        }
        // Applet symlinks: /bin/<applet> -> "busybox" (relative
        // target). The supervisor resolves them at exec time; the
        // host kernel never has to (spec section 2b).
        for (applet in applets) {
            val link = File(bin, applet)
            if (!link.exists()) {
                try {
                    Os.symlink("busybox", link.absolutePath)
                } catch (e: Exception) {
                    appendLog("[shell] symlink $applet failed: $e")
                }
            }
        }
        writeFresh(File(rootfs, "verify.sh"), verifyScript)
    }

    /** Idempotent: build the rootfs tree the Gingerbread init
     * expects, plus the probe files. The .kmsg capture file is
     * truncated on every start: init opens it without O_TRUNC,
     * so last session's log would otherwise be overwritten in
     * place and garbled. */
    private fun prepareGBRootfs(rootfs: File, diagnosticsEnabled: Boolean) {
        for (d in listOf("bin", "dev", "proc", "sys", "system", "data", "data/property", "sbin", "tmp")) {
            File(rootfs, d).mkdirs()
        }
        for (stage in listOf("early-init", "init", "fs", "boot")) {
            File(rootfs, ".pax-stage-$stage").delete()
        }
        // Same busybox placeholder + sh symlink arrangement as
        // the probe rootfs: the exec of /bin/sh is rewritten by
        // the supervisor to libbusybox32.so (via --bb).
        val bin = File(rootfs, "bin")
        val bb = File(bin, "busybox")
        if (!bb.exists()) {
            bb.writeBytes(ByteArray(0))
        }
        val sh = File(bin, "sh")
        if (!sh.exists()) {
            try {
                Os.symlink("busybox", sh.absolutePath)
            } catch (e: Exception) {
                appendLog("[shell] symlink sh failed: $e")
            }
        }
        // Binder arenas belong to one session's supervisor;
        // stale files from a dead session must not be reused
        // (the supervisor also recreates state per pid, this is
        // belt and braces).
        File(rootfs, ".binder").deleteRecursively()
        File(rootfs, ".ashmem").deleteRecursively()
        // Guest log capture (S7 gun 3): the supervisor
        // maps /dev/log/* into this directory; start each
        // session empty so a saved log holds one session.
        File(rootfs, ".logs").deleteRecursively()
        File(rootfs, ".logs").mkdirs()
        // The four channel files must PRE-EXIST: the
        // guest opens its log devices O_WRONLY without
        // O_CREAT (device nodes simply exist on
        // hardware), and 0.9.50's field run showed every
        // /dev/log open failing -2 on the missing files
        // despite the supervisor mapping being right.
        for (ch in listOf("main", "radio", "events", "system")) {
            writeFresh(File(rootfs, ".logs/log-$ch"), "")
        }
        // cpuacct surface (S7 gun 3): on hardware /acct is
        // a cgroup mount and zygote's startup touches
        // /acct/uid/0/tasks, creating the uid dir itself
        // when the open fails. Here the mount is a plain
        // skeleton: the dirs plus an empty tasks file the
        // guest can open and write pids into.
        File(rootfs, "acct/uid/0").mkdirs()
        writeFresh(File(rootfs, "acct/uid/0/tasks"), "")
        // Fake battery surface (S9, 0.9.85): GB's
        // BatteryService JNI registration opendir()s
        // /sys/class/power_supply and returns -1 --
        // skipping RegisterNatives entirely -- when
        // the directory cannot be opened; on hardware
        // the sysfs mount always provides it, here the
        // skeleton must. Without it the 0.9.84 field's
        // system_server died 28 tenures in a row on
        // UnsatisfiedLinkError: native_update at the
        // Battery Service checkpoint. Provide a static
        // battery plus mains/usb stubs with era-plain
        // values; the JNI discovers the supplies by
        // reading each subdirectory's "type" file and
        // probes the value files with access(R_OK).
        val ps = "sys/class/power_supply"
        File(rootfs, "$ps/ac").mkdirs()
        File(rootfs, "$ps/usb").mkdirs()
        File(rootfs, "$ps/battery").mkdirs()
        writeFresh(File(rootfs, "$ps/ac/type"), "Mains\n")
        writeFresh(File(rootfs, "$ps/ac/online"), "0\n")
        writeFresh(File(rootfs, "$ps/usb/type"), "USB\n")
        writeFresh(File(rootfs, "$ps/usb/online"), "0\n")
        writeFresh(File(rootfs, "$ps/battery/type"), "Battery\n")
        writeFresh(File(rootfs, "$ps/battery/status"), "Discharging\n")
        writeFresh(File(rootfs, "$ps/battery/health"), "Good\n")
        writeFresh(File(rootfs, "$ps/battery/present"), "1\n")
        writeFresh(File(rootfs, "$ps/battery/capacity"), "50\n")
        writeFresh(File(rootfs, "$ps/battery/voltage_now"), "3700000\n")
        writeFresh(File(rootfs, "$ps/battery/temp"), "250\n")
        writeFresh(File(rootfs, "$ps/battery/technology"), "Li-ion\n")
        // Virtual framebuffer backing (S6): two 480x800x32
        // pages, zeroed per session, plus the visible-page
        // note the supervisor's fb ioctl handler maintains.
        RandomAccessFile(File(rootfs, ".fb0"), "rw").use {
            it.setLength(480L * 800 * 4 * 2)
        }
        writeFresh(File(rootfs, ".fb-page"), "0")
        // Evidence markers in /data persist across sessions
        // by design (a re-run shows -EEXIST, which is itself
        // readable evidence) -- but the S5c scenario reuses
        // the same names for different stages (death, then
        // revival), so its markers must start clean or the
        // stages become indistinguishable.
        File(rootfs, "data").listFiles()?.forEach { f ->
            val n = f.name
            if (n == "svc-list.txt" || n == "probe-ok.txt" ||
                n.startsWith("SERVE") || n.startsWith("LIST") ||
                n.startsWith("GET_H_") || n.startsWith("GONE_") ||
                n.startsWith("PING_") || n.startsWith("STAGE_IS_") ||
                n.startsWith("FROMPROBE_IS_") || n.startsWith("LB") ||
                n.startsWith("FB_")
            ) {
                f.deleteRecursively()
            }
        }
        var initRc = gbInitRc
        if (diagnosticsEnabled) {
            for (stage in listOf("early-init", "init", "fs", "boot")) {
                val action = "on $stage\n"
                initRc = initRc.replaceFirst(
                    action,
                    action + "    write /.pax-stage-$stage reached\n",
                )
            }
        }
        writeFresh(File(rootfs, "init.rc"), initRc)
        writeFresh(File(rootfs, "probe.sh"), gbProbeScript)
        // The bootanimation init service's wrapper: first
        // wait until the service manager answers and
        // SurfaceFlinger is registered (paxsvc waitmgr --
        // asked earlier, the manager's seat is still empty,
        // the driver answers DEAD_REPLY, and the stock
        // bootanimation wedges on that instead of retrying;
        // 0.9.3 device run), then run the animation with a
        // relaunch loop as a second belt.
        writeFresh(
            File(rootfs, "bootanim.sh"),
            "/system/bin/paxsvc waitmgr\n" +
                "while true; do /system/bin/bootanimation; sleep 1; done\n"
        )
        // init reads the kernel cmdline for androidboot.hardware
        // (and looks for /init.<hardware>.rc, absent on purpose).
        // This is the file init chmods to 0440 — writeFresh is
        // what keeps the next launch alive (see its doc).
        writeFresh(
            File(rootfs, "proc/cmdline"),
            "androidboot.hardware=paxvm androidboot.console=tty0\n",
        )
        // Static guest-environment faces (S10 F7 v1,
        // s10-f7-desk section 2.1): the global /proc files
        // the skeleton rootfs never had, plus the coldboot
        // marker. On hardware these come from the kernel and
        // from ueventd's coldboot pass; here /dev is already
        // populated by the shell and supervisor at t=0, so
        // the marker declares an existing fact -- without it
        // init polls for it ~1.5s a probe all field. Values
        // are one era-consistent frozen snapshot (single
        // core, 256MB, 2.6.35 generation); the desk admits
        // only advisory/reporting consumers for frozen
        // faces, meminfo first among them: GB's
        // MemInfoReader could only ever read zeros from a
        // file that did not exist. proc/net is the one
        // subdirectory the opening mkdirs does not make.
        writeFresh(
                File(rootfs, "proc/meminfo"),
                    "MemTotal:         262144 kB
" +
                    "MemFree:          104880 kB
" +
                    "Buffers:            8192 kB
" +
                    "Cached:            40960 kB
" +
                    "SwapCached:            0 kB
" +
                    "Active:            90112 kB
" +
                    "Inactive:          32768 kB
" +
                    "Active(anon):      61440 kB
" +
                    "Inactive(anon):    16384 kB
" +
                    "Active(file):      28672 kB
" +
                    "Inactive(file):    16384 kB
" +
                    "Unevictable:           0 kB
" +
                    "Mlocked:               0 kB
" +
                    "SwapTotal:             0 kB
" +
                    "SwapFree:              0 kB
" +
                    "Dirty:                 0 kB
" +
                    "Writeback:             0 kB
" +
                    "AnonPages:         57344 kB
" +
                    "Mapped:            24576 kB
" +
                    "Shmem:              1024 kB
" +
                    "Slab:              16384 kB
" +
                    "SReclaimable:       8192 kB
" +
                    "SUnreclaim:         8192 kB
" +
                    "KernelStack:        2048 kB
" +
                    "PageTables:         4096 kB
" +
                    "NFS_Unstable:          0 kB
" +
                    "Bounce:                0 kB
" +
                    "WritebackTmp:          0 kB
" +
                    "CommitLimit:      131072 kB
" +
                    "Committed_AS:     196608 kB
" +
                    "VmallocTotal:     876544 kB
" +
                    "VmallocUsed:       24576 kB
" +
                    "VmallocChunk:     798916 kB
" +
                    "HugePages_Total:       0
" +
                    "HugePages_Free:        0
" +
                    "HugePages_Rsvd:        0
" +
                    "HugePages_Surp:        0
" +
                    "Hugepagesize:       4096 kB
" +
                    "DirectMap4k:       16384 kB
" +
                    "DirectMap4M:      245760 kB
",
        )
        writeFresh(
                File(rootfs, "proc/stat"),
                    "cpu  120 5 95 6850 18 0 12 0 0 0
" +
                    "cpu0 120 5 95 6850 18 0 12 0 0 0
" +
                    "intr 12500 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
" +
                    "ctxt 18300
" +
                    "btime 1325376000
" +
                    "processes 342
" +
                    "procs_running 1
" +
                    "procs_blocked 0
",
        )
        writeFresh(File(rootfs, "proc/loadavg"), "0.00 0.00 0.00 1/87 342
")
        File(rootfs, "proc/net").mkdirs()
        writeFresh(
                File(rootfs, "proc/net/dev"),
                    "Inter-|   Receive                                                |  Transmit
" +
                    " face |bytes    packets errs drop fifo frame compressed multicast|bytes    packets errs drop fifo colls carrier compressed
" +
                    "    lo:       0       0    0    0    0     0          0         0        0       0    0    0    0     0       0          0
",
        )
        writeFresh(File(rootfs, "proc/version"), "Linux version 2.6.35.7-gebx0001 (android-build@build) (gcc version 4.4.0 (GCC) ) #1 PREEMPT Tue Nov 1 00:00:00 UTC 2011
")
        writeFresh(File(rootfs, "dev/.coldboot_done"), "")
        writeFresh(File(rootfs, ".kmsg"), "")
        writeFresh(File(rootfs, ".gbloader-err"), "")
        installGBSystem(rootfs)
    }

    /** Extract the bundled Gingerbread /system subset (assets/
     * gbsystem.zip, built by CI from the SDK system image: the
     * linker, servicemanager, toolbox, sh and their library
     * closure) into the GB rootfs, once per rootfs (marker
     * file), and recreate the toolbox applet symlinks the image
     * carries (getprop/setprop). */
    private fun installGBSystem(rootfs: File) {
        val sysDir = File(rootfs, "system")
        // Bump this marker whenever the gbsystem.zip payload
        // changes: with the old name present, extraction is
        // skipped and new payload files (paxsvc in 0.6.2) never
        // reach the rootfs -- that cost a whole device run.
        // v20 (0.9.151, S10 F7): the zip gains lib/hw/
        // gralloc.paxvm.so (a byte copy of gralloc.default.so
        // under the ro.hardware variant name); nothing else in
        // the payload changed.
        val marker = File(sysDir, ".gbsystem-v20")
        if (!marker.exists()) {
            // The payload is authoritative: wipe the old tree
            // before extracting. Overlay extraction never
            // deletes, so a file removed from a newer zip --
            // or left behind by an entirely different payload
            // -- would linger in the tree forever (2026-11-08:
            // an S2 experiment field silently re-ran the
            // previous payload's Samsung gralloc because the
            // bypass build's zip no longer contained it, but
            // the device tree still did).
            sysDir.deleteRecursively()
            sysDir.mkdirs()
            try {
                assets.open("gbsystem.zip").use { ins ->
                    ZipInputStream(ins).use { zin ->
                        var e = zin.nextEntry
                        while (e != null) {
                            val out = File(sysDir, e.name)
                            out.parentFile?.mkdirs()
                            if (!e.isDirectory) {
                                out.outputStream().use { zin.copyTo(it) }
                                out.setExecutable(true, false)
                            }
                            e = zin.nextEntry
                        }
                    }
                }
                marker.writeText("v1\n")
                appendLog("[shell] gbsystem subset installed")
            } catch (ex: Exception) {
                appendLog("[shell] gbsystem extract failed: $ex")
            }
        }
        for (link in listOf("getprop", "setprop")) {
            val f = File(sysDir, "bin/$link")
            if (!f.exists()) {
                try {
                    Os.symlink("toolbox", f.absolutePath)
                } catch (ex: Exception) {
                    appendLog("[shell] symlink $link failed: $ex")
                }
            }
        }
    }

    /** Copy the whole log view to the clipboard, so a session's
     * log can be pasted as text instead of screenshotted page by
     * page (added 0.3.5 at the user's request). */
    private fun copyLog() {
        val text = logView.text.toString()
        val cm = getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager
        cm.setPrimaryClip(ClipData.newPlainText("PaxVM log", text))
        appendLog("[shell] 日誌已複製到剪貼簿（${text.count { it == '\n' } + 1} 行）")
    }

    /** Export the session's log FILES into a fresh
     * directory under Download (Download/PaxVM-logs-<time>/):
     * session-log.txt, previous-session-log.txt, the
     * supervisor's direct mirror logs and the guest
     * /dev/log channels are copied file by file, streamed
     * through a small buffer, never loaded whole into
     * memory; a parsed, readable rendering of the guest
     * channels is added as guest-log.txt (last 500 entries
     * per channel, pixelflinger dropped as before).
     *
     * This replaces the pre-0.9.77 single-file export,
     * which composed the whole download as one string in
     * RAM (session readText + previous readText + every
     * direct log readText + concatenation copies + a
     * UTF-8 byte copy on top): at S8 log volumes that is
     * several hundred MB of live text against a 256MB
     * heap, and the resulting OutOfMemoryError is an
     * Error, not an Exception, so none of the old
     * try/catch blocks caught it -- pressing the download
     * button crashed the app deterministically
     * (2026-11-07, two fields in a row, the second on a
     * fresh launch whose only job was the export). */
    private val exportingLog =
        java.util.concurrent.atomic.AtomicBoolean(false)

    private fun saveLog() {
        if (!exportingLog.compareAndSet(false, true)) {
            appendLog("[shell] 日誌匯出進行中，請稍候")
            return
        }
        thread(name = "log-export") {
            try {
                exportLogDir()
            } catch (e: Exception) {
                appendLog("[shell] 存日誌失敗：$e")
            } finally {
                exportingLog.set(false)
            }
        }
    }

    private fun exportLogDir() {
        // Land the batched lines first (0.9.54): the
        // newest quarter-second of the session must not
        // be missing from the exported record.
        flushLogFile()
        val stamp = SimpleDateFormat(
            "yyyyMMdd-HHmmss", Locale.US,
        ).format(Date())
        // When this launch logs live, the collected
        // files join the session log in its own Download
        // directory; in the private-file fallback the
        // export makes a fresh directory, as 0.9.77 did.
        val dirName = liveLogDirName ?: "PaxVM-logs-$stamp"
        val legacyDir: File? =
            if (Build.VERSION.SDK_INT >= 29) null else {
                val d = File(
                    Environment
                        .getExternalStoragePublicDirectory(
                            Environment.DIRECTORY_DOWNLOADS,
                        ),
                    dirName,
                )
                d.mkdirs()
                d
            }
        fun sink(name: String): OutputStream? {
            return try {
                if (legacyDir != null) {
                    FileOutputStream(File(legacyDir, name))
                } else {
                    val values = ContentValues().apply {
                        put(
                            MediaStore.Downloads.DISPLAY_NAME,
                            name,
                        )
                        put(
                            MediaStore.Downloads.MIME_TYPE,
                            "text/plain",
                        )
                        put(
                            MediaStore.Downloads.RELATIVE_PATH,
                            Environment.DIRECTORY_DOWNLOADS +
                                "/" + dirName,
                        )
                    }
                    val uri = contentResolver.insert(
                        MediaStore.Downloads
                            .EXTERNAL_CONTENT_URI,
                        values,
                    ) ?: return null
                    contentResolver.openOutputStream(uri)
                }
            } catch (e: Exception) {
                null
            }
        }
        var count = 0
        fun copyFile(name: String, src: File) {
            if (!src.exists() || src.length() == 0L) return
            val out = sink(name) ?: return
            try {
                out.use { o ->
                    src.inputStream().use {
                        it.copyTo(o, 64 * 1024)
                    }
                }
                count++
            } catch (e: Exception) {
                // One bad file must not lose the rest.
            }
        }
        if (liveLogDirName == null) {
            // Fallback launches keep the session record
            // in the private files; live launches already
            // have session-log.txt in the target directory
            // (it is being written there), and inserting a
            // second copy would only rename-duplicate it.
            copyFile(
                "session-log.txt",
                File(filesDir, "session-log.txt"),
            )
            val prev = previousLogFile
            if (prev != null) {
                copyFile("previous-session-log.txt", prev)
            }
        }
        // Supervisor direct mirrors (written by the
        // supervisor processes themselves, so they
        // survive the app dying): current then -prev,
        // W0..W6 (0.9.77: the old export stopped at W4).
        val vmDir = File(filesDir, "vm0")
        for (w in 0..6) {
            for (suffix in listOf("", "-prev")) {
                copyFile(
                    "supervisor-direct-w$w$suffix.log",
                    File(vmDir, "supervisor-direct-w$w$suffix.log"),
                )
            }
        }
        // Guest /dev/log channels, raw logger_entry files.
        for (ch in listOf("main", "system", "radio", "events")) {
            copyFile(
                "log-$ch",
                File(rootfsGBDir, ".logs/log-$ch"),
            )
        }
        // Guest ANR traces (0.9.81): the stack dumps
        // the overflow menu can ask Dalvik for land in
        // the guest's /data/anr as traces*.txt; collect
        // them with the rest of the guest evidence.
        // This flow is shared by live and fallback
        // launches, so both modes pick them up.
        //
        // 0.9.146 (s9-146-desk section 4.2): the
        // traces file is the one piece of guest
        // evidence that names Java locks and their
        // holders ("waiting to lock ... held by"),
        // and the 0.9.145 field's export carried
        // none even though the guest Watchdog had
        // opened /data/anr/traces.txt: the export
        // ran while the wedged process's dump was
        // still unwritten, and the copy helper
        // silently skips zero-length files, so the
        // miss left no trace of its own. Collect
        // traces.txt by name ahead of the glob and
        // record the outcome in the session log, so
        // the next field can tell "not yet written"
        // from "never produced". The file may hold
        // an earlier tenure's dump (the guest only
        // ever keeps the latest); telling tenures
        // apart is the reader's job, not the
        // collector's.
        val anrDir = File(rootfsGBDir, "data/anr")
        val tracesFile = File(anrDir, "traces.txt")
        if (tracesFile.exists() && tracesFile.length() > 0) {
            val before = count
            copyFile("traces.txt", tracesFile)
            if (count > before) {
                appendLog(
                    "[shell] 已附帶 guest ANR traces" +
                        "（${tracesFile.length()} 位元組）",
                )
            }
        } else {
            appendLog(
                "[shell] guest ANR traces 尚不存在或為空，未附帶",
            )
        }
        val anrFiles = anrDir.listFiles()
            ?.filter {
                it.isFile && it.name != "traces.txt" &&
                    it.name.startsWith("traces") &&
                    it.name.endsWith(".txt")
            }
            ?.sortedBy { it.name }
            ?: emptyList()
        for (f in anrFiles) {
            copyFile(f.name, f)
        }
        // Readable rendering of the guest channels.
        val gout = sink("guest-log.txt")
        if (gout != null) {
            try {
                gout.use { o ->
                    for (ch in listOf("main", "system")) {
                        val body = renderGuestChannel(ch)
                        if (body.isNotEmpty()) {
                            o.write(
                                ("\n===== guest /dev/log/$ch" +
                                    " =====\n")
                                    .toByteArray(Charsets.UTF_8),
                            )
                            o.write(
                                body.toByteArray(Charsets.UTF_8),
                            )
                        }
                    }
                }
                count++
            } catch (e: Exception) {
            }
        }
        if (count > 0) {
            appendLog(
                "[shell] 日誌已存到 Download/$dirName/" +
                    "（共 $count 個檔案）",
            )
        } else {
            appendLog(
                "[shell] 存日誌失敗：沒有可匯出的日誌檔案",
            )
        }
    }

    /** Parse one guest /dev/log channel (GB logger_entry
     * stream: 20-byte header of u16 len, u16 pad, pid,
     * tid, sec, nsec; payload = priority byte,
     * NUL-terminated tag, message) into readable lines,
     * keeping only the last 500 entries and dropping the
     * pixelflinger tag (SurfaceFlinger's flood drowns the
     * runtime's own account). Reads at most the tail 8MB
     * of the channel file; the parser resyncs byte by
     * byte on a bad length, so starting mid-stream is
     * safe. Falls back to a bounded printable-strings
     * extraction when no entry parses. */
    /** 0.9.102: the strings fallback applies the same
     * masking as the structured path -- pixelflinger's
     * per-draw "Needs:" spam (previously it only got
     * dropped when entries parsed, so a torn channel
     * still flooded the export). */
    private fun keepRun(r: StringBuilder): Boolean {
        val s = r.toString()
        return !s.contains("pixelflinger") &&
            !s.contains("Needs: n=0x")
    }

    private fun renderGuestChannel(ch: String): String {
        val f = File(rootfsGBDir, ".logs/log-$ch")
        if (!f.exists() || f.length() == 0L) return ""
        val bytes = try {
            val all = f.readBytes()
            if (all.size > 8 * 1024 * 1024) {
                all.copyOfRange(
                    all.size - 8 * 1024 * 1024, all.size,
                )
            } else {
                all
            }
        } catch (e: Exception) {
            return ""
        }
        val entries = ArrayDeque<String>()
        var off = 0
        fun u16le(o: Int) =
            (bytes[o].toInt() and 0xFF) or
                ((bytes[o + 1].toInt() and 0xFF) shl 8)
        fun i32le(o: Int) =
            (bytes[o].toInt() and 0xFF) or
                ((bytes[o + 1].toInt() and 0xFF) shl 8) or
                ((bytes[o + 2].toInt() and 0xFF) shl 16) or
                ((bytes[o + 3].toInt() and 0xFF) shl 24)
        while (off + 20 <= bytes.size) {
            val len = u16le(off)
            if (len < 2 || len > 8192 ||
                off + 20 + len > bytes.size
            ) {
                off++
                continue
            }
            val pid = i32le(off + 4)
            val prio = bytes[off + 20].toInt() and 0xFF
            var p = off + 21
            val tagStart = p
            while (p < off + 20 + len &&
                bytes[p] != 0.toByte()
            ) {
                p++
            }
            if (p >= off + 20 + len) {
                off++
                continue
            }
            val tag = String(
                bytes, tagStart, p - tagStart, Charsets.UTF_8,
            )
            val msg = String(
                bytes,
                p + 1,
                (off + 20 + len - (p + 1)).coerceAtLeast(0),
                Charsets.UTF_8,
            ).trimEnd('\u0000', '\n')
            if (tag != "pixelflinger") {
                val pl = when (prio) {
                    2 -> "V"; 3 -> "D"; 4 -> "I"
                    5 -> "W"; 6 -> "E"; 7 -> "F"
                    else -> prio.toString()
                }
                entries.addLast("$pl/$tag($pid): $msg")
                if (entries.size > 500) entries.removeFirst()
            }
            off += 20 + len
        }
        if (entries.isNotEmpty()) {
            // 0.9.102: fold consecutive repeats (a guest
            // service logging the same error in a loop) so
            // the readable log shows one line per anomaly
            // with a count, not a wall of copies.
            val folded = ArrayList<String>()
            var last: String? = null
            var run = 0
            fun flushRun() {
                val l = last ?: return
                folded.add(if (run > 1) "$l (×$run)" else l)
            }
            for (e in entries) {
                if (e == last) {
                    run++
                } else {
                    flushRun()
                    last = e
                    run = 1
                }
            }
            flushRun()
            return folded.joinToString("\n")
        }
        // Fallback: printable-strings, bounded output.
        val sb = StringBuilder()
        var run = StringBuilder()
        for (b in bytes) {
            if (sb.length > 24000) break
            val c = (b.toInt() and 0xFF).toChar()
            if (c in ' '..'~' || c == '\n' || c == '\t') {
                run.append(c)
            } else {
                if (run.length >= 6 && keepRun(run)) {
                    sb.append(run).append('\n')
                }
                run = StringBuilder()
            }
        }
        if (run.length >= 6 && sb.length <= 24000 && keepRun(run)) {
            sb.append(run).append('\n')
        }
        return sb.toString()
    }

    /** Button entry point for the three start buttons:
     * flip the controls immediately, then run the start
     * (whose rootfs preparation extracts hundreds of
     * files) on a worker thread. Until 0.9.56 the whole
     * start ran on the UI thread, so the buttons' state
     * change painted only after preparation finished --
     * the user's 'button state responds slowly' report,
     * present since the GB scene grew a payload. */
    private fun queueStart(
        rootfs: File,
        guestLib: String,
        guestArgs: List<String>,
        bbLib: String? = null,
        loaderLib: String? = null,
        gb: Boolean = false,
    ) {
        startButton.isEnabled = false
        probeButton.isEnabled = false
        gbButton.isEnabled = false
        statusView.text =
            "rootfs: ${rootfs.absolutePath}\n狀態：準備中…"
        thread(name = "supervisor-start") {
            startSupervisor(rootfs, guestLib, guestArgs, bbLib, loaderLib, gb)
        }
    }

    private fun startSupervisor(
        rootfs: File,
        guestLib: String,
        guestArgs: List<String>,
        bbLib: String? = null,
        loaderLib: String? = null,
        gb: Boolean = false,
    ) {
        if (supervisor != null) return
        val diagnostics = if (gb && StartupDiagnostics.isEnabled(this)) {
            StartupDiagnostics.newSession(this, rootfs).also {
                startupDiagnostics = it
                it.record("VM rootfs 準備開始。")
            }
        } else {
            null
        }
        if (gb) {
            prepareGBRootfs(rootfs, diagnostics != null)
        } else {
            prepareRootfs(rootfs)
        }
        diagnostics?.startMonitoring(mirrorLogDir)
        val libDir = applicationInfo.nativeLibraryDir
        val cmd = mutableListOf(
            "$libDir/libsupervisor.so",
            rootfs.absolutePath,
            "$libDir/$guestLib",
        )
        if (bbLib != null) {
            cmd.add("--bb")
            cmd.add("$libDir/$bbLib")
        }
        if (loaderLib != null) {
            cmd.add("--loader")
            cmd.add("$libDir/$loaderLib")
        }
        // 0.9.78: the supervisor's direct mirror logs go
        // live to this launch's directory in the app's
        // external files dir (Android/data) when one was
        // set up; without it they stay in the vm dir.
        val md = mirrorLogDir
        if (md != null) {
            cmd.add("--logdir")
            cmd.add(md.absolutePath)
        }
        cmd.add("--")
        cmd.addAll(guestArgs)
        val proc = try {
            ProcessBuilder(cmd)
                .redirectErrorStream(true)
                .start()
        } catch (e: Exception) {
            // Do not swallow: packaging/exec problems surface here
            // verbatim (M0 spec risk 7, unchanged in M1).
            appendLog("[shell] failed to start supervisor: $e")
            diagnostics?.finish("supervisor 啟動失敗：${e.javaClass.simpleName}")
            startupDiagnostics = null
            runOnUiThread {
                startButton.isEnabled = true
                probeButton.isEnabled = true
                gbButton.isEnabled = true
                stopButton.isEnabled = false
                statusView.text = "狀態：啟動失敗（見日誌）"
            }
            return
        }
        supervisor = proc
        fieldStartNanos = System.nanoTime()
        sessionRan = true
        diagnostics?.record("supervisor process 已啟動。")
        if (gb) {
            startFbPreview(rootfs)
        }
        runOnUiThread {
            startButton.isEnabled = false
            probeButton.isEnabled = false
            gbButton.isEnabled = false
            stopButton.isEnabled = true
            statusView.text =
                "rootfs: ${rootfs.absolutePath}\n狀態：監督器執行中"
        }
        appendLog("[shell] supervisor started")
        thread(name = "supervisor-reader") {
            try {
                proc.inputStream.bufferedReader().forEachLine { line ->
                    startupDiagnostics?.onSupervisorLine(line)
                    appendLog(line)
                }
            } catch (_: Exception) {
                // Stream closed while destroying; exit line below is enough.
            }
            val code = proc.waitFor()
            if (gb) {
                // The guest init's own log, captured by the
                // supervisor's /dev/__kmsg__ redirection.
                val kmsg = File(rootfs, ".kmsg")
                if (kmsg.exists() && kmsg.length() > 0) {
                    kmsg.readLines().forEach { appendLog("[init] $it") }
                } else {
                    appendLog("[init] (kmsg capture empty)")
                }
                // Loader errors from dynamic guests (their
                // stderr is /dev/null under init services).
                val lerr = File(rootfs, ".gbloader-err")
                if (lerr.exists() && lerr.length() > 0) {
                    lerr.readLines().forEach { appendLog("[loader] $it") }
                }
            }
            startupDiagnostics?.finish("supervisor exited with code $code")
            runOnUiThread {
                supervisor = null
                startupDiagnostics = null
                fbSession = null
                startButton.isEnabled = true
                probeButton.isEnabled = true
                gbButton.isEnabled = true
                stopButton.isEnabled = false
                statusView.text =
                    "rootfs: ${rootfs.absolutePath}\n狀態：監督器已結束"
            }
            appendLog("[shell] supervisor exited: $code")
        }
    }

    /** Poll the guest framebuffer file and present the
     * visible page. The guest draws into .fb0 through the
     * supervisor's shared mapping and reports pans in
     * .fb-page; this loop (~5 fps) is the whole display
     * path for now -- the picture above the log is the
     * guest's own pixels, byte for byte. */
    private fun startFbPreview(rootfs: File) {
        fbSession = rootfs
        runOnUiThread { fbView.visibility = android.view.View.VISIBLE }
        thread(name = "fb-preview") {
            val fbFile = File(rootfs, ".fb0")
            val pageFile = File(rootfs, ".fb-page")
            val pageBytes = 480 * 800 * 4
            val buf = ByteArray(pageBytes)
            // Reused across frames (0.9.55): allocating a
            // fresh 384k IntArray per frame churned the
            // app's own GC during exactly the boot stretch
            // where the interface must stay responsive.
            val ints = IntArray(480 * 800)
            // 0.9.54: the boot stretch is when the guest
            // floods the supervisor and the interface is
            // tightest; run the preview at 2 fps for the
            // first 75 seconds, then the usual 5 fps.
            val previewStart = System.currentTimeMillis()
            while (fbSession === rootfs) {
                try {
                    val yoff =
                        pageFile.readText().trim().toIntOrNull() ?: 0
                    RandomAccessFile(fbFile, "r").use { raf ->
                        raf.seek(yoff.toLong() * 480L * 4)
                        raf.readFully(buf)
                    }
                    val bmp = fbBitmap ?: Bitmap.createBitmap(
                        480,
                        800,
                        Bitmap.Config.ARGB_8888,
                    ).also { fbBitmap = it }
                    // The guest writes framebuffer-standard
                    // pixels (u32 0xAARRGGBB, stored little-
                    // endian as B,G,R,A bytes). Read back as
                    // little-endian ints they are exactly the
                    // 0xAARRGGBB values setPixels expects --
                    // no channel juggling. (0.7.0 copied the
                    // raw bytes into the bitmap, whose memory
                    // order is R,G,B,A, swapping red/blue;
                    // 0.7.1 then swapped a second time inside
                    // the ints and landed on the same wrong
                    // picture. The int path needs no swap.)
                    ByteBuffer.wrap(buf)
                        .order(java.nio.ByteOrder.LITTLE_ENDIAN)
                        .asIntBuffer()
                        .get(ints)
                    // The guest framebuffer is an opaque
                    // display: its alpha byte carries no
                    // meaning, and the compositor's writes
                    // leave it at 0 (the file starts zeroed
                    // and nothing sets it). Android treats
                    // alpha 0 as invisible, which made the
                    // preview render solid black over pages
                    // the supervisor's census could read
                    // perfectly (gun 5's 'always black'
                    // previews). Force full opacity here --
                    // fbprobe's own writes carried 0xFF,
                    // which is why its card showed in S6a.
                    for (i in ints.indices) {
                        ints[i] = ints[i] or -0x1000000
                    }
                    bmp.setPixels(ints, 0, 480, 0, 0, 480, 800)
                    runOnUiThread { fbView.setImageBitmap(bmp) }
                } catch (_: Exception) {
                    // Mid-teardown or a torn read: the next
                    // iteration (or the session end) sorts it.
                }
                try {
                    val bootPhase =
                        System.currentTimeMillis() - previewStart < 75_000
                    Thread.sleep(if (bootPhase) 500 else 200)
                } catch (_: InterruptedException) {
                    break
                }
            }
        }
    }

    private fun stopSupervisor() {
        // Flip the controls NOW (0.9.56): the state used
        // to change only after the supervisor had fully
        // died and its captured logs were read back,
        // which reads as a dead button during a flood.
        // The reader thread's completion block sets the
        // final state when the exit lands.
        stopButton.isEnabled = false
        statusView.text = "狀態：停止中…"
        // SIGTERM; the supervisor kills the guest root first, and
        // PTRACE_O_EXITKILL takes the rest of the tree with it.
        supervisor?.destroy()
    }

    private fun appendLog(line: String) {
        // The file gets every line, unconditionally and
        // first: it is the session's durable record.
        writeLogLineToFile(line)
        // The screen is a view, not the record: collapse
        // exact repeats so a log storm cannot drown the
        // UI (0.9.22's frozen-interface run), and (0.9.54)
        // accumulate the surviving lines
        // into a batch that one UI pass appends at most
        // every 250 ms -- a boot flood previously posted
        // one UI-thread task per line (~70k per boot),
        // which was the interface stutter itself.
        val needPost: Boolean
        synchronized(logFileLock) {
            if (line == lastUiLine) {
                dupLineCount++
                return
            }
            val collapsed = dupLineCount
            dupLineCount = 0
            lastUiLine = line
            if (collapsed >= 3) {
                pendingUiText.append(
                    "[shell] （上一行重複 $collapsed 次，畫面折疊；檔案有完整記錄）\n",
                )
            }
            pendingUiText.append(line).append('\n')
            needPost = !uiFlushPosted
            if (needPost) uiFlushPosted = true
        }
        if (needPost) {
            logView.postDelayed({
                val batch: String
                synchronized(logFileLock) {
                    batch = pendingUiText.toString()
                    pendingUiText.setLength(0)
                    uiFlushPosted = false
                }
                if (batch.isNotEmpty()) {
                    logView.append(batch)
                    // An ever-growing TextView makes every
                    // append re-lay-out the whole text;
                    // keep the tail. The cap was 256 KB
                    // until 0.9.58: at flood rates a layout
                    // pass over a quarter megabyte of text
                    // takes a visible slice of a second on
                    // this phone, so during boot the UI
                    // thread lived inside layout and even
                    // a button's disabled state painted
                    // late (field report: press, wait, then
                    // grey). 48 KB keeps several hundred
                    // lines on screen -- the file remains
                    // the complete record.
                    val t = logView.text
                    if (t.length > 49152) {
                        // Keep the LAST ~24 KB. Until 0.9.74
                        // this read subSequence(24576, len) --
                        // dropping only the first 24 KB and
                        // keeping everything else, so under a
                        // log flood the view text ratcheted
                        // upward without bound and every
                        // flush re-laid-out the whole thing
                        // until the main thread OOMed (field
                        // verdict 2026-11-07: [crash] stack
                        // ends in this setText's layout, heap
                        // 261 MB of a 256 MB limit).
                        logView.text =
                            "［畫面只保留最近的日誌，完整記錄在日誌檔案］\n" +
                            t.subSequence(t.length - 24576, t.length)
                    }
                }
                scrollView.fullScroll(ScrollView.FOCUS_DOWN)
            }, 250)
        }
    }
}
