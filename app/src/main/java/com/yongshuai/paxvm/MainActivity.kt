package com.yongshuai.paxvm

import android.app.Activity
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
    private var logFileOut: FileOutputStream? = null
    private val logFileLock = Object()
    private var previousLogFile: File? = null
    private var sessionRan = false

    // On-screen log flood guards (0.9.23): exact-repeat
    // lines collapse, the view is trimmed when huge (a
    // TextView append re-lays-out the whole text, so an
    // unbounded view freezes the UI under a log storm),
    // and scrolls coalesce. The file keeps everything.
    private var lastUiLine: String? = null
    private var dupLineCount = 0
    @Volatile private var scrollPosted = false

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
        "    setprop pax.stage init",
        "",
        "on fs",
        "    setprop pax.stage fs",
        "",
        "on boot",
        "    setprop pax.stage boot",
        "    start servicemanager",
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
        // S7 gun 1: the real zygote, standing alone. No
        // --start-system-server yet (system_server is S8:
        // if it dies, GB's zygote takes itself down with
        // it, which would muddy this gun's verdict). The
        // socket line makes the stock init create
        // /dev/socket/zygote and hand app_process the fd,
        // exactly as on hardware. No user line: root, as
        // in the stock rc. The stock onrestart /sys writes
        // are omitted -- this guest has no real sysfs for
        // them to land on.
        "service zygote /system/bin/app_process -Xzygote /system/bin --zygote",
        "    socket zygote stream 666",
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
        buildUi()
        prepareRootfs(rootfsDir)
        statusView.text = "rootfs: ${rootfsDir.absolutePath}\n狀態：待命"
        val prev = previousLogFile
        if (prev != null && prev.exists() && prev.length() > 0) {
            appendLog("[shell] 上一場的日誌已保留（${prev.length()} 位元組）；本場未啟動前按「下載日誌」可取得")
        }
    }

    /** Rotate the session log files and open this
     * launch's writer. Never throws: logging must not be
     * able to take the app down. */
    private fun initLogFiles() {
        try {
            val cur = File(filesDir, "session-log.txt")
            val prev = File(filesDir, "previous-session-log.txt")
            if (cur.exists() && cur.length() > 0) {
                if (prev.exists()) prev.delete()
                cur.renameTo(prev)
                previousLogFile = prev
            }
            logFileOut = FileOutputStream(cur, true)
        } catch (e: Exception) {
            logFileOut = null
        }
    }

    private fun writeLogLineToFile(line: String) {
        val out = logFileOut ?: return
        try {
            synchronized(logFileLock) {
                out.write((line + "\n").toByteArray(Charsets.UTF_8))
            }
        } catch (e: Exception) {
            // A dead log file must not break the session.
        }
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
                startSupervisor(rootfsDir, "libbusybox.so", listOf("sh", "/verify.sh"))
            }
        }
        probeButton = Button(this).apply {
            text = "啟動32"
            setOnClickListener {
                startSupervisor(rootfs32Dir, "libbusybox32.so", listOf("sh", "/verify.sh"))
            }
        }
        gbButton = Button(this).apply {
            text = "啟動GB"
            setOnClickListener {
                startSupervisor(
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
    private fun prepareGBRootfs(rootfs: File) {
        for (d in listOf("bin", "dev", "proc", "sys", "system", "data", "data/property", "sbin", "tmp")) {
            File(rootfs, d).mkdirs()
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
        writeFresh(File(rootfs, "init.rc"), gbInitRc)
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
        val marker = File(sysDir, ".gbsystem-v18")
        if (!marker.exists()) {
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

    /** Save the whole log view as a .txt in the device's
     * Download folder (MediaStore on API 29+, no permission
     * needed; legacy public dir below that). Added 0.3.5 at the
     * user's request, alongside 複製日誌. */
    private fun saveLog() {
        // The session log FILE is the complete record; the
        // on-screen view is trimmed and can lag behind.
        // Serve the file whenever it has content -- this
        // launch's file first (it holds the whole session,
        // untrimmed), then the previous launch's (the
        // force-stop-and-reopen recovery) -- and fall back
        // to the view only when no file exists (0.9.24;
        // 0.9.23's view-first logic returned just the
        // trimmed tail for a session downloaded in the
        // same launch).
        val prev = previousLogFile
        val cur = File(filesDir, "session-log.txt")
        val fromFile: File? = when {
            cur.exists() && cur.length() > 0 -> cur
            prev != null && prev.exists() && prev.length() > 0 -> prev
            else -> null
        }
        val fromPrevious = fromFile != null && prev != null &&
            fromFile.absolutePath == prev.absolutePath
        val text = if (fromFile != null) {
            try {
                fromFile.readText()
            } catch (e: Exception) {
                logView.text.toString()
            }
        } else {
            logView.text.toString()
        }
        // Guest log channels (S7 gun 3): the supervisor
        // maps /dev/log/* to plain files under .logs/;
        // fold a printable-strings extraction of the main
        // and system channels into the saved log, so the
        // guest runtime's own error account (the thing
        // that was invisible while app_process died
        // silently) travels with every log download.
        val guestLogs = StringBuilder()
        for (ch in listOf("main", "system")) {
            val f = File(rootfsGBDir, ".logs/log-$ch")
            if (f.exists() && f.length() > 0) {
                val bytes = try {
                    f.readBytes()
                } catch (e: Exception) {
                    ByteArray(0)
                }
                // Parse the GB logger_entry stream properly
                // (20-byte header: u16 len, u16 pad, pid,
                // tid, sec, nsec; payload = priority byte,
                // NUL-terminated tag, message). The 0.9.51
                // strings extraction drowned the signal:
                // SurfaceFlinger's pixelflinger tag floods
                // the channel, so its entries are dropped
                // here and the runtime's own lines (Zygote,
                // AndroidRuntime) survive to the saved log.
                val entries = ArrayList<String>()
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
                    while (p < off + 20 + len && bytes[p] != 0.toByte()) p++
                    if (p >= off + 20 + len) {
                        off++
                        continue
                    }
                    val tag = String(bytes, tagStart, p - tagStart, Charsets.UTF_8)
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
                        entries.add("$pl/$tag($pid): $msg")
                    }
                    off += 20 + len
                }
                val body = if (entries.isNotEmpty()) {
                    entries.takeLast(500).joinToString("\n")
                } else {
                    // Fallback: the old strings extraction.
                    val sb = StringBuilder()
                    var run = StringBuilder()
                    for (b in bytes) {
                        val c = (b.toInt() and 0xFF).toChar()
                        if (c in ' '..'~' || c == '\n' || c == '\t') {
                            run.append(c)
                        } else {
                            if (run.length >= 6) sb.append(run).append('\n')
                            run = StringBuilder()
                        }
                    }
                    if (run.length >= 6) sb.append(run).append('\n')
                    sb.toString().takeLast(24000)
                }
                if (body.isNotEmpty()) {
                    guestLogs.append(
                        "\n===== guest /dev/log/$ch =====\n",
                    ).append(body)
                }
            }
        }
        val outText = text + guestLogs.toString()
        val stamp = SimpleDateFormat("yyyyMMdd-HHmmss", Locale.US).format(Date())
        val name = "paxvm-log-$stamp.txt"
        try {
            if (Build.VERSION.SDK_INT >= 29) {
                val values = ContentValues().apply {
                    put(MediaStore.Downloads.DISPLAY_NAME, name)
                    put(MediaStore.Downloads.MIME_TYPE, "text/plain")
                    put(
                        MediaStore.Downloads.RELATIVE_PATH,
                        Environment.DIRECTORY_DOWNLOADS,
                    )
                }
                val uri = contentResolver.insert(
                    MediaStore.Downloads.EXTERNAL_CONTENT_URI,
                    values,
                ) ?: throw IOException("MediaStore insert returned null")
                val out = contentResolver.openOutputStream(uri)
                    ?: throw IOException("openOutputStream returned null")
                out.use { it.write(outText.toByteArray(Charsets.UTF_8)) }
            } else {
                val dir = Environment.getExternalStoragePublicDirectory(
                    Environment.DIRECTORY_DOWNLOADS,
                )
                dir.mkdirs()
                File(dir, name).writeText(outText)
            }
            appendLog(
                if (fromPrevious) "[shell] 上一場日誌已存到 Download/$name"
                else "[shell] 日誌已存到 Download/$name"
            )
        } catch (e: Exception) {
            appendLog("[shell] 存日誌失敗：$e")
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
        if (gb) {
            prepareGBRootfs(rootfs)
        } else {
            prepareRootfs(rootfs)
        }
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
            return
        }
        supervisor = proc
        sessionRan = true
        if (gb) {
            startFbPreview(rootfs)
        }
        startButton.isEnabled = false
        probeButton.isEnabled = false
        gbButton.isEnabled = false
        stopButton.isEnabled = true
        statusView.text = "rootfs: ${rootfs.absolutePath}\n狀態：監督器執行中"
        appendLog("[shell] supervisor started")
        thread(name = "supervisor-reader") {
            try {
                proc.inputStream.bufferedReader().forEachLine { line ->
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
            runOnUiThread {
                supervisor = null
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
                    val ints = IntArray(480 * 800)
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
                    Thread.sleep(200)
                } catch (_: InterruptedException) {
                    break
                }
            }
        }
    }

    private fun stopSupervisor() {
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
        // UI thread (0.9.22's frozen-interface run).
        val collapsed: Int
        synchronized(logFileLock) {
            if (line == lastUiLine) {
                dupLineCount++
                return
            }
            collapsed = dupLineCount
            dupLineCount = 0
            lastUiLine = line
        }
        runOnUiThread {
            if (collapsed >= 3) {
                logView.append("[shell] （上一行重複 $collapsed 次，畫面折疊；檔案有完整記錄）\n")
            }
            logView.append(line + "\n")
            // An ever-growing TextView makes every append
            // re-lay-out the whole text; keep the tail.
            val t = logView.text
            if (t.length > 262144) {
                logView.text = "［畫面只保留最近的日誌，完整記錄在日誌檔案］\n" +
                    t.subSequence(131072, t.length)
            }
            if (!scrollPosted) {
                scrollPosted = true
                scrollView.postDelayed({
                    scrollPosted = false
                    scrollView.fullScroll(ScrollView.FOCUS_DOWN)
                }, 200)
            }
        }
    }
}
