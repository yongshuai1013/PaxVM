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
import android.widget.ScrollView
import android.widget.TextView
import java.io.IOException
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.io.File
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
        "    mkdir /data/misc",
        "    setprop pax.stage init",
        "",
        "on fs",
        "    setprop pax.stage fs",
        "",
        "on boot",
        "    setprop pax.stage boot",
        "    start paxprobe",
        "",
        "service paxprobe /bin/sh /probe.sh",
        "    oneshot",
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
        "/system/bin/servicemanager &",
        "sleep 1",
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
        buildUi()
        prepareRootfs(rootfsDir)
        statusView.text = "rootfs: ${rootfsDir.absolutePath}\n狀態：待命"
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
        writeFresh(File(rootfs, "init.rc"), gbInitRc)
        writeFresh(File(rootfs, "probe.sh"), gbProbeScript)
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
        val marker = File(sysDir, ".gbsystem-v1")
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
        val text = logView.text.toString()
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
                out.use { it.write(text.toByteArray(Charsets.UTF_8)) }
            } else {
                val dir = Environment.getExternalStoragePublicDirectory(
                    Environment.DIRECTORY_DOWNLOADS,
                )
                dir.mkdirs()
                File(dir, name).writeText(text)
            }
            appendLog("[shell] 日誌已存到 Download/$name")
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

    private fun stopSupervisor() {
        // SIGTERM; the supervisor kills the guest root first, and
        // PTRACE_O_EXITKILL takes the rest of the tree with it.
        supervisor?.destroy()
    }

    private fun appendLog(line: String) {
        runOnUiThread {
            logView.append(line + "\n")
            scrollView.post { scrollView.fullScroll(ScrollView.FOCUS_DOWN) }
        }
    }
}
