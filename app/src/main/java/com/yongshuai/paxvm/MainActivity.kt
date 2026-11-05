package com.yongshuai.paxvm

import android.app.Activity
import android.graphics.Typeface
import android.os.Bundle
import android.system.Os
import android.text.method.ScrollingMovementMethod
import android.view.Gravity
import android.widget.Button
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import java.io.File
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
 */
class MainActivity : Activity() {

    private lateinit var statusView: TextView
    private lateinit var logView: TextView
    private lateinit var scrollView: ScrollView
    private lateinit var startButton: Button
    private lateinit var stopButton: Button

    private var supervisor: Process? = null

    private val rootfsDir: File
        get() = File(filesDir, "vm0/rootfs")

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
        prepareRootfs()
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
            setOnClickListener { startSupervisor() }
        }
        stopButton = Button(this).apply {
            text = "停止"
            isEnabled = false
            setOnClickListener { stopSupervisor() }
        }
        buttons.addView(startButton)
        buttons.addView(stopButton)
        root.addView(buttons)

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

    /** Idempotent: build the rootfs tree the busybox guest expects. */
    private fun prepareRootfs() {
        val rootfs = rootfsDir
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
        File(rootfs, "verify.sh").writeText(verifyScript)
    }

    private fun startSupervisor() {
        if (supervisor != null) return
        prepareRootfs()
        val libDir = applicationInfo.nativeLibraryDir
        val cmd = listOf(
            "$libDir/libsupervisor.so",
            rootfsDir.absolutePath,
            "$libDir/libbusybox.so",
            "--",
            "sh",
            "/verify.sh",
        )
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
        stopButton.isEnabled = true
        statusView.text = "rootfs: ${rootfsDir.absolutePath}\n狀態：監督器執行中"
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
            runOnUiThread {
                supervisor = null
                startButton.isEnabled = true
                stopButton.isEnabled = false
                statusView.text =
                    "rootfs: ${rootfsDir.absolutePath}\n狀態：監督器已結束"
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
