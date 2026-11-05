package com.yongshuai.paxvm

import android.app.Activity
import android.graphics.Typeface
import android.os.Bundle
import android.text.method.ScrollingMovementMethod
import android.view.Gravity
import android.widget.Button
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import java.io.File
import kotlin.concurrent.thread

/**
 * PaxVM M0 shell.
 *
 * Deliberately has zero JNI: the engine lives in a standalone native
 * process (libsupervisor.so, a Rust ptrace supervisor) that the shell
 * starts with ProcessBuilder and talks to only through its stdout line
 * protocol ([sup] / [sys] / [guest] lines, printed verbatim).
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

    /** Idempotent: create the rootfs tree and seed file once. */
    private fun prepareRootfs() {
        val rootfs = rootfsDir
        File(rootfs, "tmp").mkdirs()
        val seed = File(rootfs, "seed.txt")
        if (!seed.exists()) {
            seed.writeText("seed-42")
        }
    }

    private fun startSupervisor() {
        if (supervisor != null) return
        prepareRootfs()
        val libDir = applicationInfo.nativeLibraryDir
        val cmd = listOf(
            "$libDir/libsupervisor.so",
            rootfsDir.absolutePath,
            "$libDir/libguest.so",
        )
        val proc = try {
            ProcessBuilder(cmd)
                .redirectErrorStream(true)
                .start()
        } catch (e: Exception) {
            // Do not swallow: packaging/exec problems (spec risk 7)
            // surface here verbatim.
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
        // SIGTERM; the supervisor kills the guest first, and
        // PTRACE_O_EXITKILL is the backstop (spec section 4).
        supervisor?.destroy()
    }

    private fun appendLog(line: String) {
        runOnUiThread {
            logView.append(line + "\n")
            scrollView.post { scrollView.fullScroll(ScrollView.FOCUS_DOWN) }
        }
    }
}
