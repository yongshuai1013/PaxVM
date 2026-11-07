package com.yongshuai.paxvm

import android.app.Activity
import android.os.Bundle
import android.text.InputType
import android.text.method.ScrollingMovementMethod
import android.view.Gravity
import android.widget.Button
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import java.io.IOException
import kotlin.concurrent.thread

/**
 * 系統限制 page (reached from the settings list). Android 12's
 * phantom process monitor can kill the whole supervisor
 * process group (the supervisors are child processes of the
 * app); this page pairs and connects to the device's own
 * wireless-debugging adbd via AdbLocal and turns the monitor
 * off plus raises the process cap, then reads both values
 * back. Every step lands verbatim in the on-page record view.
 * The page itself does not scroll; only the record view has
 * its own fixed-height scroll.
 */
class SystemLimitActivity : Activity() {

    private lateinit var statusView: TextView
    private lateinit var pairCodeInput: EditText
    private lateinit var pairPortInput: EditText
    private lateinit var connPortInput: EditText
    private lateinit var recordView: TextView

    private var adb: AdbLocal? = null

    // Serializes pairing / connect / lift / restore so two
    // operations never share the socket at once.
    @Volatile
    private var busy = false

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        buildUi()
    }

    override fun onDestroy() {
        adb?.close()
        super.onDestroy()
    }

    private fun buildUi() {
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(24, 24, 24, 24)
        }

        val header = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }
        val backButton = Button(this).apply {
            text = "返回"
            setOnClickListener { finish() }
        }
        header.addView(backButton)
        val title = TextView(this).apply {
            text = "系統限制"
            textSize = 18f
        }
        header.addView(title)
        root.addView(header)

        val desc = TextView(this).apply {
            text = "解除 Android 對 App 子行程的 phantom 監控與數量上限：" +
                "監督器群是 App 的子行程，監控開啟時可能被系統整組清掉。" +
                "透過無線偵錯以本機 ADB 寫入系統設定，主機固定 127.0.0.1。"
            textSize = 12f
        }
        root.addView(desc)

        statusView = TextView(this).apply {
            text = "狀態：未連接"
            textSize = 13f
        }
        root.addView(statusView)

        val pairHint = TextView(this).apply {
            text = "配對：先到「開發者選項 → 無線偵錯 → 使用配對碼配對裝置」取得配對碼與配對埠。"
            textSize = 12f
        }
        root.addView(pairHint)

        pairCodeInput = EditText(this).apply {
            hint = "配對碼（6 位）"
            inputType = InputType.TYPE_CLASS_NUMBER
        }
        root.addView(pairCodeInput)
        pairPortInput = EditText(this).apply {
            hint = "配對埠"
            inputType = InputType.TYPE_CLASS_NUMBER
        }
        root.addView(pairPortInput)
        val pairButton = Button(this).apply {
            text = "配對"
            setOnClickListener { onPairClicked() }
        }
        root.addView(pairButton)

        val connHint = TextView(this).apply {
            text = "連接埠在無線偵錯主頁顯示。"
            textSize = 12f
        }
        root.addView(connHint)
        connPortInput = EditText(this).apply {
            hint = "連接埠"
            inputType = InputType.TYPE_CLASS_NUMBER
        }
        root.addView(connPortInput)
        val connButton = Button(this).apply {
            text = "連接"
            setOnClickListener { onConnectClicked() }
        }
        root.addView(connButton)

        val liftButton = Button(this).apply {
            text = "解除限制"
            setOnClickListener { onLiftClicked(restore = false) }
        }
        root.addView(liftButton)
        val restoreButton = Button(this).apply {
            text = "還原"
            setOnClickListener { onLiftClicked(restore = true) }
        }
        root.addView(restoreButton)

        val recordTitle = TextView(this).apply {
            text = "操作紀錄"
            textSize = 13f
        }
        root.addView(recordTitle)
        recordView = TextView(this).apply {
            textSize = 11f
            typeface = android.graphics.Typeface.MONOSPACE
            movementMethod = ScrollingMovementMethod()
        }
        val recordScroll = ScrollView(this).apply { addView(recordView) }
        root.addView(
            recordScroll,
            LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                (260 * resources.displayMetrics.density).toInt(),
            ),
        )

        setContentView(root)
    }

    // ----- record / status helpers -----

    private fun record(line: String) {
        runOnUiThread { recordView.append(line + "\n") }
    }

    private fun setStatus(text: String) {
        runOnUiThread { statusView.text = "狀態：$text" }
    }

    private fun errorText(e: Exception): String =
        generateSequence<Throwable>(e) { it.cause }
            .joinToString(" ← ") { "${it.javaClass.simpleName}: ${it.message}" }

    private fun ensureAdb(): AdbLocal =
        adb ?: AdbLocal(AdbKeys(this)) { msg -> record(msg) }.also { adb = it }

    /** Runs [block] on a background thread under the busy gate. */
    private fun runOp(name: String, block: () -> Unit) {
        if (busy) {
            record("$name：已有操作進行中，請等它完成")
            return
        }
        busy = true
        thread {
            try {
                block()
            } catch (e: Exception) {
                record("$name 失敗：" + errorText(e))
            } finally {
                busy = false
            }
        }
    }

    private fun parsePort(raw: String, what: String): Int {
        val port = raw.trim().toIntOrNull()
        if (port == null || port !in 1..65535) {
            throw IOException("$what 未填或不是有效的埠號：'$raw'")
        }
        return port
    }

    // ----- actions -----

    private fun onPairClicked() {
        val code = pairCodeInput.text.toString().trim()
        val portRaw = pairPortInput.text.toString()
        runOp("配對") {
            if (code.isEmpty()) throw IOException("配對碼未填")
            val port = parsePort(portRaw, "配對埠")
            record("配對開始：127.0.0.1:$port")
            ensureAdb().pair(HOST, port, code)
            record("配對完成（之後請按「連接」）")
        }
    }

    private fun onConnectClicked() {
        val portRaw = connPortInput.text.toString()
        runOp("連接") {
            val port = parsePort(portRaw, "連接埠")
            val client = ensureAdb()
            try {
                client.connect(HOST, port)
            } catch (e: Exception) {
                client.close()
                throw e
            }
            setStatus("已連接")
            record("連接完成")
        }
    }

    private fun shellLogged(client: AdbLocal, command: String): String {
        val out = client.shell(command).trim()
        record("\$ $command")
        record(if (out.isEmpty()) "（無輸出）" else out)
        return out
    }

    private fun onLiftClicked(restore: Boolean) {
        val name = if (restore) "還原" else "解除限制"
        val portRaw = connPortInput.text.toString()
        runOp(name) {
            val client = ensureAdb()
            if (!client.isConnected) {
                val port = parsePort(portRaw, "連接埠")
                record("尚未連接，先自動連接 127.0.0.1:$port")
                try {
                    client.connect(HOST, port)
                } catch (e: Exception) {
                    client.close()
                    throw e
                }
                setStatus("已連接")
            }
            if (!restore) {
                shellLogged(client, "settings put global settings_enable_monitor_phantom_procs false")
                shellLogged(client, "device_config put activity_manager max_phantom_processes 2147483647")
            } else {
                shellLogged(client, "settings put global settings_enable_monitor_phantom_procs true")
                shellLogged(client, "device_config delete activity_manager max_phantom_processes")
            }
            val monitor = shellLogged(client, "settings get global settings_enable_monitor_phantom_procs")
            val max = shellLogged(client, "device_config get activity_manager max_phantom_processes")
            if (!restore) {
                record("驗證：settings_enable_monitor_phantom_procs=$monitor（期望 false）；" +
                    "max_phantom_processes=$max（期望 2147483647）")
                if (monitor == "false") {
                    setStatus("已解除（讀回值 false）")
                    record("解除限制完成")
                } else {
                    record("注意：monitor 讀回不是 false，解除未生效")
                }
            } else {
                record("驗證：settings_enable_monitor_phantom_procs=$monitor（期望 true）；" +
                    "max_phantom_processes=$max（期望 null）")
                record("還原完成")
            }
        }
    }

    companion object {
        private const val HOST = "127.0.0.1"
    }
}
