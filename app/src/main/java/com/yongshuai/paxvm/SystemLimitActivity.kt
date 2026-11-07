package com.yongshuai.paxvm

import android.app.Activity
import android.content.pm.PackageManager
import android.os.Build
import android.os.Bundle
import android.text.method.ScrollingMovementMethod
import android.widget.Button
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import java.io.File
import java.io.IOException
import kotlin.concurrent.thread

/**
 * 系統限制 page (reached from the settings list). Android 12's
 * phantom process monitor can kill the whole supervisor
 * process group (the supervisors are child processes of the
 * app); this page turns the monitor off plus raises the
 * process cap through the device's own wireless-debugging
 * adbd, then reads both values back.
 *
 * Pairing is notification-based: the "發出配對通知" button
 * posts a notification whose reply field takes the 6-digit
 * code while the system's pairing dialog stays open behind
 * the shade (see PairingFlow). All endpoints are discovered
 * over mDNS (AdbMdns) -- no port numbers are typed anywhere
 * on this page. The pairing outcome file is folded into the
 * record on resume. Every step lands verbatim in the on-page
 * record view. The page itself does not scroll; only the
 * record view has its own fixed-height scroll.
 */
class SystemLimitActivity : Activity() {

    private lateinit var statusView: TextView
    private lateinit var recordView: TextView

    private var adb: AdbLocal? = null

    // Serializes connect / lift / restore so two operations
    // never share the socket at once.
    @Volatile
    private var busy = false

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        // Back lives in the action bar (the user asked
        // for the up arrow where the app icon was, and
        // for the icon and title to go away there).
        actionBar?.apply {
            setDisplayHomeAsUpEnabled(true)
            setDisplayShowHomeEnabled(false)
            // Title slot carries the word 返回 next to
            // the arrow (see SettingsActivity's note).
            setDisplayShowTitleEnabled(true)
            // The genuine Android 4.4 Holo up indicator
            // (see SettingsActivity's note).
            setHomeAsUpIndicator(R.drawable.ic_ab_back_holo_dark)
        }
        setTitle("返回")
        buildUi()
    }

    override fun onOptionsItemSelected(item: android.view.MenuItem): Boolean {
        if (item.itemId == android.R.id.home) {
            finish()
            return true
        }
        return super.onOptionsItemSelected(item)
    }

    override fun onResume() {
        super.onResume()
        consumePairResult()
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

        val desc = TextView(this).apply {
            text = "解除 Android 對 App 子行程的 phantom 監控與數量上限：" +
                "監督器群是 App 的子行程，監控開啟時可能被系統整組清掉。" +
                "透過無線偵錯以本機 ADB 寫入系統設定，配對與連接埠皆以 mDNS 自動發現。"
            textSize = 12f
        }
        root.addView(desc)

        statusView = TextView(this).apply {
            text = "狀態：未連接"
            textSize = 13f
        }
        root.addView(statusView)

        val pairHint = TextView(this).apply {
            text = "配對：按「發出配對通知」後，到「開發者選項 → 無線偵錯 → 使用配對碼配對裝置」" +
                "打開配對碼畫面，下拉通知欄、在通知裡輸入 6 位配對碼（配對畫面要保持開著）。" +
                "配對結果會帶回本頁的操作紀錄。"
            textSize = 12f
        }
        root.addView(pairHint)
        val notifyButton = Button(this).apply {
            text = "發出配對通知"
            setOnClickListener { onPairNotifyClicked() }
        }
        root.addView(notifyButton)

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

    // ----- pairing result file -----

    /**
     * Folds a fresh filesDir/pair-result.txt (written by
     * PairingService) into the record once, then renames it to
     * the consumed name so later resumes do not append it again;
     * the service always writes the plain name, so a new result
     * is picked up the same way.
     */
    private fun consumePairResult() {
        try {
            val file = File(filesDir, PairingFlow.RESULT_FILE)
            if (!file.exists()) return
            val text = file.readText().trim()
            if (text.isNotEmpty()) {
                record("—— 通知配對結果 ——")
                text.lineSequence().forEach { record(it) }
                if (text.contains("配對成功")) {
                    setStatus("已配對（待連接）")
                }
            }
            val consumed = File(filesDir, PairingFlow.RESULT_FILE_CONSUMED)
            if (consumed.exists()) consumed.delete()
            if (!file.renameTo(consumed)) {
                record("注意：配對結果檔改名失敗，下次進頁可能重複顯示")
            }
        } catch (e: Exception) {
            record("讀取配對結果檔失敗：" + errorText(e))
        }
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

    // ----- actions -----

    private fun onPairNotifyClicked() {
        // Android 13+ needs the notification runtime permission;
        // ask here on the tap (never from the service) and let
        // the user tap again once granted.
        if (Build.VERSION.SDK_INT >= 33 &&
            checkSelfPermission(POST_NOTIFICATIONS_PERMISSION) != PackageManager.PERMISSION_GRANTED
        ) {
            requestPermissions(arrayOf(POST_NOTIFICATIONS_PERMISSION), REQUEST_NOTIFICATIONS)
            record("Android 13+ 需要通知權限，已請求授權；授權後請再按一次「發出配對通知」")
            return
        }
        PairingFlow.postPairingNotification(this) { msg -> record(msg) }
        record("步驟：① 到開發者選項的無線偵錯打開「使用配對碼配對裝置」畫面")
        record("步驟：② 下拉通知欄，在「PaxVM 配對」通知裡輸入 6 位配對碼（配對畫面保持開著）")
        record("步驟：③ 回到本頁，配對結果會出現在這裡")
    }

    private fun shellLogged(client: AdbLocal, command: String): String {
        val out = client.shell(command).trim()
        record("\$ $command")
        record(if (out.isEmpty()) "（無輸出）" else out)
        return out
    }

    private fun onLiftClicked(restore: Boolean) {
        val name = if (restore) "還原" else "解除限制"
        runOp(name) {
            val client = ensureAdb()
            if (!client.isConnected) {
                record("尚未連接，先以 mDNS 發現連接服務（逾時 15 秒）")
                val target = AdbMdns.discover(
                    this@SystemLimitActivity,
                    AdbMdns.TYPE_CONNECT,
                    15_000,
                ) { msg -> record(msg) }
                    ?: throw IOException("mDNS 找不到連接服務（逾時）：請確認無線偵錯已開啟、且在同一個 Wi-Fi")
                record("連接：${target.first}:${target.second}")
                try {
                    client.connect(target.first, target.second)
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
        private const val POST_NOTIFICATIONS_PERMISSION = "android.permission.POST_NOTIFICATIONS"
        private const val REQUEST_NOTIFICATIONS = 1001
    }
}
