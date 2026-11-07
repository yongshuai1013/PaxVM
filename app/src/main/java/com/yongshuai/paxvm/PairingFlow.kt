package com.yongshuai.paxvm

import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.RemoteInput
import android.app.Service
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.graphics.drawable.Icon
import android.os.Build
import android.os.IBinder
import java.io.File
import java.io.IOException
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import kotlin.concurrent.thread

/**
 * Notification-based pairing, modeled on the flow the user
 * pointed at (a competitor VM app): the user opens the system's
 * wireless-debugging pairing dialog, pulls the notification
 * shade down over it, and types the 6-digit code into this app's
 * notification reply field -- no app switching, and the pairing
 * dialog stays alive underneath. The reply lands in
 * PairReplyReceiver, which hands the code to PairingService;
 * the service discovers the pairing endpoint over mDNS, pairs
 * with AdbLocal, verifies the connect endpoint too, and writes
 * the full transcript to filesDir/pair-result.txt for the
 * system-limit page to pick up on resume.
 */
object PairingFlow {

    const val CHANNEL_ID = "paxvm_pairing"
    const val KEY_PAIR_CODE = "pair_code"
    const val ACTION_PAIR_REPLY = "com.yongshuai.paxvm.PAIR_CODE"
    const val RESULT_FILE = "pair-result.txt"
    const val RESULT_FILE_CONSUMED = "pair-result-consumed.txt"

    private const val NOTIF_ID_PAIR = 4101
    private const val NOTIF_ID_RESULT = 4102

    fun ensureChannel(context: Context) {
        if (Build.VERSION.SDK_INT < 26) return
        val nm = context.getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        if (nm.getNotificationChannel(CHANNEL_ID) == null) {
            nm.createNotificationChannel(
                NotificationChannel(CHANNEL_ID, "PaxVM 配對", NotificationManager.IMPORTANCE_HIGH).apply {
                    description = "無線偵錯配對碼輸入與配對結果"
                },
            )
        }
    }

    /** True when a notification posted now would actually show. */
    fun canPost(context: Context): Boolean {
        // POST_NOTIFICATIONS is a runtime permission only from
        // API 33; below that, posting always works.
        if (Build.VERSION.SDK_INT < 33) return true
        return context.checkSelfPermission("android.permission.POST_NOTIFICATIONS") ==
            PackageManager.PERMISSION_GRANTED
    }

    /**
     * Posts the pairing notification with a RemoteInput reply
     * action. [log] receives hints (e.g. missing permission);
     * callers route it to the page record.
     */
    fun postPairingNotification(context: Context, log: (String) -> Unit) {
        ensureChannel(context)
        if (!canPost(context)) {
            // Never pop a permission dialog from here; the page
            // requests it on the button tap instead.
            log("提醒：通知權限未授權（Android 13+ 需要 POST_NOTIFICATIONS），通知可能不會顯示")
        }
        val replyIntent = Intent(context, PairReplyReceiver::class.java).apply {
            action = ACTION_PAIR_REPLY
        }
        // RemoteInput requires a mutable PendingIntent so the
        // system can fill in the typed text as an extra.
        val replyPending = PendingIntent.getBroadcast(
            context,
            0,
            replyIntent,
            PendingIntent.FLAG_MUTABLE or PendingIntent.FLAG_UPDATE_CURRENT,
        )
        val remoteInput = RemoteInput.Builder(KEY_PAIR_CODE)
            .setLabel("輸入配對碼")
            .build()
        val replyAction = Notification.Action.Builder(
            Icon.createWithResource(context, android.R.drawable.ic_dialog_info),
            "輸入配對碼",
            replyPending,
        ).addRemoteInput(remoteInput).build()

        val text = "在無線偵錯的配對碼畫面下拉通知，在這裡輸入 6 位配對碼（配對畫面要保持開著）"
        val notification = Notification.Builder(context, CHANNEL_ID)
            .setSmallIcon(smallIcon(context))
            .setContentTitle("PaxVM 配對")
            .setContentText(text)
            .setStyle(Notification.BigTextStyle().bigText(text))
            .addAction(replyAction)
            .setOngoing(false)
            .setAutoCancel(false)
            .build()
        try {
            val nm = context.getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            nm.notify(NOTIF_ID_PAIR, notification)
            log("配對通知已發出")
        } catch (e: SecurityException) {
            log("配對通知發出失敗（權限）：${e.message}")
        }
    }

    /** Posts the outcome notification from PairingService. */
    fun postResultNotification(context: Context, success: Boolean, firstFailure: String) {
        ensureChannel(context)
        val text = if (success) "配對成功" else "配對失敗：$firstFailure"
        val notification = Notification.Builder(context, CHANNEL_ID)
            .setSmallIcon(smallIcon(context))
            .setContentTitle("PaxVM 配對結果")
            .setContentText(text)
            .setStyle(Notification.BigTextStyle().bigText(text))
            .setOngoing(false)
            .setAutoCancel(true)
            .build()
        try {
            val nm = context.getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            nm.notify(NOTIF_ID_RESULT, notification)
        } catch (e: SecurityException) {
            // Dropped silently by the system when the Android
            // 13+ permission is missing; the result file remains
            // the authoritative record.
        }
    }

    fun cancelPairingNotification(context: Context) {
        val nm = context.getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        nm.cancel(NOTIF_ID_PAIR)
    }

    private fun smallIcon(context: Context): Int {
        val res = context.applicationInfo.icon
        return if (res != 0) res else android.R.drawable.ic_dialog_info
    }
}

/** Receives the code typed into the notification reply field. */
class PairReplyReceiver : BroadcastReceiver() {
    override fun onReceive(context: Context, intent: Intent) {
        val results = RemoteInput.getResultsFromIntent(intent) ?: return
        val code = results.getCharSequence(PairingFlow.KEY_PAIR_CODE)?.toString()?.trim()
        if (code.isNullOrEmpty()) return
        // The pairing work takes tens of seconds (mDNS + TLS
        // pairing + connect check), far beyond a receiver's
        // budget: hand it to the service and return at once.
        val serviceIntent = Intent(context, PairingService::class.java).apply {
            putExtra(PairingService.EXTRA_CODE, code)
        }
        context.startService(serviceIntent)
        // The code is in; retire the input notification so the
        // shade does not keep a stale reply spinner.
        PairingFlow.cancelPairingNotification(context)
    }
}

/**
 * Runs one pairing attempt on its own thread: mDNS-discover the
 * pairing endpoint, AdbLocal.pair, then mDNS-discover the
 * connect endpoint and AdbLocal.connect to prove the whole
 * chain is alive. Writes the transcript (first line
 * 「配對成功 ...」 or 「配對失敗 ...：<reason>」) to
 * filesDir/pair-result.txt and posts a result notification.
 */
class PairingService : Service() {

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        val code = intent?.getStringExtra(EXTRA_CODE)?.trim().orEmpty()
        thread(name = "paxvm-pairing") {
            runPairing(code)
            stopSelf(startId)
        }
        return START_NOT_STICKY
    }

    private fun runPairing(code: String) {
        val lines = ArrayList<String>()
        fun log(line: String) {
            synchronized(lines) { lines.add(line) }
        }
        var success = false
        var firstFailure = ""
        val adb = AdbLocal(AdbKeys(this)) { msg -> log(msg) }
        try {
            if (code.isEmpty()) throw IOException("配對碼是空的")
            log("通知配對流程開始（碼長 ${code.length}）")
            val pairTarget = AdbMdns.discover(this, AdbMdns.TYPE_PAIRING, 20_000) { msg -> log(msg) }
                ?: throw IOException("mDNS 找不到配對服務（逾時）：請確認配對碼畫面還開著、且在同一個 Wi-Fi")
            log("配對目標：${pairTarget.first}:${pairTarget.second}")
            adb.pair(pairTarget.first, pairTarget.second, code)
            log("配對成功，接著驗證連接鏈")
            val connTarget = AdbMdns.discover(this, AdbMdns.TYPE_CONNECT, 15_000) { msg -> log(msg) }
                ?: throw IOException("mDNS 找不到連接服務（逾時）")
            log("連接目標：${connTarget.first}:${connTarget.second}")
            adb.connect(connTarget.first, connTarget.second)
            log("連接驗證成功")
            success = true
        } catch (e: Exception) {
            val chain = generateSequence<Throwable>(e) { it.cause }
                .joinToString(" ← ") { "${it.javaClass.simpleName}: ${it.message}" }
            firstFailure = chain.substringBefore(" ← ")
            log("流程失敗：$chain")
        } finally {
            try {
                adb.close()
            } catch (e: Exception) {
                log("關閉 ADB 連接時例外（忽略）：${e.message}")
            }
        }

        val stamp = SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US).format(Date())
        val header = if (success) "配對成功 $stamp" else "配對失敗 $stamp：$firstFailure"
        val body = buildString {
            append(header).append('\n')
            synchronized(lines) { lines.forEach { append(it).append('\n') } }
        }
        try {
            File(filesDir, PairingFlow.RESULT_FILE).writeText(body)
        } catch (e: Exception) {
            // The notification below still carries the verdict.
        }
        PairingFlow.postResultNotification(this, success, firstFailure)
    }

    companion object {
        const val EXTRA_CODE = "pair_code_extra"
    }
}
