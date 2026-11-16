package com.yongshuai.paxvm

import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.app.Service
import android.content.Context
import android.content.Intent
import android.content.pm.ServiceInfo
import android.os.Build
import android.os.IBinder

/** Foreground keep-alive for a running supervisor
 * session (0.9.174). Field runs kept ending early
 * because the host reaps the shell once it leaves the
 * foreground; the supervisor is the shell's child
 * process, so a reaped shell takes the whole guest
 * tree with it. While a supervisor runs, MainActivity
 * starts this service; the service's only job is to
 * hold a foreground notification so the process keeps
 * foreground priority. It owns no supervisor state:
 * MainActivity stops it when the supervisor's reader
 * thread reports the exit. */
class SupervisorService : Service() {

    override fun onBind(intent: Intent?): IBinder? = null

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        val manager = getSystemService(NotificationManager::class.java)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            manager.createNotificationChannel(
                NotificationChannel(
                    CHANNEL_ID,
                    "PaxVM 監督器",
                    NotificationManager.IMPORTANCE_LOW,
                ),
            )
        }
        val openApp = PendingIntent.getActivity(
            this,
            0,
            Intent(this, MainActivity::class.java),
            PendingIntent.FLAG_IMMUTABLE,
        )
        val notification: Notification = Notification.Builder(this, CHANNEL_ID)
            .setContentTitle("PaxVM")
            .setContentText("監督器執行中")
            .setSmallIcon(android.R.drawable.ic_dialog_info)
            .setContentIntent(openApp)
            .setOngoing(true)
            .build()
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.UPSIDE_DOWN_CAKE) {
            startForeground(
                NOTIFICATION_ID,
                notification,
                ServiceInfo.FOREGROUND_SERVICE_TYPE_SPECIAL_USE,
            )
        } else {
            startForeground(NOTIFICATION_ID, notification)
        }
        return START_NOT_STICKY
    }

    companion object {
        private const val CHANNEL_ID = "paxvm-supervisor"
        private const val NOTIFICATION_ID = 1

        /** Call only from a foreground context (the
         * start button's click qualifies): Android
         * requires startForegroundService to be issued
         * while the app is in the foreground. */
        fun start(context: Context) {
            val intent = Intent(context, SupervisorService::class.java)
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                context.startForegroundService(intent)
            } else {
                context.startService(intent)
            }
        }

        fun stop(context: Context) {
            context.stopService(Intent(context, SupervisorService::class.java))
        }
    }
}
