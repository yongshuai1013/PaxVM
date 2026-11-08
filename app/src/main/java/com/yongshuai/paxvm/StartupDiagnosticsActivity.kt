package com.yongshuai.paxvm

import android.app.Activity
import android.app.AlertDialog
import android.content.Intent
import android.os.Bundle
import android.view.Gravity
import android.widget.Button
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import java.io.File
import kotlin.concurrent.thread

class StartupDiagnosticsActivity : Activity() {
    private lateinit var previewView: TextView
    private var pendingExportRun: File? = null

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        title = "啟動診斷"

        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(16, 12, 16, 16)
        }
        val buttons = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }
        buttons.addView(Button(this).apply {
            text = "更新預覽"
            setOnClickListener { refreshPreview() }
        })
        buttons.addView(Button(this).apply {
            text = "匯出診斷 ZIP"
            setOnClickListener { confirmExport() }
        })
        root.addView(buttons)

        previewView = TextView(this).apply {
            textSize = 13f
            typeface = android.graphics.Typeface.MONOSPACE
            setTextIsSelectable(true)
            setPadding(4, 8, 4, 16)
        }
        root.addView(ScrollView(this).apply {
            addView(previewView)
        }, LinearLayout.LayoutParams(
            LinearLayout.LayoutParams.MATCH_PARENT,
            0,
            1f,
        ))
        setContentView(root)
        refreshPreview()
    }

    private fun refreshPreview() {
        previewView.text = StartupDiagnostics.preview(this)
    }

    private fun confirmExport() {
        val run = StartupDiagnostics.latestRun(this)
        if (run == null) {
            Toast.makeText(this, "尚無可匯出的啟動診斷記錄", Toast.LENGTH_LONG).show()
            return
        }
        AlertDialog.Builder(this)
            .setTitle("匯出前請留意隱私")
            .setMessage(
                "診斷檔可能包含客體日誌文字、檔案路徑、程序資訊及其他個人資料。" +
                    "目前資料僅保存在 PaxVM 的本機私有空間，不會由 app 自動上傳。" +
                    "只有在你繼續並選擇匯出位置後才會複製；若選到會同步的雲端文件提供者，" +
                    "該提供者可能自行同步。請選擇裝置上的本機位置。",
            )
            .setNegativeButton("取消", null)
            .setPositiveButton("選擇本機位置") { _, _ -> launchDocumentPicker(run) }
            .show()
    }

    private fun launchDocumentPicker(run: File) {
        pendingExportRun = run
        val intent = Intent(Intent.ACTION_CREATE_DOCUMENT).apply {
            addCategory(Intent.CATEGORY_OPENABLE)
            type = "application/zip"
            putExtra(Intent.EXTRA_TITLE, "PaxVM-startup-diagnostics-${run.name}.zip")
        }
        try {
            startActivityForResult(intent, REQUEST_CREATE_DOCUMENT)
        } catch (e: Exception) {
            pendingExportRun = null
            Toast.makeText(this, "無法開啟本機文件選擇器：${e.message}", Toast.LENGTH_LONG).show()
        }
    }

    @Deprecated("Uses the platform document picker for older supported Android versions")
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        if (requestCode != REQUEST_CREATE_DOCUMENT) return
        val run = pendingExportRun
        pendingExportRun = null
        val uri = data?.data
        if (resultCode != RESULT_OK || uri == null || run == null) {
            Toast.makeText(this, "已取消匯出", Toast.LENGTH_SHORT).show()
            return
        }
        thread(name = "startup-diagnostics-export") {
            try {
                val output = contentResolver.openOutputStream(uri)
                    ?: throw IllegalStateException("無法寫入所選位置")
                StartupDiagnostics.exportZip(run, output)
                runOnUiThread {
                    Toast.makeText(this, "診斷 ZIP 已匯出到所選位置", Toast.LENGTH_LONG).show()
                }
            } catch (e: Exception) {
                runOnUiThread {
                    Toast.makeText(this, "匯出失敗：${e.message}", Toast.LENGTH_LONG).show()
                }
            }
        }
    }

    companion object {
        private const val REQUEST_CREATE_DOCUMENT = 7301
    }
}
