package com.yongshuai.paxvm

import android.app.Activity
import android.content.Intent
import android.os.Bundle
import android.view.Gravity
import android.widget.Button
import android.widget.LinearLayout
import android.widget.TextView

/**
 * Settings page: a plain list of entries, one row per
 * destination page (the user asked for a list, not one
 * long scrolling form). Tapping a row opens that page.
 * First entry: 系統限制 (SystemLimitActivity).
 */
class SettingsActivity : Activity() {

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        buildUi()
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
            text = "設定"
            textSize = 18f
        }
        header.addView(title)
        root.addView(header)

        root.addView(
            entryRow("系統限制", "phantom 監控與子行程上限") {
                startActivity(Intent(this, SystemLimitActivity::class.java))
            },
        )

        setContentView(root)
    }

    /** One list row: name + subtitle on the left, a
     * chevron on the right; the whole row is the tap
     * target. */
    private fun entryRow(
        name: String,
        subtitle: String,
        onClick: () -> Unit,
    ): LinearLayout {
        val row = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(8, 28, 8, 28)
            isClickable = true
            setOnClickListener { onClick() }
        }
        val texts = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
        }
        texts.addView(TextView(this).apply {
            text = name
            textSize = 16f
        })
        texts.addView(TextView(this).apply {
            text = subtitle
            textSize = 12f
        })
        row.addView(
            texts,
            LinearLayout.LayoutParams(
                0,
                LinearLayout.LayoutParams.WRAP_CONTENT,
                1f,
            ),
        )
        row.addView(TextView(this).apply {
            text = "›"
            textSize = 20f
        })
        return row
    }
}
