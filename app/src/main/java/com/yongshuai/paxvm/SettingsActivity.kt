package com.yongshuai.paxvm

import android.app.Activity
import android.content.Intent
import android.os.Bundle
import android.view.Gravity
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
        // Back lives in the action bar (the user asked
        // for the up arrow where the app icon was, and
        // for the icon and title to go away there).
        actionBar?.apply {
            setDisplayHomeAsUpEnabled(true)
            setDisplayShowHomeEnabled(false)
            setDisplayShowTitleEnabled(false)
        }
        buildUi()
    }

    override fun onOptionsItemSelected(item: android.view.MenuItem): Boolean {
        if (item.itemId == android.R.id.home) {
            finish()
            return true
        }
        return super.onOptionsItemSelected(item)
    }

    private fun buildUi() {
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setPadding(24, 24, 24, 24)
        }

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
