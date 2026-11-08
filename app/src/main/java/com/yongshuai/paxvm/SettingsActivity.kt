package com.yongshuai.paxvm

import android.app.Activity
import android.content.Intent
import android.os.Bundle
import android.preference.Preference
import android.preference.PreferenceFragment
import android.preference.SwitchPreference

/**
 * Settings page: the platform's own preference list
 * (the user asked for the native layout over the
 * hand-rolled rows). Each Preference carries its
 * destination as an intent -- the native settings
 * behaviour, with native row height, typography,
 * dividers and press states. First entry: 系統限制
 * (SystemLimitActivity).
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
            // Title slot carries the word 返回 next to
            // the arrow (the user asked for the text
            // there), not the page name.
            setDisplayShowTitleEnabled(true)
            // The genuine Android 4.4 Holo up indicator
            // (ic_ab_back_holo_dark_am from AOSP 4.4) --
            // the modern framework's thin chevron looked
            // wrong to the user.
            setHomeAsUpIndicator(R.drawable.ic_ab_back_holo_dark)
        }
        setTitle("返回")
        fragmentManager.beginTransaction()
            .replace(android.R.id.content, SettingsFragment())
            .commit()
    }

    override fun onOptionsItemSelected(item: android.view.MenuItem): Boolean {
        if (item.itemId == android.R.id.home) {
            finish()
            return true
        }
        return super.onOptionsItemSelected(item)
    }

    class SettingsFragment : PreferenceFragment() {
        override fun onCreate(savedInstanceState: Bundle?) {
            super.onCreate(savedInstanceState)
            val screen = preferenceManager.createPreferenceScreen(activity)
            val limits = Preference(activity)
            limits.title = "系統限制"
            limits.summary = "phantom 監控與子行程上限"
            limits.intent = Intent(activity, SystemLimitActivity::class.java)
            screen.addPreference(limits)
            val diagnostics = SwitchPreference(activity).apply {
                key = StartupDiagnostics.PREF_KEY
                title = "啟動診斷"
                summary = "收集 Gingerbread 啟動階段與可用客體日誌；僅存本機、不自動上傳，保留最近 3 次"
                setDefaultValue(false)
            }
            screen.addPreference(diagnostics)
            val preview = Preference(activity).apply {
                title = "檢視／匯出啟動診斷"
                summary = "預覽最近一次記錄；匯出前會顯示隱私提醒"
                intent = Intent(activity, StartupDiagnosticsActivity::class.java)
            }
            screen.addPreference(preview)
            preferenceScreen = screen
        }
    }
}
