package com.yongshuai.paxvm

import android.app.Activity
import android.content.Intent
import android.os.Bundle
import android.preference.Preference
import android.preference.PreferenceFragment

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
            setDisplayShowTitleEnabled(false)
        }
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
            preferenceScreen = screen
        }
    }
}
