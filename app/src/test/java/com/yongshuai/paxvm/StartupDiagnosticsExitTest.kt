package com.yongshuai.paxvm

import org.junit.Assert.assertFalse
import org.junit.Assert.assertNotNull
import org.junit.Assert.assertTrue
import org.junit.Test

class StartupDiagnosticsExitTest {
    @Test
    fun normalCandidateExitDoesNotTriggerSnapshot() {
        val exit = parseSystemServerCandidateExit(
            "supervisor: SYSTEM_SERVER_EXIT pid=123 code=0",
        )

        assertNotNull(exit)
        assertFalse(exit!!.isAbnormal)
    }

    @Test
    fun nonzeroAndSignalCandidateExitsAreAbnormal() {
        val nonzero = parseSystemServerCandidateExit(
            "SYSTEM_SERVER_EXIT pid=123 code=1",
        )
        val signaled = parseSystemServerCandidateExit(
            "SYSTEM_SERVER_EXIT pid=124 sig=9",
        )

        assertTrue(nonzero?.isAbnormal == true)
        assertTrue(signaled?.isAbnormal == true)
    }

    @Test
    fun snapshotMessagePreservesCandidateOnlyLimitation() {
        val exit = parseSystemServerCandidateExit(
            "SYSTEM_SERVER_EXIT pid=123 sig=11",
        )!!
        val message = systemServerCandidateSnapshotMessage(exit)

        assertTrue(message.contains("候選追蹤"))
        assertTrue(message.contains("未確認為 system_server 崩潰"))
    }
}
