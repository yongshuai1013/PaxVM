package com.yongshuai.paxvm

import org.junit.Assert.assertEquals
import org.junit.Assert.assertNull
import org.junit.Test

class FbPageParseTest {
    @Test
    fun countedBodyParsesBothFields() {
        assertEquals(800 to 42L, parseFbPage("800 42"))
        assertEquals(0 to 1L, parseFbPage("0 1\n"))
    }

    @Test
    fun legacyBodyParsesWithUnknownSeq() {
        assertEquals(800 to -1L, parseFbPage("800"))
        assertEquals(0 to -1L, parseFbPage("0"))
    }

    @Test
    fun garbageParsesToNull() {
        assertNull(parseFbPage(""))
        assertNull(parseFbPage("x"))
        assertNull(parseFbPage("800 x"))
    }
}
