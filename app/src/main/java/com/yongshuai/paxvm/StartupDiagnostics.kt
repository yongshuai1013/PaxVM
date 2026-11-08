package com.yongshuai.paxvm

import android.content.Context
import android.os.SystemClock
import android.preference.PreferenceManager
import java.io.File
import java.io.FileInputStream
import java.io.FileOutputStream
import java.io.RandomAccessFile
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.zip.ZipEntry
import java.util.zip.ZipOutputStream
import kotlin.concurrent.thread

/** Local-only diagnostics for Android 2.3 guest startup. */
internal object StartupDiagnostics {
    const val PREF_KEY = "startup_diagnostics_enabled"
    private const val ROOT = "paxvm-startup-diagnostics"
    private val channels = listOf("main", "system", "events")

    fun isEnabled(context: Context): Boolean = PreferenceManager
        .getDefaultSharedPreferences(context)
        .getBoolean(PREF_KEY, false)

    fun newSession(context: Context, rootfs: File): Session =
        Session(context.applicationContext.filesDir, rootfs)

    fun latestRun(context: Context): File? = File(
        context.filesDir, ROOT,
    ).listFiles()?.filter { it.isDirectory && it.name.startsWith("run-") }
        ?.maxByOrNull { it.lastModified() }

    fun preview(context: Context): String {
        val run = latestRun(context)
            ?: return "尚無啟動診斷記錄。\n\n請先到「設定」啟用「啟動診斷」，再啟動 Gingerbread 客體。"
        val out = StringBuilder()
        fun section(title: String, body: String) {
            if (body.isBlank()) return
            out.append("\n===== ").append(title).append(" =====\n")
                .append(body.trimEnd()).append('\n')
        }
        section("摘要", readText(File(run, "summary.txt"), 16_000))
        section("啟動階段與程序事件", readText(File(run, "timeline.log"), 80_000))
        section("客體核心日誌（.kmsg）", readText(File(run, "guest-kmsg.log"), 40_000))
        for (channel in channels) {
            section("客體 /dev/log/$channel", renderLogger(File(run, "guest-log-$channel.bin")))
        }
        if (out.isEmpty()) return "診斷目錄尚無可預覽內容：${run.name}"
        return out.toString().takeLast(220_000)
    }

    fun exportZip(run: File, output: java.io.OutputStream) {
        ZipOutputStream(output).use { zip ->
            run.walkTopDown().filter { it.isFile }.forEach { file ->
                val name = file.relativeTo(run).invariantSeparatorsPath
                zip.putNextEntry(ZipEntry(name))
                FileInputStream(file).use { input -> input.copyTo(zip, 64 * 1024) }
                zip.closeEntry()
            }
        }
    }

    private fun readText(file: File, maxChars: Int): String {
        if (!file.isFile) return ""
        return try {
            val text = file.readText(Charsets.UTF_8)
            if (text.length <= maxChars) text else "（僅顯示尾端）\n" + text.takeLast(maxChars)
        } catch (_: Exception) {
            "（無法讀取）"
        }
    }

    private fun renderLogger(file: File): String {
        if (!file.isFile || file.length() == 0L) return ""
        val bytes = try {
            RandomAccessFile(file, "r").use { raf ->
                val size = minOf(raf.length(), 8L * 1024 * 1024).toInt()
                raf.seek((raf.length() - size).coerceAtLeast(0))
                ByteArray(size).also { raf.readFully(it) }
            }
        } catch (_: Exception) {
            return ""
        }
        val entries = ArrayDeque<String>()
        var off = 0
        fun u16(o: Int) = (bytes[o].toInt() and 0xff) or ((bytes[o + 1].toInt() and 0xff) shl 8)
        fun i32(o: Int) = (bytes[o].toInt() and 0xff) or
            ((bytes[o + 1].toInt() and 0xff) shl 8) or
            ((bytes[o + 2].toInt() and 0xff) shl 16) or
            ((bytes[o + 3].toInt() and 0xff) shl 24)
        while (off + 20 <= bytes.size) {
            val len = u16(off)
            if (len < 2 || len > 8192 || off + 20 + len > bytes.size) {
                off++
                continue
            }
            val pid = i32(off + 4)
            val priority = bytes[off + 20].toInt() and 0xff
            var tagEnd = off + 21
            val end = off + 20 + len
            while (tagEnd < end && bytes[tagEnd] != 0.toByte()) tagEnd++
            if (tagEnd >= end) {
                off++
                continue
            }
            val tag = String(bytes, off + 21, tagEnd - (off + 21), Charsets.UTF_8)
            val message = String(bytes, tagEnd + 1, end - tagEnd - 1, Charsets.UTF_8)
                .trimEnd('\u0000', '\n')
            val level = when (priority) {
                2 -> "V"; 3 -> "D"; 4 -> "I"; 5 -> "W"; 6 -> "E"; 7 -> "F"
                else -> priority.toString()
            }
            if (tag != "pixelflinger") {
                entries.addLast("$level/$tag($pid): $message")
                if (entries.size > 250) entries.removeFirst()
            }
            off += 20 + len
        }
        return if (entries.isNotEmpty()) entries.joinToString("\n") else
            "有原始記錄（${file.length()} 位元組），但目前尾端沒有可完整解析的 logger_entry。"
    }

    class Session internal constructor(filesDir: File, private val rootfs: File) {
        private val lock = Any()
        private val runDir: File
        private val offsets = HashMap<String, Long>()
        private val seenStages = HashSet<String>()
        private val startedAt = System.currentTimeMillis()
        private val startedElapsed = SystemClock.elapsedRealtime()
        @Volatile private var frozen = false
        @Volatile private var finished = false
        private var autoSnapshot = false
        private var mirrorDir: File? = null

        init {
            val root = File(filesDir, ROOT)
            root.mkdirs()
            val stamp = SimpleDateFormat("yyyyMMdd-HHmmss-SSS", Locale.US).format(Date())
            runDir = File(root, "run-$stamp")
            runDir.mkdirs()
            pruneRuns(root, runDir)
            synchronized(lock) {
                eventLocked("診斷開始；先於 Gingerbread rootfs 準備與 VM 啟動。")
                eventLocked("可用來源：guest .kmsg、guest /dev/log/main|system|events、init stage 標記、supervisor 啟動與程序事件。")
            }
        }

        fun startMonitoring(supervisorMirrorDir: File?) {
            mirrorDir = supervisorMirrorDir
            synchronized(lock) { eventLocked("GB rootfs 已準備；開始 VM 前記錄啟動上下文。") }
            thread(name = "startup-diagnostics", isDaemon = true) {
                while (!finished && !frozen) {
                    synchronized(lock) {
                        if (!frozen && !finished) sampleLocked()
                    }
                    try {
                        Thread.sleep(200)
                    } catch (_: InterruptedException) {
                        break
                    }
                }
            }
        }

        fun record(message: String) {
            synchronized(lock) {
                if (frozen || finished) return
                eventLocked(message)
            }
        }

        fun onSupervisorLine(line: String) {
            if (frozen || finished) return
            val candidateExit = parseSystemServerCandidateExit(line)
            val notable = listOf(
                "supervisor ctx:", "kernel:", "selinux:", "supervisor pid=",
                "supervisor niced", "rootfs=", "guest ELF:", "guest pid=",
                "guest exec completed", "tracee born:", "exec completed",
                "SYSTEM_SERVER_CANDIDATE", "SYSTEM_SERVER_EXIT", "PROC_EXITED",
                "PROC_SIGNALED", "GUEST_EXITED", "GUEST_SIGNALED", "WARN:",
            ).any(line::contains)
            if (!notable) return
            synchronized(lock) {
                if (frozen || finished) return
                eventLocked("supervisor: $line")
                if (candidateExit != null && candidateExit.isAbnormal) {
                    sampleLocked(finalCapture = true)
                    eventLocked(systemServerCandidateSnapshotMessage(candidateExit))
                    copySupervisorMirrorsLocked()
                    autoSnapshot = true
                    frozen = true
                    writeSummaryLocked()
                }
            }
        }

        fun finish(reason: String) {
            synchronized(lock) {
                if (finished) return
                if (!frozen) {
                    sampleLocked(finalCapture = true)
                    eventLocked("診斷收尾：$reason")
                    copySupervisorMirrorsLocked()
                }
                finished = true
                writeSummaryLocked()
            }
        }

        private fun sampleLocked(finalCapture: Boolean = false) {
            val sources = listOf(
                ".kmsg" to "guest-kmsg.log",
                ".logs/log-main" to "guest-log-main.bin",
                ".logs/log-system" to "guest-log-system.bin",
                ".logs/log-events" to "guest-log-events.bin",
            )
            for ((relative, destName) in sources) {
                val src = File(rootfs, relative)
                if (!src.isFile) continue
                val oldOffset = offsets[relative] ?: 0L
                try {
                    RandomAccessFile(src, "r").use { raf ->
                        val size = raf.length()
                        var offset = if (size < oldOffset) 0L else oldOffset
                        val cap = if (relative == ".kmsg") 2L * 1024 * 1024 else 4L * 1024 * 1024
                        if (finalCapture && size - offset > cap) {
                            offset = size - cap
                        }
                        var passes = 0
                        while (size > offset && passes < 32) {
                            raf.seek(offset)
                            val limit = minOf(size - offset, 256L * 1024).toInt()
                            val bytes = ByteArray(limit)
                            val count = raf.read(bytes)
                            if (count <= 0) break
                            appendBounded(
                                File(runDir, destName), bytes.copyOf(count),
                                cap,
                            )
                            offset += count
                            passes++
                        }
                        offsets[relative] = offset
                    }
                } catch (e: Exception) {
                    if (offsets[relative] == null) eventLocked("來源暫不可讀 $relative：${e.javaClass.simpleName}")
                }
            }
            val stages = listOf(
                "early-init" to ".pax-stage-early-init",
                "init" to ".pax-stage-init",
                "fs" to ".pax-stage-fs",
                "boot" to ".pax-stage-boot",
            )
            for ((stage, marker) in stages) {
                if (stage !in seenStages && File(rootfs, marker).isFile) {
                    seenStages.add(stage)
                    eventLocked("啟動階段：init $stage")
                }
            }
        }

        private fun eventLocked(message: String) {
            val stamp = SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS", Locale.US).format(Date())
            val elapsed = (SystemClock.elapsedRealtime() - startedElapsed).coerceAtLeast(0)
            val safe = message.replace('\u0000', ' ').replace('\r', ' ').take(3000)
            appendBounded(File(runDir, "timeline.log"),
                "[$stamp +${elapsed}ms] $safe\n".toByteArray(Charsets.UTF_8), 1024L * 1024)
            writeSummaryLocked()
        }

        private fun writeSummaryLocked() {
            val status = when {
                autoSnapshot -> "已在 zygote 子程序候選非正常退出時凍結上下文；身分未獨立確認。"
                finished -> "工作階段已結束；未觀察到 zygote 子程序候選非正常退出。"
                else -> "記錄進行中；僅在候選程序以非零退出碼或訊號退出時自動凍結快照。"
            }
            val body = buildString {
                appendLine("PaxVM 啟動診斷")
                appendLine("工作階段：${runDir.name}")
                appendLine("開始時間：${Date(startedAt)}")
                appendLine("狀態：$status")
                appendLine("資料位置：應用程式私有儲存空間；未自動上傳。")
                appendLine("保留策略：每個來源採有限大小尾端緩衝，最多保留最近 3 次工作階段。")
                appendLine("包含來源：時間線、可取得的 guest .kmsg、/dev/log main/system/events；快照時可取得的 supervisor direct mirror。")
                appendLine("注意：system_server 身分由現有 supervisor 的 zygote 子程序候選追蹤判定，並非 Gingerbread 裝置開機驗證。")
            }
            try {
                File(runDir, "summary.txt").writeText(body, Charsets.UTF_8)
            } catch (_: Exception) {
            }
        }

        private fun copySupervisorMirrorsLocked() {
            val dirs = listOfNotNull(mirrorDir, rootfs.parentFile).distinctBy { it.absolutePath }
            for (worker in 0..6) {
                val name = "supervisor-direct-w$worker.log"
                val source = dirs.asSequence().map { File(it, name) }.firstOrNull { it.isFile } ?: continue
                val target = File(runDir, name)
                try {
                    RandomAccessFile(source, "r").use { raf ->
                        val size = minOf(raf.length(), 1024L * 1024).toInt()
                        raf.seek((raf.length() - size).coerceAtLeast(0))
                        val bytes = ByteArray(size)
                        raf.readFully(bytes)
                        FileOutputStream(target, false).use { it.write(bytes) }
                    }
                } catch (_: Exception) {
                }
            }
        }

        private fun appendBounded(file: File, bytes: ByteArray, maxBytes: Long) {
            if (bytes.isEmpty()) return
            try {
                FileOutputStream(file, true).use { it.write(bytes) }
                val size = file.length()
                if (size <= maxBytes + 256 * 1024) return
                val temp = File(file.parentFile, file.name + ".trim")
                RandomAccessFile(file, "r").use { input ->
                    val keep = minOf(maxBytes, input.length()).toInt()
                    input.seek(input.length() - keep)
                    FileOutputStream(temp, false).use { output ->
                        val buf = ByteArray(64 * 1024)
                        var remaining = keep
                        while (remaining > 0) {
                            val n = input.read(buf, 0, minOf(buf.size, remaining))
                            if (n <= 0) break
                            output.write(buf, 0, n)
                            remaining -= n
                        }
                    }
                }
                if (temp.renameTo(file)) return
                temp.delete()
            } catch (_: Exception) {
            }
        }

        companion object {
            private fun pruneRuns(root: File, current: File) {
                val runs = root.listFiles()?.filter { it.isDirectory && it.name.startsWith("run-") }
                    ?.sortedByDescending { it.lastModified() } ?: return
                for (old in runs.drop(3)) {
                    if (old != current) old.deleteRecursively()
                }
            }
        }
    }
}
