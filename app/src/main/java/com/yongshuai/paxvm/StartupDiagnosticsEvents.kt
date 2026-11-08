package com.yongshuai.paxvm

internal data class SystemServerCandidateExit(
    val pid: Int,
    val exitCode: Int? = null,
    val signal: Int? = null,
) {
    val isAbnormal: Boolean
        get() = signal != null || (exitCode != null && exitCode != 0)
}

internal fun parseSystemServerCandidateExit(line: String): SystemServerCandidateExit? {
    val match = Regex("""SYSTEM_SERVER_EXIT\s+pid=(\d+)\s+(?:code=(\d+)|sig=(\d+))(?:\s|$)""")
        .find(line) ?: return null
    val pid = match.groupValues[1].toIntOrNull() ?: return null
    val exitCode = match.groupValues[2].takeIf(String::isNotEmpty)?.toIntOrNull()
    val signal = match.groupValues[3].takeIf(String::isNotEmpty)?.toIntOrNull()
    if (exitCode == null && signal == null) return null
    return SystemServerCandidateExit(pid, exitCode, signal)
}

internal fun systemServerCandidateSnapshotMessage(exit: SystemServerCandidateExit): String {
    val termination = exit.signal?.let { "signal $it" } ?: "exit code ${exit.exitCode}"
    return "AUTO_SNAPSHOT：zygote 子程序候選 pid=${exit.pid} 以 $termination 非正常退出；這是候選追蹤，未確認為 system_server 崩潰。後續記錄不會覆寫此快照。"
}
