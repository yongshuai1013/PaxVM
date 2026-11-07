package com.yongshuai.paxvm

import android.content.Context
import android.net.nsd.NsdManager
import android.net.nsd.NsdServiceInfo
import android.net.wifi.WifiManager
import android.os.SystemClock
import java.net.NetworkInterface
import java.util.concurrent.CountDownLatch
import java.util.concurrent.LinkedBlockingQueue
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicBoolean

/**
 * mDNS discovery for the device's own wireless-debugging adbd.
 *
 * adbd advertises two services while wireless debugging is on:
 * _adb-tls-pairing._tcp (only while the pairing dialog is open)
 * and _adb-tls-connect._tcp (the connect port). Their ports are
 * randomized per session, so the pairing/connect flows discover
 * them here instead of asking the user to type port numbers.
 *
 * Candidate rule: a resolved host that equals one of this
 * device's own interface addresses is this phone's adbd and
 * wins immediately; otherwise the first resolved candidate is
 * kept as fallback until the window closes (another device on
 * the same LAN can advertise the same service types).
 */
object AdbMdns {

    const val TYPE_PAIRING = "_adb-tls-pairing._tcp"
    const val TYPE_CONNECT = "_adb-tls-connect._tcp"

    // NsdManager allows only one outstanding resolveService on
    // older Android versions (a second concurrent call fails
    // with FAILURE_INTERNAL / max limit); all resolves in this
    // object are serialized through this lock, one at a time.
    private val resolveLock = Object()

    /**
     * Discovers [serviceType] for up to [timeoutMs]; returns the
     * chosen (host, port) or null on timeout/failure. Every
     * candidate and decision is written to [log].
     */
    fun discover(
        context: Context,
        serviceType: String,
        timeoutMs: Long,
        log: (String) -> Unit,
    ): Pair<String, Int>? {
        val appCtx = context.applicationContext
        val nsd = appCtx.getSystemService(Context.NSD_SERVICE) as? NsdManager
        if (nsd == null) {
            log("mDNS：NsdManager 不可用")
            return null
        }
        val localAddrs = localAddresses()
        log("mDNS：開始發現 $serviceType（逾時 ${timeoutMs}ms，本機位址 $localAddrs）")

        // Some devices only deliver mDNS responses while a
        // multicast lock is held; acquire best-effort and never
        // let a failure here block discovery.
        val multicastLock = try {
            val wifi = appCtx.getSystemService(Context.WIFI_SERVICE) as? WifiManager
            wifi?.createMulticastLock("paxvm-mdns")?.apply {
                setReferenceCounted(false)
                acquire()
            }
        } catch (e: Exception) {
            log("mDNS：multicast lock 取得失敗（繼續無鎖發現）：${e.message}")
            null
        }

        val found = LinkedBlockingQueue<NsdServiceInfo>()
        val seenNames = HashSet<String>()
        val discoveryStarted = AtomicBoolean(false)
        val listener = object : NsdManager.DiscoveryListener {
            override fun onDiscoveryStarted(regType: String) {
                discoveryStarted.set(true)
                log("mDNS：發現已啟動 $regType")
            }

            override fun onServiceFound(service: NsdServiceInfo) {
                val isNew = synchronized(seenNames) { seenNames.add(service.serviceName) }
                if (isNew) {
                    log("mDNS：發現服務 ${service.serviceName}（${service.serviceType}），排入解析")
                    found.put(service)
                }
            }

            override fun onServiceLost(service: NsdServiceInfo) {
                log("mDNS：服務消失 ${service.serviceName}")
            }

            override fun onDiscoveryStopped(serviceType: String) {
                log("mDNS：發現已停止 $serviceType")
            }

            override fun onStartDiscoveryFailed(serviceType: String, errorCode: Int) {
                log("mDNS：啟動發現失敗 errorCode=$errorCode")
                // Wake the waiting loop so it can bail out.
                found.put(NsdServiceInfo().apply { serviceName = "" })
            }

            override fun onStopDiscoveryFailed(serviceType: String, errorCode: Int) {
                log("mDNS：停止發現失敗 errorCode=$errorCode")
            }
        }

        var winner: Pair<String, Int>? = null
        var fallback: Pair<String, Int>? = null
        try {
            nsd.discoverServices(serviceType, NsdManager.PROTOCOL_DNS_SD, listener)
            val deadline = SystemClock.uptimeMillis() + timeoutMs
            while (winner == null) {
                val remaining = deadline - SystemClock.uptimeMillis()
                if (remaining <= 0) break
                val info = found.poll(remaining, TimeUnit.MILLISECONDS) ?: break
                if (info.serviceName.isEmpty()) break // start failed
                val resolved = resolveOne(nsd, info, remaining, log) ?: continue
                val host = resolved.first
                if (host in localAddrs) {
                    log("mDNS：選定本機候選 $host:${resolved.second}（${info.serviceName}）")
                    winner = resolved
                } else {
                    if (fallback == null) {
                        fallback = resolved
                    }
                    log("mDNS：非本機候選 $host:${resolved.second}（${info.serviceName}），繼續等本機候選")
                }
            }
        } catch (e: Exception) {
            log("mDNS：發現過程例外：${e.javaClass.simpleName}: ${e.message}")
        } finally {
            if (discoveryStarted.get()) {
                try {
                    nsd.stopServiceDiscovery(listener)
                } catch (e: Exception) {
                    log("mDNS：stopServiceDiscovery 例外（忽略）：${e.message}")
                }
            }
            try {
                if (multicastLock != null && multicastLock.isHeld) multicastLock.release()
            } catch (e: Exception) {
                log("mDNS：multicast lock 釋放例外（忽略）：${e.message}")
            }
        }

        val result = winner ?: fallback
        if (result == null) {
            log("mDNS：逾時，沒有任何候選（$serviceType）")
        } else if (winner == null) {
            log("mDNS：未發現本機候選，採用第一個候選 ${result.first}:${result.second}")
        }
        return result
    }

    /** Resolves one service, serialized (see resolveLock note). */
    private fun resolveOne(
        nsd: NsdManager,
        info: NsdServiceInfo,
        budgetMs: Long,
        log: (String) -> Unit,
    ): Pair<String, Int>? {
        synchronized(resolveLock) {
            val latch = CountDownLatch(1)
            var resolved: NsdServiceInfo? = null
            var failure: Int? = null
            val listener = object : NsdManager.ResolveListener {
                override fun onResolveFailed(serviceInfo: NsdServiceInfo, errorCode: Int) {
                    failure = errorCode
                    latch.countDown()
                }

                override fun onServiceResolved(serviceInfo: NsdServiceInfo) {
                    resolved = serviceInfo
                    latch.countDown()
                }
            }
            @Suppress("DEPRECATION")
            nsd.resolveService(info, listener)
            val waitMs = budgetMs.coerceIn(1L, 5_000L)
            if (!latch.await(waitMs, TimeUnit.MILLISECONDS)) {
                log("mDNS：解析 ${info.serviceName} 逾時（${waitMs}ms）")
                return null
            }
            val err = failure
            if (err != null) {
                log("mDNS：解析 ${info.serviceName} 失敗 errorCode=$err")
                return null
            }
            val r = resolved ?: return null
            @Suppress("DEPRECATION")
            val host = r.host?.hostAddress
            if (host == null || r.port <= 0) {
                log("mDNS：解析 ${info.serviceName} 結果不完整 host=$host port=${r.port}")
                return null
            }
            val cleanHost = host.substringBefore('%')
            log("mDNS：候選 ${r.serviceName} -> $cleanHost:${r.port}")
            return cleanHost to r.port
        }
    }

    /** All non-loopback addresses of up interfaces on this device. */
    private fun localAddresses(): Set<String> {
        val out = HashSet<String>()
        try {
            val ifaces = NetworkInterface.getNetworkInterfaces() ?: return out
            for (iface in ifaces) {
                if (!iface.isUp || iface.isLoopback) continue
                for (addr in iface.inetAddresses) {
                    if (addr.isLoopbackAddress) continue
                    addr.hostAddress?.let { out.add(it.substringBefore('%')) }
                }
            }
        } catch (e: Exception) {
            // An empty set just means no local-preference matching.
        }
        return out
    }
}
