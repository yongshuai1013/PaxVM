# S10 SF 內部 futex 凍結案（s10-sf-futex-desk）

立案：2026-11-16 凌晨，據 0.9.164 首場（612 秒／SS 九任）判讀。
標的：SF（surfaceflinger, proc 22138）內部 futex 0x41fee864 自
t≈47 秒後凍結，兩任 SS（25137、25778）因此被判 B2 楔、Watchdog 處決。

## 1. 已釘死的事實

- 凍結時點：此 futex 的 WAKE 帳最後一筆停在 **t=47289、waker=22138
  （SF 主線程）**，其後 565 秒 wakes 凍在 18 不再增長；waits 則
  11→12→16→21 一路累積。
- 受害形狀（兩次同形）：SS 線程（25220／25865）服侍入站 code=1
  期間對 SF 發同步 **code=8**，被 SF 線程（22171／25793）認領後，
  認領者 park 在 0x41fee864 永不進展；SS 側 wait-reply 永不回，
  該任 SS 被 Watchdog sig9。crash 腿 gate2 的 surf 腿（23437／24084）
  同樣死在 SF code=8——code=8 是本場 SF 的共同咽喉。
- SF 名冊（.165 審計更正）：全場共 **11 線程**（主 22138、早期
  22149／22150／22151／22154／22170／22171、晚生 25211／25793／
  25795／26622）。快照拍到的只有 7 名：兩次 B2 快照時 5 條在
  0x41fee864 上 WAIT、2 條 binder read 閒置、無一條 wait-reply。
  22150／22151 開場即正常退出（PROC_EXITED code=0）；**22149 命運
  無紀錄**——無退出行、最後現身在開場期一次 SIGSYS 救援（fake
  ioctl），此後全場沉默，是唯一在凍結窗口內狀態不明的 SF 線程。
  SF 本體活到場尾。
- 凍結是路徑專屬的：凍結之後的 SS 26526 仍走到 ready＋Launcher
  idle——SF 並非全死，只有 code=8 那條路被這把 futex 閘住。

## 2. 審計定讞：futex 是直通的（原§2 指控撤回）

.165 審計讀碼結論：**監督器不模擬 futex**——入口捕捉處註解明言
「futex passes through this engine untouched」，WAKE／WAIT 只在
停點被記帳（op 0|9／1|10、mask 0x7f），本體重啟進宿主內核、由
宿主對客體真實記憶體執行。因此：監督器沒有佇列可丟 WAKE；
WAIT 的值複核由宿主內核原子完成；wait 完成可由 wake／逾時／
EAGAIN 即時返回等任一出口觸發，出口座位一律記 last_done。
**原§2「帳目分歧」隨之撤回**：last_done=22138@453390 而其前無
WAKE，在直通語義下是平常事（逾時或值已變的即時返回都會記），
不構成模擬層丟失喚醒的證據。且凍結形狀本身反證丟失說：若釋放
者的 WAKE 被吞，鎖字面已被客體寫 0、新到 WAIT 會即時 EAGAIN
並 CAS 接鎖、不會排隊——本場是排隊 565 秒，即字面真由客體邏輯
持有未放。監督器在 futex 路上清白（唯一理論殘口：入口停點後
重啟被別的機制吞掉，但其預測形狀與觀察相反，不成立）。

## 3. 排除項

- **線程帶鎖暴斃**：大半排除。22150／22151 開場正常退出、遠在
  凍結（t=47289 後）之前；其餘快照名冊內線程全場存活。唯
  **22149 命運無紀錄**（無退出行、開場後沉默）——若它沉默是因
  長眠於某個直通 syscall（如阻塞 read），它在凍結窗口內是
  「活著但不可見」，不在暴斃之列、歸入 §4.1 的未拍攝姿勢。
- **22173**：排除。開場期 GL 客戶端線程（開 gralloc.paxvm.so、
  載 libGLES_android、日誌第 8789 行死於軟體光柵器 +0xfcea），
  從未碰過 0x41fee864、不在 SF 名冊內。附帶：22141 是 gbprobe
  本體（libc +0x15ec4）；24150 死於 SF-client 候補座
  libsurfaceflinger_client +0x14a7e，該座累計 n 再 +1（另帳）。
- **回呼環（.164 已拆）**：排除。兩次快照 servicer wait_reply=0，
  無 SF→SS 回呼在途。

## 4. 假說排序（.165 審計後修訂）

1. **持鎖者處於未被拍攝的姿勢（頭號）**：快照的 servicer-face
   只拍「有互動的線程」；一條不服侍任何人、長眠在直通 syscall
   （如阻塞 read）的線程不會入鏡。22149 是現成的候選形狀：
   開場後無紀錄、無退出行。持鎖者在其長眠前以 CAS 取鎖（不留
   futex 紀錄）即可形成全場形狀。
2. **客體 SF 自身死鎖**：次位。stock GB SF 在真機不曾把合成
   鎖凍 565 秒，但我們的客體跑在直通＋假設備的環境面上
   （/sys、fb 皆合成），GB 源碼裡等硬體事件的路徑在此可能
   永不返回——與 §4.1 在實作上同形，靠下一版儀器分辨。
3. **監督器 futex WAKE 丟失**：排除（§2 直通定讞）。

## 5. 下一版（.165）規格——審計已完，走儀器版（純觀察、零行為改）

審計結論（§2）：無罪可定，.165 為純儀器版，兩件：

- **wait 完成原因欄**：FutexAcct 加 last_done_ret（出口停點的
  futex 返回值 r0），快照印面同步。0＝被喚醒、-110＝逾時、
  -11＝值已變即時返回——下次再見「無 WAKE 的完成」可當場分型，
  不再靠猜。
- **servicer 全名冊快照**：wedge 快照回應 ServicerFace 時，除
  被點名的服侍線程外，加印該 arena 家族**未被點名**的全部線程
  （wedge-servicer-roster：pid、leader、last_syscall、park 姿勢、
  last_stop_seq 年齡）。22149 這類沉默線程下次凍結時必須入鏡。
- 預註冊判準：再遇同形凍結，快照裡必須能指出持鎖者的姿勢
  （名冊中某線程長眠於非 futex 姿勢且年齡覆蓋凍結窗口），或以
  last_done_ret 證明完成皆屬逾時／即時型；兩者皆無＝儀器仍
  不足、不判任何假說勝。
- 退出條款：若儀器指向客體自身（如持鎖者長眠於合成 /sys 的
  阻塞讀），按 GB SurfaceFlinger 源碼對該路徑另立案。

## 6. .165 首場判讀（2026-11-16）與 .166 儀器補格

.165 首場（約 783 秒、SS 三任）：同形凍結復發——SS 13480 先到
ready（systemui 13539），其後 thread 13512 的 code=3 呼叫被 SF
主線程 13181 認領、13181 park 在 futex 0x41731864 上，Watchdog
處決。凍結窗：最後 WAKE t=16855（13186）、主線程 t=26656 起排
隊、其後無完成。last_done_ret 運作正常（凍結前最後完成分型
ret=0、真喚醒）。roster 拍全 SF 家族 5 名：13183／13184 開場探
/sys fb_sleep 得 ENOENT 即退、證無辜；存活 3 名姿勢全錄。

**§5 判準判定：未達，差一欄。** 頭號嫌疑 13182（SF 合成線程、
負責 fb PAN 翻頁）於凍結時代停止翻頁、其後以 futex 姿勢沉默
至快照——但 .165 的 roster 行沒印它所等 futex 的地址，分不出
「持有字 A、等字 B」（持鎖者）與「排隊等字 A」（受害者）。
次候選：13181 主線程自持自等（serving depth=1 不排除本地作
用域持鎖）。13208 於 t≈17s 死（2 條 gate2 腿未解、死因未定
讞）；14121 活到場尾。RevAcct 再全平（89 筆全嵌套、池認領 0）。

.166 補格（純儀器、零行為）：
- roster 行補 futex 三欄（uaddr／grp／last_op），推導與 face
  行逐字相同，兩種行可直接對讀。
- roster 行加 last_stop_t：該線程最後一次被處理停點的場時
  （ProcState 新欄、進出停點兩座與 last_stop_seq 並排落戳），
  沉默長度以場時直接可讀（emit 行齡受「直通停點不發行」扭曲、
  不足以定年）。

.166 預註冊判準（下一次同形凍結）：
- roster 中沉默家族成員的 futex_uaddr ≠ 楔住的字 → 「持 A 等
  B」成立、持鎖者指認完成；下一步轉客體面（字 A 是哪把鎖、
  為何持著不放），按 GB SurfaceFlinger 源碼另立案。
- 其 futex_uaddr ＝ 楔住的字 → 存活者全員排隊；持鎖者只剩
  「主線程本地作用域自持」一形，以主線程的 serving 深度與
  last_stop_t 對讀判。
- 凍結不復發 → 儀器未受測、不下結論（同 §5 原例）。

## 7. 客體面案頭（2026-11-16）：31100 身份定讞、.166 指認撤回

源碼基底：aosp-mirror platform_frameworks_base／platform_bionic
android-2.3.7_r1 原文（SurfaceFlinger.cpp/.h、MessageQueue.cpp、
DisplayHardwareBase.cpp、ISurfaceComposer.h、bionic pthread.h）。

**31100 ＝ SurfaceFlinger 主迴圈線程（定讞）**：onFirstRef 以
run() 啟動 SF 的 Thread，其 readyToRun() 在該線程上建
DisplayHardware → DisplayHardwareBase，後者依序建 DisplayEventThread
與 ConsoleManagerThread——兩者的 clone 父皆為該主迴圈線程，與場上
家譜（31100 → {31101, 31102}）逐字吻合。31101 是 DisplayEventThread：
readyToRun 的 access 探測順序（/sys/power/wait_for_fb_sleep →
/sys/android_power/…）與場上日誌逐行相同、ENOENT 即 NO_INIT 退出；
31102 是 ConsoleManagerThread（構造在父線程上下文開 /dev/tty0 失敗、
consoleFd<0、readyToRun 直接 NO_INIT、本體零日誌退出）。

**雙字身份**：SurfaceFlinger.h 成員序——mEventQueue（MessageQueue）
→ mStateLock → mCurrentState／mDrawingState（兩個大型 State）→
mTransactionCV。mTransactionCV 與 mStateLock 相隔兩個 State 物件、
不可能落在 20 位元組內；20 位元組雙字只能是「mEventQueue 尾部
（其 mCondition 的 futex 字）＋mStateLock」。故 …850＝MessageQueue
條件字、**…864＝SurfaceFlinger::mStateLock**（行為面亦合：排隊者
是服侍 binder 的主線程與池線程、皆 mStateLock 的常客）。

**31100 的等待是健康閒置**：threadLoop → waitForEvent →
MessageQueue::waitMessage，全程不取 mStateLock；其 …850 停留是
條件等待（Condition::wait 期間釋放佇列自身的 mLock）。結構上它
不可能持著 mStateLock 睡在 …850 上。

**§6 指認撤回**：.166 首場「31100＝持鎖者」是排除法誤判——排除
法預設持鎖者必在某個 futex 上等待；源碼證明 SF 內所有持
mStateLock 又等待的路徑（mTransactionCV 的 wait／waitRelative）
在等待期間都釋放 mStateLock，**不存在「持 mStateLock 停在 futex
上」的姿勢**。真正的持鎖者姿勢必為非 futex 型：服侍中向外同步
binder 等回覆、阻塞型非 futex syscall（gralloc／驅動路徑）、或
使用者空間自旋——皆在現行印面（roster 只覆蓋推送 worker 的分片、
face 的 parked-binder 分不出池閒置與向外阻塞）之外。

凍結力學不變：最後放鎖 31088@t=18795（主線程以池身分服侍完一
單），其後無人放鎖、waits 累積至 41、SF 不死使凍結跨 SS 任存續。

**.167 儀器提案（待拍板）**：B2 判讀觸發時加一輪「持鎖候選掃描」
——對 servicer 家族根，向全 worker 廣播專用 push，各 worker 印
本分片內該家族全員的姿勢＋服侍棧**頂框**（非深度）＋last_stop_t，
補上 roster 的分片覆蓋缺口與 parked-binder 的分辨力。純儀器。
另記：serving 深度帳 oneway 框只進不出（膨脹至 4221）是模型帳
毛病、與本掃描的頂框印法相衝突，修頂框前須先修退框或改印真棧。

## 8. .167 規格與預註冊判準（2026-11-16）

兩件，一真修一儀器：

**(a) oneway 退框（模型帳真修）**：ServingFrame::Other 此前只被後來的
BC_REPLY 順路吃掉，服侍 oneway 洪流的線程（SF 池）無界累積（.166 場
深度 4221）、深度印面失真。新填料開新組時先 purge_completed_oneway：
舊組的 Other 全清、Reply 全留（已認領的雙向服侍開著直到其 BC_REPLY
收）。內核語義：線程再次讀取＝已回迴圈（或在所服侍等待的嵌套讀中），
舊 oneway 在其 handler 返回時即離開交易棧、必然早於下一次讀。配對
不受影響（Reply 框不動、.130 續答紀律不變）。

**(b) 持鎖候選掃描（純儀器）**：B／B2 判讀成立時，binder_wedge_chain
回傳 sweep＝(servicer arena、其 leader pid)；協調器先印
wedge-holder-stack（該 arena 深度>0 的線程：深度＋serving_context
＝最新組第一個 Reply 框的 sender/code），再以 MSG_PUSH_HOLDER_SWEEP
（45）廣播；每個 worker 對其分片內 root 相符的**全部**成員印
wedge-holder-face（與 roster 同欄位：last_syscall／state／futex 三欄
／last_stop_age／last_stop_t）。

**預註冊場判**：
- 退框面：SF 線程的 serving 深度回到個位／低雙位（對照 4221）；
  RevAcct 續全平、.164 直送不退化（marked＝nested、池認領 0）。
- 掃描面：每張 B2 快照的 holder-face 覆蓋 SF 全家族（含池後生線程，
  不只入鏡四名）；決定性讀法——某成員 posture 非 futex 排隊
  （parked-binder 且 holder-stack 有 ctx、或 parked-other、或
  no-pending）且不是 31100 本人＝持鎖候選首次具名。
- 退出條款：掃描開火而仍無候選分離（全員非在 …864 排隊、即 31100
  閒置、即無 ctx 的池閒置讀）→ 持鎖者不是活著的 SF 線程姿勢，
  下一步回案頭想剩餘形狀（如自旋偵測），不再加儀器。
