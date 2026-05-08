# TODO — Ripple (CRN Computable Numbers, Lean 4)

---

## Status: Ripple 0 sorry / 0 axiom decl across all six pillars

**完工于 2026-05-07 晚**:
- Core / ODE / DualRail / LPP / Number / Number/Modular 全部 0 sorry / 0 axiom decl
- phi41 → CM-163 链路：commit ec52333d 收尾
- 完整链条见 CHECKPOINT.md

## 后续可选项目（非阻塞）

- [ ] **CRT-route certificate** — 把 `phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` 的 `native_decide` 换成 CRT 严格证明，去掉对 native compiler 的信任。helpers 已就位
  (`phi41Level41RecurrenceCoeffArrayFirstZero_of_crt_certificate` 等)。
- [ ] **LevelOneCuspWeight\*.lean cleanup** — 30+ 个 per-weight 文件已被
  `LevelOneSturmGeneric.lean` 取代。要么删，要么把
  `LevelOneSmallWeights.lean` 重写走 generic 路径。
- [ ] **`set_option maxHeartbeats 800000` audit** — 项目里到处散落，看哪些
  可以缩回 200000 默认。
- [ ] **Library 化** — Ripple 抽出可复用 CRN Lean 4 library
  (`CRN.Core` / `CRN.Number` / `CRN.Modular` 三个独立包)。

---

_上次更新：2026-05-07_
