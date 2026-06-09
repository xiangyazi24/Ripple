# TODO: Merge Ripple + PP-Proof into unified GPAC/CRN/PP Lean library

**Created:** 2026-04-27 (Xiang voice 4789)
**Status:** deferred — execute after Ripple ζ(3) Frobenius work收口
**Owner:** Xiang (re-plan), Zinan (execution)

## Background

Per Xiang voice 2026-04-27: Ripple (continuous side: GPAC, PIVP, CRN) and PP-Proof (stochastic side: population protocols, supermartingale convergence) are two halves of the same library. They were started separately for tactical reasons but belong under one roof long-term.

> "我们以后肯定是要把 PP-proof 这个 repository 也一并并进 Ripple 这个 repository 里面来——因为它们都是一大类的东西. ... 我们要把这两个 project 并在一起, 做成一个大的、关于 GPAC、CRN、population protocol 的一大个库. 里面有 continuous 项的, 也有像 PP proof 这里面是 stochastic 项的. 这个会对人很有用." — Xiang, 2026-04-27

## Trigger condition

Wait until **Ripple's ζ(3) Frobenius track is closed** (F4, F5 discharged via Frobenius framework, or formally folded into Mathlib if upstream lands first). At that point Ripple has stable shape and is the natural anchor repo for the merge.

Do **not** start the merge while Frobenius is mid-construction — the structural churn would interfere.

## What needs to happen at merge time

1. Re-plan with Xiang. Don't auto-merge; he'll want to design the directory layout.
2. Decide anchor: probably keep Ripple as the repo, import PP-Proof as a subdirectory `Ripple/Stochastic/` or similar. Alternative: rename to a project-level name (`GpacCrnPp` or similar).
3. Migrate PP-Proof modules + UNDERSTANDING.md + lessons.
4. Cross-link the existing techniques in `wiki/projects/cross-project-techniques.md` — once merged, "cross-project" becomes "cross-module" and the wiki entry simplifies.
5. Update CLAUDE.md / OPEN_PROBLEMS.md to reflect unified scope.

## Reminder mechanism

- This file lives at Ripple repo root so I see it every time I work in Ripple.
- When Frobenius `## Open questions` empties out (or shrinks to non-blocking items), surface this TODO to Xiang via Telegram with a "ready to plan?" message.
- Cross-referenced from `wiki/projects/cross-project-techniques.md` § "为什么有这个文件".

## Why not start now

- Frobenius construction is mid-flight (gap B atom 19 + ~25 follow-up commits). Reorg would lose that momentum.
- PP-Proof is also mid-construction (lessons 0046-0052 all reference active PP-Proof work).
- Unifying两个还在演化的项目会双倍复杂度.
- "做成大库"是稳态目标, 不是动态目标; 等两边各自收口再统一.
