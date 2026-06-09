# Doty time-half — Avenue F: the trajectory-level concentration FRAMEWORK (common prerequisite)

Directive: 绝对不退缩. The recurring gap across A0/B/S1/S2b is the SAME: turning a per-step / single-window
potential-drift bound into a kernel-level multi-step PhaseConvergence, usable for every phase + clock level +
front level, so A1's compose_n_phases finishes. S1 did this AD HOC for one window (constantDensity via
lintegral_decay_on_absorbing). Avenue F extracts the GENERAL builder — the common prerequisite that unblocks
S2b-multilevel, S3, the remaining ~9 phases, and the clock re-composition.

Repo: ~/.openclaw/workspace/projects/Ripple (local, NO .git). Build: nice -n 15 env LEAN_NUM_THREADS=2
~/.elan/bin/lake build <Module>. Read: S1's Probability/ConstantDensityEpidemic.lean
(`lintegral_decay_on_absorbing`, `measure_ge_one_on_absorbing`, `windowPot_contracts_on_floor`,
`constantDensity_tail` — the single-window template to GENERALIZE), Probability/PhaseConvergence.lean
(PhaseConvergence struct + compose_n_phases = A1's consumer), Probability/TimeComposition.lean (A1),
Probability/JansonHitting.lean (MilestonePhase.toPhaseConvergence — the existing unit-coverage builder, λ=2
hardwired; your general builder must allow arbitrary λ/rate). Probability/MarkovChain.lean
(ae_of_stepDistOrSelf_support_preserved — the a.e.-invariance S1 used).

## What to build (NEW file Probability/WindowConcentration.lean)
A GENERAL, reusable builder turning a potential-drift window into a PhaseConvergence:

1. `windowDrift_PhaseConvergence` (the keystone abstraction): given
   - `K : Kernel`, potential `Φ : Config → ℝ≥0∞`, absorbing predicate `Q` (one-step-support-closed),
   - goal `Post` with `Φ c &lt; θ → Post c` (or `¬Post → Φ ≥ θ`),
   - per-step contraction ON Q: `∀ c, Q c → ∫ Φ d(K c) ≤ r · Φ c` with `r &lt; 1`,
   - start `c₀ ∈ Q`, budget `t`,
   produce a `PhaseConvergence K` with that `Post`, `t`, and `ε = r^t · Φ(c₀)/θ` (or the clean closed form).
   PROVE it by generalizing `lintegral_decay_on_absorbing` + `measure_ge_one_on_absorbing` from S1 (lift them
   out of the constant-density specifics into this abstract statement; S1 then becomes one instantiation).
2. A DUAL form for UPPER-bounding growth (S2b's direction: front stays small) — `windowGrowth_PhaseConvergence`
   or a sign-flip of the same lemma (potential = exp(s·(value)), contraction = suppression). If the same lemma
   covers both by choice of Φ, just document it; else build the twin.
3. Re-instantiate S1's `constantDensity_epidemic_O1_parallel` THROUGH `windowDrift_PhaseConvergence` as a
   sanity check that the general builder reproduces the proven S1 result (don't break S1; new file, separate
   instantiation lemma `s1_via_framework`).

## Why this is the unblock
With `windowDrift_PhaseConvergence`, each remaining piece is "define Φ + prove one-step contraction on its
window" (the easy, mechanical part) and the kernel-level multi-step tail + PhaseConvergence wrapping comes for
free, feeding A1's `doty_time_headline`. The ~30-page §6 trajectory analysis collapses to: one general
concentration lemma (this) + per-piece potential definitions + the cross-level union bound (compose_n_phases,
already done).

## HARD RULES (automode, NO effort cap; 绝对不退缩)
NEW file WindowConcentration.lean only; do NOT edit existing files (S1/S2/S2b/clock/A1). Lift/generalize S1's
lintegral_decay_on_absorbing (re-prove abstractly, don't edit S1). No sorry/admit/new axiom/native_decide.
Iterate lake build until clean. If a Mathlib kernel/integral primitive is genuinely absent, name it EXACTLY +
build self-contained or STOP and report (do NOT fake). Do NOT git. Final message: the general builder
statement(s) + the `s1_via_framework` sanity instantiation, build verdict, #print axioms, and an honest verdict
on whether this builder cleanly unblocks the remaining phases/levels (the framework de-risk).