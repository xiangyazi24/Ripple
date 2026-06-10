# HANDOFF: E4 expected-time assembly (family2 letter, task b3aeb916, 2026-06-10)

Source: ChatGPT Pro (family2, Ripple connector on opus-wip). 15,040 B via network path.

---

[intro]
I’ll ground this in the landed E1–E3 files and the current headline interface, then propose the E4 assembly as a tail-sum/restart lemma rather than a fake conditional-expectation split.

E1 already has the exact split-geometric shape: `expectedHitting_split_geometric` bounds `E[T]` by `t₀ + δ·s·(1−q)⁻¹`. E3’s real-kernel wrappers provide per-phase expected progress under a carried clock floor; importantly, `mC ≥ 2` is still a hypothesis/floor input, not something global from arbitrary reachable states.

[answer]
## Verdict

The E4 expected-time assembly should **not** be written as a conditional-expectation split over “good / bad / tiny” events. In this kernel formalism, the start `c₀` is deterministic, while the role-split outcome is a random event at a later checkpoint. The right Lean shape is:

```lean id="06fnsj"
E[T] ≤ Tgood + ∑' t, (K ^ (Tgood + t)) c₀ Doneᶜ
```

then bound the shifted tail by a **block restart from any reachable not-done state**. This is exactly what `ExpectedHitting.expectedHitting_split_geometric` was built for:

```lean id="b3q7fe"
theorem expectedHitting_split_geometric ...
    (hblock : ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ q)
    ...
    (hδ : (K ^ t₀) c₀ Doneᶜ ≤ δ) :
    expectedHitting K c₀ Done ≤ (t₀ : ℝ≥0∞) + δ * s * (1 - q)⁻¹
```

So E4 reduces to two inputs:

1. the whp headline at `Tgood`, giving `hδ : (K^Tgood)c₀ Doneᶜ ≤ δ`;
2. a uniform recovery/block bound from every not-done reachable state, giving `hblock`.

This avoids fake conditioning entirely. The tail-sum definition and split-geometric theorem are already in E1. fileciteturn / bad-big-clock / tiny-clock” split should be **internal to the recovery bound**, not a conditional expectation at the first checkpoint.

The Lean chain is:

```lean id="q3ivgx"
K0    := (NonuniformMajority L K).transitionKernel
Done  := {c | majorityStableEndpoint (L := L) (K := K) init c}
Tgood := ∑ i : Fin 21, (phases i).t
δgood := ∑ i : Fin 21, ((phases i).ε : ℝ≥0∞)
```

Step 1: use the seam-corrected whp headline:

```lean id="ic4bvb"
doty_time_headline_W2
```

to get

```lean id="jxz83k"
(K0 ^ Tgood) c₀ Doneᶜ ≤ 1 / n
Tgood ≤ 21 * C0 * n * (L + 1)
```

or, if you keep the sharper 21-term budget, use `doty_time_composition_W2` directly and set `δgood := ∑ εᵢ`. The current `doty_time_headline_W2` is the honest 21-instance statement; the older 11-instance `doty_time_headline_W` has a note explaining why the direct work-to-work bridges were pointwise false. fileciteturn54file0L4-L6ky"
hRecover :
  ∀ b ∈ Doneᶜ,
    expectedHitting K0 b Done ≤ Brecover
```

or, better, the invariant-relative version restricted to the valid reachable shell if `Doneᶜ` contains junk configs.

Step 3: convert `hRecover` to a block failure bound with E1’s Markov lemma:

```lean id="3l2nep"
bad_le_half_of_expectedHitting
```

That lemma states that if `expectedHitting K c Done ≤ B` and `B * 2 ≤ s`, then `(K^s)c Doneᶜ ≤ 1/2`. fileciteturn43file0 b ∈ Doneᶜ, (K0 ^ sRecover) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) := by
  intro b hb
  exact bad_le_half_of_expectedHitting K0 hDone hDoneAbs b sRecover hspos
    Brecover hBfin (hRecover b hb) hsRecover
```

Step 4: feed `hδ` and `hblock` to:

```lean id="scn24c"
expectedHitting_split_geometric K0 hDone hDoneAbs
  sRecover hsRecover_ne (1 / 2) hblock c₀ Tgood δgood hδ
```

This yields

```lean id="lpjfv0"
expectedHitting K0 c₀ Done
  ≤ Tgood + δgood * sRecover * (1 - 1/2)⁻¹
```

and `(1 - 1/2)⁻¹ = 2`, so the recovery contribution is at most `2 * δgood * sRecover`. If `sRecover = 2 * Brecover`, this is the usual constant-factor `4 * δgood * Brecover`.

## 2. What supplies `hRecover`

This is the only conceptual E4 content. It is not new probability; it is a deterministic classification plus E2/E3 expected-time theorems.

### Good/big-clock timed phases

For timed phases, E3 provides:

```lean id="89u9wg"
timed_phase_progress_real_bigClock
```

with conclusion

```lean id="s81dlm"
expectedHitting K0 c (Engine.potBelow (clockCounterSumAt p) 1)
  ≤ counterMax * (11 * n)
```

under a carried floor `n / 5 ≤ mC` and the protocol-level floor hypothesis

```lean id="4919f5"
hfloor :
  ∀ b, AllClockGEpCard p n b →
    mC ≤ posClockCount p b
```

E3 also has the tiny-clock fallback:

```lean id="4tilo2"
timed_phase_progress_real_tinyClock
```

with conclusion

```lean id="47e4eh"
expectedHitting K0 c (Engine.potBelow (clockCounterSumAt p) 1)
  ≤ counterMax * (n * n)
```

assuming only `2 ≤ mC`. These real-kernel wrappers discharge `InvClosed`, `PotNonincrOn`, and the rectangle drop probability; their remaining input is exactly the clock floor carried by E4. fileciteturn51file0L83 backup:

```lean id="k28eve"
phase10_expected_stabilization_O_nsq_log
```

with

```lean id="xoekxk"
expectedHitting K0 c (potBelow (fun c => wrongACount c) 1)
  ≤ 3 * (n^2 * ofReal (1 + 2 * log n))
```

from an `S1` start. fileciteturn61file0 the uncollapsed theorem is:

```lean id="trb0fx"
phase10_expected_stabilization_tie
```

and the refined tie-stage section follows it. For E4, use a single uniform backup cap `≤ 3 * n² * (1 + 2 log n)` for both majority and tie, since the majority constant dominates. fileciteturn64file0 What is currently visibly formalized is:

```lean id="j720tp"
theorem clockCount_ge_two_of_RoleSplitGood
    ... (hgood : RoleSplitGood η n c) :
    2 ≤ clockCount c
```

and `RoleSplitGood` also gives the linear `n/5` floor through the RoleSplitGood clock lower bound. fileciteturn62file0 confirms the floor is a **carried input**, not a global theorem: it requires `hfloor : ∀ b, AllClockGEpCard p n b → mC ≤ posClockCount p b`. fileciteturn51file0L83-Le7kv0"
hClockFloorBig :
  ∀ p b, TimedReachableGood p b → n / 5 ≤ phaseClockCount p b
```

and

```lean id="r4u6ko"
hClockFloorTiny :
  ∀ p b, TimedReachableTiny p b → 2 ≤ phaseClockCount p b
```

or a single deterministic “phase initialized implies at least two clocks” lemma if that is later proved. Do not pretend it is already a global reachable invariant.

## 3. Parallel-time conversion and bottleneck

Everything in E1/E2/E3/DotyTimeHeadline is in **interactions**. Parallel time is interactions divided by `n`. E2’s header explicitly states this convention: Phase-10 `O(n log n)` parallel time is `O(n² log n)` interactions. filecitep0hh9u"
Tgood ≤ 21*C0*n*(L+1)
Brecover ≤ Cbad*n^2*(L+1)
δgood ≤ 1/n^2
sRecover ≈ 2*Brecover
q = 1/2
```

Then E1 gives

```text id="dj92bi"
E[T] ≤ Tgood + δgood * sRecover * (1-q)^(-1)
     ≤ 21*C0*n*(L+1) + (1/n^2) * (2*Cbad*n^2*(L+1)) * 2
     = 21*C0*n*(L+1) + 4*Cbad*(L+1).
```

For `n ≥ 1`, the second term is `≤ 4*Cbad*n*(L+1)`, so the final interaction bound is

```text id="dc3gwm"
E[T_interactions] ≤ C * n * (L+1).
```

Thus the bad-event contribution is not a bottleneck. Even if the recovery block uses the Phase-10 backup bound `3n²(1+2log n)` interactions, multiplying by `1/n²` gives only `O(log n)` interactions, which is `o(n log n)` and certainly absorbed by `C*n*(L+1)`.

The tiny-clock fallback with E3’s `counterMax*n²` bound is also `O(n²(L+1))` interactions before multiplication. With probability `≤ 1/n²`, it contributes `O(L+1)` interactions; with super-polynomial tiny probability, it is even smaller.

## 4. Target Lean statements

### 4.1 Pure E4 block builder

This is the first theorem I would add, probably in a new `DotyExpectedTime.lean`.

```lean id="xr8xno"
theorem block_half_from_recovery_expected
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (B : ℝ≥0∞) (hBfin : B ≠ ⊤)
    (s : ℕ) (hspos : 0 < s)
    (hs : B * 2 ≤ (s : ℝ≥0∞))
    (hRecover : ∀ b ∈ (Doneᶜ : Set α), expectedHitting K b Done ≤ B) :
    ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) := by
  intro b hb
  exact bad_le_half_of_expectedHitting K hDone hAbs b s hspos B hBfin
    (hRecover b hb) hs
```

This is just E1’s `bad_le_half_of_expectedHitting`. fileciteturn43file0mi1dvw"
theorem expected_time_from_whp_and_recovery
    {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (c₀ : α) {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (δgood B : ℝ≥0∞)
    (hBfin : B ≠ ⊤)
    (hspos : 0 < sRecover)
    (hs : B * 2 ≤ (sRecover : ℝ≥0∞))
    (hδ : (K ^ Tgood) c₀ Doneᶜ ≤ δgood)
    (hRecover : ∀ b ∈ (Doneᶜ : Set α), expectedHitting K b Done ≤ B) :
    expectedHitting K c₀ Done
      ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
  have hblock :
      ∀ b ∈ (Doneᶜ : Set α), (K ^ sRecover) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) :=
    block_half_from_recovery_expected K hDone hAbs B hBfin sRecover hspos hs hRecover
  exact expectedHitting_split_geometric K hDone hAbs
    sRecover hsRecover (1 / 2 : ℝ≥0∞) hblock c₀ Tgood δgood hδ
```

This is the exact conditioning-free version of the paper’s split.

### 4.3 Doty-specific expected-time statement

Use the seam-corrected 21-instance headline surface:

```lean id="cwqpxo"
noncomputable def StableDone (L K : ℕ)
    (init : Config (AgentState L K)) : Set (Config (AgentState L K)) :=
  {c | majorityStableEndpoint (L := L) (K := K) init c}
```

Then:

```lean id="o30fyc"
theorem doty_expected_time
    {L K n C0 Cexp : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    -- stable endpoint absorbing:
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    -- recovery expected-time cap, assembled from E2/E3:
    (Brecover : ℝ≥0∞) (hBfin : Brecover ≠ ⊤)
    (sRecover : ℕ) (hsRecover_pos : 0 < sRecover)
    (hsRecover : Brecover * 2 ≤ (sRecover : ℝ≥0∞))
    (hRecover : ∀ b ∈ (StableDone L K init)ᶜ,
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ Brecover)
    -- final arithmetic:
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (harith :
      ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
        + (1 / n : ℝ≥0∞) * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹
      ≤ ((Cexp * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ ((Cexp * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  classical
  let K0 := (NonuniformMajority L K).transitionKernel
  let Tgood : ℕ := ∑ i, (phases i).t
  have hhead := doty_time_headline_W2
    (L := L) (K := K) (n := n) (C0 := C0)
    init c₀ Cphase δ phases ht hε h_chain hx₀ h_post hC0 hδ
  have hfail :
      (K0 ^ Tgood) c₀ (StableDone L K init)ᶜ ≤ (1 / n : ℝ≥0∞) := by
    -- `hhead.1` has the same bad set `{c | ¬ majorityStableEndpoint init c}`.
    simpa [K0, Tgood, StableDone] using hhead.1
  have hT :
      (Tgood : ℝ≥0∞) ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hhead.2

  have hsplit :=
    expected_time_from_whp_and_recovery
      K0 c₀ hDone hDoneAbs Tgood sRecover
      (by omega : sRecover ≠ 0)
      (1 / n : ℝ≥0∞) Brecover hBfin hsRecover_pos hsRecover
      hfail hRecover

  calc expectedHitting K0 c₀ (StableDone L K init)
      ≤ (Tgood : ℝ≥0∞)
          + (1 / n : ℝ≥0∞) * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := hsplit
    _ ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
          + (1 / n : ℝ≥0∞) * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
        gcongr
    _ ≤ ((Cexp * n * (L + 1 : ℕ)) : ℝ≥0∞) := harith
```

This is the right top-level assembly: no new probability, only the whp headline plus a recovery expectation cap.

## 5. Recovery cap statement to feed `doty_expected_time`

The recovery cap should be a separate theorem, because it is deterministic classification + E2/E3.

A clean target shape is:

```lean id="fps9mu"
theorem doty_recovery_expected_bound
    {L K n : ℕ} (hn : 18 ≤ n)
    (init : Config (AgentState L K))
    (Brecover : ℝ≥0∞)
    (hBrecover :
      3 * (((n ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 + 2 * Real.log n))
        + ((21 * (50 * (L + 1)) * (n * n) : ℕ) : ℝ≥0∞)
      ≤ Brecover)
    -- deterministic classification of every valid reachable not-stable state:
    (hClassify :
      ∀ b ∈ (StableDone L K init)ᶜ,
        RecoveryClass (L := L) (K := K) n init b)
    -- each class has the corresponding E2/E3 bridge to StableDone:
    (hClassBound :
      ∀ b, RecoveryClass (L := L) (K := K) n init b →
        expectedHitting (NonuniformMajority L K).transitionKernel b
          (StableDone L K init) ≤ Brecover) :
    ∀ b ∈ (StableDone L K init)ᶜ,
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ Brecover := by
  intro b hb
  exact hClassBound b (hClassify b hb)
```

`RecoveryClass` should be a disjunction:

```lean id="p3fxqr"
inductive RecoveryClass ... (b : Config (AgentState L K)) : Prop
| bigClockTimed :
    -- some timed phase p, AllClockGEpCard p n, n/5 floor,
    -- phase-counter cap
    ...
| tinyClockTimed :
    -- some timed phase p, AllClockGEpCard p n, 2 ≤ mC,
    -- phase-counter cap
    ...
| phase10Majority :
    Phase10ExpectedTime.S1 n b → ...
| phase10Tie :
    Phase10ExpectedTime.Tie1plus n b → ...
```

The `bigClockTimed` branch uses `timed_phase_progress_real_bigClock`; the `tinyClockTimed` branch uses `timed_phase_progress_real_tinyClock`; the phase-10 branches use `phase10_expected_stabilization_O_nsq_log` and the tie analogue. E3 explicitly states that the wrappers are E4-ready and that the only remaining input is the clock floor. file

## 6. One important correction to the paper-style prose

The split should not be described as “AT TIME 0” in Lean. The start `c₀` is deterministic. The role-split event materializes at the Phase-0 checkpoint inside the run. In Lean, it enters only through the bound

```lean id="mr2wth"
(K0 ^ Tgood) c₀ Doneᶜ ≤ δgood
```

or through a deterministic `RecoveryClass` theorem applied to arbitrary post-checkpoint states. The expected-time theorem should never mention conditional probability; it should only use `expectedHitting_split_geometric`.

## 7. Minimal assembly sequence

The final proof order is:

1. `doty_time_headline_W2` or `doty_time_composition_W2`  
   gives the good horizon and failure bound. fileciteturn54file0L27-L61 `timed_phase_progress_real_bigClock`,
   `timed_phase_progress_real_tinyClock`,
   `phase10_expected_stabilization_O_nsq_log`,
   and tie backup. fileciteturnTgood ≤ 21*C0*n*(L+1)` and
   `(1/n²) * O(n²(L+1)) ≤ O(n(L+1))`.

That is E4: a pure tail-sum assembly over the already landed engines.

---

## STATUS — IMPLEMENTED 2026-06-10 (Probability/DotyExpectedTime.lean)

All four blueprint stages landed in the new append-only file
`Probability/DotyExpectedTime.lean`. Single-file `lake env lean … DotyExpectedTime.lean`
EXIT 0, zero warnings; `#print axioms` on all 7 headlines ⊆ `[propext, Classical.choice,
Quot.sound]`; 0 sorry / 0 admit / 0 axiom / 0 native_decide. Commit `2b9f0986`.

### Delivered theorems
- `block_half_from_recovery_expected` (§4.1) — exactly E1 `bad_le_half_of_expectedHitting`.
- `expected_time_from_whp_and_recovery` (§4.2) — exactly E1 `expectedHitting_split_geometric`
  at `q = 1/2`.
- `StableDone`, `compl_StableDone` — the Done set; its complement is the headline's bad set (rfl).
- `RecoveryClass`, `RecoveryClass.expectedHitting_le`, `doty_recovery_expected_bound` (§5).
- `doty_expected_time` (§4.3) — top-level assembly.
- `doty_harith_concrete`, `doty_expected_time_concrete` — concrete `Cexp = 21·C0 + 4·Cbad`.

### Final hypothesis surface of `doty_expected_time`
`{L K n C0 Cexp : ℕ}`, `init c₀`, the 8 `doty_time_headline_W2` inputs
(`Cphase δ phases ht hε h_chain hx₀ h_post hC0 hδ`), `hDone`/`hDoneAbs` (StableDone measurable +
absorbing), the recovery cap quartet (`Brecover hBfin sRecover hsRecover_pos hsRecover hRecover`),
and the explicit `harith`. Conclusion:
`expectedHitting K0 c₀ (StableDone L K init) ≤ ((Cexp*n*(L+1) : ℕ) : ℝ≥0∞)`.

### Concrete corollary `doty_expected_time_concrete`
`Cexp = 21·C0 + 4·Cbad`, `sRecover = 2·Brecover`. The single genuinely-open numeric side
condition is `hrecmass : (1/n)·(2·Brecover)·(1−1/2)⁻¹ ≤ ((4·Cbad·n·(L+1) : ℕ) : ℝ≥0∞)`
(blueprint §3 "recovery contribution is O(n(L+1))" estimate), kept as an explicit hypothesis.

### Blueprint signatures that DRIFTED from the real repo
1. **E3 wrappers** are `ConditionalPhaseProgress.timed_phase_progress_real_bigClock/_tinyClock`
   and conclude on `Engine.potBelow (clockCounterSumAt p) 1`, NOT on `StableDone`. The blueprint's
   §5 hoped to discharge `hClassBound` directly from them; in reality the progress-set ⟹ StableDone
   transfer is missing, so `RecoveryClass` carries each branch's StableDone witness as explicit
   constructor data and `hClassify` stays named. This is the documented protocol residual.
2. **`doty_time_headline_W2`** uses `(phases lastPhaseW2).Post` (`private lastPhaseW2 := ⟨21-1,_⟩`)
   in `h_post`; the blueprint's `⟨21-1, by omega⟩` is defeq (Fin proof irrelevance) and used verbatim.
3. **E2 stabilization headlines** (`phase10_expected_stabilization_O_nsq_log` `≤ 3·n²(1+2 log n)`,
   tie analogue `≤ 2·n²(1+2 log n)`) live in `ExactMajority.Phase10Drop`; `S1`/`Tie1plus` likewise.
4. **`doty_expected_time` proof body**: the blueprint's `let K0 := …` / `set Tgood := …` rewrites
   inside `phases`'s kernel-indexed type, producing a `phases✝` application mismatch. Fixed by
   computing the headline `hhead` BEFORE any abbreviation and inlining the kernel literally.
