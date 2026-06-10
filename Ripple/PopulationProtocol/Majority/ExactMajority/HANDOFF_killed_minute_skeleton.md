The highest-risk check found a real mismatch: the killed-minute plan is not sound literally with the current GatedDrift.killK plus guarded rSeedPotSeed/rSeedPotBulk potentials. The current killK has a documented one-step lag: from some x with x ∈ G, it steps to some y even if y ∉ G; only the next step sends that ungated alive state to none 

GatedEscape

. Therefore “alive states satisfy Q_mix by construction” is false for the existing killK. This is exactly where a guarded potential if Q then Φ else ⊤ explodes.

The minimal safe route is either:

Use unguarded potentials and weaken alive Post to the numerical crossing only, so alive-off-Q_mix endpoints are not automatically failures; this works for the seed leg but the bulk leg still needs the mC/10 floor invariant tracked along the killed path.

Introduce an immediate-kill variant killK_now, where successors outside the gate are mapped to none in the same step. Then the “alive implies gate” statement is true, guarded potentials and none ∈ Post work cleanly, and the killed seed/bulk phases can be proved by a kernel-parametric weak window-drift builder.

I would implement option 2 for tonight’s compile. Everything below is written around that minimal correction. If you insist on using the current GatedDrift.killK, the exact breakpoints are marked.

1. Exact current inventory
Mixed window

Current Q_mix is a 0.9 prior-level floor, not full crossing:

lean
structure Q_mix (n mC T : ℕ) (c : Config (AgentState L K)) : Prop where
  /-- The full population size (Main/Reserve included). -/
  card : c.card = n
  /-- Clock-role agents are at phase EXACTLY 3 ... -/
  clockPhase3 : ∀ a ∈ c, a.role = .clock → a.phase.val = 3
  /-- The carried clock population size. -/
  clockSize : clockCount (L := L) (K := K) c = mC
  /-- The level-`T` 0.9-floor ... -/
  crossedT : 9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c

So the seed proof does not need a previous full crossing; it consumes exactly crossedT. 

ClockRealMixed

Base potential

From ClockRealKernel:

lean
def rClamp (n T : ℕ) (c : Config (AgentState L K)) : ℕ :=
  min (rBeyond (T + 1) c) n

def rFinished (n T : ℕ) (c : Config (AgentState L K)) : Prop :=
  n ≤ rBeyond (T + 1) c

noncomputable def rSeedPot (n T : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if n ≤ rBeyond (T + 1) c then 0
  else ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (rClamp n T c : ℝ))))

This is target-level-parametric: seed instantiates target seedLo mC, bulk instantiates target bulkHi mC. 

ClockRealKernel

Seed target and drift

The actual seed leg is in ClockRealSeed, not ClockRealMixed.rSeedPotMix.

lean
def seedLo (mC : ℕ) : ℕ := mC / 10

Seed source floor:

lean
theorem seed_drip_floor (mC m rT : ℕ)
    (hcr : 9 * mC / 10 ≤ rT) (hm : m < seedLo mC) :
    (mC / 10) * (mC / 10) ≤ (rT - m) * (rT - m - 1)

Seed drift:

lean
theorem rSeedPot_contracts_seed (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hcap : T < K * (L + 1)) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hnc : rBeyond (L := L) (K := K) (T + 1) c < seedLo mC) :
    ∫⁻ c', rSeedPot (L := L) (K := K) (seedLo mC) T s c'
        ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ)
            / ((n : ℝ) * ((n : ℝ) - 1)))
          * (1 - Real.exp (-s)))
        * rSeedPot (L := L) (K := K) (seedLo mC) T s c

The current packaged seed phase uses guarded rSeedPotSeed, with ⊤ off Q_mix: 

ClockRealSeed

 

ClockRealSeed

lean
noncomputable def rSeedPotSeed (n mC T : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) : ℝ≥0∞ :=
  open Classical in
  if Q_mix (L := L) (K := K) n mC T c then
    rSeedPot (L := L) (K := K) (seedLo mC) T s c
  else ⊤

habs_mix enters seed packaging in exactly these places:

lean
-- hQ_abs to windowDrift_PhaseConvergence
(fun c => Q_mix (L := L) (K := K) n mC T c)
habs_mix

-- guarded-potential rewrite under the successor integral
exact rSeedPotSeed_eq_on_window n mC T (Real.log 2) x
  (habs_mix c x hQ hsupp)

-- Post closure
refine ⟨habs_mix c c' hQ hc', ?_⟩
have hmono := hmono_mix_discharged n mC T c c' hQ hc'
omega

ClockRealSeed

 

ClockRealSeed

Bulk target and drift

Bulk target:

lean
def bulkHi (mC : ℕ) : ℕ := 9 * mC / 10

Bulk window:

lean
def QbulkWin (n mC T : ℕ) (c : Config (AgentState L K)) : Prop :=
  Q_mix (L := L) (K := K) n mC T c ∧
    mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c

Bulk drift:

lean
theorem rSeedPot_contracts_bulk (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hcap : T < K * (L + 1)) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hlo : mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c)
    (hnc : rBeyond (L := L) (K := K) (T + 1) c < bulkHi mC) :
    ∫⁻ c', rSeedPot (L := L) (K := K) (bulkHi mC) T s c'
        ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ)
            / ((n : ℝ) * ((n : ℝ) - 1)))
          * (1 - Real.exp (-s)))
        * rSeedPot (L := L) (K := K) (bulkHi mC) T s c

The bulk proof consumes hlo; this is why a killed bulk phase needs the inner invariant QbulkWin, not merely Q_mix, while the phase is running. 

ClockRealBulk

 

ClockRealBulk

Markov/tail extraction engine

The current extraction engine is Protocol-parametric, not arbitrary-kernel-parametric:

lean
noncomputable def windowDrift_PhaseConvergence (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config Λ → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)
    (Pre Post : Config Λ → Prop)
    (hPost_abs : ∀ c c', Post c → c' ∈ (P.stepDistOrSelf c).support → Post c')
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ c, ¬ Post c → θ ≤ Φ c)
    (hPre_Q : ∀ c, Pre c → Q c)
    (Φ₀ : ℝ≥0∞) (hPre_bound : ∀ c, Pre c → Φ c ≤ Φ₀)
    (t : ℕ) (ε : ℝ≥0)
    (hε : r ^ t * Φ₀ / θ ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence P.transitionKernel

So it cannot be instantiated directly at κQ : Kernel (Option Config) (Option Config). You need a kernel-parametric weak copy, returning PhaseConvergenceW κQ. 

WindowConcentration

The already-landed weak target is:

lean
structure PhaseConvergenceW {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (K : Kernel Ω Ω) where
  Pre : Ω → Prop
  Post : Ω → Prop
  t : ℕ
  ε : ℝ≥0
  convergence : ∀ x, Pre x → (K ^ t) x {y | ¬Post y} ≤ (ε : ℝ≥0∞)

and composition is:

lean
theorem composeW_two_phases
    {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] {K : Kernel Ω Ω}
    [IsMarkovKernel K]
    (phase1 phase2 : PhaseConvergenceW K)
    (h_chain : ∀ x, phase1.Post x → phase2.Pre x)
    (x₀ : Ω) (hx₀ : phase1.Pre x₀) :
    (K ^ (phase1.t + phase2.t)) x₀ {y | ¬phase2.Post y} ≤
      (phase1.ε + phase2.ε : ℝ≥0∞)

PhaseConvergenceWeak

 

PhaseConvergenceWeak

2. habs_mix replacement move

In the real packaged seed/bulk phases, habs_mix is used to prove support closure of the window and to rewrite guarded potentials after successor integration.

For the killed replacement, do not try to prove the old habs_mix. Instead make the killed kernel enforce:

lean
o' ∈ (κQ o).support ∧ Alive o'  → Q_mix ... (Option.get ...)

With the current GatedDrift.killK, that statement is false because of the one-step lag. With an immediate-kill kernel it is true by construction.

The Lean-level successor split you want in killed proofs is:

lean
rcases o' with _ | c'
 · -- cemetery
   simp [GatedDrift.killΦ]
 · -- alive successor
   have hQ' : Q_mix (L := L) (K := K) n mC T c' := by
     exact alive_support_implies_Q hsupport
   -- now guarded-potential rewrite is legal:
   rw [rSeedPotSeed_eq_on_window n mC T (Real.log 2) c' hQ']

For bulk, the analogous alive fact must be the stronger one:

lean
QbulkWin (L := L) (K := K) n mC T c'

That is obtained from Q_mix alive-support plus monotonicity preserving the seed floor:

lean
have hmono := hmono_mix_discharged n mC T c c' hQ hsupp_real
exact ⟨hQ', le_trans hlo hmono⟩

For none ∈ Post, define Option-phase predicates with none accepted in both Pre and Post for the second phase; otherwise the weak composer cannot chain seed cemetery states into bulk Pre.

So do not use:

lean
Pre := fun o => ∃ c, o = some c ∧ seedPre c

for both phases. Use:

lean
Pre  := fun o => o = none ∨ ∃ c, o = some c ∧ realPre c
Post := fun o => o = none ∨ ∃ c, o = some c ∧ realPost c

Then the chain map is:

lean
intro o ho
rcases ho with rfl | ⟨c, rfl, hseedPost⟩
 · exact Or.inl rfl
 · exact Or.inr ⟨c, rfl, hseedPost⟩
3. Minimal helper to add: kernel-parametric weak window drift

This is the generic helper I would add first, probably in WindowConcentration.lean or a small new file. It is the same proof as windowDrift_PhaseConvergence, but:
Protocol → arbitrary Kernel, and PhaseConvergence → PhaseConvergenceW.

lean
namespace ExactMajority
namespace WindowConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem kernel_lintegral_decay_on_absorbing
    {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    {K : Kernel Ω Ω} [IsMarkovKernel K]
    (Φ : Ω → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Ω → Prop)
    (hQ_abs : ∀ x y, Q x → y ∈ (K x).support → Q y)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, Q x → ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x₀ : Ω) (hQ0 : Q x₀) :
    ∫⁻ y, Φ y ∂((K ^ t) x₀) ≤ r ^ t * Φ x₀ := by
  -- Copy `WindowConcentration.lintegral_decay_on_absorbing`.
  -- Replace `Protocol.ae_of_stepDistOrSelf_support_preserved`
  -- by the kernel support-preservation induction:
  --
  --   have hsupp_ae : ∀ᵐ y ∂(K x), Q y := by
  --     rw [ae_iff, ... PMF.toMeasure_apply_eq_zero_iff if K is PMF-backed]
  --
  -- In fully general kernel form, prove a small lemma:
  --   kernel_ae_of_support_preserved :
  --     Q x → ∀ᵐ y ∂(K x), Q y
  -- from `support`.
  --
  -- Then the rest is byte-for-byte the existing proof.
  sorry

theorem kernel_windowDrift_tail
    {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    {K : Kernel Ω Ω} [IsMarkovKernel K]
    (Φ : Ω → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Ω → Prop)
    (hQ_abs : ∀ x y, Q x → y ∈ (K x).support → Q y)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, Q x → ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (Post : Ω → Prop)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ x, ¬ Post x → θ ≤ Φ x)
    (t : ℕ) (x₀ : Ω) (hQ0 : Q x₀) :
    (K ^ t) x₀ {y | ¬ Post y} ≤ r ^ t * Φ x₀ / θ := by
  have hsubset : {y : Ω | ¬ Post y} ⊆ {y | θ ≤ Φ y} :=
    fun y hy => hlink y hy
  calc
    (K ^ t) x₀ {y | ¬ Post y}
        ≤ (K ^ t) x₀ {y | θ ≤ Φ y} := measure_mono hsubset
    _ ≤ r ^ t * Φ x₀ / θ := by
      -- Markov inequality + `kernel_lintegral_decay_on_absorbing`.
      -- This is the same body as `WindowConcentration.measure_ge_thresh_on_absorbing`.
      sorry

noncomputable def kernelWindowDrift_PhaseConvergenceW
    {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    {K : Kernel Ω Ω} [IsMarkovKernel K]
    (Φ : Ω → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Ω → Prop)
    (hQ_abs : ∀ x y, Q x → y ∈ (K x).support → Q y)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, Q x → ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (Pre Post : Ω → Prop)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ x, ¬ Post x → θ ≤ Φ x)
    (hPre_Q : ∀ x, Pre x → Q x)
    (Φ₀ : ℝ≥0∞) (hPre_bound : ∀ x, Pre x → Φ x ≤ Φ₀)
    (t : ℕ) (ε : ℝ≥0)
    (hε : r ^ t * Φ₀ / θ ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre := Pre
  Post := Post
  t := t
  ε := ε
  convergence := by
    intro x₀ hx₀
    have hQ0 : Q x₀ := hPre_Q x₀ hx₀
    calc
      (K ^ t) x₀ {y | ¬ Post y}
          ≤ r ^ t * Φ x₀ / θ :=
            kernel_windowDrift_tail Φ hΦ Q hQ_abs r hdrift Post
              θ hθ hθ_top hlink t x₀ hQ0
      _ ≤ r ^ t * Φ₀ / θ := by
            gcongr
            exact hPre_bound x₀ hx₀
      _ ≤ (ε : ℝ≥0∞) := hε

end WindowConcentration
end ExactMajority
4. Killed minute skeleton

This is the skeleton I would compile-fill. I write κQ_now because the existing killK has the alive-off-gate lag. If you bind κQ_now to the current GatedDrift.killK, the hQ_abs proofs below are exactly where it breaks.

lean
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealSeed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedEscape

namespace ExactMajority
namespace ClockKilledMinute

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators
open ClockRealKernel ClockRealMixed ClockRealSeed ClockRealBulk ClockMonoDischarge
open GatedDrift

variable {L K : ℕ}

abbrev Cfg (L K : ℕ) := Config (AgentState L K)

noncomputable abbrev realκ (L K : ℕ) : Kernel (Cfg L K) (Cfg L K) :=
  (NonuniformMajority L K).transitionKernel

def Qset (n mC T : ℕ) : Set (Cfg L K) :=
  {c | Q_mix (L := L) (K := K) n mC T c}

def SeedPre (n mC T : ℕ) (c : Cfg L K) : Prop :=
  Q_mix (L := L) (K := K) n mC T c ∧
    9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c

def SeedPost (n mC T : ℕ) (c : Cfg L K) : Prop :=
  Q_mix (L := L) (K := K) n mC T c ∧
    mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c

def BulkPre (n mC T : ℕ) (c : Cfg L K) : Prop :=
  QbulkWin (L := L) (K := K) n mC T c

def BulkPost (n mC T : ℕ) (c : Cfg L K) : Prop :=
  Q_mix (L := L) (K := K) n mC T c ∧
    bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c

def optLift (P : Cfg L K → Prop) : Option (Cfg L K) → Prop
  | none => True
  | some c => P c

noncomputable def seedΦ (n mC T : ℕ) : Option (Cfg L K) → ℝ≥0∞ :=
  GatedDrift.killΦ
    (fun c => rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c)

noncomputable def bulkΦ (n mC T : ℕ) : Option (Cfg L K) → ℝ≥0∞ :=
  GatedDrift.killΦ
    (fun c => rSeedPot (L := L) (K := K) (bulkHi mC) T (Real.log 2) c)

noncomputable def minuteRate (n mC : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) /
      ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-Real.log 2)))

/-
Use an immediate-kill kernel here.

Required behavior:

* `none` is absorbing.
* From `some c`, if `Q_mix n mC T c`, the kernel maps the real successor `c'`
  to `some c'` only when `Q_mix n mC T c'`; otherwise to `none`.
* From `some c` with `¬ Q_mix ... c`, it maps to `none`.

This is the correction to current `GatedDrift.killK`.
-/
noncomputable abbrev κQ_now (n mC T : ℕ) :
    Kernel (Option (Cfg L K)) (Option (Cfg L K)) := by
  -- Define as:
  --   if current is `some c ∈ Qset`, map `realκ c` through
  --     fun c' => if c' ∈ Qset then some c' else none
  --   else dirac none.
  --
  -- Or add this as a reusable `GatedDrift.killK_now`.
  exact GatedDrift.killK (realκ L K) (Qset (L := L) (K := K) n mC T)
  -- WARNING: this line uses the current lagged killK and is intentionally the
  -- compile-break if you do not replace it by immediate-kill semantics.

lemma killed_seed_drift
    (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1)) :
    ∀ o, optLift (SeedPre (L := L) (K := K) n mC T) o →
      ∫⁻ o', seedΦ (L := L) (K := K) n mC T o'
          ∂(κQ_now (L := L) (K := K) n mC T o)
        ≤ minuteRate n mC * seedΦ (L := L) (K := K) n mC T o := by
  intro o ho
  cases o with
  | none =>
      -- cemetery branch: kernel is dirac none, potential none = 0
      -- simp [κQ_now, seedΦ, optLift]
      sorry
  | some c =>
      rcases ho with ⟨hQ, _hprior⟩
      have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      -- With immediate kill:
      --   split real successors into alive-in-Q and killed-to-none.
      --   `none` contributes 0 to `killΦ`.
      --   alive integral is bounded by the real unguarded seed drift.
      by_cases hfin : seedLo mC ≤ rBeyond (L := L) (K := K) (T + 1) c
      · -- finished branch copied from `clock_real_advance_seed`, but over killed kernel.
        have hΦc0 :
            rSeedPot (L := L) (K := K) (seedLo mC) T (Real.log 2) c = 0 := by
          unfold rSeedPot
          rw [if_pos hfin]
        -- RHS is zero; use `hmono_mix_discharged` plus immediate-kill support split.
        -- Alive successors preserve finished; `none` has potential zero.
        sorry
      · have hnc : rBeyond (L := L) (K := K) (T + 1) c < seedLo mC := by omega
        -- Reduce killed integral to the real integral of unguarded `rSeedPot`,
        -- dropping killed-to-none mass since `killΦ none = 0`.
        -- Then:
        have hreal :=
          rSeedPot_contracts_seed (L := L) (K := K)
            n mC T hn hmC hT (Real.log 2) hs c hQ hnc
        -- finish by `simpa [seedΦ, minuteRate, realκ]` after the killed-integral rewrite.
        sorry

lemma killed_bulk_drift
    (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1)) :
    ∀ o, optLift (BulkPre (L := L) (K := K) n mC T) o →
      ∫⁻ o', bulkΦ (L := L) (K := K) n mC T o'
          ∂(κQ_now (L := L) (K := K) n mC T o)
        ≤ minuteRate n mC * bulkΦ (L := L) (K := K) n mC T o := by
  intro o ho
  cases o with
  | none =>
      -- cemetery branch
      sorry
  | some c =>
      rcases ho with ⟨hQ, hlo⟩
      have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      by_cases hfin : bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c
      · -- finished branch: alive successors preserve by `hmono_mix_discharged`,
        -- killed successors contribute zero.
        sorry
      · have hnc : rBeyond (L := L) (K := K) (T + 1) c < bulkHi mC := by omega
        have hreal :=
          rSeedPot_contracts_bulk (L := L) (K := K)
            n mC T hn hmC hT (Real.log 2) hs c hQ hlo hnc
        -- finish by killed-integral rewrite as above
        sorry

noncomputable def killedSeedPhase
    (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1))
    (tseed : ℕ) (εseed : ℝ≥0)
    (hεs : minuteRate n mC ^ tseed *
        ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1
        ≤ (εseed : ℝ≥0∞)) :
    PhaseConvergenceW (κQ_now (L := L) (K := K) n mC T) :=
  WindowConcentration.kernelWindowDrift_PhaseConvergenceW
    (seedΦ (L := L) (K := K) n mC T)
    (by fun_prop)
    (optLift (SeedPre (L := L) (K := K) n mC T))
    (by
      -- hQ_abs for immediate kill:
      -- none -> none
      -- some c with SeedPre:
      --   alive successor satisfies Q_mix by kernel construction;
      --   prior floor at level T is preserved by `Q_mix` itself / monotonicity as needed.
      -- For the current lagged `killK`, this is false.
      sorry)
    (minuteRate n mC)
    (killed_seed_drift (L := L) (K := K) n mC T hn hmC hT)
    (optLift (SeedPre (L := L) (K := K) n mC T))
    (optLift (SeedPost (L := L) (K := K) n mC T))
    1 one_ne_zero ENNReal.one_ne_top
    (by
      intro o hnot
      cases o with
      | none =>
          -- impossible because `optLift _ none = True`
          exfalso
          exact hnot trivial
      | some c =>
          -- `¬ SeedPost` and seed window imply unfinished at `seedLo`.
          -- Then `not_finished_imp_rSeedPot_ge_one`.
          unfold optLift SeedPost seedΦ GatedDrift.killΦ at hnot ⊢
          by_cases hQ : Q_mix (L := L) (K := K) n mC T c
          · have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
            have hnf : ¬ rFinished (L := L) (K := K) (seedLo mC) T c := by
              unfold rFinished
              intro hfin
              exact hnot ⟨hQ, by simpa [seedLo] using hfin⟩
            exact not_finished_imp_rSeedPot_ge_one
              (L := L) (K := K) (seedLo mC) T (Real.log 2) hs c hnf
          · -- If Pre/Q invariant is arranged correctly this branch should not be needed
            -- for starts, but `hlink` is global. Use unguarded potential: if post fails
            -- due only to missing Q, this branch is not generally true.
            --
            -- This is another reason to prefer alive Post = numerical crossing only
            -- if staying with lagged `killK`.
            sorry)
    (fun o ho => ho)
    (ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))))
    (by
      intro o ho
      cases o with
      | none => simp [seedΦ]
      | some c =>
          rcases ho with ⟨hQ, _⟩
          simp [seedΦ]
          have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          exact rSeedPot_le_max (L := L) (K := K) (seedLo mC) T (Real.log 2) hs c)
    tseed εseed hεs

noncomputable def killedBulkPhase
    (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1))
    (tbulk : ℕ) (εbulk : ℝ≥0)
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1
        ≤ (εbulk : ℝ≥0∞)) :
    PhaseConvergenceW (κQ_now (L := L) (K := K) n mC T) :=
  WindowConcentration.kernelWindowDrift_PhaseConvergenceW
    (bulkΦ (L := L) (K := K) n mC T)
    (by fun_prop)
    (optLift (BulkPre (L := L) (K := K) n mC T))
    (by
      -- hQ_abs:
      -- none is absorbing;
      -- from some c with QbulkWin:
      --   immediate kill gives either none or alive c' with Q_mix;
      --   hmono_mix_discharged preserves `mC/10 ≤ rBeyond (T+1)`.
      sorry)
    (minuteRate n mC)
    (killed_bulk_drift (L := L) (K := K) n mC T hn hmC hT)
    (optLift (BulkPre (L := L) (K := K) n mC T))
    (optLift (BulkPost (L := L) (K := K) n mC T))
    1 one_ne_zero ENNReal.one_ne_top
    (by
      intro o hnot
      cases o with
      | none =>
          exfalso
          exact hnot trivial
      | some c =>
          unfold optLift BulkPost bulkΦ GatedDrift.killΦ at hnot ⊢
          by_cases hQ : Q_mix (L := L) (K := K) n mC T c
          · have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
            have hnf : ¬ rFinished (L := L) (K := K) (bulkHi mC) T c := by
              unfold rFinished
              intro hfin
              exact hnot ⟨hQ, hfin⟩
            exact not_finished_imp_rSeedPot_ge_one
              (L := L) (K := K) (bulkHi mC) T (Real.log 2) hs c hnf
          · sorry)
    (fun o ho => ho)
    (ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))))
    (by
      intro o ho
      cases o with
      | none => simp [bulkΦ]
      | some c =>
          rcases ho with ⟨hQ, hlo⟩
          simp [bulkΦ]
          have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          exact rSeedPot_le_max (L := L) (K := K) (bulkHi mC) T (Real.log 2) hs c)
    tbulk εbulk hεb

theorem clock_killed_stepW
    (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1))
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : minuteRate n mC ^ tseed *
        ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1
        ≤ (εseed : ℝ≥0∞))
    (hεb : minuteRate n mC ^ tbulk *
        ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1
        ≤ (εbulk : ℝ≥0∞))
    (o₀ : Option (Cfg L K))
    (ho₀ : optLift (SeedPre (L := L) (K := K) n mC T) o₀) :
    ((κQ_now (L := L) (K := K) n mC T) ^ (tseed + tbulk)) o₀
      {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o}
      ≤ (εseed + εbulk : ℝ≥0∞) := by
  let seed :=
    killedSeedPhase (L := L) (K := K) n mC T hn hmC hT tseed εseed hεs
  let bulk :=
    killedBulkPhase (L := L) (K := K) n mC T hn hmC hT tbulk εbulk hεb
  have hchain : ∀ o, seed.Post o → bulk.Pre o := by
    intro o ho
    cases o with
    | none =>
        exact trivial
    | some c =>
        -- seed.Post some c is `Q_mix ∧ mC/10 ≤ rBeyond(T+1)`,
        -- definitionally `QbulkWin`.
        exact ho
  exact composeW_two_phases seed bulk hchain o₀ ho₀

Two notes on that skeleton:

If you keep Post some c := Q_mix c ∧ threshold, then the hlink branches where ¬Q_mix c are not true for unguarded rSeedPot. Those branches disappear if immediate-kill gives alive → Q_mix on all relevant support, but the global hlink field still sees arbitrary states. A cleaner version defines Post some c := threshold for killed phases, then separately proves that endpoint Q_mix is handled by escape/side-event accounting. This is the better choice with current lagged killK.

If you use guarded rSeedPotSeed/rSeedPotBulk instead of killΦ rSeedPot, then immediate-kill is mandatory; current killK will put some c' off-window under the integral, where the guarded potential is ⊤.

5. Real gated step via killed step

This part works with the landed real_le_killed shape. Let:

lean
def RealMinutePost (n mC T : ℕ) (c : Cfg L K) : Prop :=
  BulkPost (L := L) (K := K) n mC T c

Then the real-to-killed endpoint argument is:

lean
theorem clock_real_step_gated
    (n mC T : ℕ)
    (tseed tbulk : ℕ) (εseed εbulk εesc : ℝ≥0∞)
    (c₀ : Cfg L K)
    (hpre : SeedPre (L := L) (K := K) n mC T c₀)
    (hesc :
      ((κQ_now (L := L) (K := K) n mC T) ^ (tseed + tbulk)) (some c₀)
        {(none : Option (Cfg L K))} ≤ εesc)
    (hkilled :
      ((κQ_now (L := L) (K := K) n mC T) ^ (tseed + tbulk)) (some c₀)
        {o | ¬ optLift (BulkPost (L := L) (K := K) n mC T) o}
        ≤ (εseed + εbulk))
    (hpost_imp :
      ∀ c, optLift (BulkPost (L := L) (K := K) n mC T) (some c) →
        RealMinutePost (L := L) (K := K) n mC T c) :
    ((realκ L K) ^ (tseed + tbulk)) c₀
      {c | ¬ RealMinutePost (L := L) (K := K) n mC T c}
      ≤ εesc + (εseed + εbulk) := by
  classical
  set bad : Cfg L K → Prop :=
    fun c => ¬ RealMinutePost (L := L) (K := K) n mC T c
  have hdom :=
    GatedDrift.real_le_killed
      (K := realκ L K)
      (G := Qset (L := L) (K := K) n mC T)
      bad
      (tseed + tbulk) c₀

  -- For `κQ_now`, use its corresponding `real_le_killed_now`.
  -- With current `GatedDrift.killK`, `hdom` is exactly the landed lemma.
  refine le_trans hdom ?_

  let A : Set (Option (Cfg L K)) := {(none : Option (Cfg L K))}
  let B : Set (Option (Cfg L K)) :=
    {o | ∃ c, o = some c ∧ bad c}

  have hsub :
      {o : Option (Cfg L K) | o = none ∨ (∃ c, o = some c ∧ bad c)}
        ⊆ A ∪ B := by
    intro o ho
    rcases ho with hnone | hsome
    · left
      simpa [A] using hnone
    · right
      simpa [B] using hsome

  calc
    ((κQ_now (L := L) (K := K) n mC T) ^ (tseed + tbulk)) (some c₀)
      {o | o = none ∨ (∃ c, o = some c ∧ bad c)}
        ≤ ((κQ_now (L := L) (K := K) n mC T) ^ (tseed + tbulk)) (some c₀)
            (A ∪ B) := measure_mono hsub
    _ ≤ ((κQ_now (L := L) (K := K) n mC T) ^ (tseed + tbulk)) (some c₀) A
          + ((κQ_now (L := L) (K := K) n mC T) ^ (tseed + tbulk)) (some c₀) B :=
        measure_union_le _ _
    _ ≤ εesc + (εseed + εbulk) := by
      apply add_le_add
      · simpa [A] using hesc
      · -- `some bad` is contained in killed phase failure.
        refine le_trans (measure_mono ?_) hkilled
        intro o ho hp
        rcases ho with ⟨c, rfl, hbad⟩
        exact hbad (hpost_imp c hp)

For the escape input hesc, with the landed prefix-union lemma you should produce:

lean
have hesc :
    ((GatedDrift.killK (realκ L K) (Qset (L := L) (K := K) n mC T)) ^ M) (some c₀)
      {(none : Option (Cfg L K))}
      ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, ((realκ L K) ^ τ) c₀ Sᶜ :=
  GatedDrift.kill_escape_le_prefix_union
    (K := realκ L K)
    (G := Qset (L := L) (K := K) n mC T)
    S q hstep M c₀ hQ₀

The exact landed signature is: 

GatedEscape

lean
theorem kill_escape_le_prefix_union [IsMarkovKernel K] (S : Set α) (q : ℝ≥0∞)
    (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q)
    (M : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (killK K G ^ M) (some x₀) {(none : Option α)} ≤
      (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ τ) x₀ Sᶜ
6. Mismatch checklist

Here are the exact mismatches I would fix before coding the final brick:

WindowConcentration.windowDrift_PhaseConvergence is not usable at κQ. It is Protocol-parametric and returns strong PhaseConvergence P.transitionKernel; killed minute needs Kernel-parametric PhaseConvergenceW.

Current killK does not make alive states satisfy the gate. It has the one-step-lag behavior. Guarded potentials with ⊤ off-window therefore do not work unless you switch to immediate kill or avoid guarded potentials.

The actual seed drift is rSeedPot_contracts_seed, not rSeedPotMix. rSeedPotMix targets full mC and belongs to the older full-crossing mixed advance. The real per-minute faithful seed target is seedLo mC = mC/10.

Bulk drift needs the current-state hlo. You cannot prove a bulk killed phase from merely Q_mix; its window must include mC/10 ≤ rBeyond (T+1), and that invariant must be preserved along alive killed successors.

none must be in both Post and the next phase’s Pre. Otherwise composeW_two_phases cannot chain cemetery endpoints from seed into bulk.

For clock_real_step_gated, the killed alive-post must imply the complement of some bad. If bad := ¬RealMinutePost, then you need:

lean
∀ c, killedBulkPost (some c) → RealMinutePost c

If RealMinutePost includes Q_mix, either killed alive post must include Q_mix, or the off-window alive mass must be charged to escape/side-event separately.
