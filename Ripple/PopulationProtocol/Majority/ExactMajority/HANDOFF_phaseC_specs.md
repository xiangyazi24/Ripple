I’ll read the paper sections and the Lean template/engines side by side, then map each missing phase to a concrete instance spec rather than guessing from phase names.

I have the paper map now. The biggest structural distinction is that phases 0/1/5/6/7/8 are counter-timed, while 2/4/9 are untimed epidemics/detection and phase 10 is the slow backup; this matters for which Lean convergence shape is appropriate.

0. First: what the existing Lean template actually gives

The reusable target shape is exactly PhaseConvergence:

lean
structure PhaseConvergence ... (K : Kernel Ω Ω) where
  Pre : Ω → Prop
  Post : Ω → Prop
  t : ℕ
  ε : ℝ≥0
  post_absorbing : ∀ x, Post x → K x {y | Post y} = 1
  convergence : ∀ x, Pre x → (K ^ t) x {y | ¬Post y} ≤ (ε : ℝ≥0∞)

So every Phase C file must output one of these over (NonuniformMajority L K).transitionKernel. 

PhaseConvergence

Phase2Convergence.lean is a good template because it does not assume a clock: it builds a real-kernel PhaseConvergence from an absorbing window plus a potential drift. Its comment says the mechanism is an opinion-union epidemic; the informed count is informedU; the window Q2 says all agents are in Phase 2 and opinions lie in {U,v}; and the convergence is built through WindowConcentration.windowDrift_PhaseConvergence. 

DotyParams

 The deliverable is:

lean
noncomputable def phase2Convergence ... (t : ℕ) (ε : ℝ≥0) ... :
    PhaseConvergence (NonuniformMajority L K).transitionKernel

with Pre := Qwin U v n, Post := Qwin U v n ∧ oFinished U n, and the arithmetic tail hypothesis hε. 

DotyParams

The most important generic engine is therefore:

lean
WindowConcentration.windowDrift_PhaseConvergence

which packages an absorbing window Q, a one-step contraction ∫ Φ dK ≤ r Φ, a link ¬Post → θ ≤ Φ, and an initial potential bound into PhaseConvergence. 

WindowConcentration

1. Phase-by-phase audit

I use interaction-count horizons below. Paper “O(log n) time” means O(log n) parallel time, so in the Lean kernel this is normally Θ(n log n) interactions. The paper’s time convention divides interactions by n. 
arXiv

Phase 0 — role assignment + clock creation
Paper event structure

Phase 0 initializes everyone as RoleMCR; two RoleMCR agents become one Main and one RoleCR; a Main meeting RoleCR converts the RoleCR to Main; two RoleCR agents become one Clock and one Reserve; clocks run the standard counter. 
arXiv

The paper’s key probabilistic result is Lemma 5.2: by the end of Phase 0, with probability at least 1 - O(1/n²), all RoleMCR agents are gone, |Main| is close to n/2, and |Clock|, |Reserve| are each at least roughly n/4. It also gives deterministic fallback bounds if RoleMCR = 0 and Phase 1 initializes without entering error backup. 
arXiv

Lean status

Analysis/Phase0Convergence.lean exists, but it is not yet the Phase C instance. It defines:

lean
def mcrCount ...
def phase0Milestone ...
noncomputable def phase0MilestonePhase ...

and proves a MilestonePhase whose milestones are about decreasing mcrCount. 

EarlyDripMarked

 

Phase0Convergence

This is useful, but insufficient. It tracks only the RoleMCR collapse and its own comment notes the slow tail issue near M = 2:

lean
meanTime = Σ n*(n-1)/(M*(M-1)) = O(n²)

which is not the full paper Phase 0 O(log n) parallel-time role split. 

EarlyDripMarked

The local deterministic pieces already exist in PhaseProgress.lean: counter decrement, zero-counter phase advance, and Phase 0 role transformations. 

EarlyDripMarked

 

EarlyDripMarked

 

EarlyDripMarked

 

EarlyDripMarked

Lean instance spec

Recommended new file: Probability/Phase0Convergence.lean.

lean
def Phase0Pre (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  ∀ a ∈ c, a.phase.val = 0 ∧ a.role = .mcr
  -- plus initial bias/output/assigned fields, if the campaign wants exact initial state.

def RoleCountsGood (η : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  roleMCRCount c = 0 ∧
  ((1 - η) * (n : ℝ) / 2 ≤ mainCount c : ℝ) ∧
  ((mainCount c : ℝ) ≤ (1 + η) * (n : ℝ) / 2) ∧
  ((1 - η) * (n : ℝ) / 4 ≤ clockCount c : ℝ) ∧
  ((1 - η) * (n : ℝ) / 4 ≤ reserveCount c : ℝ)

def Phase0Post (η : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, 1 ≤ a.phase.val) ∧
  RoleCountsGood (L := L) (K := K) η n c

t: ⌈C₀ * n * log n⌉ interactions.
ε: O(1/n²), plus the clock-counter failure budget.
Engine: new role-split concentration engine + counter-timeout engine. Existing JansonHitting.MilestonePhase is a component, but not enough by itself. The generic Janson wrapper gives milestone hitting tails once per-step milestone probabilities are available. 

JansonHitting

 

JansonHitting

Phase 1 — averaging / cancellation before opinion collection
Paper event structure

Phase 1 uses the standard counter subroutine. RoleMCR entering Phase 1 is an error path to Phase 10; RoleCR becomes Reserve; two Main agents average opposite-signed biases. 
arXiv

The paper’s Lemma 5.3 gives the Phase 1 outcome: if the initial gap is large, the protocol stabilizes in Phase 2; if the gap is small, by the end of Phase 1 every bias is in {−1,0,+1} and at most 0.03|M| Main agents remain biased, with failure probability O(1/n²). 
arXiv

Lean instance spec

Recommended file: Probability/Phase1Convergence.lean.

lean
def Phase1Pre (η : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  RoleCountsGood (L := L) (K := K) η n c ∧
  (∀ a ∈ c, a.phase.val = 1) ∧
  -- no RoleMCR; clocks have initialized counters; Main biases initialized.

def Phase1SmallGapPost (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, a.role = .main →
    a.bias ∈ {Bias.minusOne, Bias.zero, Bias.plusOne}) ∧
  biasedMainCount c ≤ 3 * mainCount c / 100

def Phase1Post (η : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, 2 ≤ a.phase.val) ∧
  (LargeGapStablePhase2Ready (L := L) (K := K) n c ∨
   Phase1SmallGapPost (L := L) (K := K) n c)

t: ⌈C₁ * n * log n⌉.
ε: O(1/n²).
Engine: not currently present as a named engine. It needs a Phase 1 averaging/cancellation engine, probably built from WindowConcentration.windowDrift_PhaseConvergence for a suitable bias potential plus a counter-timeout wrapper. The local counter facts are already available in PhaseProgress.lean. 

EarlyDripMarked

Dependency: the clock-count lower bound from Lemma 5.2 is needed to make clock-clock counter decrements happen at constant per-interaction probability.

Phase 4 — tie detection / non-tie continuation
Paper event structure

Phase 4 is the post-clock tie detection. If all biased agents have the minimum exponent −L, then the gap |g| < 1, hence g = 0, and the protocol stabilizes to tie output T. If some agent has bias magnitude larger than 2^{-L}, the protocol proceeds to Phase 5. 
arXiv
 The pseudocode says Phase 4 either detects a non-minimal exponent and advances, or sets output T. 
arXiv

The probabilistic input is really from Phase 3: in the tie case, Theorem 6.1 says that at the end of Phase 3 all biased agents have exponent −L whp 1 - O(1/n²); in the non-tie case, Theorem 6.2 gives the structured majority/minority exponent bounds used by Phases 5–8. 
arXiv
 
arXiv

Lean instance spec

Recommended file: Probability/Phase4Convergence.lean.

lean
def Phase4TieReady (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  (∀ a ∈ c, a.phase.val = 4) ∧
  (∀ a ∈ c, a.role = .main → a.bias ≠ .zero →
    biasExponent a.bias = L)

def Phase4NonTieReady (l : ℕ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  (∀ a ∈ c, a.phase.val = 4) ∧
  Phase3StructuredNonTiePost (L := L) (K := K) l n c ∧
  ∃ a ∈ c, a.role = .main ∧ biasExponent a.bias < L

def Phase4Pre (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase4TieReady (L := L) (K := K) n c ∨
  Phase4NonTieReady (L := L) (K := K) l n c

def Phase4Post (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  StableTieOutput (L := L) (K := K) c ∨
  Phase5Pre (L := L) (K := K) l n c

t: ⌈C₄ * n * log n⌉ if the non-tie witness must epidemic-advance the whole population.
ε: either 0 conditional on already being in the exact tie/non-tie structural Pre, or O(1/n²) if this file absorbs the Phase 3 theorem’s failure.
Engine: unit epidemic / milestone epidemic. This is closest to the Phase 2 template: define an “advanced to Phase 5” informed predicate and use WindowConcentration.windowDrift_PhaseConvergence, or use JansonHitting.MilestonePhase.

This is one of the easiest missing files.

Phase 5 — Reserve agents sample biased Main agents
Paper event structure

This is the first phase where the campaign warning is important. In Phase 5, each Reserve agent samples the exponent of the first biased Main agent it meets. The pseudocode sets sample = ⊥ at initialization; when a Reserve with sample = ⊥ meets a biased Main, it records the Main’s exponent. 
arXiv
 
arXiv

Lemma 7.1: by the end of Phase 5, all Reserve agents have sampled, whp 1 - O(1/n²). The proof uses Theorem 6.2 to ensure a large population of biased Main agents and then applies the one-sided interaction lemma to make every Reserve meet such a Main. 
arXiv

But Phase 6 needs more than “sampled”: it needs concentration of sampled exponent classes. The paper uses Chernoff-style concentration to ensure enough Reserves sampled the right exponent level, e.g. enough R_{−l} or R_{−(l+1)} reserves, depending on which Main exponent class has enough mass. 
arXiv

Lean instance spec

Recommended file: Probability/Phase5Convergence.lean, plus probably Probability/ReserveSampling.lean.

lean
def Phase5Pre (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  RoleCountsGoodConst (L := L) (K := K) n c ∧
  Phase3StructuredNonTiePost (L := L) (K := K) l n c ∧
  (∀ a ∈ c, a.phase.val = 5) ∧
  (∀ a ∈ c, a.role = .reserve → a.sample = Sample.none)

def ReserveSampled (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .reserve → a.sample ≠ Sample.none

def ReserveSampleGood (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  ReserveSampled (L := L) (K := K) c ∧
  -- enough reserves sampled exponent -l or -(l+1), matching the paper case split.

def Phase5Post (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, 6 ≤ a.phase.val) ∧
  ReserveSampleGood (L := L) (K := K) l n c

t: ⌈C₅ * n * log n⌉.
ε: O(1/n²).
Engine: new sampling engine. The “everyone samples” part is a one-sided cancel/epidemic-style lemma; the sample distribution concentration is not covered by Phase2Convergence or ConstantDensityEpidemic as-is. It needs a ReserveSamplingChernoff lemma, because the samples are first-encounter samples from a biased Main population, not just an epidemic count.

Dependency: Phase 5 depends on the Phase 3 non-tie structure and the Lemma 5.2 role counts.

Phase 6 — Reserve fuel splits high-exponent biased agents
Paper event structure

Phase 6 uses Reserve agents as fuel for splitting. A Reserve whose sample matches an appropriate exponent can split a biased Main agent, lowering exponent mass. The goal is to ensure all biased agents have exponent at most −l. 
arXiv

Lemma 7.2: at the end of Phase 6, all biased agents have exponent at most −l, whp 1 - O(1/n²). The proof relies on the sampling concentration from Phase 5 and the existence of enough sampled Reserve agents at the relevant level. 
arXiv

Lemma 7.3 separately controls Main-agent loss: by the end of Phase 6, at least 0.87|M| Main agents remain, very high probability. 
arXiv

Lean instance spec

Recommended file: Probability/Phase6Convergence.lean.

lean
def Phase6Pre (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  RoleCountsGoodConst (L := L) (K := K) n c ∧
  Phase3StructuredNonTiePost (L := L) (K := K) l n c ∧
  ReserveSampleGood (L := L) (K := K) l n c ∧
  ∀ a ∈ c, a.phase.val = 6

def Phase6Post (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, a.role = .main → a.bias ≠ .zero →
    biasExponent a.bias ≥ l) ∧
  mainCount c ≥ 87 * initialMainCount n / 100 ∧
  ∀ a ∈ c, 7 ≤ a.phase.val

t: ⌈C₆ * n * log n⌉.
ε: O(1/n²).
Engine: new gated reserve-splitting drift, most naturally through WindowConcentration.windowDrift_PhaseConvergence once a one-step contraction for the “mass above −l” potential is proved. The generic builder is already present, but the phase-specific drift is not. 

WindowConcentration

 

WindowConcentration

This is one of the harder phases because it depends on Phase 5’s sampling concentration.

Phase 7 — cancel remaining high-level minority mass
Paper event structure

Phase 7 cancels minority agents at exponent levels −l, −(l+1), and −(l+2). The pseudocode explicitly checks the exponent gap and cancels opposite signs when their exponents differ by 0, 1, or 2. 
arXiv
 
arXiv

Lemma 7.4: by the end of Phase 7, at least 0.8|M| Main agents remain.
Lemma 7.5: by the end of Phase 7, all minority agents have exponent below −(l+2), whp 1 - O(1/n²). 
arXiv

The proof applies the one-sided elimination lemma successively to the three exponent classes; the paper gives explicit parallel-time pieces 6.41 + 6.45 + 6.51 < 20 ln n. 
arXiv

Lean instance spec

Recommended file: Probability/Phase7Convergence.lean.

lean
def Phase7Pre (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  Phase6PostCore (L := L) (K := K) l n c ∧
  ∀ a ∈ c, a.phase.val = 7

def NoMinorityAtOrAboveL2 (l : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .main → IsMinority a →
    biasExponent a.bias > l + 2

def Phase7Post (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  NoMinorityAtOrAboveL2 (L := L) (K := K) l c ∧
  mainCount c ≥ 8 * initialMainCount n / 10 ∧
  ∀ a ∈ c, 8 ≤ a.phase.val

t: ⌈C₇ * n * log n⌉, with C₇ corresponding to the three subwindows.
ε: O(1/n²).
Engine: a new OneSidedCancel wrapper over JansonHitting.MilestonePhase is the cleanest. JansonHitting already provides a milestone framework and tail bound, but no phase-specific one-sided cancellation engine is present in the files I inspected. 

JansonHitting

 

JansonHitting

This is relatively easy once the one-sided cancellation engine exists.

Phase 8 — consume the last minority agents
Paper event structure

Phase 8 eliminates the remaining minority agents. The pseudocode says a majority Main agent with full = false can consume an opposite-sign Main agent, making the minority zero and marking the majority as full. 
arXiv

Lemma 7.6: by the end of Phase 8, no minority agents remain, whp 1 - O(1/n²). The proof uses the fact that after Phase 7 at least 0.8|M| majority Main agents remain, and at most 0.2|M| minority agents remain. 
arXiv

Lean instance spec

Recommended file: Probability/Phase8Convergence.lean.

lean
def Phase8Pre (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  Phase7PostCore (L := L) (K := K) l n c ∧
  (∀ a ∈ c, a.phase.val = 8)
  -- plus the Phase8 initialization fact that majority Main agents start with full = false.

def NoMinority (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .main → ¬ IsMinority a

def Phase8Post (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  NoMinority (L := L) (K := K) c ∧
  ∀ a ∈ c, 9 ≤ a.phase.val

t: ⌈C₈ * n * log n⌉.
ε: O(1/n²).
Engine: one-sided cancellation/consumption, again best factored as a reusable OneSidedCancel engine based on JansonHitting.

Potential missing deterministic lemma: the repository needs a local Phase8Transition_consume_minority lemma analogous to the Phase 0 local progress lemmas, unless it already exists later in PhaseProgress.lean.

Phase 10 — slow stable backup
Paper event structure

Phase 10 is the slow backup exact-majority protocol. It cancels opposite outputs while active; inactive agents adopt active output; and if all active opinions agree, the output stabilizes. The paper describes it as a slow Θ(n log n) backup entered only with probability O(1/n²), so it does not hurt expected time. 
arXiv
 The pseudocode is in Phase 10. 
arXiv

Lemma 7.7: Phase 10 stabilizes in O(n log n) time in expectation and with high probability. The proof first cancels one sign, then uses coupon-collector epidemics to spread the final output. 
arXiv
 
arXiv

Lean status

Invariants.lean already has deterministic stability facts:

lean
phase10_unanimous_output_preserved_by_step
phase10_unanimous_output_preserved_by_reachable
phase10_unanimous_output_isStable

So once unanimity is reached, stability is already formalized. 

ClimbTail

 

ClimbTail

What is missing is the probabilistic convergence to unanimity.

Lean instance spec

Recommended file: Probability/Phase10Convergence.lean.

lean
def Phase10Pre (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  ∀ a ∈ c, a.phase.val = 10

def Phase10Post (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∃ o : Output, ∀ a ∈ c, a.phase.val = 10 ∧ a.output = o

t: if paper time is parallel time, use ⌈C₁₀ * n^2 * log n⌉ interactions.
ε: e.g. O(1/n²) for the high-probability backup instance.
Engine: new slow exact-majority backup engine: cancellation plus coupon-collector epidemic. Deterministic absorption can reuse phase10_unanimous_output_isStable. 

ClimbTail

2. Reserve-agent sampling mechanism for Phases 5–8

The correct §7.1 structure is:

After Phase 3, in the non-tie case, the Main agents have a structured majority around exponents −l, −(l+1), −(l+2), with tiny minority mass. This is Theorem 6.2. 
arXiv

Phase 5: each Reserve samples the exponent of the first biased Main agent it meets. Lemma 7.1 only guarantees that every Reserve gets some sample by the end of Phase 5. 
arXiv

Sampling concentration: Phase 6 needs enough Reserve agents with useful sampled exponents. The paper proves, using Chernoff bounds, that the sampled Reserve populations at the needed levels are large enough, e.g. enough reserves sampled −l or −(l+1) depending on the Main distribution. 
arXiv

Phase 6: those sampled Reserves are consumed as split fuel to lower high-exponent biased agents until all biased exponents are at most −l. Lemma 7.2 is the main statement; Lemma 7.3 controls Main-agent loss. 
arXiv
 
arXiv

Phase 7: cancellation removes minority mass at the top three levels. Lemmas 7.4 and 7.5. 
arXiv

Phase 8: final consumption removes all remaining minority agents. Lemma 7.6. 
arXiv

Existing engines cover only pieces: WindowConcentration gives the generic drift-to-PhaseConvergence builder, and JansonHitting gives a milestone hitting-time wrapper. Neither directly gives the first-encounter sampling concentration needed for Phase 5. 

WindowConcentration

 

JansonHitting

3. Clock-count Θ(n) role-split concentration: explicit Phase C deliverable

The needed statement should be separated from Phase 0 as a reusable lemma, because the clock constants feed every timed phase.

Paper Lemma 5.2 gives exactly the required shape: by the end of Phase 0, RoleMCR = 0, |Main| = n/2 ± εn, and both |Clock| and |Reserve| are at least (1−ε)n/4, with failure O(1/n²). It also records deterministic fallback bounds once RoleMCR = 0. 
arXiv

Lean target:

lean
def RoleSplitGood (η : ℝ) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  roleMCRCount (L := L) (K := K) c = 0 ∧
  ((1 - η) * (n : ℝ) / 2 ≤ (mainCount c : ℝ)) ∧
  ((mainCount c : ℝ) ≤ (1 + η) * (n : ℝ) / 2) ∧
  ((1 - η) * (n : ℝ) / 4 ≤ (clockCount c : ℝ)) ∧
  ((1 - η) * (n : ℝ) / 4 ≤ (reserveCount c : ℝ))

theorem phase0_roleSplit_whp
    (n : ℕ) (hn : N0 ≤ n)
    (η : ℝ) (hη : 0 < η) (c₀ : Config (AgentState L K))
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (tRole : ℕ)
    (εRole : ℝ≥0)
    (hbudget : roleSplitTail n η tRole ≤ (εRole : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ tRole) c₀
      {c | ¬ RoleSplitGood (L := L) (K := K) η n c}
      ≤ (εRole : ℝ≥0∞)

For timed counters, the downstream corollary should expose a constant lower bound:

lean
theorem clockCount_linear_of_RoleSplitGood
    (η : ℝ) (hη : η ≤ 1/25)
    (hgood : RoleSplitGood (L := L) (K := K) η n c) :
    (n : ℝ) / 5 ≤ (clockCount (L := L) (K := K) c : ℝ)

The paper proof technique is a role-splitting process plus Chernoff concentration. The repo currently has local role-transition facts and a partial MCR milestone process, but not the full count-concentration lemma. 

EarlyDripMarked

 

Phase0Convergence

4. Recommended implementation order
Foundational, do first

Probability/RoleSplitConcentration.lean
Prove Lemma 5.2-style RoleSplitGood and especially clockCount = Θ(n). This feeds all counter-timed phases.

Probability/CounterTimeout.lean
Generic timed-phase wrapper: if at least c n clocks exist and every clock-clock interaction decrements positive counters, then all phase counters finish in C n log n interactions whp. Local deterministic facts are already in PhaseProgress.lean. 

EarlyDripMarked

Upgrade Phase 0
Use role split + counter timeout to produce the real PhaseConvergence.

Parallelizable after that

Phase4Convergence.lean
Mostly deterministic + epidemic. Independent of Reserve sampling.

Phase10Convergence.lean
Backup convergence. Uses deterministic stability already in Invariants.lean; probability engine is separate. 

ClimbTail

Phase1Convergence.lean
Depends on clock-count/counter timeout; probability engine for bias averaging is new.

Reserve block

ReserveSampling.lean / Phase5Convergence.lean
Needed before Phase 6.

Phase6Convergence.lean
Hardest Reserve phase; depends on Phase 5 sampling.

OneSidedCancel.lean, then Phase7Convergence.lean and Phase8Convergence.lean
Phase 7 and 8 can be developed against abstract Pre hypotheses from Phase 6/7, so they are parallelizable once the generic cancellation engine exists.

5. Three easiest worker-start sketches
A. Phase 4
lean
namespace ExactMajority.Phase4Convergence

def HasPhase4Witness (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, a.phase.val = 4 ∧ a.role = .main ∧
    2 ^ L < biasMagnitudeNumerator a.bias -- placeholder for |bias| > 2^-L

def Phase4Pre (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  (∀ a ∈ c, a.phase.val = 4) ∧
  (TieAllMinExp (L := L) (K := K) c ∨
   Phase3StructuredNonTiePost (L := L) (K := K) l n c)

def Phase4Post (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  StableTieOutput (L := L) (K := K) c ∨
  Phase5Pre (L := L) (K := K) l n c

noncomputable def phase4Convergence
    (l n : ℕ) (hn : 2 ≤ n)
    (t : ℕ) (ε : ℝ≥0)
    -- arithmetic/geometric tail for epidemic from one witness
    (hε : phase4WitnessTail n t ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  -- Use WindowConcentration.windowDrift_PhaseConvergence
  -- or a small MilestonePhase epidemic on `phase ≥ 5`.

end ExactMajority.Phase4Convergence

Why easy: no Reserve sampling and no new quantitative population split; probability is just epidemic-style spread from a witness, while the tie branch is deterministic once Phase 3 gives the structural input.

B. Phase 7
lean
namespace ExactMajority.Phase7Convergence

def Phase7Pre (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  Phase6PostCore (L := L) (K := K) l n c ∧
  ∀ a ∈ c, a.phase.val = 7

def Phase7Post (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  NoMinorityAtOrAboveL2 (L := L) (K := K) l c ∧
  mainCount (L := L) (K := K) c ≥ 8 * initialMainCount n / 10 ∧
  ∀ a ∈ c, 8 ≤ a.phase.val

noncomputable def phase7Convergence
    (l n : ℕ) (hn : 2 ≤ n)
    (t : ℕ) (ε : ℝ≥0)
    (hε : phase7CancelTail l n t ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  -- Instantiate a reusable OneSidedCancel engine three times:
  -- levels -l, -(l+1), -(l+2).
  -- Then compose the three subphases and the counter-timeout wrapper.

end ExactMajority.Phase7Convergence

Why easy after OneSidedCancel: the paper proof is explicitly three successive one-sided elimination windows. 
arXiv

C. Phase 8
lean
namespace ExactMajority.Phase8Convergence

def Phase8Pre (l n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
  Phase7PostCore (L := L) (K := K) l n c ∧
  ∀ a ∈ c, a.phase.val = 8

def Phase8Post (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  NoMinority (L := L) (K := K) c ∧
  ∀ a ∈ c, 9 ≤ a.phase.val

noncomputable def phase8Convergence
    (l n : ℕ) (hn : 2 ≤ n)
    (t : ℕ) (ε : ℝ≥0)
    (hε : phase8ConsumeTail l n t ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  -- One-sided consumption/cancellation:
  -- majority pool ≥ 0.8|M|, minority pool ≤ 0.2|M|.
  -- Use OneSidedCancel / JansonHitting, plus local Phase8 transition lemma.

end ExactMajority.Phase8Convergence

Why easy after OneSidedCancel: it is a single remaining-minority elimination window, not a sampling or split-fuel process.

Final dependency summary

Already usable: Phase2Convergence template; WindowConcentration.windowDrift_PhaseConvergence; JansonHitting.MilestonePhase; deterministic counter/role local lemmas; deterministic Phase 10 stability.

Missing but generic: CounterTimeout, OneSidedCancel.

Missing and phase-specific: RoleSplitConcentration for Lemma 5.2; ReserveSamplingChernoff for Phase 5; Phase6ReserveSplit drift.

Hardest: Phase 6.

Most parallelizable: Phase 4, Phase 10, and the generic OneSidedCancel work feeding Phases 7–8.
