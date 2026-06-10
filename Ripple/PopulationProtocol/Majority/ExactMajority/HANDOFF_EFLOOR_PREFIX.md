# HANDOFF: εfloor MGF — post-gated floor prefix (family2 letter, task 6d41629e, 2026-06-10)

Source: ChatGPT Pro (family2, Ripple connector). Delivered 20,926 B via bridge after MBP reload. Verbatim answer below.

---

The file already has the exact floor-consuming rate: phase0_mcrCount_decrease_prob_floor packages the combined MCR×MCR plus MCR×assignable mass into mcrCount * a₀ /(n(n−1)), and MilestonePhaseOn is present to carry a side invariant/floor through Janson. The remaining problem is exactly proving the floor side predicate with a prefix-sum bound, not rebuilding the Stage-1 milestone machinery.

Verdict: do not try to prove

∑ τ<t, (K^τ) c₀ {c | assignableCount c < a₀} ≤ n⁻²


from the all-MCR start. That statement is false as written: at τ = 0, pool = 0, so the sum already contains mass 1; and after Stage 1 has already succeeded, Rule 4 may later drain the CR side, so an ungated floor event after Post is irrelevant but still charged. The honest target is the warm-up-shifted, post-gated floor residual:

∑ τ ∈ Finset.range t,
  (K ^ (T₀ + τ)) c₀
    {c | assignableCount c < a₀ ∧ ¬ roleSplitGoodMile n hn2 c}
  ≤ εfloor n


or equivalently use a gate

floorOrDoneGate n a₀ hn2 :=
  floorGate n a₀ ∪ {c | roleSplitGoodMile n hn2 c}


so “floor failure after success” is not counted.

This is the one design change I would make to the current _final form. The existing phase0_stage1_whp_final specializes S := floorGate n a₀, so its residual is the full floorGateᶜ prefix, not post-gated; the theorem currently ends with

((t : ℝ≥0∞) * q +
  ∑ τ ∈ Finset.range t, ((NonuniformMajority L K).transitionKernel ^ τ) c₀
    (floorGate n a₀)ᶜ)


which is structurally correct as an upper bound, but too crude for the desired n^{-2} floor residual. 

RoleSplitConcentration

1. Honest region decomposition

The key current code is already right: floorGate is exactly the gate consumed by the floor-to-rate bridge:

def floorGate (n a₀ : ℕ) : Set (Config (AgentState L K)) :=
  {c | Multiset.card c = n ∧ a₀ ≤ assignableCount c ∧
    (∀ a ∈ c, a.role = .mcr → a.phase.val = 0)}


and the bridge is

theorem phase0_mcrCount_decrease_prob_floor ...
  (h_floor : a₀ ≤ assignableCount c) :
  ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | mcrCount c' < mcrCount c}
    ≥ ofReal ((mcrCount c * a₀ : ℕ) / (n * (n - 1) : ℝ))


with floorRate n a₀ M = M * a₀ / (n * (n - 1)). 

RoleSplitConcentration

 

RoleSplitConcentration

 

RoleSplitConcentration

For the floor residual itself, split the process into these regions.

Region W: warm-up from pool = 0

Use a buffer level, not the final floor:

A₀ := a₀
A₁ := 2 * a₀


On

u = mcrCount c ≥ n / 2
pool = assignableCount c < A₁


R1 births dominate. R1 contributes +2 to pool, and Rule 4 contributes -2, with drain rate bounded by the unassigned-CR count squared, hence by pool^2. So for Φ(c) = exp (-s * pool c),

E[Φ(next) | c] / Φ(c)
≤ 1
  - pBirth(c) * (1 - exp(-2s))
  + pDeath(c) * (exp(2s) - 1)


where

pBirth(c) ≥ u(u-1)/(n(n-1)),
pDeath(c) ≤ crFresh(c)(crFresh(c)-1)/(n(n-1)) ≤ pool(c)^2/(n(n-1)).


On u ≥ n/2, pool ≤ 2a₀, and a₀ = n/10, one has roughly

pBirth ≥ 1/4,
pDeath ≤ 1/25,


so choose a fixed small s > 0 and get a contraction

∫⁻ c', expNegPool s c' ∂K c ≤ rWarm * expNegPool s c


with rWarm < 1.

This is the correct place to use WindowConcentration.windowDrift_tail: it is exactly the abstract “potential contracts on a window, so the multi-step tail is small” builder. Its hypothesis shape is

(hdrift : ∀ c, Q c →
  ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)


and the conclusion bounds the bad mass by r^t * Φ(c₀) / θ. 

WindowConcentration

Region M: main floor-maintenance while u ≥ uMin

Once pool ≥ 2a₀, the event you need to suppress is a drop back below a₀ before either Stage 1 succeeds or the low-u checkpoint is reached. Use the deficit potential

Φfloor c := ENNReal.ofReal (Real.exp (s * ((2*a₀ : ℝ) - assignableCount c)))


or equivalently exp(-s * pool) with threshold conversion. The drift is favorable only in the band

a₀ ≤ pool c ≤ 2*a₀
uMin ≤ mcrCount c


because the crude death bound is ≤ (2a₀)^2 / n^2, while R1 births are ≥ uMin^2 / n^2. Thus choose, for example,

uMin := 3 * a₀        -- or 4*a₀ for easier constants


so

uMin² > (2a₀)²


with slack for the exp(±2s) factors.

The supermartingale is again

E[exp(-s pool(next)) | c] ≤ rMid * exp(-s pool(c))


on the gated band. The gate should not be “all time”; it should be stopped at

roleSplitGoodMile n hn2 c ∨ mcrCount c < uMin ∨ assignableCount c < a₀


so the theorem proves “floor does not fail before the low-u checkpoint or success.”

Region L: low u < uMin

Do not try to prove the same exp(-s * pool) drift from R1 births here. It is genuinely false: R1 birth rate is now too small. Resolve the apparent circularity by making the residual post-gated and either:

add a low-u checkpoint theorem, started from the buffered event, proving completion before floor failure; or

use a stronger checkpoint predicate that includes a durable fresh-main/reservoir condition.

The minimal version I would formalize first is the checkpoint theorem:

def LowStartGood (n a₀ uMin : ℕ) (c : Config (AgentState L K)) : Prop :=
  cardPhaseShell n c ∧
  mcrCount c ≤ uMin ∧
  2 * a₀ ≤ assignableCount c


and prove a separate bound

((K ^ tLate) c) {c' | assignableCount c' < a₀ ∧ ¬ roleSplitGoodMile n hn2 c'}
  ≤ εlate n


from LowStartGood. This is the only genuinely new probabilistic piece beyond the warm-up/floor-maintenance MGF.

2. Warm-up theorem shape

The current phase0_stage1_whp_final cannot be started directly from Phase0Initial with linear a₀, because it requires

(hc₀ : c₀ ∈ floorGate n a₀)


but Phase0Initial has pool = 0. 

RoleSplitConcentration

So add a checkpoint theorem, not a direct replacement:

def Phase0WarmGood (n a₀ uMin : ℕ) (c : Config (AgentState L K)) : Prop :=
  cardPhaseShell (L := L) (K := K) n c ∧
  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  2 * a₀ ≤ assignableCount (L := L) (K := K) c

theorem phase0_floor_warmup_whp
    (n a₀ uMin T₀ : ℕ) (εwarm : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    -- arithmetic constants, e.g. a₀ = n/10, uMin = 3*a₀, T₀ = C*n:
    (hwarm_arith : WarmupArithmetic n a₀ uMin T₀ εwarm)
    -- one-step MGF drift on the warm band:
    (hwarm_drift : WarmupPoolDrift (L := L) (K := K) n a₀ uMin) :
    ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
      {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
      ≤ εwarm


The proof should instantiate WindowConcentration.windowDrift_tail with

Φ c = ENNReal.ofReal (Real.exp (-s * (assignableCount c : ℝ)))
Q c = cardPhaseShell n c ∧ uMin ≤ mcrCount c ∧ assignableCount c < 2*a₀
Post c = 2*a₀ ≤ assignableCount c
θ = ENNReal.ofReal (Real.exp (-s * (2*a₀ : ℝ)))


Use windowDrift_tail, not killK_now, for warm-up, because warm-up is a direct “hit a floor before leaving a window” MGF estimate. killK_now is better for the milestone engine, where alive successors must automatically satisfy the gate; the file already uses that idea via alive_support_gate. 

GatedKillNow

3. Per-region drift lemma statement

Make the drift lemma kernel-local and rate-parametric first, then instantiate with protocol rule lemmas. This keeps the analytic inequality independent of transition bookkeeping.

noncomputable def poolExpNeg (s : ℝ) :
    Config (AgentState L K) → ℝ≥0∞ :=
  fun c => ENNReal.ofReal
    (Real.exp (-s * (assignableCount (L := L) (K := K) c : ℝ)))

structure PoolDriftRegion (n a₀ uMin Ahi : ℕ)
    (c : Config (AgentState L K)) : Prop where
  shell : cardPhaseShell (L := L) (K := K) n c
  u_ge : uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c
  pool_le : assignableCount (L := L) (K := K) c ≤ Ahi

theorem pool_expNeg_one_step_drift
    (n a₀ uMin Ahi : ℕ) (s : ℝ) (r : ℝ≥0∞)
    (hs : 0 < s)
    -- protocol-rate facts:
    (hbirth : ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
      birthR1Mass (L := L) (K := K) c ≥
        ENNReal.ofReal (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)))
    (hdeath : ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
      r4FreshCRDrainMass (L := L) (K := K) c ≤
        ENNReal.ofReal (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)))
    -- scalar inequality saying births dominate deaths after exponential tilting:
    (hfav :
      ScalarPoolFav s n uMin Ahi r) :
    ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ r * poolExpNeg (L := L) (K := K) s c


The scalar condition should be exactly the inequality

1 - b*(1-exp(-2s)) + d*(exp(2s)-1) ≤ r


where

b = uMin*(uMin-1)/(n*(n-1)),
d = Ahi*Ahi/(n*(n-1)).


For Ahi = 2*a₀, uMin = 3*a₀ or 4*a₀, small fixed s, this gives r < 1.

4. Assembled floor-prefix theorem

I would add the assembled theorem in a post-gated form and then separately use it to refine phase0_stage1_whp_final.

def floorFailsBeforePost (n a₀ : ℕ) (hn2 : 2 ≤ n)
    (c : Config (AgentState L K)) : Prop :=
  assignableCount (L := L) (K := K) c < a₀ ∧
  ¬ roleSplitGoodMile (L := L) (K := K) n hn2 c

theorem floor_prefix_le
    (n a₀ uMin T₀ t : ℕ) (hn2 : 2 ≤ n)
    (εwarm εmid εlate : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    -- warm-up reaches buffer:
    (hwarm :
      ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
        {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
        ≤ εwarm)
    -- from warm-good states, floor failure before low-u/post is small:
    (hmid :
      ∀ c, Phase0WarmGood (L := L) (K := K) n a₀ uMin c →
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | assignableCount (L := L) (K := K) c' < a₀ ∧
                  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c' ∧
                  ¬ roleSplitGoodMile (L := L) (K := K) n hn2 c'}
        ≤ εmid)
    -- low-u checkpoint completion before floor failure:
    (hlate :
      ∀ c, LowStartGood (L := L) (K := K) n a₀ uMin c →
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c'}
        ≤ εlate) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}
      ≤ εwarm + εmid + εlate


Then define

def εfloor (n : ℕ) : ℝ≥0∞ :=
  εwarm n + εmid n + εlate n


and set the intended final target as

theorem floor_prefix_le_inv_sq
    ... :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}
      ≤ ENNReal.ofReal (((n : ℝ)^2)⁻¹)


after choosing constants so each piece is, say, ≤ 1/(3 n²).

5. How it plugs into existing code

The existing structural chain is already good:

roleSplitKernelMilestone builds the killed-kernel milestone witness with rate floorRate n a₀ (n - i.val). 

RoleSplitConcentration

roleSplitKernelMilestone_pMin_meanTime proves the Janson potential becomes harmonic-sum/logarithmic and independent of a₀, i.e. the floor cancels in pMin * meanTime. 

RoleSplitConcentration

real_bad_le_janson_add_escape is the abstract assembly: real bad mass ≤ Janson tail + escape prefix. 

RoleSplitConcentration

kill_escape_le_prefix_union is the exact generic prefix-union escape lemma. 

GatedEscape

phase0_stage1_whp instantiates the witness and exposes only q plus the prefix residual. 

RoleSplitConcentration

So the minimal edit is not to rebuild Janson or killed kernels. Add only:

def floorOrDoneGate (n a₀ : ℕ) (hn2 : 2 ≤ n) :
    Set (Config (AgentState L K)) :=
  floorGate (L := L) (K := K) n a₀ ∪
    {c | roleSplitGoodMile (L := L) (K := K) n hn2 c}


then a variant of _final whose prefix term is

∑ τ ∈ Finset.range t,
  (K^τ) c₀ {c | assignableCount c < a₀ ∧ ¬ roleSplitGoodMile n hn2 c}


rather than full floorGateᶜ.

That is the honest endpoint: Janson tail + warm-up failure + post-gated floor-prefix failure. The current branch already has the first term and the floor-to-rate bridge; the last remaining Lean work is exactly the MGF proof that the post-gated floor prefix is small.

The clean answer is: do not try to make floorGate n a₀ true from time 0. From the all-MCR start, assignableCount = 0, so an unshifted

∑ τ ∈ Finset.range t, (K ^ τ) c₀ {c | assignableCount c < a₀}


is already at least 1. The correct final residual must either start after a warm-up checkpoint T₀ = Θ(n), or use a regime-dependent floor, for example floor 0 before T₀ and floor a₀ after T₀.

The branch already has the right structural endpoint: phase0_stage1_whp_final bounds Stage-1 bad mass by Janson plus

((t : ℝ≥0∞) * q +
  ∑ τ ∈ Finset.range t, ((NonuniformMajority L K).transitionKernel ^ τ) c₀
    (floorGate (L := L) (K := K) n a₀)ᶜ)


where floorGate is the card/phase shell plus a₀ ≤ assignableCount. 

RoleSplitConcentration

 The new work should only replace that prefix term by a warm-up-shifted floor-prefix theorem.

1. Region decomposition

Let

pool c := assignableCount (L := L) (K := K) c
u c    := ExactMajority.mcrCount (L := L) (K := K) c


Use constants such as

a₀    := n / 10
Ahi   := 2 * a₀
uMin  := 3 * a₀     -- or 4*a₀ if you want easier scalar inequalities
T₀    := C₀ * n


The drift of exp(-s * pool) is favorable only in a band where u is still linear. The one-step scalar inequality is:

E[exp(-s pool')] / exp(-s pool)
≤ 1
  - pBirth * (1 - exp(-2s))
  + pDeath * (exp(2s) - 1).


Here

pBirth ≥ u(u-1)/(n(n-1)),
pDeath ≤ freshCR(freshCR-1)/(n(n-1)) ≤ pool²/(n(n-1)).


So on

pool ≤ Ahi,    u ≥ uMin,


you get favorable drift whenever roughly

uMin² > Ahi².


With Ahi = 2a₀ and uMin = 3a₀, births dominate deaths by a fixed constant factor.

The branch’s existing floor-to-rate bridge is exactly the consumer of this floor:

theorem phase0_mcrCount_decrease_prob_floor
    (c : Config (AgentState L K)) (n a₀ : ℕ)
    ...
    (h_floor : a₀ ≤ assignableCount (L := L) (K := K) c) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
          ExactMajority.mcrCount (L := L) (K := K) c} ≥
      ENNReal.ofReal
        (((ExactMajority.mcrCount (L := L) (K := K) c * a₀ : ℕ) : ℝ) /
          (n * (n - 1) : ℝ))


and the rate is already named:

noncomputable def floorRate (n a₀ M : ℕ) : ℝ :=
  ((M * a₀ : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))


RoleSplitConcentration

So the right split is:

WARM-UP:
  u ≥ n/2, pool < 2a₀.
  Show pool reaches 2a₀ by T₀ = Θ(n) whp.

MAINTENANCE:
  u ≥ uMin, pool ∈ [a₀, 2a₀].
  Show pool does not fall below a₀ before either success or low-u.

LATE:
  u < uMin.
  Do not use exp(-s pool) birth drift here. Instead stop the floor analysis at low-u
  and charge the remaining time to the milestone/Janson completion tail, or use a
  joint “floor-or-done” gate.


The late regime is where a naive proof becomes circular. If u < uMin, R1 births are no longer strong enough. The fix is to stop the floor martingale at

roleSplitGoodMile n hn2 c ∨ u c < uMin ∨ pool c < a₀


and then handle the low-u window by the same milestone progress/Janson tail, not by pool drift.

2. Warm-up shape

From pool = 0, use a checkpoint theorem:

def Phase0WarmGood (n a₀ uMin : ℕ) (c : Config (AgentState L K)) : Prop :=
  cardPhaseShell (L := L) (K := K) n c ∧
  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  2 * a₀ ≤ assignableCount (L := L) (K := K) c


Target:

theorem phase0_floor_warmup_whp
    (n a₀ uMin T₀ : ℕ) (εwarm : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hwarm_drift : WarmupPoolDrift (L := L) (K := K) n a₀ uMin T₀ εwarm) :
    ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
      {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
      ≤ εwarm


This should plug into WindowConcentration.windowDrift_tail, not into killK_now. The WindowConcentration builder already has exactly the needed form: given a measurable potential Φ, an absorbing/window predicate Q, and a drift

∀ c, Q c →
  ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c


it gives a kernel-level tail

(P.transitionKernel ^ t) c₀ {c | ¬ Post c} ≤ r ^ t * Φ c₀ / θ


WindowConcentration

For warm-up, use

Φ c := ENNReal.ofReal
  (Real.exp (-s * (assignableCount (L := L) (K := K) c : ℝ)))

Post c := 2 * a₀ ≤ assignableCount (L := L) (K := K) c
Q c :=
  cardPhaseShell (L := L) (K := K) n c ∧
  n / 2 ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  assignableCount (L := L) (K := K) c < 2 * a₀


Then ¬ Post implies Φ ≥ exp(-s * (2a₀)), so Markov’s inequality gives the warm-up tail.

3. Per-region drift lemma

Minimize new machinery by proving a single abstract one-step pool drift lemma whose hypotheses are protocol-rate facts.

noncomputable def poolExpNeg (s : ℝ) :
    Config (AgentState L K) → ℝ≥0∞ :=
  fun c =>
    ENNReal.ofReal
      (Real.exp (-s * (assignableCount (L := L) (K := K) c : ℝ)))

def PoolDriftRegion (n a₀ uMin Ahi : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  cardPhaseShell (L := L) (K := K) n c ∧
  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  assignableCount (L := L) (K := K) c ≤ Ahi


Then:

theorem pool_expNeg_one_step_drift
    (n a₀ uMin Ahi : ℕ) (s : ℝ) (r : ℝ≥0∞)
    (hs : 0 < s)
    (hbirth :
      ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
        birthR1Mass (L := L) (K := K) c ≥
          ENNReal.ofReal
            (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)))
    (hdeath :
      ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
        r4FreshCRDrainMass (L := L) (K := K) c ≤
          ENNReal.ofReal
            (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)))
    (hfav :
      ScalarPoolFav s n uMin Ahi r) :
    ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ r * poolExpNeg (L := L) (K := K) s c


ScalarPoolFav should just expand to the real inequality

def ScalarPoolFav (s : ℝ) (n uMin Ahi : ℕ) (r : ℝ≥0∞) : Prop :=
  ENNReal.ofReal
    (1
      - (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (1 - Real.exp (-2*s))
      + (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (Real.exp (2*s) - 1))
    ≤ r


This is intentionally rate-parametric. The protocol-specific lemmas birthR1Mass and r4FreshCRDrainMass are the only new count-mass facts.

4. Assembled floor prefix

Use a shifted theorem. This is the honest target:

def floorBadAfterWarmup (n a₀ : ℕ) :
    Set (Config (AgentState L K)) :=
  {c | assignableCount (L := L) (K := K) c < a₀}

theorem floor_prefix_le
    (n a₀ uMin T₀ t : ℕ)
    (εwarm εmid εlate : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hwarm :
      ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
        {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
        ≤ εwarm)
    (hmid :
      ∀ c, Phase0WarmGood (L := L) (K := K) n a₀ uMin c →
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | assignableCount (L := L) (K := K) c' < a₀ ∧
                  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c'}
        ≤ εmid)
    (hlate :
      ∀ c, Phase0WarmGood (L := L) (K := K) n a₀ uMin c →
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | assignableCount (L := L) (K := K) c' < a₀ ∧
                  ExactMajority.mcrCount (L := L) (K := K) c' < uMin}
        ≤ εlate) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | assignableCount (L := L) (K := K) c < a₀}
      ≤ εwarm + εmid + εlate


Then expose the paper-scale version:

def εfloor (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹)

theorem floor_prefix_le_inv_sq
    ... :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | assignableCount (L := L) (K := K) c < a₀}
      ≤ εfloor n


For plugging into the branch, the cleanest path is:

phase0_floor_warmup_whp: use WindowConcentration.windowDrift_tail.

pool_expNeg_one_step_drift: feeds that same window-drift engine for the mid regime.

floor_prefix_le: pure union/checkpoint composition.

Refine phase0_stage1_whp_final by replacing its raw prefix with the shifted floor_prefix_le.

Do not add a new Janson engine. The branch already has roleSplitKernelMilestone, KernelMilestone, killK_now, and real_bad_le_janson_add_escape. The existing witness already proves that the floor-driven Janson potential is logarithmic:

theorem roleSplitKernelMilestone_pMin_meanTime ... :
  (roleSplitKernelMilestone ...).pMin *
    (roleSplitKernelMilestone ...).meanTime =
    ∑ i : Fin (n - 1), (2 : ℝ) / ((n : ℝ) - (i.val : ℝ))


RoleSplitConcentration

So the residual really is only the warm-up-shifted floor prefix. The rest of the branch is already structurally ready.
