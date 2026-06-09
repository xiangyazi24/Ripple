# Doty time-half — discharge `hmono_mix`: rBeyond(T+1) non-decreasing on the real kernel (deterministic)

Directive: 挨个做，绝对不退缩，不 over-claim. Avenue (a)/(d) carry `hmono_mix` as a structural hypothesis:
`∀ c c', Q_mix n mC T c → c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → rBeyond (T+1) c ≤
rBeyond (T+1) c'`. It is DETERMINISTIC and TRUE — discharge it from existing lemmas (no probability).

## Why it's true (the proof sketch — verify against the lemmas)
`rBeyond (T+1) c = Multiset.countP (fun a => a.role = .clock ∧ T+1 ≤ a.minute.val) c`. A one-step transition
replaces the interacting ORDERED pair (s,t) by their post-states, leaves all other agents fixed. To show the
count of (clock ∧ minute ≥ T+1) does not drop:
- **Clock role is permanent:** `Transition_preserves_clock_role_left/right` (DeterministicChain.lean) — a clock
  stays a clock through any Transition.
- **A clock's minute never decreases (no phase-3 re-entry):** `phaseInit` resets minute ONLY at phase-3 entry
  (`phaseInit_minute_eq_of_ne_three`, ClockRealKernel.lean); phase only increases (`advancePhase_phase_nondec`),
  so a clock already at phase ≥ 3 (Q_mix gives phase = 3) never RE-enters phase 3 ⟹ no minute reset; the
  clock-clock / clock-other minute steps are non-decreasing (`Transition_clock_pair`, the drip/sync lemmas).
- **Q_mix (all clock-role agents at phase 3) rules out the one reset path:** the only minute reset is a phase-2→3
  epidemic entry; since every CLOCK is already at phase 3 (Q_mix), the agent entering phase 3 is a non-clock
  (doesn't affect the clock count). So no counted clock loses its membership.
Hence every agent counted in `rBeyond (T+1) c` is still counted in `c'` ⟹ `rBeyond (T+1) c ≤ rBeyond (T+1) c'`.

## Task
Add to a NEW file `Probability/ClockMonoDischarge.lean` (imports ClockRealKernel + ClockRealMixed) the theorem
`hmono_mix_discharged (n mC T : ℕ) : ∀ c c', Q_mix n mC T c → c' ∈ ((NonuniformMajority L K).stepDistOrSelf
c).support → rBeyond (T+1) c ≤ rBeyond (T+1) c'`, proven from the existing lemmas above (NOT carried, NOT
assumed). Strategy: `stepDistOrSelf` support is `{c}` (size < 2) ∪ `{stepOrSelf c s t : applicable pairs}`; on
the self/no-op case it's `≤ rfl`; on the `stepOrSelf c s t` case, `rBeyond` over `c.erase s |>.erase t + {s',t'}`
— show countP doesn't drop by: the two removed agents s,t, if counted (clock ∧ ≥T+1), have post-states s',t'
still counted (role permanent + minute non-decreasing). Use `Multiset.countP_le_of...` / explicit
add/erase countP arithmetic. Look at how `rBeyondGE3_ge_monotone` / `rBeyond_stepOrSelf_ge` (ClockRealKernel.lean)
prove the all-clocks version — MIRROR that, but use clock-role permanence + minute-nondecrease instead of the
AllClockGE3 assumption (that is the only thing that changes).

## HARD RULES
NEW file ClockMonoDischarge.lean only; do NOT edit existing files, do NOT weaken proven lemmas. No
sorry/admit/new axiom/native_decide. The result MUST be genuinely proven (it discharges a carried hyp — the
whole point). Iterate `lake build Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockMonoDischarge`
until clean. If a per-pair role/minute lemma is missing for the mixed (non-clock-involving) pairs, build it from
the transition. Do NOT git. Final message: the `hmono_mix_discharged` statement verbatim, build verdict,
`#print axioms` (must be [propext, Classical.choice, Quot.sound]), and HONEST status: fully discharged from
existing lemmas, or the exact missing per-pair fact. Do not over-claim.
