import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
namespace ExactMajority
variable {L K : ℕ}
open ExactMajority

/-- `stdCounterSubroutine` advances phase only when `counter = 0`. -/
private lemma stdCounter_phase_pos_imp_counter_zero (a : AgentState L K)
    (h : a.phase.val < (stdCounterSubroutine L K a).phase.val) : a.counter.val = 0 := by
  unfold stdCounterSubroutine at h
  split at h
  · assumption
  · simp at h

-- LEFT exit lemma
theorem Phase0Transition_left_phase_pos_imp_src_clock_zero
    (s t : AgentState L K) (hs0 : s.phase.val = 0)
    (hexit : 0 < (Phase0Transition L K s t).1.phase.val) :
    s.role = .clock ∧ s.counter.val = 0 := by
  -- mirror the cascade
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  -- The output .1 is s5
  change 0 < s5.phase.val at hexit
  -- counter tracing: s1,s2,s3 leave counter = s.counter (rules 1-3 don't touch counter)
  have hc1 : s1.counter = s.counter := by dsimp [s1]; split_ifs <;> rfl
  have hc2 : s2.counter = s1.counter := by dsimp [s2]; split_ifs <;> rfl
  have hc3 : s3.counter = s2.counter := by dsimp [s3]; split_ifs <;> rfl
  -- phase tracing: s1..s4 leave phase = s.phase = 0
  have hp1 : s1.phase.val = 0 := by dsimp [s1]; split_ifs <;> simpa [hs0]
  have hp2 : s2.phase.val = 0 := by dsimp [s2]; split_ifs <;> simp [hp1] <;> simpa [hp1] using hp1
  sorry

end ExactMajority
