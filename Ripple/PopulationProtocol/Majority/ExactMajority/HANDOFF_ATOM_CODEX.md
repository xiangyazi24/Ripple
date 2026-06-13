# HANDOFF — atom campaign codex parallelization (2026-06-11 night, Claude usage low)

## State at handoff
Public main = 1347f49 + tag doty-thm31-v51-2026-06-11 (released, double-build verified).
opus-wip = a411125: six codex packages landed (PkgA-FAtoms.lean), all single-file
`lake env lean` EXIT 0, 0-sorry, banned-token-clean, sampled axiom audit ⊆ 3 axioms.

## The six packages (each PRODUCES WorkInputsV51 fields; honest remainders carried)
- PkgAAtoms: hext1H / hpull1H (P1=(n-g+3)/4) / hpt1.  Remainder: +3 witness, entry gap g.
- PkgBAtoms: hwit7 / hwit8 / hpt7 / hpt8.
- PkgCAtoms: hmain5_of_pointwise_confinement (exact, needs pointwise success at b),
  hmain5_bad_event_whp_from_phase3_hours (whp route), mainConfinementProfile_feeder_of_paper.
  HONEST GAP: whp kernel event does NOT yield pointwise hmain5 alone.
- PkgDAtoms: hescε1/6/7/8, hClosed5 carried, hdrop6/q6/hpt6.
- PkgEAtoms: hConc / εConc.
- PkgFAtoms: work0/2/3/9, hPhase10Sign_of_rooted, hNoOvershoot counter-reset + non-reset guards.

## IN FLIGHT at handoff (uisai2 — survive independently, collect when usage returns)
1. opus subagent: FinalAssemblyV6.lean — consumes the six producers into the V51
   bundle (shrink DotyResidualAtomsV6). Iron rule: consumption table mandatory.
   Will commit to workspace origin main + sync mirror itself.
2. codex (uisai2 ~/repos/Ripple-atoms): adversarial audit of the six packages,
   report → /tmp/pkgaudit_report.md. Verdict per file CLEAN/CONDITIONAL/DEFECT.

## Resume steps when Claude usage returns
1. Read /tmp/pkgaudit_report.md (the package audit) — fix any DEFECT findings.
2. Check FinalAssemblyV6 landed (git log opus-wip); if so, independent codex
   consumption-sweep audit on V6 (the recurring assembly-shortcut trap), then
   fresh-checkout double build (bare + explicit V6 target) → tag v6.
3. Remaining true-open atoms after V6 = the named paper-probability facts
   (Lemma 5.3/7.1/7.4/7.6 cores, the pointwise-hmain5 gap, hClosed5). These are
   the genuine math, the next campaign.

## Infra notes
- Shared codex checkout: uisai2 ~/repos/Ripple-atoms (opus-wip, full oleans
  prebuilt). codex at ~/.local/bin/codex (login-shell PATH). NO push creds on
  uisai2 — collect via scp to mini, commit+push from mini (gh auth there).
- Launcher: /tmp/launch_codex.sh; package briefs: /tmp/pkg{A-F}.md.

## ⚠️ AUDIT RESULT (codex pkg audit, /tmp/pkgaudit_report.md on uisai2) — READ BEFORE TRUSTING THE SIX PACKAGES
- PkgA/B/C = **DEFECT** (same root cause): the producers smuggle a GLOBALLY-FALSE
  bridge `Phase{1,7,8}Honest → Phase{1,7,8}AllMain` (PkgA:117/136, PkgB:48/72,
  PkgC:74 via ∀-config MainProfileConfinedToUseful). This is the all-Main window
  vacuity we already fixed (HonestWindows) — codex re-introduced it because it
  lacked that history. These three packages' field productions are VACUOUS as stated.
  Their clean parts: PkgA hpt1 arithmetic OK; PkgC's whp route + mainConfinementProfile
  feeder OK; the defect is specifically the pointwise/all-Main bridge.
- PkgD/E/F = **CONDITIONAL** (honest carries, acceptable): D hescW*/hClosed5 carried;
  E hConc depends on phase5WidthSurvivalExport (= the named clockSeparationEscape);
  F five non-reset guards + seed-step are identity/named carries.
- **CONSEQUENCE for V6**: if FinalAssemblyV6 consumed PkgA/B/C producers, it
  INHERITED the false bridge (compiles fine — a false hypothesis is legal Lean,
  just unsatisfiable). V6's consumption table will look complete but A/B/C rows
  are vacuous. FIX: redo A/B/C to produce the fields from the HONEST windows
  (Phase{1,7,8}Honest directly, NOT via AllMain) — the honest drain machinery in
  HonestDrainSlots/HonestWindows already works on phase-only windows; the floors
  (hpull1H/hwit7/hwit8) must be derived without the all-Main collapse.
- META-LESSON: parallel codex is fast but reintroduces already-fixed bugs it has
  no memory of; the independent audit caught all three immediately. Audit is load-bearing.

## V6 LANDED (59e7243d, mirror 85dc198) — confirms the inheritance
- FinalAssemblyV6.lean: 4 theorems (whp/expected + numerals), same conclusions as V51,
  24 producers on the proof path, full consumption table, axiom-clean, single-file EXIT 0.
- CONFIRMED it consumed PkgA/B/C producers (consumption table L337 hpull1H, L356 hmain5,
  L381 hwit7, L391 hwit8) → V6 INHERITS the A/B/C false all-Main-bridge DEFECT. V6 compiles
  but those four field rows are vacuous-as-stated. Redo A/B/C on honest windows → V6 auto-fixes
  (the consumption wiring stays; only the three packages produce honestly).
- Net: V6 is the structurally-complete target; the math-honesty gap = A/B/C redo +
  the genuine paper cores (Lemma 5.3/7.1/7.4/7.6, pointwise-hmain5, hClosed5).
