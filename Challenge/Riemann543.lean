/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.Riemann744
public import Cryptids.Machines.Riemann543
public import Cryptids.Propositions

/-!
# Challenge.Riemann543

543-state Riemann Hypothesis Turing machine challenge specification.
-/

@[expose] public section

namespace ConjectureMachines.Riemann543

/-- 744-state Riemann Hypothesis reference machine
(`riemann_744`, Matiyasevich–Davis–O'Rear 2016). -/
abbrev reference : BundledMachine 2 := Machines.riemann744.bundle

/-- 543-state Riemann Hypothesis candidate machine (`riemann_543`). -/
abbrev candidate : BundledMachine 2 := Machines.riemann543.bundle

theorem candidate_fewer_states : candidate.states < reference.states := by
  sorry

theorem candidate_equivalent : Halts candidate ↔ Halts reference := by
  sorry

namespace Semantics

/-- **Part I (Turing Machine ↔ Elementary Counterexample)**:
The 744-state machine `reference` (`riemann_744`) halts on the blank tape if and only if there
exists an integer `x` satisfying `MatiyasevichRiemannCounterexample x`. -/
theorem halts_reference_iff_exists_counterexample :
    Halts reference ↔ ∃ x : ℕ, MatiyasevichRiemannCounterexample x := by
  sorry

/-- The 543-state machine `candidate` (`riemann_543`) halts on the blank tape if and only if there
exists an integer `x` satisfying `MatiyasevichRiemannCounterexample x`. -/
theorem halts_candidate_iff_exists_counterexample :
    Halts candidate ↔ ∃ x : ℕ, MatiyasevichRiemannCounterexample x := by
  sorry

/-- The 744-state baseline machine `reference` (`riemann_744`) halts on the blank tape
if and only if the Riemann Hypothesis is false. -/
theorem halts_reference_iff_not_riemannHypothesis :
    Halts reference ↔ ¬ RiemannHypothesis := by
  sorry

/-- The 543-state machine `candidate` (`riemann_543`) halts on the blank tape
if and only if the Riemann Hypothesis is false. -/
theorem halts_candidate_iff_not_riemannHypothesis :
    Halts candidate ↔ ¬ RiemannHypothesis := by
  sorry

end Semantics

end ConjectureMachines.Riemann543
