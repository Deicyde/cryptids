/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann104
public import Cryptids.Semantics.Riemann120.VonMangoldt
public import Cryptids.Semantics.Riemann120.Bridge

/-!
# Halting Equivalence for `riemann120` and `riemann104`

This module connects all layers of the formalization of Joseph M. Shunia's 120-state,
2-symbol Turing machine (`riemann120`, `arXiv:2609.30306`, September 2026) and its 104-state
reduction (`riemann104`) into the complete end-to-end equivalences:

- `Halts riemann120 ↔ ¬ RiemannHypothesis`
- `Halts ConjectureMachines.Riemann104.candidate ↔ ¬ RiemannHypothesis`.
-/

@[expose] public section

namespace ConjectureMachines.Riemann120

open Turing ConjectureMachines
theorem quarterClock_eq_quarterClockStep :
    ∀ z : ℕ, VonMangoldt.quarterClock z = Riemann120Analytic.quarterClockStep z
  | 0 => by rw [VonMangoldt.quarterClock, Riemann120Analytic.quarterClockStep]
  | z + 1 => by
    rw [VonMangoldt.quarterClock, Riemann120Analytic.quarterClockStep]
    exact congrArg (1 + ·) (quarterClock_eq_quarterClockStep (z / 4))

theorem halts_riemann120_iff_not_riemannHypothesis :
    Halts riemann120 ↔ ¬ RiemannHypothesis := by
  refine halts_riemann120_iff_not_riemannHypothesis_of_large ?_
  intro hRH n hn
  have hlt :=
    ConjectureMachines.Riemann120.VonMangoldt.theta_sub_lt_quarterClock_of_ge_21846 hRH n hn
  rw [quarterClock_eq_quarterClockStep] at hlt
  exact le_of_lt hlt

end ConjectureMachines.Riemann120

namespace ConjectureMachines.Riemann104.Semantics

open ConjectureMachines

/-- The 104-state record machine `riemann_104` (`ConjectureMachines.Riemann104.candidate`) halts on
the blank tape if and only if Mathlib's `RiemannHypothesis` is false. -/
theorem halts_candidate_iff_not_riemannHypothesis :
    Halts ConjectureMachines.Riemann104.candidate ↔ ¬ RiemannHypothesis :=
  ConjectureMachines.Riemann104.candidate_equivalent.trans
    ConjectureMachines.Riemann120.halts_riemann120_iff_not_riemannHypothesis

end ConjectureMachines.Riemann104.Semantics

end
