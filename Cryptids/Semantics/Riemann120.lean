/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann120.VonMangoldt
public import Cryptids.Semantics.Riemann120.Bridge

/-!
# Halting Equivalence for Shunia's 120-State Riemann Machine (`riemann120`)

This module connects all layers of the formalization of Joseph M. Shunia's 120-state,
2-symbol Turing machine (`riemann120`, `arXiv:2609.30306`, September 2026) into the complete
end-to-end equivalence:

`Halts riemann120 ↔ ¬ RiemannHypothesis`.
-/

@[expose] public section

namespace ConjectureMachines.Riemann120

open Turing ConjectureMachines
open _root_.Riemann120Analytic (quarterClockStep)

theorem halts_riemann120_iff_not_riemannHypothesis :
    Halts riemann120 ↔ ¬ RiemannHypothesis := by
  refine halts_riemann120_iff_not_riemannHypothesis_of_large ?_
  intro hRH n hn
  have hlt :=
    ConjectureMachines.Riemann120.VonMangoldt.theta_sub_lt_quarterClock_of_ge_21846 hRH n hn
  have hq : ConjectureMachines.Riemann120.VonMangoldt.quarterClock (n - 1) =
      quarterClockStep (n - 1) := by
    rw [quarterClockStep_eq_program_quarterClock]
    clear hRH hn hlt
    generalize n - 1 = z
    induction z using Nat.strongRecOn with
    | ind z ih =>
      cases z with
      | zero => simp [VonMangoldt.quarterClock, Layer2.quarterClock]
      | succ z =>
        simp only [VonMangoldt.quarterClock, Layer2.quarterClock]
        rw [ih (z / 4) (by omega)]
  rw [hq] at hlt
  exact le_of_lt hlt

end ConjectureMachines.Riemann120

end
