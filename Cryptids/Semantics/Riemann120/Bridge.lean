/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann120.Backend
public import Cryptids.Semantics.Riemann120.Program
public import Cryptids.Semantics.Riemann120.Analytic

/-!
# Top-Level Riemann Hypothesis Bridge for `riemann120`

Combines:
1. 5-cell window de-merging `halts_riemann120_iff_halts_riemann121` (`Cryptids/Riemann120.lean`),
2. Lockstep dispatcher simulation `halts_riemann121_iff_rhRegHalts` (`Backend.lean`),
3. 5-register self-sieving recurrence `rhRegHalts_iff_exists_shuniaCounterexample` (`Program.lean`),
4. Analytic & Chebyshev equivalence
   `exists_shuniaCounterexampleExact_iff_not_riemannHypothesis_of_large`
   (`Analytic.lean`).
-/

@[expose] public section

namespace ConjectureMachines.Riemann120

open Turing StateTransition ConjectureMachines
open ConjectureMachines.Riemann120.Layer2 (rhRegHalts_iff_exists_shuniaCounterexample)
open Riemann120Analytic
  (quarterClockStep ShuniaCounterexampleExact shuniaCounterexampleExact_iff
   exists_shuniaCounterexampleExact_iff_not_riemannHypothesis_of_large)

theorem exists_shuniaCounterexample_iff_shuniaCounterexampleExact :
    (∃ n ≥ 2, ShuniaCounterexample n) ↔ ∃ n, ShuniaCounterexampleExact n :=
  ⟨fun ⟨n, hn2, hce⟩ => ⟨n, shuniaCounterexampleExact_iff.mpr ⟨hn2, hce⟩⟩,
   fun ⟨n, hce⟩ =>
    let ⟨hn2, hce'⟩ := shuniaCounterexampleExact_iff.mp hce
    ⟨n, hn2, hce'⟩⟩

/-- **Top-Level Halting Bridge Theorem for `riemann120`**:
Given the explicit large-`n` RH bound (`21845 < n`), the 120-state Turing machine
`riemann120` halts on the blank tape if and only if the Riemann Hypothesis is false. -/
theorem halts_riemann120_iff_not_riemannHypothesis_of_large
    (hLarge : RiemannHypothesis → ∀ n : ℕ, 21845 < n →
      (n : ℝ) - Chebyshev.theta n ≤
        ((quarterClockStep (n - 1) + 1) * 2 ^ quarterClockStep (n - 1) : ℝ) * Real.log n) :
    ConjectureMachines.Halts riemann120 ↔ ¬ RiemannHypothesis :=
  halts_riemann120_iff_halts_riemann121
    |>.trans halts_riemann121_iff_rhRegHalts
    |>.trans rhRegHalts_iff_exists_shuniaCounterexample
    |>.trans exists_shuniaCounterexample_iff_shuniaCounterexampleExact
    |>.trans (exists_shuniaCounterexampleExact_iff_not_riemannHypothesis_of_large hLarge)

end ConjectureMachines.Riemann120

end
