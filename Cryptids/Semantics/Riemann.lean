/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann.Gadgets
public import Cryptids.Semantics.Riemann.Dispatcher
public import Cryptids.Semantics.Riemann.RegisterMachine
public import Cryptids.Semantics.Riemann.Analytic

/-!
# Semantics of the Riemann Hypothesis Turing Machines (`riemann_744` and `riemann_543`)

This file formalizes the semantics of the 744-state baseline Turing machine `reference`
(`riemann_744`) and the 543-state compressed Turing machine `candidate` (`riemann_543`), connecting
their halting problem on the blank tape to the negation of Mathlib's `RiemannHypothesis`.

## Provenance and Attribution

* **744-state Riemann Hypothesis Turing machine (`riemann_744`, 2016)**:
  Designed by **Yuri Matiyasevich**, **Scott Aaronson**, and **Stefan O'Rear** in
  [`sorear/metamath-turing-machines`](https://github.com/sorear/metamath-turing-machines)
  (`machines/2016-riemann-matiyasevich-aaronson-744/riemann.nql`), encoding an elementary
  counterexample search for the Riemann Hypothesis via harmonic numbers and
  $\operatorname{lcm}(1, \dots, x)$ building on Schoenfeld's (1976) explicit bound for
  $|\psi(x) - x|$ and Lagarias's (2002) elementary reformulation.
* **543-state compression and halting-equivalence proof (`riemann_543`, 2026)**:
  Maxence Faldor (using Gemini Argon) found the 543-state machine `candidate` (`riemann_543`) and
  proved `Halts candidate ↔ Halts reference` in `Cryptids.Riemann543`.
* **This formalization (`Cryptids.Semantics.Riemann` & submodules)**:
  Formalized in Lean 4 by Maxence Faldor and Moritz Firsching (using Gemini Argon).

## Architecture

The equivalence is factored through the elementary integer predicate
`MatiyasevichRiemannCounterexample (x : ℕ) : Prop` directly computed by `riemann.nql`:

1. **Part I (`halts_reference_iff_exists_counterexample`, 0 `sorry`s)**:
   `Halts reference ↔ ∃ x : ℕ, MatiyasevichRiemannCounterexample x`
   - **Layer 1 (`Cryptids.Semantics.Riemann.Gadgets`)**: Canonical tape layout (`entryCfg`,
     `postPcCfg`), return scan loops, 11-bit ripple-carry PC adder, and primitive unary register
     operations (`reg_init_eval`, `reg_incr_eval`, `reg_decr_eval`).
   - **Layer 2 (`Cryptids.Semantics.Riemann.Dispatcher`)**: Bounded-window symbolic evaluator
     (`WinState`), complete 2,048-entry BDD instruction decoder (`program : ℕ → Instr`), reachable
     invariant (`RegInv`), and halting simulation (`halts_reference_iff_regHalts`).
   - **Layer 3 (`Cryptids.Semantics.Riemann.RegisterMachine`)**: Complete verification of the
     16-register NQL counter machine (`regHalts_iff_exists_counterexample`).
2. **Part II (`Cryptids.Semantics.Riemann.Analytic`)**:
   `(∃ x : ℕ, MatiyasevichRiemannCounterexample x) ↔ ¬ RiemannHypothesis`
   Proves the identity $\psi(x) = \log \operatorname{lcm}(1, \dots, x)$, the Euler–Mascheroni
   harmonic bounds, and the reduction to Schoenfeld's (1976) explicit bound and Schmidt's (1903)
   oscillation theorem.
-/

@[expose] public section

namespace ConjectureMachines.Riemann543.Semantics

open Turing StateTransition
open ConjectureMachines.Riemann543

/-- Unconditional halting equivalence between the 744-state Turing machine `reference`
and the 16-register NQL counter machine `RegHalts`, combining Layer 1 and Layer 2. -/
theorem halts_reference_iff_regHalts_unconditional :
    Halts reference ↔ RegHalts := by
  apply halts_reference_iff_regHalts Layer1.entryCfg_zero_nil
  · intro pc regs _
    exact Layer1.reg_init_eval pc regs
  · intro k pc regs hk _
    simpa [List.getElem?_eq_getElem hk] using Layer1.reg_incr_eval k.val k.isLt pc regs hk
  · intro k pc regs hk _
    obtain ⟨s, hs, heval⟩ := Layer1.reg_decr_eval k.val k.isLt pc regs hk
    simp only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some]
    refine ⟨s, hs, ?_⟩
    rw [heval]
    congr 1
    by_cases hz : regs[k.val] = 0
    · simp [hz]
    · have hbeq : (regs[k.val] == 0) = false := beq_eq_false_iff_ne.mpr hz
      simp [hz, hbeq]

/-!
## 2. Two-Part Decomposition of the Main Equivalence
-/

/-- **Part I (Turing Machine ↔ Elementary Counterexample)**:
The 744-state machine `reference` (`riemann_744`) halts on the blank tape if and only if there
exists an integer `x` satisfying `MatiyasevichRiemannCounterexample x`. -/
theorem halts_reference_iff_exists_counterexample :
    Halts reference ↔ ∃ x : ℕ, MatiyasevichRiemannCounterexample x :=
  halts_reference_iff_regHalts_unconditional.trans regHalts_iff_exists_counterexample

/-- The 543-state machine `candidate` (`riemann_543`) halts on the blank tape if and only if there
exists an integer `x` satisfying `MatiyasevichRiemannCounterexample x`. -/
theorem halts_candidate_iff_exists_counterexample :
    Halts candidate ↔ ∃ x : ℕ, MatiyasevichRiemannCounterexample x :=
  candidate_equivalent.trans halts_reference_iff_exists_counterexample

/-- The 744-state baseline machine `reference` (`riemann_744`) halts on the blank tape
if and only if the Riemann Hypothesis is false. -/
theorem halts_reference_iff_not_riemannHypothesis :
    Halts reference ↔ ¬ RiemannHypothesis :=
  halts_reference_iff_exists_counterexample.trans exists_counterexample_iff_not_riemannHypothesis

/-- The 543-state machine `candidate` (`riemann_543`) halts on the blank tape
if and only if the Riemann Hypothesis is false. -/
theorem halts_candidate_iff_not_riemannHypothesis :
    Halts candidate ↔ ¬ RiemannHypothesis :=
  candidate_equivalent.trans halts_reference_iff_not_riemannHypothesis

end ConjectureMachines.Riemann543.Semantics
