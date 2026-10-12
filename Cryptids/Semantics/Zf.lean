/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Zf.Gadgets
public import Cryptids.Semantics.Zf.Boot
public import Cryptids.Semantics.Zf.Dispatcher
public import Cryptids.Semantics.Zf.Soundness
public import Cryptids.Semantics.Zf.RegisterMachine
public import Cryptids.Semantics.Zf.Subroutines

/-!
# End-to-End Mathematical Semantics of `zf_432`

This module formalizes the complete, zero-`sorry` mathematical specification of Stefan O'Rear's
`zf2.nql` Zermelo–Fraenkel (ZF) set theory proof-enumerating register machine and Andrew Wade's
432-state compilation `zf_432_wade.tm` (`Machines.zf432`).

## Architecture

The formalization is structured into six modular components, all verified with **zero `sorry`s**:

1. **Part II — Gödel Numbering, Hilbert System, & Soundness in Mathlib's `ZFSet.{0}`
   (`Cryptids.Semantics.Zf.Soundness`, 0 `sorry`s)**:
   - Encodes formulas of first-order set theory via the Cantor pairing function `cantorPair` and
     its inverse `cantorUnpair` (`cantorUnpair_cantorPair`, `cantorPair_cantorUnpair`).
   - Defines O'Rear's Tarski $S_2$ + Metamath ZF Hilbert system `ZFProvable` (`axB1..axB8c`,
     `axRep`, `axPow`, `axUni`, `axInf`, `mp`, `gen`) and `ZFInconsistent`.
   - Defines a total well-founded Tarski satisfaction relation `zfHolds` on `ℕ` and proves full
     soundness of all 19 constructors of `ZFProvable` in Mathlib's cumulative hierarchy
     `ZFSet.{0}` (`zfProvable_sound_zfSet` and `not_zfInconsistent : ¬ ZFInconsistent`).

2. **Layer 1 — Tape Layout & Two-Pass Register Gadgets
   (`Cryptids.Semantics.Zf.Gadgets`, 0 `sorry`s)**:
   - Formalizes the canonical tape layout `zfRootCfg` at `main().0` (State `126`) and proves the
     two-pass register increment and conditional decrement gadgets (`stage3_inc_pass2`,
     `stage3_decnz_pass2_zero`, `stage3_decnz_pass2_pos`) as well as the `4.dispatch`, `5.root`,
     `6.continue.0..3`, and `6.break.0..2` return-scan and cleanup phases.

3. **Layer 1b — Bootstrapping Verification (`Cryptids.Semantics.Zf.Boot`, 0 `sorry`s)**:
   - Proves `boot_to_root`, showing that starting from the blank initial configuration
     `init = ⟨0, default⟩`, `Machines.zf432` executes all 8 exponential
     rounds of `0a.boot1.A..E` (2,133,492 steps) and all 1,909 cycles of `0b.boot2` to reach
     `zfRootCfg 3821 [] (List.replicate 1909 0)` at `main().0` (State `126`).

4. **Layer 2 — Call-Stack Decision-Tree Dispatcher
   (`Cryptids.Semantics.Zf.Dispatcher`, 0 `sorry`s)**:
   - Formalizes the 336-state unary call-stack decision tree (`States 96..431`), proves universal
     tree-walk soundness (`walkTape_sound`) and stack-bound invariance (`validStack`), and proves
     the halting bisimulation `halts_reference_iff_zfRegHalts : Halts Machines.zf432 ↔ ZfRegHalts`.

5. **Layer 3 — 11-Register Machine & Wff-Stack Verification
   (`Cryptids.Semantics.Zf.RegisterMachine`, 0 `sorry`s)**:
   - Proves that the `pair` and `unpair` register loops compute `cantorPair` and `cantorUnpair`,
     verifies the 20 reverse-Polish notation (RPN) axiom/rule clauses of `zf_432_wade.tm`
     (`rpnAllClauses_eq_zfClauseDispatch`), and proves both Soundness
     (`wadeZFInconsistent_of_mainLoopHalts`) and Completeness
     (`mainLoopHalts_of_wadeZFInconsistent`), establishing `mainLoopHalts_iff_wadeZFInconsistent :
     MainLoopHalts ↔ WadeZFInconsistent`.

6. **Layer 3b — Full Subroutine & Main-Spine Verification
   (`Cryptids.Semantics.Zf.Subroutines`, 0 `sorry`s)**:
   - Verifies all 336 call-stack decision-tree subroutine states (`96..431`) and all 135 steps of
     the outer `main()` spine (`main().0..134`) against `zfReg11Step`, proving
     `zfRegHalts_iff_mainLoopHalts : ZfRegHalts ↔ MainLoopHalts`.

## Formal Discovery of the `B6a` Register-Restoration Bug in `zf_432_wade.tm`

During the formal verification of `main().0..134` in `Cryptids.Semantics.Zf.Subroutines`, we
discovered that the baseline Turing machine `baselines/sources/zf_432_wade.tm` was compiled from
Andrew Wade's `zf2.py` prior to his August 31, 2025 bugfix commit `10fcf152b3`
(*"Bugfix for B6a where correct variables were not being restored"*):
- In `zf_432_wade.tm`, `main().n_140.1` (State `299`) transitions on `0` to State `403`
  (`while_decnz(scratch1, 3.param1.inc).0`) instead of State `407`
  (`while_decnz(scratch1, 3.param3.inc).0`).
- As a result, during the first distinctness check (`param1 ≠ param3`) of Clause 9 (`B6a`),
  `param3` is drained into `param1` (`param1 := p1 + p3, param3 := 0`), so the second check
  compares `param2` against `param3 = 0` (`p2 ≠ 0` instead of `p2 ≠ p3`), and subsequent clauses
  (`ac = 10..17`) see `param1 = p1 + p3` and `param3 = 0`.
- `WadeZFProvable` (`Cryptids.Semantics.Zf.RegisterMachine`) captures the exact 20-clause
  deductive system enumerated by `zf_432_wade.tm`, while `ZFProvable`
  (`Cryptids.Semantics.Zf.Soundness`) captures O'Rear's `zf2.nql` / Wade's post-`10fcf152b3`
  Hilbert system and proves its soundness in Mathlib's `ZFSet.{0}` (`not_zfInconsistent`).
-/

@[expose] public section

namespace ConjectureMachines.Semantics.Zf

open Turing StateTransition

/-! ## Section 1: Unconditional Layer 1 + Layer 2 Halting Equivalence -/

/-- Unconditional halting equivalence between the 432-state baseline Turing machine `zf_432`
(`Machines.zf432`) and the 11-register call-stack machine `ZfRegHalts`,
combining `Boot.boot_to_root`, `Layer1.stage3_inc_pass2`, `Layer1.stage3_decnz_pass2_zero`,
`Layer1.stage3_decnz_pass2_pos`, and `Layer2.halts_reference_iff_zfRegHalts`. -/
theorem halts_reference_iff_zfRegHalts_unconditional :
    ConjectureMachines.Halts Machines.zf432 ↔ Layer2.ZfRegHalts :=
  Layer2.halts_reference_iff_zfRegHalts
    Boot.boot_to_root
    Layer1.stage3_inc_pass2
    Layer1.stage3_decnz_pass2_zero
    Layer1.stage3_decnz_pass2_pos

/-! ## Section 2: End-to-End Turing Machine Equivalence Theorem -/

/-- The 432-state baseline machine `zf_432` (`Machines.zf432`) halts on the blank tape if and only
if `WadeZFProvable` proves `v_0 ∈ v_0` (`WadeZFInconsistent`). -/
theorem halts_zf432_iff_wadeZFInconsistent :
    ConjectureMachines.Halts Machines.zf432 ↔ WadeZFInconsistent :=
  halts_reference_iff_zfRegHalts_unconditional.trans
    (zfRegHalts_iff_mainLoopHalts.trans mainLoopHalts_iff_wadeZFInconsistent)

end ConjectureMachines.Semantics.Zf
