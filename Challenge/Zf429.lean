/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.Zf432
public import Cryptids.Machines.Zf429
public import Cryptids.Propositions

/-!
# Challenge.Zf429

429-state ZF Turing machine challenge specification.
-/

@[expose] public section

namespace ConjectureMachines.Zf429

/-- 432-state ZF consistency reference machine (`zf_432`, Wade 2025). -/
abbrev reference : BundledMachine 2 := Machines.zf432.bundle

/-- 429-state ZF consistency candidate machine (`zf_429`). -/
abbrev candidate : BundledMachine 2 := Machines.zf429.bundle

theorem candidate_fewer_states : candidate.states < reference.states := by
  sorry

theorem candidate_equivalent : Halts candidate ↔ Halts reference := by
  sorry

end ConjectureMachines.Zf429

namespace ConjectureMachines.Semantics.Zf

/-- Soundness of the `ZFProvable` Hilbert system with respect to Mathlib's `ZFSet.{0}`:
any provable well-formed formula holds under every variable assignment `v : ℕ → ZFSet.{0}`. -/
theorem zfProvable_sound_zfSet (φ : ZFFormula) (h : ZFProvable φ.code)
    (v : ℕ → ZFSet.{0}) : φ.Holds v := by
  sorry

/-- Relative consistency of `ZFProvable` from Mathlib's `ZFSet.{0}` model of ZFC:
`ZFInconsistent` is false assuming `zfProvable_sound_zfSet`. -/
theorem not_zfInconsistent : ¬ ZFInconsistent := by
  sorry

/-- The 432-state baseline machine `zf_432` (`ConjectureMachines.Zf429.reference`) halts on the
blank tape if and only if `WadeZFProvable` proves `v_0 ∈ v_0` (`WadeZFInconsistent`). -/
theorem halts_reference_iff_wadeZFInconsistent :
    Halts ConjectureMachines.Zf429.reference ↔ WadeZFInconsistent := by
  sorry

/-- The 429-state reduced machine `zf_429` (`ConjectureMachines.Zf429.candidate`) halts on the
blank tape if and only if `WadeZFProvable` proves `v_0 ∈ v_0` (`WadeZFInconsistent`). -/
theorem halts_candidate_429_iff_wadeZFInconsistent :
    Halts ConjectureMachines.Zf429.candidate ↔ WadeZFInconsistent := by
  sorry

end ConjectureMachines.Semantics.Zf

