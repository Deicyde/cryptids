/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.Zf432
public import Cryptids.Machines.Zf430

/-!
# Challenge.Zf430

430-state ZF Turing machine challenge specification.
-/

@[expose] public section

namespace ConjectureMachines.Zf430

/-- 432-state ZF consistency reference machine (`zf_432`, Wade 2025). -/
abbrev reference : BundledMachine 2 := Machines.zf432.bundle

/-- 430-state ZF consistency candidate machine (`zf_430`). -/
abbrev candidate : BundledMachine 2 := Machines.zf430.bundle

theorem candidate_fewer_states : candidate.states < reference.states := by
  sorry

theorem candidate_equivalent : Halts candidate ↔ Halts reference := by
  sorry

end ConjectureMachines.Zf430
