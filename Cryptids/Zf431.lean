/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.Zf432
public import Cryptids.Machines.Zf431

/-!
# Zf431

431-state Turing machine halting-equivalent to the 432-state ZF machine.
-/

@[expose] public section

namespace ConjectureMachines.Zf431

open Turing StateTransition

/-- 432-state ZF consistency reference machine (`zf_432`, Wade 2025). -/
abbrev reference : Machine 432 2 := Machines.zf432

/-- 431-state ZF consistency candidate machine (`zf_431`). -/
abbrev candidate : Machine 431 2 := Machines.zf431

def mapState (q : Fin 432) : Fin 431 :=
  if q.val = 42 then ⟨13, by decide⟩
  else if h : q.val < 42 then ⟨q.val, by omega⟩
  else ⟨q.val - 1, by omega⟩

set_option maxHeartbeats 0 in
-- Exhaustive finite check over all 432 states and 2 symbols.
set_option maxRecDepth 200000 in
theorem transition_mapState (q : Fin 432) (a : Fin 2) :
    candidate.transition (mapState q) a =
      (reference.transition q a).map fun t => (t.1, t.2.1, mapState t.2.2) := by
  revert q a; decide

theorem step_mapState (q : Fin 432) (T : Tape (Fin 2)) :
    step candidate ⟨mapState q, T⟩ =
      (step reference ⟨q, T⟩).map fun c => ⟨mapState c.state, c.tape⟩ := by
  simp only [step, transition_mapState, Option.map_map]
  rcases reference.transition q T.head with _ | ⟨a, d, q'⟩ <;> rfl

theorem respects :
    Respects (step reference) (step candidate)
      fun c₁ c₂ => c₂ = ⟨mapState c₁.state, c₁.tape⟩ := by
  intro c₁ c₂ h
  subst h
  obtain ⟨q, T⟩ := c₁
  rcases e : step reference ⟨q, T⟩ with _ | c
  · simpa [step_mapState] using e
  · exact ⟨⟨mapState c.state, c.tape⟩, rfl,
      Relation.TransGen.single (by simp [step_mapState, e])⟩

theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  StateTransition.tr_eval_dom respects rfl

end ConjectureMachines.Zf431
