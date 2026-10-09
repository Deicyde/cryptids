/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines

/-!
# Zf430

430-state Turing machine halting-equivalent to the 432-state ZF machine.
-/

@[expose] public section

namespace ConjectureMachines.Zf430

open Turing StateTransition

/-- 432-state ZF consistency reference machine (`zf_432`, Wade 2025). -/
abbrev reference : BundledMachine 2 := Machines.zf432.bundle

/-- 430-state ZF consistency candidate machine (`zf_430`). -/
abbrev candidate : BundledMachine 2 := Machines.zf430.bundle

theorem candidate_fewer_states : candidate.states < reference.states := by
  decide

def mapState (q : Fin 432) : Fin 430 :=
  if q.val = 42 then ⟨13, by decide⟩
  else if q.val = 95 then ⟨346, by decide⟩
  else if h1 : q.val < 42 then ⟨q.val, by omega⟩
  else if h2 : q.val < 95 then ⟨q.val - 1, by omega⟩
  else ⟨q.val - 2, by omega⟩

def validState (q : Fin 432) (l h : Fin 2) : Bool :=
  (q.val != 351 || l == 1) &&
  (q.val != 357 || l == 1) &&
  (q.val != 95 || h == 1)

def checkNext (q : Fin 432) (l h x : Fin 2) : Bool :=
  match Machines.zf432.transition q h with
  | none => true
  | some (w, Dir.right, q') => validState q' w x
  | some (_, Dir.left, q') => validState q' x l

set_option maxHeartbeats 0 in
-- Exhaustive finite check over all 432 states and window configurations.
set_option maxRecDepth 200000 in
theorem validState_next (q : Fin 432) (l h x : Fin 2) :
    validState q l h = true → checkNext q l h x = true := by
  revert q l h x; decide

set_option maxHeartbeats 0 in
-- Exhaustive finite check over all 432 states and window configurations.
set_option maxRecDepth 200000 in
theorem transition_mapState (q : Fin 432) (l h : Fin 2) :
    validState q l h = true →
    Machines.zf430.transition (mapState q) h =
      (Machines.zf432.transition q h).map fun t => (t.1, t.2.1, mapState t.2.2) := by
  revert q l h; decide

theorem step_mapState (q : Fin 432) (T : Tape (Fin 2))
    (hv : validState q T.left.head T.head = true) :
    step Machines.zf430 ⟨mapState q, T⟩ =
      (step Machines.zf432 ⟨q, T⟩).map fun c => ⟨mapState c.state, c.tape⟩ := by
  simp only [step, transition_mapState q T.left.head T.head hv, Option.map_map]
  rcases Machines.zf432.transition q T.head with _ | ⟨a, d, q'⟩ <;> rfl

theorem step_preserves_valid (q : Fin 432) (T : Tape (Fin 2))
    (hv : validState q T.left.head T.head = true) :
    match step Machines.zf432 ⟨q, T⟩ with
    | none => True
    | some c => validState c.state c.tape.left.head c.tape.head = true := by
  have hnext := validState_next q T.left.head T.head
  dsimp only [step]
  rcases e : Machines.zf432.transition q T.head with _ | ⟨w, d, q'⟩
  · trivial
  · cases d
    · simpa [checkNext, e, Tape.move, Tape.write] using hnext T.left.tail.head hv
    · simpa [checkNext, e, Tape.move, Tape.write] using hnext T.right.head hv

def Rel (c₁ : Cfg 432 2) (c₂ : Cfg 430 2) : Prop :=
  validState c₁.state c₁.tape.left.head c₁.tape.head = true ∧
  c₂ = ⟨mapState c₁.state, c₁.tape⟩

theorem respects : Respects (step Machines.zf432) (step Machines.zf430) Rel := by
  intro c₁ c₂ ⟨hv, h⟩
  subst h
  obtain ⟨q, T⟩ := c₁
  have hpres := step_preserves_valid q T hv
  rcases e : step Machines.zf432 ⟨q, T⟩ with _ | c
  · simpa [step_mapState q T hv] using e
  · rw [e] at hpres
    exact ⟨⟨mapState c.state, c.tape⟩, ⟨hpres, rfl⟩,
      Relation.TransGen.single (by simp [step_mapState q T hv, e])⟩

theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  StateTransition.tr_eval_dom respects ⟨rfl, rfl⟩

end ConjectureMachines.Zf430
