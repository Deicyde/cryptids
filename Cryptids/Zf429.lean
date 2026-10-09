/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.Zf432
public import Cryptids.Machines.Zf429

/-!
# Zf429

429-state Turing machine halting-equivalent to the 432-state ZF machine.
-/

@[expose] public section

namespace ConjectureMachines.Zf429

open Turing StateTransition

/-- 432-state ZF consistency reference machine (`zf_432`, Wade 2025). -/
abbrev reference : Machine 432 2 := Machines.zf432

/-- 429-state ZF consistency candidate machine (`zf_429`). -/
abbrev candidate : Machine 429 2 := Machines.zf429

def renum (q : Nat) : Fin 429 :=
  let s := (if q > 42 then 1 else 0) + (if q > 91 then 1 else 0) + (if q > 95 then 1 else 0)
  if h : q - s < 429 then ⟨q - s, h⟩ else ⟨0, by decide⟩

def mapState (q : Fin 432) (l0 h : Fin 2) : Fin 429 :=
  if q.val = 42 then renum 13
  else if q.val = 95 then renum 331
  else if q.val = 94 then renum (if h.val = 0 then 94 else 372)
  else if q.val = 93 then renum (if h.val = 0 then 93 else 420)
  else if q.val = 91 then
    if h.val = 0 then renum 46
    else if l0.val = 1 then renum 93
    else renum 94
  else renum q.val

def isL0Eq1State (q : Nat) : Bool :=
  q == 114 || q == 330 || q == 334 || q == 349 || q == 355 ||
  q == 372 || q == 373 || q == 375 || q == 376 || q == 378 ||
  q == 379 || q == 383 || q == 389 || q == 400 || q == 402 ||
  q == 404 || q == 406 || q == 408 || q == 413 || q == 417 ||
  q == 423 || q == 426

def validState (q : Fin 432) (l2 l1 l0 h : Fin 2) : Bool :=
  (!isL0Eq1State q.val || l0 == 1) &&
  (!(q.val == 331 || q.val == 335 || q.val == 350 || q.val == 356) || (l0 == 1 && l1 == 1)) &&
  (!(q.val == 351 || q.val == 357) || (l0 == 1 && l1 == 1 && l2 == 1)) &&
  (q.val != 113 || l0 == 0) &&
  (q.val != 114 || l1 == 0) &&
  (q.val != 115 || (l0 == 0 && l1 == 1)) &&
  (q.val != 116 || (l0 == 1 && l1 == 1 && l2 == 0)) &&
  (q.val != 348 || (l0 == 0 && l1 == 1 && l2 == 1)) &&
  (q.val != 95 || (h == 1 && l0 == 1 && l1 == 1)) &&
  (q.val != 94 || ((h == 0 && l0 == 1 && l1 == 1) || (h == 1 && l0 == 1))) &&
  (q.val != 93 || ((h == 0 && l0 == 1) || h == 1)) &&
  (q.val != 91 || ((h == 1 && l0 == 1 && l1 == 0) || (h == 1 && l0 == 0) || h == 0))

def checkNext (q : Fin 432) (l2 l1 l0 h x : Fin 2) : Bool :=
  match reference.transition q h with
  | none => true
  | some (w, Dir.right, q') => validState q' l1 l0 w x
  | some (_, Dir.left, q') => validState q' x l2 l1 l0

set_option maxHeartbeats 0 in
-- Exhaustive finite check over all 432 states and 4-cell window configurations.
set_option maxRecDepth 200000 in
theorem validState_next (q : Fin 432) (l2 l1 l0 h x : Fin 2) :
    validState q l2 l1 l0 h = true → checkNext q l2 l1 l0 h x = true := by
  revert q l2 l1 l0 h x; decide

def expectedTransition (q : Fin 432) (l1 l0 h x : Fin 2) : Option (Fin 2 × Dir × Fin 429) :=
  match reference.transition q h with
  | none => none
  | some (w, Dir.right, q') => some (w, Dir.right, mapState q' w x)
  | some (w, Dir.left, q') => some (w, Dir.left, mapState q' l1 l0)

set_option maxHeartbeats 0 in
-- Exhaustive finite check over all 432 states and 4-cell window configurations.
set_option maxRecDepth 200000 in
theorem transition_mapState (q : Fin 432) (l2 l1 l0 h x : Fin 2) :
    validState q l2 l1 l0 h = true →
    candidate.transition (mapState q l0 h) h = expectedTransition q l1 l0 h x := by
  revert q l2 l1 l0 h x; decide

theorem step_mapState (q : Fin 432) (T : Tape (Fin 2))
    (hv : validState q T.left.tail.tail.head T.left.tail.head T.left.head T.head = true) :
    step candidate ⟨mapState q T.left.head T.head, T⟩ =
      (step reference ⟨q, T⟩).map fun c =>
        ⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩ := by
  have htr :=
    transition_mapState q T.left.tail.tail.head T.left.tail.head T.left.head T.head T.right.head hv
  dsimp only [step]
  rw [htr]
  rcases e : reference.transition q T.head with _ | ⟨w, d, q'⟩
  · simp [expectedTransition, e]
  · cases d <;> simp [expectedTransition, e, Tape.move, Tape.write]

theorem step_preserves_valid (q : Fin 432) (T : Tape (Fin 2))
    (hv : validState q T.left.tail.tail.head T.left.tail.head T.left.head T.head = true) :
    match step reference ⟨q, T⟩ with
    | none => True
    | some c =>
      validState c.state c.tape.left.tail.tail.head c.tape.left.tail.head c.tape.left.head
        c.tape.head = true := by
  have hnext := validState_next q T.left.tail.tail.head T.left.tail.head T.left.head T.head
  dsimp only [step]
  rcases e : reference.transition q T.head with _ | ⟨w, d, q'⟩
  · trivial
  · cases d
    · simpa [checkNext, e, Tape.move, Tape.write] using hnext T.left.tail.tail.tail.head hv
    · simpa [checkNext, e, Tape.move, Tape.write] using hnext T.right.head hv

def Rel (c₁ : Cfg 432 2) (c₂ : Cfg 429 2) : Prop :=
  validState c₁.state c₁.tape.left.tail.tail.head c₁.tape.left.tail.head c₁.tape.left.head
    c₁.tape.head = true ∧
  c₂ = ⟨mapState c₁.state c₁.tape.left.head c₁.tape.head, c₁.tape⟩

theorem respects : Respects (step reference) (step candidate) Rel := by
  intro c₁ c₂ ⟨hv, h⟩
  subst h
  obtain ⟨q, T⟩ := c₁
  have hpres := step_preserves_valid q T hv
  rcases e : step reference ⟨q, T⟩ with _ | c
  · simpa [step_mapState q T hv] using e
  · rw [e] at hpres
    exact ⟨⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩, ⟨hpres, rfl⟩,
      Relation.TransGen.single (by simp [step_mapState q T hv, e])⟩

theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  StateTransition.tr_eval_dom respects ⟨rfl, rfl⟩

end ConjectureMachines.Zf429
