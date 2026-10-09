/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cryptids.Machines

/-!
# Goldbach24

24-state Turing machine halting-equivalent to the 25-state Goldbach machine.
-/

namespace ConjectureMachines.Goldbach24

open Turing StateTransition

/-- 25 states, 2 symbols,
SHA-256 `da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67`. -/
def reference : Machine 25 2 := Machine.ofRows [
  [some (1, .right, 1), some (1, .right, 3)],
  [some (1, .left, 2), some (1, .right, 1)],
  [some (0, .right, 0), some (1, .left, 2)],
  [some (0, .left, 16), some (1, .right, 4)],
  [some (0, .left, 5), some (1, .right, 6)],
  [some (0, .left, 2), some (1, .left, 5)],
  [some (0, .left, 5), some (0, .left, 7)],
  [some (1, .left, 16), some (1, .left, 8)],
  [some (0, .right, 9), some (0, .left, 8)],
  [some (1, .right, 10), some (0, .left, 9)],
  [some (0, .right, 11), some (0, .right, 18)],
  [some (1, .right, 11), some (0, .right, 12)],
  [some (1, .right, 13), some (1, .right, 12)],
  [some (0, .left, 14), some (0, .left, 20)],
  [some (0, .left, 15), some (1, .left, 14)],
  [some (1, .right, 7), some (1, .left, 23)],
  [some (1, .left, 17), some (1, .left, 16)],
  [some (0, .right, 10), some (0, .left, 19)],
  [some (1, .left, 17), some (1, .right, 18)],
  [none, some (1, .right, 2)],
  [some (1, .left, 21), some (1, .left, 20)],
  [some (0, .left, 22), some (0, .left, 9)],
  [some (0, .right, 10), some (0, .left, 22)],
  [some (1, .right, 24), some (1, .left, 23)],
  [some (1, .right, 4), some (1, .right, 24)]]

/-- 24 states, 2 symbols,
SHA-256 `9b8b92a609ca9ae891856957b21a4d5ff9ba4317c27835e31265a249d236b2dc`. -/
def candidate : Machine 24 2 := Machine.ofRows [
  [some (1, .right, 1), some (1, .right, 3)],
  [some (1, .right, 17), some (1, .right, 1)],
  [some (0, .right, 0), some (1, .left, 2)],
  [some (0, .left, 5), some (1, .right, 4)],
  [some (0, .left, 15), some (1, .right, 6)],
  [some (0, .left, 2), some (1, .left, 5)],
  [some (0, .left, 5), some (0, .left, 7)],
  [some (1, .left, 15), some (1, .left, 21)],
  [some (1, .right, 9), some (0, .left, 8)],
  [some (0, .right, 10), some (0, .right, 17)],
  [some (1, .right, 10), some (0, .right, 11)],
  [some (1, .right, 12), some (1, .right, 11)],
  [some (0, .left, 13), some (0, .left, 19)],
  [some (0, .left, 14), some (1, .left, 13)],
  [some (1, .right, 7), some (1, .left, 22)],
  [some (1, .left, 16), some (1, .left, 15)],
  [some (0, .right, 9), some (0, .left, 18)],
  [some (1, .left, 16), some (1, .right, 17)],
  [none, some (1, .right, 2)],
  [some (1, .left, 20), some (1, .left, 19)],
  [some (0, .left, 21), some (0, .left, 8)],
  [some (0, .right, 9), some (0, .left, 21)],
  [some (1, .right, 23), some (1, .left, 22)],
  [some (1, .right, 4), some (1, .right, 23)]]

-- Step 1: Relate the 24-state `candidate` to the 25-state `edited` machine
-- (which is `reference` with the 4 transition edits `(1,0)->1R18`, `(3,0)->0L5`,
-- `(4,0)->0L16`, `(7,1)->1L22` that make state 8 unreachable).

def edited : Machine 25 2 := Machine.ofRows [
  [some (1, .right, 1), some (1, .right, 3)],
  [some (1, .right, 18), some (1, .right, 1)],
  [some (0, .right, 0), some (1, .left, 2)],
  [some (0, .left, 5), some (1, .right, 4)],
  [some (0, .left, 16), some (1, .right, 6)],
  [some (0, .left, 2), some (1, .left, 5)],
  [some (0, .left, 5), some (0, .left, 7)],
  [some (1, .left, 16), some (1, .left, 22)],
  [some (0, .right, 9), some (0, .left, 8)],
  [some (1, .right, 10), some (0, .left, 9)],
  [some (0, .right, 11), some (0, .right, 18)],
  [some (1, .right, 11), some (0, .right, 12)],
  [some (1, .right, 13), some (1, .right, 12)],
  [some (0, .left, 14), some (0, .left, 20)],
  [some (0, .left, 15), some (1, .left, 14)],
  [some (1, .right, 7), some (1, .left, 23)],
  [some (1, .left, 17), some (1, .left, 16)],
  [some (0, .right, 10), some (0, .left, 19)],
  [some (1, .left, 17), some (1, .right, 18)],
  [none, some (1, .right, 2)],
  [some (1, .left, 21), some (1, .left, 20)],
  [some (0, .left, 22), some (0, .left, 9)],
  [some (0, .right, 10), some (0, .left, 22)],
  [some (1, .right, 24), some (1, .left, 23)],
  [some (1, .right, 4), some (1, .right, 24)]
]

def embed (q : Fin 24) : Fin 25 :=
  if q.val < 8 then ⟨q.val, by omega⟩ else ⟨q.val + 1, by omega⟩

theorem transition_embed (q : Fin 24) (a : Fin 2) :
    edited.transition (embed q) a =
      (candidate.transition q a).map fun t => (t.1, t.2.1, embed t.2.2) := by
  revert q a; decide

theorem step_embed (q : Fin 24) (T : Tape (Fin 2)) :
    step edited ⟨embed q, T⟩ =
      (step candidate ⟨q, T⟩).map fun c => ⟨embed c.state, c.tape⟩ := by
  simp only [step, transition_embed, Option.map_map]
  rcases candidate.transition q T.head with _ | ⟨a, d, q'⟩ <;> rfl

theorem respects_embed :
    Respects (step candidate) (step edited)
      fun c₁ c₂ => c₂ = ⟨embed c₁.state, c₁.tape⟩ := by
  intro c₁ c₂ h
  subst h
  obtain ⟨q, T⟩ := c₁
  rcases e : step candidate ⟨q, T⟩ with _ | c
  · simpa [step_embed] using e
  · exact ⟨⟨embed c.state, c.tape⟩, rfl,
      Relation.TransGen.single (by simp [step_embed, e])⟩

theorem candidate_iff_edited : Halts candidate ↔ Halts edited :=
  (StateTransition.tr_eval_dom respects_embed rfl).symm

-- Step 2: Bounded multi-step execution & domain invariance (`nSteps_eval_dom`)

def nSteps (M : Machine 25 2) (n : ℕ) : Cfg 25 2 → Option (Cfg 25 2) :=
  Nat.rec (motive := fun _ => Cfg 25 2 → Option (Cfg 25 2))
    (fun c => some c)
    (fun _ ih c => (step M c).bind ih)
    n

@[simp]
theorem nSteps_zero (M : Machine 25 2) (c : Cfg 25 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ (M : Machine 25 2) (n : ℕ) (c : Cfg 25 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

attribute [eqns nSteps_zero nSteps_succ] nSteps

theorem nSteps_reaches {M : Machine 25 2} {n : ℕ} {c c' : Cfg 25 2}
    (h : nSteps M n c = some c') : Reaches (step M) c c' := by
  induction n generalizing c with
  | zero =>
    injection h with h'
    subst h'
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [nSteps, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, hstep, hrest⟩ := h
    exact Relation.ReflTransGen.head hstep (ih hrest)

theorem nSteps_eval_dom {M : Machine 25 2} {n : ℕ} {c c' : Cfg 25 2}
    (h : nSteps M n c = some c') :
    (eval (step M) c).Dom ↔ (eval (step M) c').Dom := by
  rw [StateTransition.reaches_eval (nSteps_reaches h)]

theorem nSteps_add {M : Machine 25 2} (m n : ℕ) (c : Cfg 25 2) :
    nSteps M (m + n) c = (nSteps M m c).bind (nSteps M n) := by
  induction m generalizing c with
  | zero => simp [nSteps]
  | succ m ih =>
    rw [Nat.succ_add, nSteps, nSteps]
    cases step M c <;> simp [ih]

theorem nSteps_bind_eq {M : Machine 25 2} {m n : ℕ} {c c₁ c₂ : Cfg 25 2}
    (h₁ : nSteps M m c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (m + n) c = some c₂ := by
  rw [nSteps_add, h₁, Option.bind_some, h₂]

theorem step_nSteps {M : Machine 25 2} {n : ℕ} {c c₁ c₂ : Cfg 25 2}
    (h₁ : step M c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (n + 1) c = some c₂ := by
  rw [nSteps, h₁, Option.bind_some, h₂]

theorem step_one {M : Machine 25 2} {c c₁ : Cfg 25 2} (h : step M c = some c₁) :
    nSteps M 1 c = some c₁ := by
  rw [nSteps, h]; rfl

-- Step 3: Exact Bootstrap Equivalence (`init` -> `State 19` on `(3, 1)` vs `(4, 2)`)

theorem mk_append_replicate_zero (l : List (Fin 2)) (n : ℕ) :
    ListBlank.mk (l ++ List.replicate n 0) = ListBlank.mk l :=
  Quotient.sound' (Or.inr ⟨n, rfl⟩)

theorem boot_reference_47 :
    nSteps reference 47 init =
      some ⟨19, ⟨1, ListBlank.mk [1, 1], ListBlank.mk [0, 1]⟩⟩ := by
  have h : nSteps reference 47 init =
      some ⟨19, ⟨1, ListBlank.mk ([1, 1] ++ List.replicate 2 0), ListBlank.mk [0, 1]⟩⟩ := rfl
  rw [h, mk_append_replicate_zero]

theorem boot_edited_101 :
    nSteps edited 101 init =
      some ⟨19, ⟨1, ListBlank.mk [1, 1, 1], ListBlank.mk [0, 1, 1]⟩⟩ := by
  have h : nSteps edited 101 init =
      some ⟨19, ⟨1, ListBlank.mk ([1, 1, 1] ++ List.replicate 2 0),
        ListBlank.mk ([0, 1, 1] ++ List.replicate 1 0)⟩⟩ := rfl
  rw [h, mk_append_replicate_zero, mk_append_replicate_zero]

theorem halts_reference_iff_boot :
    Halts reference ↔
      (eval (step reference) ⟨19, ⟨1, ListBlank.mk [1, 1], ListBlank.mk [0, 1]⟩⟩).Dom :=
  nSteps_eval_dom boot_reference_47

theorem halts_edited_iff_boot :
    Halts edited ↔
      (eval (step edited) ⟨19, ⟨1, ListBlank.mk [1, 1, 1], ListBlank.mk [0, 1, 1]⟩⟩).Dom :=
  nSteps_eval_dom boot_edited_101

-- Step 4: Symbolic Tape Primitives & Case-Free Scanner Inductions (`Tape.mkL`, `Tape.mk'`)

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  revert a; decide

def Tape.mkL (L R : ListBlank (Fin 2)) : Tape (Fin 2) :=
  ⟨L.head, L.tail, R⟩

@[simp]
theorem Tape.mkL_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mkL (L.cons a) R = ⟨a, L, R⟩ := by
  simp [Tape.mkL]

@[simp]
theorem Tape.mk'_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mk' L (R.cons a) = ⟨a, L, R⟩ := by
  simp [Tape.mk']

theorem step_left {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', ⟨L.head, L.tail, R.cons b⟩⟩ := by
  simp [step, h, Tape.write, Tape.move]

theorem step_right {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', ⟨R.head, L.cons b, R.tail⟩⟩ := by
  simp [step, h, Tape.write, Tape.move]

theorem step_left_cons {M : Machine 25 2} {q q' : Fin 25} {a b c : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, ⟨a, L.cons c, R⟩⟩ = some ⟨q', ⟨c, L, R.cons b⟩⟩ := by
  simp [step, h, Tape.write, Tape.move]

theorem step_right_cons {M : Machine 25 2} {q q' : Fin 25} {a b c : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, ⟨a, L, R.cons c⟩⟩ = some ⟨q', ⟨c, L.cons b, R⟩⟩ := by
  simp [step, h, Tape.write, Tape.move]

theorem step_mkL_left {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {M : Machine 25 2} {q q' : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem append_replicate_cons (k : ℕ) (b : Fin 2) (L : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate k b) (L.cons b) =
      ListBlank.append (List.replicate (k + 1) b) L := by
  rw [List.replicate_succ', ListBlank.append_assoc, ListBlank.append, ListBlank.append]

theorem nSteps_mkL_left_scan {M : Machine 25 2} {q : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {M : Machine 25 2} {q : Fin 25} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

-- Step 5: Trial Division Lockstep Zipper Simulation (`reference` on `p` vs `edited` on `p + 1`)

/-- `LeftOfMid seg T₁ T₂` holds when `T₁` and `T₂` have the same `head` and `left`,
and their `right` half-tapes share a common prefix `seg : List (Fin 2)` followed by
`R` in `T₁` and `R.cons 1` in `T₂`. -/
def LeftOfMid (seg : List (Fin 2)) (T₁ T₂ : Tape (Fin 2)) : Prop :=
  ∃ (a : Fin 2) (L R : ListBlank (Fin 2)),
    T₁ = ⟨a, L, ListBlank.append seg R⟩ ∧
    T₂ = ⟨a, L, ListBlank.append seg (R.cons 1)⟩

theorem sim_leftOfMid_left {q q' : Fin 25} {a b : Fin 2} {seg : List (Fin 2)}
    {L R : ListBlank (Fin 2)}
    (href : reference.transition q a = some (b, .left, q'))
    (hedit : edited.transition q a = some (b, .left, q')) :
    step reference ⟨q, ⟨a, L, ListBlank.append seg R⟩⟩ =
      some ⟨q', ⟨L.head, L.tail, ListBlank.append (b :: seg) R⟩⟩ ∧
    step edited ⟨q, ⟨a, L, ListBlank.append seg (R.cons 1)⟩⟩ =
      some ⟨q', ⟨L.head, L.tail, ListBlank.append (b :: seg) (R.cons 1)⟩⟩ :=
  ⟨step_left href L (ListBlank.append seg R),
   step_left hedit L (ListBlank.append seg (R.cons 1))⟩

theorem sim_leftOfMid_right {q q' : Fin 25} {a b c : Fin 2} {seg : List (Fin 2)}
    {L R : ListBlank (Fin 2)}
    (href : reference.transition q a = some (b, .right, q'))
    (hedit : edited.transition q a = some (b, .right, q')) :
    step reference ⟨q, ⟨a, L, ListBlank.append (c :: seg) R⟩⟩ =
      some ⟨q', ⟨c, L.cons b, ListBlank.append seg R⟩⟩ ∧
    step edited ⟨q, ⟨a, L, ListBlank.append (c :: seg) (R.cons 1)⟩⟩ =
      some ⟨q', ⟨c, L.cons b, ListBlank.append seg (R.cons 1)⟩⟩ :=
  ⟨step_right_cons href L (ListBlank.append seg R),
   step_right_cons hedit L (ListBlank.append seg (R.cons 1))⟩

/-- At `State 11 (L)` when `head = 1` (the stopper at `c + 1`),
`reference` takes 1 step (`11 -> 12`) from `⟨1, L, R⟩` to `Tape.mk' (L.cons 0) R`,
while `edited` takes 2 steps (`11 -> 12 -> 12`) from `⟨1, L, R.cons 1⟩`
to `Tape.mk' ((L.cons 0).cons 1) R`. -/
theorem sim_state11_stopper (L R : ListBlank (Fin 2)) :
    step reference ⟨11, ⟨1, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 0) R⟩ ∧
    Reaches₁ (step edited) ⟨11, ⟨1, L, R.cons 1⟩⟩ ⟨12, Tape.mk' ((L.cons 0).cons 1) R⟩ := by
  constructor
  · exact step_right rfl L R
  · exact Relation.TransGen.head (step_right_cons rfl L R)
      (Relation.TransGen.single (step_right rfl (L.cons 0) R))

/-- In `State 12 (M)`, for ANY `L R`, 1 step of `reference` from `Tape.mk' L R`
matches 1 step of `edited` from `Tape.mk' (L.cons 1) R`, preserving the extra `.cons 1` on `L`. -/
theorem sim_state12 (L R : ListBlank (Fin 2)) :
    let q' : Fin 25 := if R.head = 0 then 13 else 12
    step reference ⟨12, Tape.mk' L R⟩ = some ⟨q', Tape.mk' (L.cons 1) R.tail⟩ ∧
    step edited ⟨12, Tape.mk' (L.cons 1) R⟩ = some ⟨q', Tape.mk' ((L.cons 1).cons 1) R.tail⟩ := by
  rcases fin2_cases R.head with h0 | h1
  · simp only [Tape.mk', h0, ↓reduceIte]
    exact ⟨step_right rfl L R.tail, step_right rfl (L.cons 1) R.tail⟩
  · simp only [Tape.mk', h1, show (1 : Fin 2) = 0 ↔ False by decide, ↓reduceIte]
    exact ⟨step_right rfl L R.tail, step_right rfl (L.cons 1) R.tail⟩

/-- At `State 13 (N)`, for ANY `L R`, 1 step of `reference` from `Tape.mk' L R`
matches 2 steps of `edited` from `Tape.mk' (L.cons 1) R`, transferring the extra `.cons 1`
from `L` back to `R` (`(R.tail.cons 0).cons 1`) in state `q' ∈ {14, 20}`! -/
theorem sim_state13 (L R : ListBlank (Fin 2)) :
    let q' : Fin 25 := if R.head = 0 then 14 else 20
    step reference ⟨13, Tape.mk' L R⟩ =
      some ⟨q', ⟨L.head, L.tail, (R.tail.cons 0)⟩⟩ ∧
    Reaches₁ (step edited) ⟨13, Tape.mk' (L.cons 1) R⟩
      ⟨q', ⟨L.head, L.tail, (R.tail.cons 0).cons 1⟩⟩ := by
  rcases fin2_cases R.head with h0 | h1
  · simp only [Tape.mk', h0, ↓reduceIte]
    exact ⟨step_left rfl L R.tail,
      Relation.TransGen.head (step_left_cons (q' := 14) rfl L R.tail)
        (Relation.TransGen.single (step_left rfl L (R.tail.cons 0)))⟩
  · simp only [Tape.mk', h1, show (1 : Fin 2) = 0 ↔ False by decide, ↓reduceIte]
    exact ⟨step_left rfl L R.tail,
      Relation.TransGen.head (step_left_cons (q' := 20) rfl L R.tail)
        (Relation.TransGen.single (step_left rfl L (R.tail.cons 0)))⟩

/-- In `State 14 (O)` or `State 20 (U)` when `head = 1`, 1 step of `reference`
from `⟨1, L, R⟩` matches 1 step of `edited` from `⟨1, L, R.cons 1⟩`, preserving `.cons 1` on `R`! -/
theorem sim_state14_one (L R : ListBlank (Fin 2)) :
    step reference ⟨14, ⟨1, L, R⟩⟩ = some ⟨14, ⟨L.head, L.tail, R.cons 1⟩⟩ ∧
    step edited ⟨14, ⟨1, L, R.cons 1⟩⟩ = some ⟨14, ⟨L.head, L.tail, (R.cons 1).cons 1⟩⟩ :=
  ⟨step_left rfl L R, step_left rfl L (R.cons 1)⟩

theorem sim_state20_one (L R : ListBlank (Fin 2)) :
    step reference ⟨20, ⟨1, L, R⟩⟩ = some ⟨20, ⟨L.head, L.tail, R.cons 1⟩⟩ ∧
    step edited ⟨20, ⟨1, L, R.cons 1⟩⟩ = some ⟨20, ⟨L.head, L.tail, (R.cons 1).cons 1⟩⟩ :=
  ⟨step_left rfl L R, step_left rfl L (R.cons 1)⟩

/-- At `State 24 (Y)` when `head = 0` (at `c + 1`) and `R = R'.cons 1`,
2 steps of `reference` (`24 -> 4 -> 6`) and 2 steps of `edited` (`24 -> 4 -> 6`)
preserve the exact zipper relation `Tape.mk' L_new R'` vs `Tape.mk' L_new (R'.cons 1)`
at `State 6`! -/
theorem sim_state24_to_6 (L R' : ListBlank (Fin 2)) :
    nSteps reference 2 ⟨24, ⟨0, L, R'.cons 1⟩⟩ =
      some ⟨6, Tape.mk' ((L.cons 1).cons 1) R'⟩ ∧
    nSteps edited 2 ⟨24, ⟨0, L, (R'.cons 1).cons 1⟩⟩ =
      some ⟨6, Tape.mk' ((L.cons 1).cons 1) (R'.cons 1)⟩ := by
  constructor
  · exact step_nSteps (step_right_cons (q' := 4) rfl L R')
      (step_one (step_right (q' := 6) rfl (L.cons 1) R'))
  · exact step_nSteps (step_right_cons (q' := 4) rfl L (R'.cons 1))
      (step_one (step_right (q' := 6) rfl (L.cons 1) (R'.cons 1)))

/-- Universal divisor-entry theorem for ALL `d = k + 2 >= 2`:
From `State 6 (G)` on `1`, `reference` takes `k + 6` steps (`6->7->8*->9->10`)
and `edited` takes `3*k + 14` steps (`6->7->22*->10->11*->12->13->20->21->9*->10`)
to reach `State 10 (K)` in exact `LeftOfMid (List.replicate k 0 ++ [1])` lockstep! -/
theorem sim_state6_d_ref (k : ℕ) (L_base R_rest : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    let R_mid := R_rest.cons 0
    nSteps reference (2 + ((k + 2) + 2)) ⟨6, Tape.mk' (L_cnt.cons 1) (R_rest.cons 1)⟩ =
      some ⟨10, Tape.mk' ((L_base.cons 0).cons 1)
        (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) R_mid)⟩ := by
  dsimp only
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
      (step_one (step_mkL_left (b := 1) (q' := 8) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 8) (a := 1) (b := 0) rfl (k + 2) _ _) ?_
  rw [List.replicate_succ, List.replicate_succ, ListBlank.append, ListBlank.append]
  refine step_nSteps (step_mkL_right (b := 0) (q' := 9) rfl _ _) ?_
  apply step_one
  simpa [ListBlank.append_assoc] using
    step_mk'_right (M := reference) (q := 9) (q' := 10) (a := 0) (b := 1) rfl
      (L_base.cons 0) (ListBlank.append (0 :: List.replicate k 0) ((R_rest.cons 0).cons 1))

theorem sim_state6_d_edit (k : ℕ) (L_base R_rest : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    let R_mid := R_rest.cons 0
    nSteps edited (2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + 1))))))
      ⟨6, Tape.mk' (L_cnt.cons 1) ((R_rest.cons 1).cons 1)⟩ =
      some ⟨10, Tape.mk' ((L_base.cons 0).cons 1)
        (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) (R_mid.cons 1))⟩ := by
  dsimp only
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
      (step_one (step_mkL_left (b := 1) (q' := 22) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 22) (a := 1) (b := 0) rfl (k + 2) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 0) (q' := 10) rfl _ _)
      (step_one (step_mk'_right (b := 0) (q' := 11) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 11) (a := 0) (b := 1) rfl (k + 1) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_right (b := 0) (q' := 12) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 13) rfl _ _)
        (step_nSteps (step_mk'_left (b := 0) (q' := 20) rfl _ _)
          (step_nSteps (step_mkL_left (b := 1) (q' := 20) rfl _ _)
            (step_nSteps (step_mkL_left (b := 1) (q' := 21) rfl _ _)
              (step_one (step_mkL_left (b := 0) (q' := 9) rfl _ _))))))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 9) (a := 1) (b := 0) rfl k _ _) ?_
  rw [append_replicate_cons, List.replicate_succ, ListBlank.append]
  apply step_one
  simpa [ListBlank.append_assoc] using
    step_mkL_right (M := edited) (q := 9) (q' := 10) (a := 0) (b := 1) rfl
      (L_base.cons 0) (ListBlank.append (0 :: List.replicate k 0) (((R_rest.cons 0).cons 1).cons 1))

/-- Prime acceptance at `State 6 (G)` (`d = p - 1`):
`reference` accepts in 1 step (`6 -> 5`), while `edited` runs the final Pass 0 (`d = p - 1`)
and accepts in `3*k + 17` steps (`6->7->22*->10->11*->12->13->14->15->23*->24*->4->6->5`),
reaching `State 5 (F)` with the exact same `R_end.cons 0` and `(L_cnt.cons 1).cons 1`! -/
theorem sim_state6_accept_ref (k : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    step reference ⟨6, Tape.mk' (L_cnt.cons 1) (R_end.cons 0)⟩ =
      some ⟨5, Tape.mkL (L_cnt.cons 1) (R_end.cons 0)⟩ :=
  step_mk'_left (a := 0) (b := 0) (q' := 5) rfl _ _

theorem sim_state6_accept_edit (k : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    let L_cnt := ListBlank.append (List.replicate (k + 2) 1) (L_base.cons 0)
    nSteps edited (2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + (2 + (k + 3))))))))
      ⟨6, Tape.mk' (L_cnt.cons 1) ((R_end.cons 0).cons 1)⟩ =
      some ⟨5, Tape.mkL ((L_cnt.cons 1).cons 1) (R_end.cons 0)⟩ := by
  dsimp only
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 0) (q' := 7) rfl _ _)
      (step_one (step_mkL_left (b := 1) (q' := 22) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 22) (a := 1) (b := 0) rfl (k + 2) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 0) (q' := 10) rfl _ _)
      (step_one (step_mk'_right (b := 0) (q' := 11) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 11) (a := 0) (b := 1) rfl (k + 1) _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_right (b := 0) (q' := 12) rfl _ _)
      (step_nSteps (step_mk'_right (b := 1) (q' := 13) rfl _ _)
        (step_nSteps (step_mk'_left (b := 0) (q' := 14) rfl _ _)
          (step_nSteps (step_mkL_left (b := 1) (q' := 14) rfl _ _)
            (step_nSteps (step_mkL_left (b := 0) (q' := 15) rfl _ _)
              (step_one (step_mkL_left (b := 1) (q' := 23) rfl _ _))))))) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 23) (a := 1) (b := 1) rfl k _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right (b := 1) (q' := 24) rfl _ _)
      (step_one (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mk'_right (b := 1) (q' := 24) rfl _ _))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 24) (a := 1) (b := 1) rfl k _ _) ?_
  rw [append_replicate_cons, append_replicate_cons]
  refine step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl _ _) ?_
  refine step_nSteps (step_mk'_right (b := 1) (q' := 6) rfl _ _) ?_
  exact step_one (step_mk'_left (a := 0) (b := 0) (q' := 5) rfl _ _)

/-- Composite rejection at `State 15 (P)` (`z = d`):
2 steps of `reference` (`15 -> 7 -> 16`) and 2 steps of `edited` (`15 -> 7 -> 16`)
transition to `State 16 (Q)` preserving `.cons 1` on `R_mid`! -/
theorem sim_state15_reject (L_cnt R_mid : ListBlank (Fin 2)) :
    nSteps reference 2 ⟨15, Tape.mk' L_cnt ((R_mid.cons 0).cons 0)⟩ =
      some ⟨16, Tape.mkL (L_cnt.cons 1) (R_mid.cons 1)⟩ ∧
    nSteps edited 2 ⟨15, Tape.mk' L_cnt (((R_mid.cons 1).cons 0).cons 0)⟩ =
      some ⟨16, Tape.mkL (L_cnt.cons 1) ((R_mid.cons 1).cons 1)⟩ := by
  constructor
  · exact step_nSteps
      (step_mk'_right (M := reference) (q := 15) (a := 0) (b := 1) (q' := 7) rfl _ _)
      (step_one (step_mk'_left (M := reference) (q := 7) (a := 0) (b := 1) (q' := 16) rfl _ _))
  · exact step_nSteps (step_mk'_right (M := edited) (q := 15) (a := 0) (b := 1) (q' := 7) rfl _ _)
      (step_one (step_mk'_left (M := edited) (q := 7) (a := 0) (b := 1) (q' := 16) rfl _ _))

theorem nSteps_reaches₁ {M : Machine 25 2} {n : ℕ} {c c' : Cfg 25 2}
    (hn : 1 ≤ n) (h : nSteps M n c = some c') : Reaches₁ (step M) c c' := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [nSteps_succ, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, hstep, hrest⟩ := h
    exact Relation.TransGen.head' hstep (nSteps_reaches hrest)

theorem nSteps_det {M : Machine 25 2} {i : ℕ} {c c₁ c₂ : Cfg 25 2}
    (h₁ : nSteps M i c = some c₁) (h₂ : nSteps M i c = some c₂) : c₁ = c₂ := by
  rw [h₁] at h₂; injection h₂

theorem nSteps_split {M : Machine 25 2} {i r : ℕ} {c c' : Cfg 25 2}
    (hi : i < r) (h : nSteps M r c = some c') :
    ∃ ci ci_next,
      nSteps M i c = some ci ∧
      step M ci = some ci_next ∧
      nSteps M (i + 1) c = some ci_next ∧
      nSteps M (r - (i + 1)) ci_next = some c' := by
  have hr : r = i + (1 + (r - (i + 1))) := by omega
  rw [hr, nSteps_add] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨ci, hi_eq, hrest⟩ := h
  rw [nSteps_add] at hrest
  simp only [Option.bind_eq_some_iff] at hrest
  obtain ⟨ci_next, hstep1, hrem⟩ := hrest
  have hstep : step M ci = some ci_next := by
    simpa [nSteps_succ, Option.bind_eq_some_iff] using hstep1
  have hi1 : nSteps M (i + 1) c = some ci_next := by
    rw [nSteps_add, hi_eq, Option.bind_some, hstep1]
  exact ⟨ci, ci_next, hi_eq, hstep, hi1, hrem⟩

theorem nSteps_rem {M : Machine 25 2} {i s : ℕ} {c ci c' : Cfg 25 2}
    (hi : i ≤ s) (hi_eq : nSteps M i c = some ci) (hs_eq : nSteps M s c = some c') :
    nSteps M (s - i) ci = some c' := by
  have hs : s = i + (s - i) := by omega
  rw [hs, nSteps_add, hi_eq, Option.bind_some] at hs_eq
  exact hs_eq

def MacroStep (BaseTr : Cfg 25 2 → Cfg 25 2 → Prop) (c₁ c₂ : Cfg 25 2) : Prop :=
  ∃ r s c₁' c₂', 1 ≤ r ∧ r ≤ s ∧
    nSteps reference r c₁ = some c₁' ∧
    nSteps edited s c₂ = some c₂' ∧
    (BaseTr c₁' c₂' ∨ (step reference c₁' = none ∧ step edited c₂' = none))

def ExpandedTr (BaseTr : Cfg 25 2 → Cfg 25 2 → Prop) (c₁_curr c₂_curr : Cfg 25 2) : Prop :=
  (∃ c₁ c₂ r s c₁' c₂' i,
    BaseTr c₁ c₂ ∧ 1 ≤ r ∧ r ≤ s ∧ i < r ∧
    nSteps reference r c₁ = some c₁' ∧
    nSteps edited s c₂ = some c₂' ∧
    (BaseTr c₁' c₂' ∨ (step reference c₁' = none ∧ step edited c₂' = none)) ∧
    nSteps reference i c₁ = some c₁_curr ∧
    nSteps edited i c₂ = some c₂_curr) ∨
  (step reference c₁_curr = none ∧ step edited c₂_curr = none)

theorem base_imp_expanded {BaseTr : Cfg 25 2 → Cfg 25 2 → Prop}
    (h_macro : ∀ c₁ c₂, BaseTr c₁ c₂ → MacroStep BaseTr c₁ c₂)
    {c₁ c₂ : Cfg 25 2} (h : BaseTr c₁ c₂) : ExpandedTr BaseTr c₁ c₂ := by
  obtain ⟨r, s, c₁', c₂', hr1, hrs, href, hedit, hpost⟩ := h_macro c₁ c₂ h
  exact Or.inl ⟨c₁, c₂, r, s, c₁', c₂', 0, h, hr1, hrs, hr1, href, hedit, hpost, rfl, rfl⟩

theorem respects_expandedTr (BaseTr : Cfg 25 2 → Cfg 25 2 → Prop)
    (h_macro : ∀ c₁ c₂, BaseTr c₁ c₂ → MacroStep BaseTr c₁ c₂) :
    Respects (step reference) (step edited) (ExpandedTr BaseTr) := by
  intro c₁_curr c₂_curr hexp
  rcases hexp with ⟨c₁, c₂, r, s, c₁', c₂', i, hb, hr1, hrs, hir, href, hedit, hpost, hi1, hi2⟩ |
    ⟨hhalt1, hhalt2⟩
  · obtain ⟨ci1, ci1_next, hi1', hstep1, hi1_next, hrem1⟩ := nSteps_split hir href
    cases nSteps_det hi1 hi1'
    rw [hstep1]
    by_cases hir1 : i + 1 < r
    · obtain ⟨ci2, ci2_next, hi2', hstep2, hi2_next, _⟩ := nSteps_split (by omega : i < s) hedit
      cases nSteps_det hi2 hi2'
      refine ⟨ci2_next, ?_, Relation.TransGen.single hstep2⟩
      exact Or.inl
        ⟨c₁, c₂, r, s, c₁', c₂', i + 1, hb, hr1, hrs, hir1, href, hedit, hpost, hi1_next, hi2_next⟩
    · have hir_eq : r - (i + 1) = 0 := by omega
      rw [hir_eq, nSteps_zero] at hrem1
      injection hrem1 with h_eq1
      subst h_eq1
      have hrem2 := nSteps_rem (by omega : i ≤ s) hi2 hedit
      have hreaches2 : Reaches₁ (step edited) c₂_curr c₂' :=
        nSteps_reaches₁ (by omega : 1 ≤ s - i) hrem2
      rcases hpost with hb' | hhalt
      · exact ⟨c₂', base_imp_expanded h_macro hb', hreaches2⟩
      · exact ⟨c₂', Or.inr hhalt, hreaches2⟩
  · rw [hhalt1]
    exact hhalt2

theorem macro_eval_dom (BaseTr : Cfg 25 2 → Cfg 25 2 → Prop)
    (h_macro : ∀ c₁ c₂, BaseTr c₁ c₂ → MacroStep BaseTr c₁ c₂)
    {c₁ c₂ : Cfg 25 2} (h₀ : BaseTr c₁ c₂) :
    (eval (step edited) c₂).Dom ↔ (eval (step reference) c₁).Dom :=
  StateTransition.tr_eval_dom (respects_expandedTr BaseTr h_macro) (base_imp_expanded h_macro h₀)


/-- From `State 19 (T)` on `head = 1` (at the right end of `p1`, followed by `0` and `R_p2`),
2 steps (`19 -> 2 -> 0`) of both `reference` and `edited` reach `State 0 (A)` at `R_p2`! -/
theorem sim_state19_to_0 (L₁ L₂ R₁ R₂ : ListBlank (Fin 2)) :
    nSteps reference 2 ⟨19, ⟨1, L₁, R₁.cons 0⟩⟩ =
      some ⟨0, Tape.mk' ((L₁.cons 1).cons 0) R₁⟩ ∧
    nSteps edited 2 ⟨19, ⟨1, L₂, R₂.cons 0⟩⟩ =
      some ⟨0, Tape.mk' ((L₂.cons 1).cons 0) R₂⟩ := by
  constructor
  · exact step_nSteps (step_right_cons (q' := 2) rfl L₁ R₁)
      (step_one (step_right (q' := 0) rfl (L₁.cons 1) R₁))
  · exact step_nSteps (step_right_cons (q' := 2) rfl L₂ R₂)
      (step_one (step_right (q' := 0) rfl (L₂.cons 1) R₂))

/-- Case `p = 1` (`M = 2` in `edited`) at `State 0 (A)`:
`reference` takes 2 steps (`0 -> 3 -> 16`) and `edited` takes 3 steps (`0 -> 3 -> 4 -> 16`)
to reach `State 16 (Q)` (composite rejection of `p = 1`)! -/
theorem sim_state0_p1 (L₁ L₂ R₁ R₂ : ListBlank (Fin 2)) :
    nSteps reference 2 ⟨0, Tape.mk' L₁ ((R₁.cons 0).cons 1)⟩ =
      some ⟨16, Tape.mkL (L₁.cons 1) (R₁.cons 0)⟩ ∧
    nSteps edited 3 ⟨0, Tape.mk' L₂ (((R₂.cons 0).cons 1).cons 1)⟩ =
      some ⟨16, Tape.mkL ((L₂.cons 1).cons 1) (R₂.cons 0)⟩ := by
  constructor
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₁ (R₁.cons 0))
      (step_one (step_mk'_left (a := 0) (b := 0) (q' := 16) rfl (L₁.cons 1) R₁))
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₂ ((R₂.cons 0).cons 1))
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₂.cons 1) (R₂.cons 0))
        (step_one (step_mk'_left (a := 0) (b := 0) (q' := 16) rfl ((L₂.cons 1).cons 1) R₂)))

/-- Case `p = 2` (`M = 3` in `edited`) at `State 0 (A)`:
`reference` takes 3 steps (`0 -> 3 -> 4 -> 5`) and `edited` takes 4 steps (`0 -> 3 -> 4 -> 6 -> 5`)
to reach `State 5 (F)` (prime acceptance of `p = 2`)! -/
theorem sim_state0_p2 (L₁ L₂ R₁ R₂ : ListBlank (Fin 2)) :
    nSteps reference 3 ⟨0, Tape.mk' L₁ (((R₁.cons 0).cons 1).cons 1)⟩ =
      some ⟨5, Tape.mkL ((L₁.cons 1).cons 1) (R₁.cons 0)⟩ ∧
    nSteps edited 4 ⟨0, Tape.mk' L₂ ((((R₂.cons 0).cons 1).cons 1).cons 1)⟩ =
      some ⟨5, Tape.mkL (((L₂.cons 1).cons 1).cons 1) (R₂.cons 0)⟩ := by
  constructor
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₁ ((R₁.cons 0).cons 1))
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₁.cons 1) (R₁.cons 0))
        (step_one (step_mk'_left (a := 0) (b := 0) (q' := 5) rfl ((L₁.cons 1).cons 1) R₁)))
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₂ (((R₂.cons 0).cons 1).cons 1))
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₂.cons 1) ((R₂.cons 0).cons 1))
        (step_nSteps (step_mk'_right (b := 1) (q' := 6) rfl ((L₂.cons 1).cons 1) (R₂.cons 0))
          (step_one
            (step_mk'_left (a := 0) (b := 0) (q' := 5) rfl (((L₂.cons 1).cons 1).cons 1) R₂))))

/-- Case `p >= 3` (`M = p + 1 >= 4` in `edited`) at `State 0 (A)`:
`reference` takes 3 steps (`0 -> 3 -> 4 -> 6`) and `edited` takes 3 steps (`0 -> 3 -> 4 -> 6`)
to reach `State 6 (G)` (divisor `d = 2`, i.e., `k = 0` of `sim_state6_d`)! -/
theorem sim_state0_p_ge3 (L₁ L₂ R₁ R₂ : ListBlank (Fin 2)) :
    nSteps reference 3 ⟨0, Tape.mk' L₁ (((R₁.cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L₁.cons 1).cons 1).cons 1) R₁⟩ ∧
    nSteps edited 3 ⟨0, Tape.mk' L₂ ((((R₂.cons 1).cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (((L₂.cons 1).cons 1).cons 1) (R₂.cons 1)⟩ := by
  constructor
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₁ ((R₁.cons 1).cons 1))
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₁.cons 1) (R₁.cons 1))
        (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L₁.cons 1).cons 1) R₁)))
  · exact step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl L₂ (((R₂.cons 1).cons 1).cons 1))
      (step_nSteps (step_mk'_right (b := 1) (q' := 4) rfl (L₂.cons 1) ((R₂.cons 1).cons 1))
        (step_one (step_mk'_right (b := 1) (q' := 6) rfl ((L₂.cons 1).cons 1) (R₂.cons 1))))


/-- Universal right-block composite rejection (`State 16 ->* 17 -> 19`):
Scans `d` ones left across `p2`, writes `1` at the `0` separator (`16, 0 -> 1L17`),
and erases the rightmost `1` of `p1` (`17, 1 -> 0L19`), landing at `State 19`! -/
theorem nSteps_state16_to_19_right {M : Machine 25 2}
    (h16_1 : M.transition 16 1 = some (1, .left, 16))
    (h16_0 : M.transition 16 0 = some (1, .left, 17))
    (h17_1 : M.transition 17 1 = some (0, .left, 19))
    (d : ℕ) (L_p1 R_p2 : ListBlank (Fin 2)) :
    nSteps M (d + 2)
      ⟨16, Tape.mkL (ListBlank.append (List.replicate d 1) ((L_p1.cons 1).cons 0)) R_p2⟩ =
      some ⟨19, Tape.mkL L_p1 (((ListBlank.append (List.replicate d 1) R_p2).cons 1).cons 0)⟩ := by
  refine nSteps_bind_eq (nSteps_mkL_left_scan h16_1 d _ _) ?_
  refine step_nSteps (step_mkL_left h16_0 _ _) ?_
  exact step_one (step_mkL_left h17_1 _ _)

/-- Universal left-block composite rejection (`State 16 ->* 17 -> 10 -> 18 ->* 17 -> 19`):
Scans `d` ones left to `0` at the left of `p1`, steps `16 -> 17 -> 10 -> 18`,
scans `N + 1` ones right across `p1` to the `0` separator, writes `1` (`18, 0 -> 1L17`),
and erases the rightmost `1` of `p1` (`17, 1 -> 0L19`), landing at `State 19`! -/
theorem nSteps_state16_to_19_left {M : Machine 25 2}
    (h16_1 : M.transition 16 1 = some (1, .left, 16))
    (h16_0 : M.transition 16 0 = some (1, .left, 17))
    (h17_0 : M.transition 17 0 = some (0, .right, 10))
    (h10_1 : M.transition 10 1 = some (0, .right, 18))
    (h18_1 : M.transition 18 1 = some (1, .right, 18))
    (h18_0 : M.transition 18 0 = some (1, .left, 17))
    (h17_1 : M.transition 17 1 = some (0, .left, 19))
    (d m : ℕ) (L_blank R_p2 : ListBlank (Fin 2)) :
    nSteps M (d + (3 + ((d + m + 1) + 2)))
      ⟨16, Tape.mkL (ListBlank.append (List.replicate d 1) ((L_blank.cons 0).cons 0))
        (ListBlank.append (List.replicate (m + 1) 1) (R_p2.cons 0))⟩ =
      some ⟨19, Tape.mkL (ListBlank.append (List.replicate (d + m) 1) ((L_blank.cons 0).cons 0))
        ((R_p2.cons 1).cons 0)⟩ := by
  refine nSteps_bind_eq (nSteps_mkL_left_scan h16_1 d _ _) ?_
  have h_rep : ListBlank.append (List.replicate d 1)
      (ListBlank.append (List.replicate (m + 1) 1) (R_p2.cons 0)) =
      ListBlank.append (List.replicate (d + m + 1) 1) (R_p2.cons 0) := by
    rw [← ListBlank.append_assoc, ← List.replicate_add, Nat.add_assoc]
  rw [h_rep]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_left h16_0 _ _)
      (step_nSteps (step_mkL_right h17_0 _ _)
        (step_one (step_mk'_right h10_1 _ _)))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan h18_1 (d + m + 1) _ _) ?_
  refine step_nSteps (step_mk'_left h18_0 _ _) ?_
  rw [List.replicate_succ, ListBlank.append]
  exact step_one (step_mkL_left h17_1 _ _)

/-- Universal right-block prime acceptance (`State 5 ->* 2 ->* 0`):
Scans `P2` ones left in `State 5`, crosses the `0` separator (`5, 0 -> 0L2`),
scans `P1` ones left in `State 2`, and steps `2, 0 -> 0R0` to `State 0` at `P1`! -/
theorem nSteps_state5_to_0_right {M : Machine 25 2}
    (h5_1 : M.transition 5 1 = some (1, .left, 5))
    (h5_0 : M.transition 5 0 = some (0, .left, 2))
    (h2_1 : M.transition 2 1 = some (1, .left, 2))
    (h2_0 : M.transition 2 0 = some (0, .right, 0))
    (P1 P2 : ℕ) (L_blank R_end : ListBlank (Fin 2)) :
    nSteps M (P2 + (1 + (P1 + 1)))
      ⟨5, Tape.mkL (ListBlank.append (List.replicate P2 1)
        ((ListBlank.append (List.replicate P1 1) (L_blank.cons 0)).cons 0)) (R_end.cons 0)⟩ =
      some ⟨0, Tape.mk' (L_blank.cons 0)
        (ListBlank.append (List.replicate P1 1)
          ((ListBlank.append (List.replicate P2 1) (R_end.cons 0)).cons 0))⟩ := by
  refine nSteps_bind_eq (nSteps_mkL_left_scan h5_1 P2 _ _) ?_
  refine nSteps_bind_eq (step_one (step_mkL_left h5_0 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h2_1 P1 _ _) ?_
  exact step_one (step_mkL_right h2_0 _ _)


theorem append_replicate_add (m n : ℕ) (b : Fin 2) (L : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate m b) (ListBlank.append (List.replicate n b) L) =
      ListBlank.append (List.replicate (m + n) b) L := by
  rw [← ListBlank.append_assoc, ← List.replicate_add]

/-- Left-block prime acceptance in `reference` (`State 5 ->* 2 -> 0 -> 1 ->* 2 ->* 0`):
Merges `p1` and `p2` into `p1 + p2 + 2` ones and reaches `State 0` at the left end of
`p1' = p1 + p2 + 2` (with `p2' = 0` ones after the separator)! -/
theorem sim_state5_to_0_left_ref (p1 p2 : ℕ) (L_blank R_end : ListBlank (Fin 2)) :
    nSteps reference (p1 + (3 + (p1 + (1 + ((p1 + 1) + 1)))))
      ⟨5, Tape.mkL (ListBlank.append (List.replicate p1 1) ((L_blank.cons 0).cons 0))
        ((ListBlank.append (List.replicate p2 1) (R_end.cons 0)).cons 0)⟩ =
      some ⟨0, Tape.mk' (L_blank.cons 0)
        (ListBlank.append (List.replicate (p1 + p2 + 2) 1) (R_end.cons 0))⟩ := by
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 5) (a := 1) (b := 1) rfl p1 _ _) ?_
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_left (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
        (step_one (step_mk'_right (b := 1) (q' := 1) rfl _ _)))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 1) (a := 1) (b := 1) rfl p1 _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq (step_one (step_mk'_left (b := 1) (q' := 2) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 2) (a := 1) (b := 1) rfl (p1 + 1) _ _) ?_
  have h_merge : ListBlank.append (List.replicate (p1 + 1) 1)
      ((ListBlank.append (List.replicate p2 1) (R_end.cons 0)).cons 1) =
      ListBlank.append (List.replicate (p1 + p2 + 2) 1) (R_end.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : p1 + 1 + 1 + p2 = p1 + p2 + 2 := by omega
    rw [this]
  rw [h_merge]
  exact step_one (step_mkL_right (b := 0) (q' := 0) rfl _ _)

/-- Left-block prime acceptance in `edited`
(`State 5 ->* 2 -> 0 -> 1 ->* 18 ->* 17 -> 19 -> 2 -> 0 -> 3 -> 5 -> 2 ->* 0`):
Merges `p1 + 1` and `p2 + 1` into `(p1 + p2 + 3, 1)`, accepts `M2' = 1`, and reaches
`State 0` at the left end of `M1' = p1 + p2 + 3 = (p1 + p2 + 2) + 1`
(with `M2' = 1` after the separator)! -/
theorem sim_state5_to_0_left_edit (p1 p2 : ℕ) (L_blank R_end : ListBlank (Fin 2)) :
    nSteps edited ((p1 + 1) + (3 + ((p1 + 1) + (1 + ((p2 + 1) + (8 + ((p1 + p2 + 3) + 1)))))))
      ⟨5, Tape.mkL (ListBlank.append (List.replicate (p1 + 1) 1) ((L_blank.cons 0).cons 0))
        ((ListBlank.append (List.replicate (p2 + 1) 1) ((R_end.cons 0).cons 0)).cons 0)⟩ =
      some ⟨0, Tape.mk' (L_blank.cons 0)
        (ListBlank.append (List.replicate (p1 + p2 + 3) 1) (((R_end.cons 0).cons 1).cons 0))⟩ := by
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 5) (a := 1) (b := 1) rfl (p1 + 1) _ _) ?_
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_left (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
        (step_one (step_mk'_right (b := 1) (q' := 1) rfl _ _)))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 1) (a := 1) (b := 1) rfl (p1 + 1) _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq (step_one (step_mk'_right (b := 1) (q' := 18) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 18) (a := 1) (b := 1) rfl (p2 + 1) _ _) ?_
  have h_left : ListBlank.append (List.replicate (p2 + 1) 1)
      ((ListBlank.append (List.replicate (p1 + 1 + 1) 1) (L_blank.cons 0)).cons 1) =
      ListBlank.append (List.replicate (p1 + p2 + 4) 1) (L_blank.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : p2 + 1 + 1 + (p1 + 1 + 1) = p1 + p2 + 4 := by omega
    rw [this]
  rw [h_left]
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 1) (q' := 17) rfl _ _)
      (step_nSteps (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mkL_left (b := 0) (q' := 19) rfl _ _)
        (step_nSteps (by
          rw [List.replicate_succ, ListBlank.append]
          exact step_mkL_right (b := 1) (q' := 2) rfl _ _)
          (step_nSteps (step_mk'_right (b := 0) (q' := 0) rfl _ _)
            (step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl _ _)
              (step_nSteps (step_mk'_left (b := 0) (q' := 5) rfl _ _)
                (step_nSteps (step_mkL_left (b := 1) (q' := 5) rfl _ _)
                  (step_one (step_mkL_left (b := 0) (q' := 2) rfl _ _))))))))) ?_
  have h_rep : ((ListBlank.append (List.replicate (p1 + p2 + 2) 1) (L_blank.cons 0)).cons 1) =
      ListBlank.append (List.replicate (p1 + p2 + 3) 1) (L_blank.cons 0) := rfl
  rw [h_rep]
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 2) (a := 1) (b := 1) rfl (p1 + p2 + 3) _ _) ?_
  exact step_one (step_mkL_right (b := 0) (q' := 0) rfl _ _)


def counterTape (A B : ℕ) (L_base : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (List.replicate B 1)
    ((ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 0)

theorem nSteps_pass_11_to_13 {M : Machine 25 2}
    (h11_1 : M.transition 11 1 = some (0, .right, 12))
    (h12_1 : M.transition 12 1 = some (1, .right, 12))
    (h12_0 : M.transition 12 0 = some (1, .right, 13))
    (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M (1 + (m + 1))
      ⟨11, Tape.mk' L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ =
      some ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ := by
  refine nSteps_bind_eq (step_one (step_mk'_right h11_1 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan h12_1 m _ _) ?_
  exact step_one (step_mk'_right h12_0 _ _)

theorem nSteps_pass_13_one_to_21 {M : Machine 25 2}
    (h13_1 : M.transition 13 1 = some (0, .left, 20))
    (h20_1 : M.transition 20 1 = some (1, .left, 20))
    (h20_0 : M.transition 20 0 = some (1, .left, 21))
    (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M (1 + ((m + 1) + 1))
      ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) (R.cons 1)⟩ =
      some ⟨21, Tape.mkL L ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ := by
  refine nSteps_bind_eq (step_one (step_mk'_left h13_1 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h20_1 (m + 1) _ _) ?_
  exact step_one (step_mkL_left h20_0 _ _)

theorem nSteps_pass_13_zero_to_15 {M : Machine 25 2}
    (h13_0 : M.transition 13 0 = some (0, .left, 14))
    (h14_1 : M.transition 14 1 = some (1, .left, 14))
    (h14_0 : M.transition 14 0 = some (0, .left, 15))
    (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps M (1 + ((m + 1) + 1))
      ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) (R.cons 0)⟩ =
      some ⟨15, Tape.mkL L ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 0)⟩ := by
  refine nSteps_bind_eq (step_one (step_mk'_left h13_0 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h14_1 (m + 1) _ _) ?_
  exact step_one (step_mkL_left h14_0 _ _)

theorem nSteps_pass_21_b0_to_11 {M : Machine 25 2}
    (h21_0 : M.transition 21 0 = some (0, .left, 22))
    (h22_1 : M.transition 22 1 = some (0, .left, 22))
    (h22_0 : M.transition 22 0 = some (0, .right, 10))
    (h10_0 : M.transition 10 0 = some (0, .right, 11))
    (h11_0 : M.transition 11 0 = some (1, .right, 11))
    (A : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M (1 + (A + (2 + A)))
      ⟨21, Tape.mkL (counterTape A 0 L_base) R⟩ =
      some ⟨11, Tape.mk' (counterTape 0 A L_base) R⟩ := by
  unfold counterTape
  simp only [List.replicate_zero, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left h21_0 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h22_1 A _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right h22_0 _ _)
      (step_one (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mk'_right h10_0 _ _))) ?_
  exact nSteps_mk'_right_scan h11_0 A _ _

theorem nSteps_pass_21_bsucc_to_11 {M : Machine 25 2}
    (h21_1 : M.transition 21 1 = some (0, .left, 9))
    (h9_1 : M.transition 9 1 = some (0, .left, 9))
    (h9_0 : M.transition 9 0 = some (1, .right, 10))
    (h10_0 : M.transition 10 0 = some (0, .right, 11))
    (h11_0 : M.transition 11 0 = some (1, .right, 11))
    (A b : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M (1 + (b + (2 + b)))
      ⟨21, Tape.mkL (counterTape A (b + 1) L_base) R⟩ =
      some ⟨11, Tape.mk' (counterTape (A + 1) b L_base) R⟩ := by
  unfold counterTape
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left h21_1 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h9_1 b _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right h9_0 _ _)
      (step_one (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mk'_right h10_0 _ _))) ?_
  exact nSteps_mk'_right_scan h11_0 b _ _

theorem nSteps_pass_15_bsucc_to_6 {M : Machine 25 2}
    (h15_1 : M.transition 15 1 = some (1, .left, 23))
    (h23_1 : M.transition 23 1 = some (1, .left, 23))
    (h23_0 : M.transition 23 0 = some (1, .right, 24))
    (h24_1 : M.transition 24 1 = some (1, .right, 24))
    (h24_0 : M.transition 24 0 = some (1, .right, 4))
    (h4_1 : M.transition 4 1 = some (1, .right, 6))
    (A b : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M (1 + (b + (1 + ((b + 1) + 2))))
      ⟨15, Tape.mkL (counterTape A (b + 1) L_base) ((R.cons 1).cons 0)⟩ =
      some ⟨6, Tape.mk'
        ((ListBlank.append (List.replicate (A + b + 3) 1) (L_base.cons 0)).cons 1) R⟩ := by
  unfold counterTape
  rw [List.replicate_succ, ListBlank.append]
  refine nSteps_bind_eq (step_one (step_mkL_left h15_1 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan h23_1 b _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq (step_one (step_mkL_right h23_0 _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan h24_1 (b + 1) _ _) ?_
  have h_cnt : ListBlank.append (List.replicate (b + 1) 1)
      ((ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 1) =
      ListBlank.append (List.replicate (A + b + 2) 1) (L_base.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : b + 1 + 1 + A = A + b + 2 := by omega
    rw [this]
  rw [h_cnt]
  refine step_nSteps (step_mk'_right h24_0 _ _) ?_
  exact step_one (step_mk'_right h4_1 _ _)

theorem nSteps_pass_15_b0_to_16 {M : Machine 25 2}
    (h15_0 : M.transition 15 0 = some (1, .right, 7))
    (h7_0 : M.transition 7 0 = some (1, .left, 16))
    (h16_1 : M.transition 16 1 = some (1, .left, 16))
    (A m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps M (2 + (A + 1))
      ⟨15, Tape.mkL (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R_end.cons 0)).cons 0)⟩ =
      some ⟨16, Tape.mkL (L_base.cons 0)
        (ListBlank.append (List.replicate (A + m + 3) 1) (R_end.cons 0))⟩ := by
  unfold counterTape
  simp only [List.replicate_zero, ListBlank.append]
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_right h15_0 _ _)
      (step_one (step_mk'_left h7_0 _ _))) ?_
  have h_cnt : (ListBlank.append (List.replicate A 1) (L_base.cons 0)).cons 1 =
      ListBlank.append (List.replicate (A + 1) 1) (L_base.cons 0) := rfl
  rw [h_cnt]
  refine Eq.trans (nSteps_mkL_left_scan h16_1 (A + 1) _ _) ?_
  congr 2
  rw [append_replicate_cons, append_replicate_add]
  have : A + 1 + 1 + (m + 1) = A + m + 3 := by omega
  rw [this]


/-- One single pass of `M` from `State 11` to `State 11` when `r = r' + 1` and `B = 0`: -/
theorem nSteps_pass_11_b0 {M : Machine 25 2}
    (h11_1 : M.transition 11 1 = some (0, .right, 12))
    (h12_1 : M.transition 12 1 = some (1, .right, 12))
    (h12_0 : M.transition 12 0 = some (1, .right, 13))
    (h13_1 : M.transition 13 1 = some (0, .left, 20))
    (h20_1 : M.transition 20 1 = some (1, .left, 20))
    (h20_0 : M.transition 20 0 = some (1, .left, 21))
    (h21_0 : M.transition 21 0 = some (0, .left, 22))
    (h22_1 : M.transition 22 1 = some (0, .left, 22))
    (h22_0 : M.transition 22 0 = some (0, .right, 10))
    (h10_0 : M.transition 10 0 = some (0, .right, 11))
    (h11_0 : M.transition 11 0 = some (1, .right, 11))
    (A m : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (A + (2 + A)))))
      ⟨11, Tape.mk' (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate m 1) ((R.cons 1).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape 0 A L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 h11_1 h12_1 h12_0 m _ _)
    (nSteps_bind_eq (nSteps_pass_13_one_to_21 h13_1 h20_1 h20_0 m _ _)
      (nSteps_pass_21_b0_to_11 h21_0 h22_1 h22_0 h10_0 h11_0 A _ _))

/-- One single pass of `M` from `State 11` to `State 11` when `r = r' + 1` and `B = b + 1`: -/
theorem nSteps_pass_11_bsucc {M : Machine 25 2}
    (h11_1 : M.transition 11 1 = some (0, .right, 12))
    (h12_1 : M.transition 12 1 = some (1, .right, 12))
    (h12_0 : M.transition 12 0 = some (1, .right, 13))
    (h13_1 : M.transition 13 1 = some (0, .left, 20))
    (h20_1 : M.transition 20 1 = some (1, .left, 20))
    (h20_0 : M.transition 20 0 = some (1, .left, 21))
    (h21_1 : M.transition 21 1 = some (0, .left, 9))
    (h9_1 : M.transition 9 1 = some (0, .left, 9))
    (h9_0 : M.transition 9 0 = some (1, .right, 10))
    (h10_0 : M.transition 10 0 = some (0, .right, 11))
    (h11_0 : M.transition 11 0 = some (1, .right, 11))
    (A b m : ℕ) (L_base R : ListBlank (Fin 2)) :
    nSteps M ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (2 + b)))))
      ⟨11, Tape.mk' (counterTape A (b + 1) L_base)
        ((ListBlank.append (List.replicate m 1) ((R.cons 1).cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape (A + 1) b L_base)
        ((ListBlank.append (List.replicate (m + 1) 1) (R.cons 0)).cons 1)⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 h11_1 h12_1 h12_0 m _ _)
    (nSteps_bind_eq (nSteps_pass_13_one_to_21 h13_1 h20_1 h20_0 m _ _)
      (nSteps_pass_21_bsucc_to_11 h21_1 h9_1 h9_0 h10_0 h11_0 A b _ _))

/-- Complete final pass of `M` from `State 11` to `State 6` when `r = 0` and `B = b + 1`: -/
theorem nSteps_pass_11_to_6 {M : Machine 25 2}
    (h11_1 : M.transition 11 1 = some (0, .right, 12))
    (h12_1 : M.transition 12 1 = some (1, .right, 12))
    (h12_0 : M.transition 12 0 = some (1, .right, 13))
    (h13_0 : M.transition 13 0 = some (0, .left, 14))
    (h14_1 : M.transition 14 1 = some (1, .left, 14))
    (h14_0 : M.transition 14 0 = some (0, .left, 15))
    (h15_1 : M.transition 15 1 = some (1, .left, 23))
    (h23_1 : M.transition 23 1 = some (1, .left, 23))
    (h23_0 : M.transition 23 0 = some (1, .right, 24))
    (h24_1 : M.transition 24 1 = some (1, .right, 24))
    (h24_0 : M.transition 24 0 = some (1, .right, 4))
    (h4_1 : M.transition 4 1 = some (1, .right, 6))
    (A b m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps M ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (1 + (b + (1 + ((b + 1) + 2))))))
      ⟨11, Tape.mk' (counterTape A (b + 1) L_base)
        ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
      some ⟨6, Tape.mk' ((ListBlank.append (List.replicate (A + b + 3) 1) (L_base.cons 0)).cons 1)
        (ListBlank.append (List.replicate m 1) (R_end.cons 0))⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 h11_1 h12_1 h12_0 m _ _)
    (nSteps_bind_eq (nSteps_pass_13_zero_to_15 h13_0 h14_1 h14_0 m _ _)
      (nSteps_pass_15_bsucc_to_6 h15_1 h23_1 h23_0 h24_1 h24_0 h4_1 A b _ _))

/-- Complete final pass of `M` from `State 11` to `State 16` when `r = 0` and `B = 0`: -/
theorem nSteps_pass_11_to_16 {M : Machine 25 2}
    (h11_1 : M.transition 11 1 = some (0, .right, 12))
    (h12_1 : M.transition 12 1 = some (1, .right, 12))
    (h12_0 : M.transition 12 0 = some (1, .right, 13))
    (h13_0 : M.transition 13 0 = some (0, .left, 14))
    (h14_1 : M.transition 14 1 = some (1, .left, 14))
    (h14_0 : M.transition 14 0 = some (0, .left, 15))
    (h15_0 : M.transition 15 0 = some (1, .right, 7))
    (h7_0 : M.transition 7 0 = some (1, .left, 16))
    (h16_1 : M.transition 16 1 = some (1, .left, 16))
    (A m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    nSteps M ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (2 + (A + 1))))
      ⟨11, Tape.mk' (counterTape A 0 L_base)
        ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
      some ⟨16, Tape.mkL (L_base.cons 0)
        (ListBlank.append (List.replicate (A + m + 3) 1) (R_end.cons 0))⟩ :=
  nSteps_bind_eq (nSteps_pass_11_to_13 h11_1 h12_1 h12_0 m _ _)
    (nSteps_bind_eq (nSteps_pass_13_zero_to_15 h13_0 h14_1 h14_0 m _ _)
      (nSteps_pass_15_b0_to_16 h15_0 h7_0 h16_1 A m _ _))


/-- Double-pass induction for `edited` dividing an even block `2 * w` by `d = 2`:
Each iteration consumes two `1`s from `2 * w`, flips
`counterTape 1 0` -> `counterTape 0 1` -> `counterTape 1 0`,
and adds two `1`s to the middle block `m` (`m -> m + 2`)! -/
theorem edited_even_div2_loop (w m : ℕ) (L_base R_end : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧
      nSteps edited s
        ⟨11, Tape.mk' (counterTape 1 0 L_base)
          ((ListBlank.append (List.replicate m 1)
            ((ListBlank.append (List.replicate (2 * w) 1) (R_end.cons 0)).cons 0)).cons 1)⟩ =
        some ⟨16, Tape.mkL (L_base.cons 0)
          (ListBlank.append (List.replicate (m + 2 * w + 4) 1) (R_end.cons 0))⟩ := by
  induction w generalizing m with
  | zero =>
    simp only [Nat.mul_zero, List.replicate_zero, ListBlank.append, Nat.add_zero]
    have h_fin : nSteps edited ((1 + (m + 1)) + ((1 + ((m + 1) + 1)) + (2 + (1 + 1))))
        ⟨11, Tape.mk' (counterTape 1 0 L_base)
          ((ListBlank.append (List.replicate m 1) ((R_end.cons 0).cons 0)).cons 1)⟩ =
        some ⟨16, Tape.mkL (L_base.cons 0)
          (ListBlank.append (List.replicate (m + 4) 1) (R_end.cons 0))⟩ := by
      simpa [Nat.add_comm 1 (m + 3), Nat.add_left_comm, Nat.add_assoc] using
        nSteps_pass_11_to_16 (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl 1 m L_base R_end
    exact ⟨_, by omega, h_fin⟩
  | succ w ih =>
    have h_two : ListBlank.append (List.replicate (2 * (w + 1)) 1) (R_end.cons 0) =
        ((ListBlank.append (List.replicate (2 * w) 1) (R_end.cons 0)).cons 1).cons 1 := by
      rw [Nat.mul_succ, List.replicate_succ, List.replicate_succ,
        ListBlank.append, ListBlank.append]
    rw [h_two]
    have h_p1 := nSteps_pass_11_b0 (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      1 m L_base ((ListBlank.append (List.replicate (2 * w) 1) (R_end.cons 0)).cons 1)
    have h_p2 := nSteps_pass_11_bsucc (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      0 0 (m + 1) L_base (ListBlank.append (List.replicate (2 * w) 1) (R_end.cons 0))
    obtain ⟨s_rest, hs1, h_rest⟩ := ih (m + 2)
    have h_arith : m + 2 + 2 * w + 4 = m + 2 * (w + 1) + 4 := by omega
    rw [h_arith] at h_rest
    exact ⟨_, by omega, nSteps_bind_eq h_p1 (nSteps_bind_eq h_p2 h_rest)⟩


theorem edited_halts_from_19 (w : ℕ) (L_blank R_end : ListBlank (Fin 2)) :
    ∃ s c₂', 1 ≤ s ∧
      nSteps edited s
        ⟨19, Tape.mkL ((L_blank.cons 0).cons 1)
          ((ListBlank.append (List.replicate (2 * w + 5) 1) (R_end.cons 0)).cons 0)⟩ = some c₂' ∧
      step edited c₂' = none := by
  obtain ⟨s_loop, hs_loop, h_loop⟩ := edited_even_div2_loop w 1 ((L_blank.cons 0).cons 1) R_end
  have h_19_to_6 : nSteps edited (2 + 3)
      ⟨19, Tape.mkL ((L_blank.cons 0).cons 1)
        ((ListBlank.append (List.replicate (2 * w + 5) 1) (R_end.cons 0)).cons 0)⟩ =
      some ⟨6, Tape.mk' ((((((L_blank.cons 0).cons 1).cons 0).cons 1).cons 1).cons 1)
        ((ListBlank.append (List.replicate (2 * w + 1) 1) (R_end.cons 0)).cons 1)⟩ := by
    have h_rep : ListBlank.append (List.replicate (2 * w + 5) 1) (R_end.cons 0) =
        ((((ListBlank.append (List.replicate (2 * w + 1) 1)
          (R_end.cons 0)).cons 1).cons 1).cons 1).cons 1 := by
      have : 2 * w + 5 = (2 * w + 1) + 4 := by omega
      rw [this]; rfl
    rw [h_rep, Tape.mkL_cons]
    exact nSteps_bind_eq ((sim_state19_to_0 L_blank (L_blank.cons 0) R_end _).2)
      ((sim_state0_p_ge3 L_blank _ R_end _).2)
  have h_6_to_11 : nSteps edited ((2 + (0 + 2 + (2 + (0 + 1 + (6 + (0 + 1)))))) + 1)
      ⟨6, Tape.mk' ((((((L_blank.cons 0).cons 1).cons 0).cons 1).cons 1).cons 1)
        ((ListBlank.append (List.replicate (2 * w + 1) 1) (R_end.cons 0)).cons 1)⟩ =
      some ⟨11, Tape.mk' (counterTape 1 0 ((L_blank.cons 0).cons 1))
        ((ListBlank.append (List.replicate 1 1)
          ((ListBlank.append (List.replicate (2 * w) 1) (R_end.cons 0)).cons 0)).cons 1)⟩ := by
    have h_r : ListBlank.append (List.replicate (2 * w + 1) 1) (R_end.cons 0) =
        (ListBlank.append (List.replicate (2 * w) 1) (R_end.cons 0)).cons 1 := by
      rw [List.replicate_succ, ListBlank.append]
    rw [h_r]
    refine nSteps_bind_eq (sim_state6_d_edit 0 ((L_blank.cons 0).cons 1) _) ?_
    exact step_one (step_mk'_right (M := edited) (q := 10) (q' := 11) (a := 0) (b := 0) rfl _ _)
  have h_16_to_19 : nSteps edited 2
      ⟨16, Tape.mkL (((L_blank.cons 0).cons 1).cons 0)
        (ListBlank.append (List.replicate (1 + 2 * w + 4) 1) (R_end.cons 0))⟩ =
      some ⟨19, Tape.mkL (L_blank.cons 0)
        (((ListBlank.append (List.replicate (1 + 2 * w + 4) 1) (R_end.cons 0)).cons 1).cons 0)⟩ :=
    nSteps_state16_to_19_right (M := edited) rfl rfl rfl 0 (L_blank.cons 0) _
  refine ⟨_, _, by omega,
    nSteps_bind_eq h_19_to_6 (nSteps_bind_eq h_6_to_11 (nSteps_bind_eq h_loop h_16_to_19)), ?_⟩
  simp [step, Tape.mkL]; rfl


def B0 : ListBlank (Fin 2) := ListBlank.mk []

@[simp]
theorem B0_cons_zero : B0.cons 0 = B0 :=
  mk_append_replicate_zero [] 1

def LBase1 : Bool → ℕ → ListBlank (Fin 2)
  | true, q => ListBlank.append (List.replicate (q + 1) 1) B0
  | false, _ => B0

def LBase2 : Bool → ℕ → ListBlank (Fin 2)
  | true, q => ListBlank.append (List.replicate (q + 2) 1) B0
  | false, _ => B0

def REnd1 : Bool → ℕ → ListBlank (Fin 2)
  | true, _ => B0
  | false, q => ListBlank.append (List.replicate q 1) B0

def REnd2 : Bool → ℕ → ListBlank (Fin 2)
  | true, _ => B0
  | false, q => ListBlank.append (List.replicate (q + 1) 1) B0

inductive BaseTr : Cfg 25 2 → Cfg 25 2 → Prop
  | chk0 (is_right : Bool) (w q p : ℕ) (hp : 1 ≤ p)
      (hsum : q + p = 2 * w + (if is_right then 3 else 4)) :
      BaseTr
        ⟨0, Tape.mk' ((LBase1 is_right q).cons 0)
          (ListBlank.append (List.replicate p 1) ((REnd1 is_right q).cons 0))⟩
        ⟨0, Tape.mk' ((LBase2 is_right q).cons 0)
          (ListBlank.append (List.replicate (p + 1) 1) ((REnd2 is_right q).cons 0))⟩
  | chk6 (is_right : Bool) (w q k r : ℕ)
      (hsum : q + (k + 3 + r) = 2 * w + (if is_right then 3 else 4)) :
      BaseTr
        ⟨6, Tape.mk'
          ((ListBlank.append (List.replicate (k + 2) 1) ((LBase1 is_right q).cons 0)).cons 1)
          (ListBlank.append (List.replicate r 1) ((REnd1 is_right q).cons 0))⟩
        ⟨6, Tape.mk'
          ((ListBlank.append (List.replicate (k + 2) 1) ((LBase2 is_right q).cons 0)).cons 1)
          (ListBlank.append (List.replicate (r + 1) 1) ((REnd2 is_right q).cons 0))⟩
  | chk11 (is_right : Bool) (w q A B m r : ℕ) (hAB : 1 ≤ A + B)
      (hsum : q + (A + B + 3 + m + r) = 2 * w + (if is_right then 3 else 4)) :
      BaseTr
        ⟨11, Tape.mk' (counterTape A B (LBase1 is_right q))
          ((ListBlank.append (List.replicate m 1)
            ((ListBlank.append (List.replicate r 1) ((REnd1 is_right q).cons 0)).cons 0)).cons 1)⟩
        ⟨11, Tape.mk' (counterTape A B (LBase2 is_right q))
          ((ListBlank.append (List.replicate (m + 1) 1)
            ((ListBlank.append (List.replicate r 1) ((REnd2 is_right q).cons 0)).cons 0)).cons 1)⟩
  | chkExit (is_right is_prime : Bool) (w q p : ℕ) (hp : 1 ≤ p)
      (hsum : q + p = 2 * w + (if is_right then 3 else 4)) :
      BaseTr
        ⟨if is_prime then 5 else 16, Tape.mkL ((LBase1 is_right q).cons 0)
          (ListBlank.append (List.replicate p 1) ((REnd1 is_right q).cons 0))⟩
        ⟨if is_prime then 5 else 16, Tape.mkL ((LBase2 is_right q).cons 0)
          (ListBlank.append (List.replicate (p + 1) 1) ((REnd2 is_right q).cons 0))⟩


theorem macro_chk0 (is_right : Bool) (w q p : ℕ) (hp : 1 ≤ p)
    (hsum : q + p = 2 * w + (if is_right then 3 else 4)) :
    MacroStep BaseTr
      ⟨0, Tape.mk' ((LBase1 is_right q).cons 0)
        (ListBlank.append (List.replicate p 1) ((REnd1 is_right q).cons 0))⟩
      ⟨0, Tape.mk' ((LBase2 is_right q).cons 0)
        (ListBlank.append (List.replicate (p + 1) 1) ((REnd2 is_right q).cons 0))⟩ := by
  rcases Nat.eq_or_lt_of_le hp with rfl | hp2
  · -- Case p = 1:
    obtain ⟨h1, h2⟩ := sim_state0_p1 ((LBase1 is_right q).cons 0) ((LBase2 is_right q).cons 0)
      (REnd1 is_right q) (REnd2 is_right q)
    have hr : nSteps reference (2 + 1)
        ⟨0, Tape.mk' ((LBase1 is_right q).cons 0)
          (ListBlank.append (List.replicate 1 1) ((REnd1 is_right q).cons 0))⟩ =
        some ⟨16, Tape.mkL ((LBase1 is_right q).cons 0)
          (ListBlank.append (List.replicate 1 1) ((REnd1 is_right q).cons 0))⟩ :=
      nSteps_bind_eq h1 (step_one
        (step_mkL_left (M := reference) (q := 16) (q' := 16) (a := 1) (b := 1) rfl _ _))
    have hs : nSteps edited (3 + 2)
        ⟨0, Tape.mk' ((LBase2 is_right q).cons 0)
          (ListBlank.append (List.replicate 2 1) ((REnd2 is_right q).cons 0))⟩ =
        some ⟨16, Tape.mkL ((LBase2 is_right q).cons 0)
          (ListBlank.append (List.replicate 2 1) ((REnd2 is_right q).cons 0))⟩ :=
      nSteps_bind_eq h2 (step_nSteps
        (step_mkL_left (M := edited) (q := 16) (q' := 16) (a := 1) (b := 1) rfl _ _)
        (step_one (step_mkL_left (M := edited) (q := 16) (q' := 16) (a := 1) (b := 1) rfl _ _)))
    exact ⟨3, 5, _, _, by omega, by omega, hr, hs,
      Or.inl (BaseTr.chkExit is_right false w q 1 hp hsum)⟩
  · rcases Nat.eq_or_lt_of_le hp2 with rfl | hp3
    · -- Case p = 2:
      obtain ⟨h1, h2⟩ := sim_state0_p2 ((LBase1 is_right q).cons 0) ((LBase2 is_right q).cons 0)
        (REnd1 is_right q) (REnd2 is_right q)
      have hr : nSteps reference (3 + 2)
          ⟨0, Tape.mk' ((LBase1 is_right q).cons 0)
            (ListBlank.append (List.replicate 2 1) ((REnd1 is_right q).cons 0))⟩ =
          some ⟨5, Tape.mkL ((LBase1 is_right q).cons 0)
            (ListBlank.append (List.replicate 2 1) ((REnd1 is_right q).cons 0))⟩ :=
        nSteps_bind_eq h1 (step_nSteps
          (step_mkL_left (M := reference) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _)
          (step_one (step_mkL_left (M := reference) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _)))
      have hs : nSteps edited (4 + 3)
          ⟨0, Tape.mk' ((LBase2 is_right q).cons 0)
            (ListBlank.append (List.replicate 3 1) ((REnd2 is_right q).cons 0))⟩ =
          some ⟨5, Tape.mkL ((LBase2 is_right q).cons 0)
            (ListBlank.append (List.replicate 3 1) ((REnd2 is_right q).cons 0))⟩ :=
        nSteps_bind_eq h2 (step_nSteps
          (step_mkL_left (M := edited) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _)
          (step_nSteps (step_mkL_left (M := edited) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _)
            (step_one (step_mkL_left (M := edited) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _))))
      exact ⟨5, 7, _, _, by omega, by omega, hr, hs,
        Or.inl (BaseTr.chkExit is_right true w q 2 hp hsum)⟩
    · -- Case p >= 3 (p = r0 + 3):
      obtain ⟨r0, rfl⟩ : ∃ r0, p = r0 + 3 := ⟨p - 3, by omega⟩
      obtain ⟨h1, h2⟩ := sim_state0_p_ge3 ((LBase1 is_right q).cons 0) ((LBase2 is_right q).cons 0)
        (ListBlank.append (List.replicate r0 1) ((REnd1 is_right q).cons 0))
        (ListBlank.append (List.replicate r0 1) ((REnd2 is_right q).cons 0))
      have h_rep1 : (((ListBlank.append (List.replicate r0 1)
          ((REnd1 is_right q).cons 0)).cons 1).cons 1).cons 1 =
          ListBlank.append (List.replicate (r0 + 3) 1) ((REnd1 is_right q).cons 0) := rfl
      have h_rep2 : ((((ListBlank.append (List.replicate r0 1)
          ((REnd2 is_right q).cons 0)).cons 1).cons 1).cons 1).cons 1 =
          ListBlank.append (List.replicate (r0 + 3 + 1) 1) ((REnd2 is_right q).cons 0) := rfl
      rw [h_rep1] at h1
      rw [h_rep2] at h2
      exact ⟨3, 3, _, _, by omega, by omega, h1, h2,
        Or.inl (BaseTr.chk6 is_right w q 0 r0 (by omega))⟩


theorem macro_chk6 (is_right : Bool) (w q k r : ℕ)
    (hsum : q + (k + 3 + r) = 2 * w + (if is_right then 3 else 4)) :
    MacroStep BaseTr
      ⟨6, Tape.mk'
        ((ListBlank.append (List.replicate (k + 2) 1) ((LBase1 is_right q).cons 0)).cons 1)
        (ListBlank.append (List.replicate r 1) ((REnd1 is_right q).cons 0))⟩
      ⟨6, Tape.mk'
        ((ListBlank.append (List.replicate (k + 2) 1) ((LBase2 is_right q).cons 0)).cons 1)
        (ListBlank.append (List.replicate (r + 1) 1) ((REnd2 is_right q).cons 0))⟩ := by
  cases r with
  | zero =>
    simp only [List.replicate_zero, ListBlank.append]
    have h1 := sim_state6_accept_ref k (LBase1 is_right q) (REnd1 is_right q)
    have h2 := sim_state6_accept_edit k (LBase2 is_right q) (REnd2 is_right q)
    have h_cnt1 :
        (ListBlank.append (List.replicate (k + 2) 1) ((LBase1 is_right q).cons 0)).cons 1 =
        ListBlank.append (List.replicate (k + 3) 1) ((LBase1 is_right q).cons 0) := rfl
    have h_cnt2 :
        ((ListBlank.append (List.replicate (k + 2) 1) ((LBase2 is_right q).cons 0)).cons 1).cons 1 =
        ListBlank.append (List.replicate (k + 4) 1) ((LBase2 is_right q).cons 0) := rfl
    have hr : nSteps reference (1 + (k + 3))
        ⟨6, Tape.mk'
          ((ListBlank.append (List.replicate (k + 2) 1) ((LBase1 is_right q).cons 0)).cons 1)
          ((REnd1 is_right q).cons 0)⟩ =
        some ⟨5, Tape.mkL ((LBase1 is_right q).cons 0)
          (ListBlank.append (List.replicate (k + 3) 1) ((REnd1 is_right q).cons 0))⟩ := by
      refine nSteps_bind_eq (step_one h1) ?_
      rw [h_cnt1]
      exact nSteps_mkL_left_scan (M := reference) (q := 5) (a := 1) (b := 1) rfl (k + 3) _ _
    have hs :
        nSteps edited ((2 + ((k + 2) + (2 + ((k + 1) + (6 + (k + (2 + (k + 3)))))))) + (k + 4))
        ⟨6, Tape.mk'
          ((ListBlank.append (List.replicate (k + 2) 1) ((LBase2 is_right q).cons 0)).cons 1)
          (((REnd2 is_right q).cons 0).cons 1)⟩ =
        some ⟨5, Tape.mkL ((LBase2 is_right q).cons 0)
          (ListBlank.append (List.replicate (k + 4) 1) ((REnd2 is_right q).cons 0))⟩ := by
      refine nSteps_bind_eq h2 ?_
      rw [h_cnt2]
      exact nSteps_mkL_left_scan (M := edited) (q := 5) (a := 1) (b := 1) rfl (k + 4) _ _
    exact ⟨_, _, _, _, by omega, by omega, hr, hs,
      Or.inl (BaseTr.chkExit is_right true w q (k + 3) (by omega) (by omega))⟩
  | succ r' =>
    have h_rep1 : ListBlank.append (List.replicate (r' + 1) 1) ((REnd1 is_right q).cons 0) =
        (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0)).cons 1 := rfl
    have h_rep2 : ListBlank.append (List.replicate (r' + 1 + 1) 1) ((REnd2 is_right q).cons 0) =
        ((ListBlank.append (List.replicate r' 1) ((REnd2 is_right q).cons 0)).cons 1).cons 1 := rfl
    rw [h_rep1, h_rep2]
    have h1 := sim_state6_d_ref k (LBase1 is_right q)
      (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
    have h2 := sim_state6_d_edit k (LBase2 is_right q)
      (ListBlank.append (List.replicate r' 1) ((REnd2 is_right q).cons 0))
    have h10_to_11 {M : Machine 25 2}
        (h10 : M.transition 10 0 = some (0, .right, 11))
        (h11 : M.transition 11 0 = some (1, .right, 11))
        (L_b R_m : ListBlank (Fin 2)) :
        nSteps M (1 + k)
          ⟨10, Tape.mk' ((L_b.cons 0).cons 1)
            (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) R_m)⟩ =
          some ⟨11, Tape.mk' (counterTape 1 k L_b) (R_m.cons 1)⟩ := by
      rw [ListBlank.append, ListBlank.append_assoc, ListBlank.append, ListBlank.append]
      refine nSteps_bind_eq (step_one (step_mk'_right h10 _ _)) ?_
      exact nSteps_mk'_right_scan h11 k _ _
    have hr := nSteps_bind_eq h1 (h10_to_11 (M := reference) rfl rfl (LBase1 is_right q) _)
    have hs := nSteps_bind_eq h2 (h10_to_11 (M := edited) rfl rfl (LBase2 is_right q) _)
    exact ⟨_, _, _, _, by omega, by omega, hr, hs,
      Or.inl (BaseTr.chk11 is_right w q 1 k 0 r' (by omega) (by omega))⟩

theorem macro_chk11 (is_right : Bool) (w q A B m r : ℕ) (hAB : 1 ≤ A + B)
    (hsum : q + (A + B + 3 + m + r) = 2 * w + (if is_right then 3 else 4)) :
    MacroStep BaseTr
      ⟨11, Tape.mk' (counterTape A B (LBase1 is_right q))
        ((ListBlank.append (List.replicate m 1)
          ((ListBlank.append (List.replicate r 1) ((REnd1 is_right q).cons 0)).cons 0)).cons 1)⟩
      ⟨11, Tape.mk' (counterTape A B (LBase2 is_right q))
        ((ListBlank.append (List.replicate (m + 1) 1)
          ((ListBlank.append (List.replicate r 1)
            ((REnd2 is_right q).cons 0)).cons 0)).cons 1)⟩ := by
  cases r with
  | zero =>
    simp only [List.replicate_zero, ListBlank.append]
    cases B with
    | zero =>
      have hr := nSteps_pass_11_to_16 (M := reference) rfl rfl rfl rfl rfl rfl rfl rfl rfl
        A m (LBase1 is_right q) (REnd1 is_right q)
      have hs := nSteps_pass_11_to_16 (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl
        A (m + 1) (LBase2 is_right q) (REnd2 is_right q)
      have h_eq : A + (m + 1) + 3 = (A + m + 3) + 1 := by omega
      rw [h_eq] at hs
      exact ⟨_, _, _, _, by omega, by omega, hr, hs,
        Or.inl (BaseTr.chkExit is_right false w q (A + m + 3) (by omega) (by omega))⟩
    | succ b =>
      have hr := nSteps_pass_11_to_6 (M := reference)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        A b m (LBase1 is_right q) (REnd1 is_right q)
      have hs := nSteps_pass_11_to_6 (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        A b (m + 1) (LBase2 is_right q) (REnd2 is_right q)
      have h_eq : A + b + 3 = (A + b + 1) + 2 := by omega
      rw [h_eq] at hr hs
      exact ⟨_, _, _, _, by omega, by omega, hr, hs,
        Or.inl (BaseTr.chk6 is_right w q (A + b + 1) m (by omega))⟩
  | succ r' =>
    have h_rep1 : ListBlank.append (List.replicate (r' + 1) 1) ((REnd1 is_right q).cons 0) =
        (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0)).cons 1 := rfl
    have h_rep2 : ListBlank.append (List.replicate (r' + 1) 1) ((REnd2 is_right q).cons 0) =
        (ListBlank.append (List.replicate r' 1) ((REnd2 is_right q).cons 0)).cons 1 := rfl
    rw [h_rep1, h_rep2]
    cases B with
    | zero =>
      have hr := nSteps_pass_11_b0 (M := reference) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        A m (LBase1 is_right q) (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
      have hs := nSteps_pass_11_b0 (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        A (m + 1) (LBase2 is_right q)
        (ListBlank.append (List.replicate r' 1) ((REnd2 is_right q).cons 0))
      exact ⟨_, _, _, _, by omega, by omega, hr, hs,
        Or.inl (BaseTr.chk11 is_right w q 0 A (m + 1) r' (by omega) (by omega))⟩
    | succ b =>
      have hr := nSteps_pass_11_bsucc (M := reference) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        A b m (LBase1 is_right q)
        (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
      have hs := nSteps_pass_11_bsucc (M := edited) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        A b (m + 1) (LBase2 is_right q)
        (ListBlank.append (List.replicate r' 1) ((REnd2 is_right q).cons 0))
      exact ⟨_, _, _, _, by omega, by omega, hr, hs,
        Or.inl (BaseTr.chk11 is_right w q (A + 1) b (m + 1) r' (by omega) (by omega))⟩




theorem sim_state19_to_0_mkL (L₁ L₂ R₁ R₂ : ListBlank (Fin 2)) :
    nSteps reference 2 ⟨19, Tape.mkL (L₁.cons 1) (R₁.cons 0)⟩ =
      some ⟨0, Tape.mk' ((L₁.cons 1).cons 0) R₁⟩ ∧
    nSteps edited 2 ⟨19, Tape.mkL (L₂.cons 1) (R₂.cons 0)⟩ =
      some ⟨0, Tape.mk' ((L₂.cons 1).cons 0) R₂⟩ := by
  simp only [Tape.mkL_cons]
  exact sim_state19_to_0 L₁ L₂ R₁ R₂

theorem macro_chkExit_ff (w q p : ℕ) (hp : 1 ≤ p)
    (hsum : q + p = 2 * w + (if false = true then 3 else 4)) :
    MacroStep BaseTr
      ⟨16, Tape.mkL ((LBase1 false q).cons 0)
        (ListBlank.append (List.replicate p 1) ((REnd1 false q).cons 0))⟩
      ⟨16, Tape.mkL ((LBase2 false q).cons 0)
        (ListBlank.append (List.replicate (p + 1) 1) ((REnd2 false q).cons 0))⟩ := by
  simp only [Bool.false_eq_true, ↓reduceIte] at hsum
  simp only [LBase1, LBase2, REnd1, REnd2, B0_cons_zero]
  rcases Nat.eq_or_lt_of_le hp with rfl | hp2
  · have hq : q = 2 * w + 3 := by omega
    subst hq
    have hr : nSteps reference 6
        ⟨16, Tape.mkL B0
          (ListBlank.append (List.replicate 1 1)
            ((ListBlank.append (List.replicate (2 * w + 3) 1) B0).cons 0))⟩ =
        some ⟨19, Tape.mkL B0
          ((ListBlank.append (List.replicate (2 * w + 4) 1) B0).cons 0)⟩ := by
      simpa [B0_cons_zero, List.replicate_succ, ListBlank.append] using
        nSteps_state16_to_19_left (M := reference) rfl rfl rfl rfl rfl rfl rfl 0 0 B0
          (ListBlank.append (List.replicate (2 * w + 3) 1) B0)
    have hs1 : nSteps edited 7
        ⟨16, Tape.mkL B0
          (ListBlank.append (List.replicate 2 1)
            ((ListBlank.append (List.replicate (2 * w + 4) 1) B0).cons 0))⟩ =
        some ⟨19, Tape.mkL ((B0.cons 0).cons 1)
          ((ListBlank.append (List.replicate (2 * w + 5) 1) (B0.cons 0)).cons 0)⟩ := by
      simpa [B0_cons_zero, List.replicate_succ, ListBlank.append, Tape.mkL] using
        nSteps_state16_to_19_left (M := edited) rfl rfl rfl rfl rfl rfl rfl 0 1 B0
          (ListBlank.append (List.replicate (2 * w + 4) 1) B0)
    obtain ⟨s_halt, c₂', hs_halt1, hs_halt2, h_none2⟩ := edited_halts_from_19 w B0 B0
    have h_none1 : step reference ⟨19, Tape.mkL B0
        ((ListBlank.append (List.replicate (2 * w + 4) 1) B0).cons 0)⟩ = none := by
      rw [← B0_cons_zero]; simp [step, Tape.mkL]; rfl
    exact ⟨6, 7 + s_halt, _, c₂', by omega, by omega, hr, nSteps_bind_eq hs1 hs_halt2,
      Or.inr ⟨h_none1, h_none2⟩⟩
  · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
    have hr1 : nSteps reference (p' + 7)
        ⟨16, Tape.mkL B0
          (ListBlank.append (List.replicate (p' + 2) 1)
            ((ListBlank.append (List.replicate q 1) B0).cons 0))⟩ =
        some ⟨19, Tape.mkL (ListBlank.append (List.replicate (p' + 1) 1) B0)
          ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0)⟩ := by
      simpa [B0_cons_zero, List.replicate_succ, ListBlank.append,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        nSteps_state16_to_19_left (M := reference) rfl rfl rfl rfl rfl rfl rfl 0 (p' + 1) B0
          (ListBlank.append (List.replicate q 1) B0)
    have hs1 : nSteps edited (p' + 8)
        ⟨16, Tape.mkL B0
          (ListBlank.append (List.replicate (p' + 3) 1)
            ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0))⟩ =
        some ⟨19, Tape.mkL (ListBlank.append (List.replicate (p' + 2) 1) B0)
          ((ListBlank.append (List.replicate (q + 2) 1) B0).cons 0)⟩ := by
      simpa [B0_cons_zero, List.replicate_succ, ListBlank.append,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        nSteps_state16_to_19_left (M := edited) rfl rfl rfl rfl rfl rfl rfl 0 (p' + 2) B0
          (ListBlank.append (List.replicate (q + 1) 1) B0)
    obtain ⟨hr2, hs2⟩ := sim_state19_to_0_mkL
      (ListBlank.append (List.replicate p' 1) B0)
      (ListBlank.append (List.replicate (p' + 1) 1) B0)
      (ListBlank.append (List.replicate (q + 1) 1) B0)
      (ListBlank.append (List.replicate (q + 2) 1) B0)
    have h_chk0 : BaseTr
        ⟨0, Tape.mk' (((ListBlank.append (List.replicate p' 1) B0).cons 1).cons 0)
          (ListBlank.append (List.replicate (q + 1) 1) B0)⟩
        ⟨0, Tape.mk' (((ListBlank.append (List.replicate (p' + 1) 1) B0).cons 1).cons 0)
          (ListBlank.append (List.replicate (q + 2) 1) B0)⟩ := by
      simpa [LBase1, LBase2, REnd1, REnd2, B0_cons_zero,
          List.replicate_succ, ListBlank.append] using
        BaseTr.chk0 true w p' (q + 1) (by omega) (by simp; omega)
    exact ⟨(p' + 7) + 2, (p' + 8) + 2, _, _, by omega, by omega,
      nSteps_bind_eq hr1 hr2, nSteps_bind_eq hs1 hs2, Or.inl h_chk0⟩

theorem macro_chkExit_tf (w q p : ℕ) (hp : 1 ≤ p)
    (hsum : q + p = 2 * w + (if true = true then 3 else 4)) :
    MacroStep BaseTr
      ⟨16, Tape.mkL ((LBase1 true q).cons 0)
        (ListBlank.append (List.replicate p 1) ((REnd1 true q).cons 0))⟩
      ⟨16, Tape.mkL ((LBase2 true q).cons 0)
        (ListBlank.append (List.replicate (p + 1) 1) ((REnd2 true q).cons 0))⟩ := by
  simp only [↓reduceIte] at hsum
  simp only [LBase1, LBase2, REnd1, REnd2, B0_cons_zero]
  cases q with
  | zero =>
    have hp_eq : p = 2 * w + 3 := by omega
    subst hp_eq
    have hr : nSteps reference 2
        ⟨16, Tape.mkL ((B0.cons 1).cons 0)
          (ListBlank.append (List.replicate (2 * w + 3) 1) B0)⟩ =
        some ⟨19, Tape.mkL B0
          (((ListBlank.append (List.replicate (2 * w + 3) 1) B0).cons 1).cons 0)⟩ :=
      nSteps_state16_to_19_right (M := reference) rfl rfl rfl 0 B0 _
    have hs1 : nSteps edited 2
        ⟨16, Tape.mkL (((B0.cons 1).cons 1).cons 0)
          (ListBlank.append (List.replicate (2 * w + 4) 1) B0)⟩ =
        some ⟨19, Tape.mkL ((B0.cons 0).cons 1)
          ((ListBlank.append (List.replicate (2 * w + 5) 1) (B0.cons 0)).cons 0)⟩ := by
      simpa [B0_cons_zero, List.replicate_succ, ListBlank.append, Tape.mkL] using
        nSteps_state16_to_19_right (M := edited) rfl rfl rfl 0 (B0.cons 1)
          (ListBlank.append (List.replicate (2 * w + 4) 1) B0)
    obtain ⟨s_halt, c₂', hs_halt1, hs_halt2, h_none2⟩ := edited_halts_from_19 w B0 B0
    have h_none1 : step reference ⟨19, Tape.mkL B0
        (((ListBlank.append (List.replicate (2 * w + 3) 1) B0).cons 1).cons 0)⟩ = none := by
      rw [← B0_cons_zero]; simp [step, Tape.mkL]; rfl
    exact ⟨2, 2 + s_halt, _, c₂', by omega, by omega, hr, nSteps_bind_eq hs1 hs_halt2,
      Or.inr ⟨h_none1, h_none2⟩⟩
  | succ q' =>
    have hr1 := nSteps_state16_to_19_right (M := reference) rfl rfl rfl 0
      (ListBlank.append (List.replicate (q' + 1) 1) B0)
      (ListBlank.append (List.replicate p 1) B0)
    have hs1 := nSteps_state16_to_19_right (M := edited) rfl rfl rfl 0
      (ListBlank.append (List.replicate (q' + 2) 1) B0)
      (ListBlank.append (List.replicate (p + 1) 1) B0)
    obtain ⟨hr2, hs2⟩ := sim_state19_to_0_mkL
      (ListBlank.append (List.replicate q' 1) B0)
      (ListBlank.append (List.replicate (q' + 1) 1) B0)
      (ListBlank.append (List.replicate (p + 1) 1) B0)
      (ListBlank.append (List.replicate (p + 2) 1) B0)
    have h_chk0 : BaseTr
        ⟨0, Tape.mk' (((ListBlank.append (List.replicate q' 1) B0).cons 1).cons 0)
          (ListBlank.append (List.replicate (p + 1) 1) B0)⟩
        ⟨0, Tape.mk' (((ListBlank.append (List.replicate (q' + 1) 1) B0).cons 1).cons 0)
          (ListBlank.append (List.replicate (p + 2) 1) B0)⟩ := by
      simpa [LBase1, LBase2, REnd1, REnd2, B0_cons_zero,
          List.replicate_succ, ListBlank.append] using
        BaseTr.chk0 true w q' (p + 1) (by omega) (by simp; omega)
    exact ⟨2 + 2, 2 + 2, _, _, by omega, by omega,
      nSteps_bind_eq hr1 hr2, nSteps_bind_eq hs1 hs2, Or.inl h_chk0⟩

theorem macro_chkExit_tt (w q p : ℕ) (_hp : 1 ≤ p)
    (hsum : q + p = 2 * w + (if true = true then 3 else 4)) :
    MacroStep BaseTr
      ⟨5, Tape.mkL ((LBase1 true q).cons 0)
        (ListBlank.append (List.replicate p 1) ((REnd1 true q).cons 0))⟩
      ⟨5, Tape.mkL ((LBase2 true q).cons 0)
        (ListBlank.append (List.replicate (p + 1) 1) ((REnd2 true q).cons 0))⟩ := by
  simp only [↓reduceIte] at hsum
  simp only [LBase1, LBase2, REnd1, REnd2, B0_cons_zero]
  have h_scan {M : Machine 25 2}
      (h5_0 : M.transition 5 0 = some (0, .left, 2))
      (h2_1 : M.transition 2 1 = some (1, .left, 2))
      (h2_0 : M.transition 2 0 = some (0, .right, 0))
      (Q P : ℕ) :
      nSteps M (1 + (Q + 1))
        ⟨5, Tape.mkL ((ListBlank.append (List.replicate Q 1) (B0.cons 0)).cons 0)
          (ListBlank.append (List.replicate P 1) B0)⟩ =
        some ⟨0, Tape.mk' (B0.cons 0)
          (ListBlank.append (List.replicate Q 1)
            ((ListBlank.append (List.replicate P 1) B0).cons 0))⟩ := by
    refine nSteps_bind_eq (step_one (step_mkL_left h5_0 _ _)) ?_
    refine nSteps_bind_eq (nSteps_mkL_left_scan h2_1 Q _ _) ?_
    exact step_one (step_mkL_right h2_0 _ _)
  have hr : nSteps reference (1 + ((q + 1) + 1))
      ⟨5, Tape.mkL ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0)
        (ListBlank.append (List.replicate p 1) B0)⟩ =
      some ⟨0, Tape.mk' ((LBase1 false p).cons 0)
        (ListBlank.append (List.replicate (q + 1) 1) ((REnd1 false p).cons 0))⟩ := by
    simpa [LBase1, REnd1, B0_cons_zero] using h_scan (M := reference) rfl rfl rfl (q + 1) p
  have hs : nSteps edited (1 + ((q + 2) + 1))
      ⟨5, Tape.mkL ((ListBlank.append (List.replicate (q + 2) 1) B0).cons 0)
        (ListBlank.append (List.replicate (p + 1) 1) B0)⟩ =
      some ⟨0, Tape.mk' ((LBase2 false p).cons 0)
        (ListBlank.append (List.replicate (q + 2) 1) ((REnd2 false p).cons 0))⟩ := by
    simpa [LBase2, REnd2, B0_cons_zero] using h_scan (M := edited) rfl rfl rfl (q + 2) (p + 1)
  exact ⟨_, _, _, _, by omega, by omega, hr, hs,
    Or.inl (BaseTr.chk0 false w p (q + 1) (by omega) (by simp; omega))⟩


theorem sim_state5_to_0_left_from_0_ref (p1 p2 : ℕ) (L_blank R_end : ListBlank (Fin 2)) :
    nSteps reference (3 + (p1 + (1 + ((p1 + 1) + 1))))
      ⟨5, Tape.mkL ((L_blank.cons 0).cons 0)
        (ListBlank.append (List.replicate p1 1)
          ((ListBlank.append (List.replicate p2 1) (R_end.cons 0)).cons 0))⟩ =
      some ⟨0, Tape.mk' (L_blank.cons 0)
        (ListBlank.append (List.replicate (p1 + p2 + 2) 1) (R_end.cons 0))⟩ := by
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_left (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
        (step_one (step_mk'_right (b := 1) (q' := 1) rfl _ _)))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 1) (a := 1) (b := 1) rfl p1 _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq (step_one (step_mk'_left (b := 1) (q' := 2) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 2) (a := 1) (b := 1) rfl (p1 + 1) _ _) ?_
  have h_merge : ListBlank.append (List.replicate (p1 + 1) 1)
      ((ListBlank.append (List.replicate p2 1) (R_end.cons 0)).cons 1) =
      ListBlank.append (List.replicate (p1 + p2 + 2) 1) (R_end.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : p1 + 1 + 1 + p2 = p1 + p2 + 2 := by omega
    rw [this]
  rw [h_merge]
  exact step_one (step_mkL_right (b := 0) (q' := 0) rfl _ _)

theorem sim_state5_to_0_left_from_0_edit (p1 p2 : ℕ) (L_blank R_end : ListBlank (Fin 2)) :
    nSteps edited (3 + ((p1 + 1) + (1 + ((p2 + 1) + (8 + ((p1 + p2 + 3) + 1))))))
      ⟨5, Tape.mkL ((L_blank.cons 0).cons 0)
        (ListBlank.append (List.replicate (p1 + 1) 1)
          ((ListBlank.append (List.replicate (p2 + 1) 1) ((R_end.cons 0).cons 0)).cons 0))⟩ =
      some ⟨0, Tape.mk' (L_blank.cons 0)
        (ListBlank.append (List.replicate (p1 + p2 + 3) 1) (((R_end.cons 0).cons 1).cons 0))⟩ := by
  refine nSteps_bind_eq
    (step_nSteps (step_mkL_left (b := 0) (q' := 2) rfl _ _)
      (step_nSteps (step_mkL_right (b := 0) (q' := 0) rfl _ _)
        (step_one (step_mk'_right (b := 1) (q' := 1) rfl _ _)))) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 1) (a := 1) (b := 1) rfl (p1 + 1) _ _) ?_
  rw [append_replicate_cons]
  refine nSteps_bind_eq (step_one (step_mk'_right (b := 1) (q' := 18) rfl _ _)) ?_
  refine nSteps_bind_eq (nSteps_mk'_right_scan (q := 18) (a := 1) (b := 1) rfl (p2 + 1) _ _) ?_
  have h_left : ListBlank.append (List.replicate (p2 + 1) 1)
      ((ListBlank.append (List.replicate (p1 + 1 + 1) 1) (L_blank.cons 0)).cons 1) =
      ListBlank.append (List.replicate (p1 + p2 + 4) 1) (L_blank.cons 0) := by
    rw [append_replicate_cons, append_replicate_add]
    have : p2 + 1 + 1 + (p1 + 1 + 1) = p1 + p2 + 4 := by omega
    rw [this]
  rw [h_left]
  refine nSteps_bind_eq
    (step_nSteps (step_mk'_left (b := 1) (q' := 17) rfl _ _)
      (step_nSteps (by
        rw [List.replicate_succ, ListBlank.append]
        exact step_mkL_left (b := 0) (q' := 19) rfl _ _)
        (step_nSteps (by
          rw [List.replicate_succ, ListBlank.append]
          exact step_mkL_right (b := 1) (q' := 2) rfl _ _)
          (step_nSteps (step_mk'_right (b := 0) (q' := 0) rfl _ _)
            (step_nSteps (step_mk'_right (b := 1) (q' := 3) rfl _ _)
              (step_nSteps (step_mk'_left (b := 0) (q' := 5) rfl _ _)
                (step_nSteps (step_mkL_left (b := 1) (q' := 5) rfl _ _)
                  (step_one (step_mkL_left (b := 0) (q' := 2) rfl _ _))))))))) ?_
  have h_rep : ((ListBlank.append (List.replicate (p1 + p2 + 2) 1) (L_blank.cons 0)).cons 1) =
      ListBlank.append (List.replicate (p1 + p2 + 3) 1) (L_blank.cons 0) := rfl
  rw [h_rep]
  refine nSteps_bind_eq (nSteps_mkL_left_scan (q := 2) (a := 1) (b := 1) rfl (p1 + p2 + 3) _ _) ?_
  exact step_one (step_mkL_right (b := 0) (q' := 0) rfl _ _)

theorem macro_chkExit_ft (w q p : ℕ) (_hp : 1 ≤ p)
    (hsum : q + p = 2 * w + (if false = true then 3 else 4)) :
    MacroStep BaseTr
      ⟨5, Tape.mkL ((LBase1 false q).cons 0)
        (ListBlank.append (List.replicate p 1) ((REnd1 false q).cons 0))⟩
      ⟨5, Tape.mkL ((LBase2 false q).cons 0)
        (ListBlank.append (List.replicate (p + 1) 1) ((REnd2 false q).cons 0))⟩ := by
  simp only [Bool.false_eq_true, ↓reduceIte] at hsum
  have hr := sim_state5_to_0_left_from_0_ref p q B0 B0
  have hs := sim_state5_to_0_left_from_0_edit p q B0 B0
  simp only [B0_cons_zero] at hr hs
  simp only [LBase1, LBase2, REnd1, REnd2, B0_cons_zero]
  have h_chk0 : BaseTr
      ⟨0, Tape.mk' B0 (ListBlank.append (List.replicate (p + q + 2) 1) B0)⟩
      ⟨0, Tape.mk' B0 (ListBlank.append (List.replicate (p + q + 3) 1) ((B0.cons 1).cons 0))⟩ := by
    simpa [LBase1, LBase2, REnd1, REnd2, B0_cons_zero] using
      BaseTr.chk0 false (w + 1) 0 (p + q + 2) (by omega) (by simp; omega)
  exact ⟨_, _, _, _, by omega, by omega, hr, hs, Or.inl h_chk0⟩

theorem baseTr_macroStep (c₁ c₂ : Cfg 25 2) (h : BaseTr c₁ c₂) : MacroStep BaseTr c₁ c₂ := by
  rcases h with ⟨is_right, w, q, p, hp, hsum⟩ | ⟨is_right, w, q, k, r, hsum⟩ |
    ⟨is_right, w, q, A, B, m, r, hAB, hsum⟩ | ⟨is_right, is_prime, w, q, p, hp, hsum⟩
  · exact macro_chk0 is_right w q p hp hsum
  · exact macro_chk6 is_right w q k r hsum
  · exact macro_chk11 is_right w q A B m r hAB hsum
  · cases is_right <;> cases is_prime
    · exact macro_chkExit_ff w q p hp hsum
    · exact macro_chkExit_ft w q p hp hsum
    · exact macro_chkExit_tf w q p hp hsum
    · exact macro_chkExit_tt w q p hp hsum


theorem boot_chk0_ref :
    nSteps reference 49 init =
      some ⟨0, Tape.mk' ((LBase1 true 2).cons 0)
        (ListBlank.append (List.replicate 1 1) ((REnd1 true 2).cons 0))⟩ := by
  have h47 : nSteps reference 47 init =
      some ⟨19, ⟨1, ListBlank.append (List.replicate 2 1) B0,
        (ListBlank.append (List.replicate 1 1) B0).cons 0⟩⟩ := boot_reference_47
  obtain ⟨h2, _⟩ := sim_state19_to_0
    (ListBlank.append (List.replicate 2 1) B0)
    (ListBlank.append (List.replicate 3 1) B0)
    (ListBlank.append (List.replicate 1 1) B0)
    (ListBlank.append (List.replicate 2 1) B0)
  simpa [LBase1, REnd1, B0_cons_zero] using nSteps_bind_eq h47 h2

theorem boot_chk0_edit :
    nSteps edited 103 init =
      some ⟨0, Tape.mk' ((LBase2 true 2).cons 0)
        (ListBlank.append (List.replicate 2 1) ((REnd2 true 2).cons 0))⟩ := by
  have h101 : nSteps edited 101 init =
      some ⟨19, ⟨1, ListBlank.append (List.replicate 3 1) B0,
        (ListBlank.append (List.replicate 2 1) B0).cons 0⟩⟩ := boot_edited_101
  obtain ⟨_, h2⟩ := sim_state19_to_0
    (ListBlank.append (List.replicate 2 1) B0)
    (ListBlank.append (List.replicate 3 1) B0)
    (ListBlank.append (List.replicate 1 1) B0)
    (ListBlank.append (List.replicate 2 1) B0)
  simpa [LBase2, REnd2, B0_cons_zero] using nSteps_bind_eq h101 h2

theorem edited_iff_reference : Halts edited ↔ Halts reference := by
  unfold Halts
  rw [nSteps_eval_dom boot_chk0_edit, nSteps_eval_dom boot_chk0_ref]
  exact macro_eval_dom BaseTr baseTr_macroStep (BaseTr.chk0 true 0 2 1 (by omega) (by simp))

theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  candidate_iff_edited.trans edited_iff_reference

end ConjectureMachines.Goldbach24
