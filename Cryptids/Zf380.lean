/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Zf393

/-!
# Zf380

380-state Turing machine halting-equivalent to the 393-state ZF machine.
-/

@[expose] public section

namespace ConjectureMachines.Zf380

open Turing StateTransition Machines
open Zf393
  (zf393Trans_eq BootState stateOfBoot bitOfBool stepBootR stepBootL stepBoot runBoot
   bootChkL_7 bootChkR_7 boot_phase1_39734)

/-- 393-state ZF consistency reference machine (`zf_393`, Wade 2026). -/
abbrev reference : BundledMachine 2 := Machines.zf393.bundle

/-- 380-state ZF consistency candidate machine (`zf_380`). -/
abbrev candidate : BundledMachine 2 := Machines.zf380.bundle

/-- Alias for `Machines.zf393`. -/
abbrev refM : Machine 393 2 := Machines.zf393

/-- Alias for `Machines.zf380`. -/
abbrev candM : Machine 380 2 := Machines.zf380

theorem candidate_fewer_states : candidate.states < reference.states := by
  decide

set_option maxRecDepth 200000

def nSteps {N : ℕ} [NeZero N] (M : Machine N 2) (n : ℕ) : Cfg N 2 → Option (Cfg N 2) :=
  Nat.rec (motive := fun _ => Cfg N 2 → Option (Cfg N 2))
    (fun c => some c)
    (fun _ ih c => (step M c).bind ih)
    n

@[simp]
theorem nSteps_zero {N : ℕ} [NeZero N] (M : Machine N 2) (c : Cfg N 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ {N : ℕ} [NeZero N] (M : Machine N 2) (n : ℕ) (c : Cfg N 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

attribute [eqns nSteps_zero nSteps_succ] nSteps

theorem nSteps_reaches {N : ℕ} [NeZero N] {M : Machine N 2} {n : ℕ} {c c' : Cfg N 2}
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

theorem nSteps_eval_dom {N : ℕ} [NeZero N] {M : Machine N 2} {n : ℕ} {c c' : Cfg N 2}
    (h : nSteps M n c = some c') :
    (eval (step M) c).Dom ↔ (eval (step M) c').Dom := by
  rw [StateTransition.reaches_eval (nSteps_reaches h)]

def Tape.mkL (L R : ListBlank (Fin 2)) : Tape (Fin 2) :=
  ⟨L.head, L.tail, R⟩

theorem mkL_cons_eq_mk'_cons (l : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mkL (L.cons l) R = Tape.mk' L (R.cons l) := by
  simp [Tape.mkL, Tape.mk']

theorem default_cons_zero :
    (default : ListBlank (Fin 2)).cons 0 = default := by
  change ListBlank.cons 0 (ListBlank.mk []) = ListBlank.mk []
  rw [ListBlank.cons_mk]
  exact Quotient.sound' (Or.inr ⟨1, rfl⟩)

theorem step_mk'_none {N : ℕ} [NeZero N] {M : Machine N 2} {q : Fin N} {a : Fin 2}
    (h : M.transition q a = none) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = none := by
  simp [step, h, Tape.mk']

theorem step_mk'_right {N : ℕ} [NeZero N] {M : Machine N 2} {q q' : Fin N} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {N : ℕ} [NeZero N] {M : Machine N 2} {q q' : Fin N} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

def cfgOfFast {N : ℕ} [NeZero N] (q : Fin N) (L : List (Fin 2)) (h : Fin 2)
    (R : List (Fin 2)) : Cfg N 2 :=
  ⟨q, Tape.mk' (ListBlank.append L default) ((ListBlank.append R default).cons h)⟩

def stepFast {N : ℕ} [NeZero N] (M : Machine N 2) (q : Fin N) (L : List (Fin 2))
    (h : Fin 2) (R : List (Fin 2)) :
    Option (Fin N × List (Fin 2) × Fin 2 × List (Fin 2)) :=
  match M.transition q h with
  | none => none
  | some (w, .right, q') =>
    match R with
    | [] => some (q', w :: L, 0, [])
    | r :: rs => some (q', w :: L, r, rs)
  | some (w, .left, q') =>
    match L with
    | [] => some (q', [], 0, w :: R)
    | l :: ls => some (q', ls, l, w :: R)

def runFast {N : ℕ} [NeZero N] (M : Machine N 2) :
    ℕ → Fin N → List (Fin 2) → Fin 2 → List (Fin 2) →
    Option (Fin N × List (Fin 2) × Fin 2 × List (Fin 2))
  | 0, q, L, h, R => some (q, L, h, R)
  | n + 1, q, L, h, R =>
    match stepFast M q L h R with
    | none => none
    | some (q', L', h', R') => runFast M n q' L' h' R'

theorem step_cfgOfFast {N : ℕ} [NeZero N] (M : Machine N 2) (q : Fin N)
    (L : List (Fin 2)) (h : Fin 2) (R : List (Fin 2)) :
    step M (cfgOfFast q L h R) =
      (stepFast M q L h R).map fun x => cfgOfFast x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  dsimp only [stepFast, cfgOfFast]
  rcases htr : M.transition q h with _ | ⟨w, d, q'⟩
  · exact step_mk'_none htr _ _
  · cases d with
    | right =>
      cases R with
      | nil =>
        have hs := step_mk'_right htr (ListBlank.append L default) default
        dsimp only [ListBlank.append] at hs ⊢
        rw [hs, Option.map_some]
        simp only [ListBlank.append, default_cons_zero]
      | cons r rs =>
        exact step_mk'_right htr (ListBlank.append L default)
          ((ListBlank.append rs default).cons r)
    | left =>
      cases L with
      | nil =>
        have hs := step_mk'_left htr default (ListBlank.append R default)
        dsimp only [ListBlank.append] at hs ⊢
        rw [hs, Option.map_some, default_cons_zero.symm, mkL_cons_eq_mk'_cons]
        simp only [ListBlank.append, default_cons_zero]
      | cons l ls =>
        have hs := step_mk'_left htr ((ListBlank.append ls default).cons l)
          (ListBlank.append R default)
        dsimp only [ListBlank.append] at hs ⊢
        rw [hs, Option.map_some, mkL_cons_eq_mk'_cons]
        rfl

theorem nSteps_of_runFast {N : ℕ} [NeZero N] (M : Machine N 2) (n : ℕ) (q : Fin N)
    (L : List (Fin 2)) (h : Fin 2)
    (R : List (Fin 2)) :
    nSteps M n (cfgOfFast q L h R) =
      (runFast M n q L h R).map fun x => cfgOfFast x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  induction n generalizing q L h R with
  | zero => rfl
  | succ n ih =>
    rw [nSteps_succ, step_cfgOfFast, runFast]
    rcases stepFast M q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'

theorem runFast_add {N : ℕ} [NeZero N] (M : Machine N 2) (m n : ℕ) (q : Fin N)
    (L : List (Fin 2)) (h : Fin 2)
    (R : List (Fin 2)) :
    runFast M (m + n) q L h R =
      match runFast M m q L h R with
      | none => none
      | some (q', L', h', R') => runFast M n q' L' h' R' := by
  induction m generalizing q L h R with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.succ_add, runFast, runFast]
    rcases stepFast M q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'

theorem init_eq_cfgOfFast {N : ℕ} [NeZero N] : (init : Cfg N 2) = cfgOfFast 0 [] 0 [] := by
  simp only [init, Tape.mk₁, Tape.mk₂, cfgOfFast, ListBlank.append, default_cons_zero]
  rfl

abbrev stateOfBootRef : BootState → Fin 393 := stateOfBoot

def stateOfBootCand : BootState → Fin 380
  | .b0 => 0 | .b1 => 1 | .b2 => 2 | .b3 => 3 | .b4 => 4 | .b68 => 65


theorem stepFast_of_stepBootRef {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hs : stepBoot q L h R = some (q', L', h', R')) :
    stepFast refM (stateOfBootRef q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBootRef q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  cases q <;> cases h <;> simp only [stepBoot] at hs
  all_goals try cases hs
  all_goals
    cases L <;> cases R <;>
    simp only [stepBootR, stepBootL, Option.some.injEq, Prod.mk.injEq] at hs <;>
    rcases hs with ⟨rfl, rfl, rfl, rfl⟩ <;>
    rfl

theorem runFast_of_runBootRef (n : ℕ) {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hr : runBoot n q L h R = some (q', L', h', R')) :
    runFast refM n (stateOfBootRef q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBootRef q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  induction n generalizing q L h R with
  | zero =>
    simp only [runBoot, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ n ih =>
    simp only [runBoot] at hr
    rcases hst : stepBoot q L h R with _ | ⟨q1, L1, h1, R1⟩
    · rw [hst] at hr; cases hr
    · rw [hst] at hr
      rw [runFast, stepFast_of_stepBootRef hst]
      exact ih hr

theorem stepFast_of_stepBootCand {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hs : stepBoot q L h R = some (q', L', h', R')) :
    stepFast candM (stateOfBootCand q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBootCand q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  cases q <;> cases h <;> simp only [stepBoot] at hs
  all_goals try cases hs
  all_goals
    cases L <;> cases R <;>
    simp only [stepBootR, stepBootL, Option.some.injEq, Prod.mk.injEq] at hs <;>
    rcases hs with ⟨rfl, rfl, rfl, rfl⟩ <;>
    rfl

theorem runFast_of_runBootCand (n : ℕ) {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hr : runBoot n q L h R = some (q', L', h', R')) :
    runFast candM n (stateOfBootCand q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBootCand q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  induction n generalizing q L h R with
  | zero =>
    simp only [runBoot, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ n ih =>
    simp only [runBoot] at hr
    rcases hst : stepBoot q L h R with _ | ⟨q1, L1, h1, R1⟩
    · rw [hst] at hr; cases hr
    · rw [hst] at hr
      rw [runFast, stepFast_of_stepBootCand hst]
      exact ih hr

def bootR_39753 : List (Fin 2) :=
  (1 :: List.replicate 18 0) ++ bootChkR_7.map bitOfBool

theorem boot_fast_19_ref :
    runFast refM 19 68 (bootChkL_7.map bitOfBool) 0 (bootChkR_7.map bitOfBool) =
      some (64, [], 0, bootR_39753) := by
  decide

theorem boot_fast_19_cand :
    runFast candM 19 65 (bootChkL_7.map bitOfBool) 0 (bootChkR_7.map bitOfBool) =
      some (64, [], 0, bootR_39753) := by
  decide

theorem boot_ref :
    nSteps refM 39753 init = some (cfgOfFast 64 [] 0 bootR_39753) := by
  rw [init_eq_cfgOfFast, nSteps_of_runFast]
  have hadd : (39753 : ℕ) = 39734 + 19 := rfl
  have h34 :=
    runFast_of_runBootRef 39734 (q := .b0) (L := []) (h := false) (R := []) boot_phase1_39734
  dsimp only [stateOfBootRef, Zf393.stateOfBoot, List.map, bitOfBool] at h34
  rw [hadd, runFast_add, h34]
  dsimp only
  rw [boot_fast_19_ref]
  rfl

theorem boot_cand :
    nSteps candM 39753 init = some (cfgOfFast 64 [] 0 bootR_39753) := by
  rw [init_eq_cfgOfFast, nSteps_of_runFast]
  have hadd : (39753 : ℕ) = 39734 + 19 := rfl
  have h34 :=
    runFast_of_runBootCand 39734 (q := .b0) (L := []) (h := false) (R := []) boot_phase1_39734
  dsimp only [stateOfBootCand, Zf393.stateOfBoot, List.map, bitOfBool] at h34
  rw [hadd, runFast_add, h34]
  dsimp only
  rw [boot_fast_19_cand]
  rfl

def renum (q : Nat) : Fin 380 :=
  let s :=
    (if q > 65 then 1 else 0) +
    (if q > 68 then 1 else 0) +
    (if q > 266 then 1 else 0) +
    (if q > 278 then 1 else 0) +
    (if q > 322 then 1 else 0) +
    (if q > 335 then 1 else 0) +
    (if q > 341 then 1 else 0) +
    (if q > 353 then 1 else 0) +
    (if q > 359 then 1 else 0) +
    (if q > 361 then 1 else 0) +
    (if q > 379 then 1 else 0) +
    (if q > 387 then 1 else 0) +
    (if q > 389 then 1 else 0)
  if h : q - s < 380 then ⟨q - s, h⟩ else ⟨0, by decide⟩

def mapState (q : Fin 393) (l0 h : Fin 2) : Fin 380 :=
  if q.val = 67 then renum 292
  else if q.val = 66 then renum (if h.val = 0 then 350 else 338)
  else if q.val = 65 then renum (if h.val = 0 then 45 else 342)
  else if q.val = 21 ∧ h.val = 1 then renum 17
  else if q.val = 266 then renum 272
  else if q.val = 278 then renum (if l0.val = 0 then 252 else 270)
  else if q.val = 322 then renum 280
  else if q.val = 341 then renum 46
  else if q.val = 347 then renum 80
  else if q.val = 353 then renum 82
  else if q.val = 359 then renum 356
  else if q.val = 379 then renum 376
  else if q.val = 334 then renum 385
  else if q.val = 335 then renum 337
  else if q.val = 370 then renum 371
  else if q.val = 389 then renum 388
  else if q.val = 361 then renum 76
  else if q.val = 387 then renum 345
  else renum q.val

def isL0Eq1State (q : Nat) : Bool :=
  q == 87 || q == 291 || q == 295 || q == 310 || q == 316 ||
  q == 333 || q == 334 || q == 335 || q == 336 || q == 338 ||
  q == 340 || q == 344 || q == 349 || q == 361 || q == 363 ||
  q == 365 || q == 367 || q == 369 || q == 374 || q == 378 ||
  q == 384 || q == 387 || q == 266 || q == 280 || q == 359 || q == 379 ||
  q == 371 || q == 389 ||
  q == 140 || q == 218 || q == 220 || q == 240 || q == 252 ||
  q == 80 || q == 81 || q == 82 ||
  q == 98 || q == 105 || q == 155 || q == 195

def isL0Eq0State (q : Nat) : Bool :=
  q == 45 || q == 350 || q == 272 || q == 322 || q == 337 || q == 346 ||
  q == 376 || q == 385 || q == 370 || q == 388 || q == 339 || q == 341 ||
  q == 76 || q == 345 || q == 351 || q == 360 ||
  q == 265 || q == 270 ||
  q == 79 || q == 347 || q == 353 ||
  q == 356 || q == 362 || q == 354 || q == 355

def validState (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) : Bool :=
  q.val >= 5 && q.val != 68 &&
  (q.val != 22 || r0 == 1) &&
  (q.val != 20 || !(h == 0 && l0 == 1)) &&
  (!isL0Eq1State q.val || l0 == 1) &&
  (!isL0Eq0State q.val || l0 == 0) &&
  (q.val != 46 || (l0 == 1 && l1 == 0)) &&
  (q.val != 361 || (l0 == 1 && l1 == 0 && l2 == 1)) &&
  (q.val != 80 || (l0 == 1 && l1 == 0)) &&
  (q.val != 82 || (l0 == 1 && l1 == 1)) &&
  (!(q.val == 345 || q.val == 360 || q.val == 362) || (l0 == 0 && l1 == 1)) &&
  (!(q.val == 354 || q.val == 355) || (l0 == 0 && l1 == 1 && l2 == 1)) &&
  (q.val != 278 || l1 == 1) &&
  (!(q.val == 156 || q.val == 157 || q.val == 196 || q.val == 197 ||
    q.val == 292 || q.val == 296 || q.val == 311 || q.val == 317) || (l0 == 1 && l1 == 1)) &&
  (!(q.val == 312 || q.val == 318) || (l0 == 1 && l1 == 1 && l2 == 1)) &&
  (q.val != 88 || (l0 == 0 && l1 == 1)) &&
  (q.val != 309 || (l0 == 0 && l1 == 1 && l2 == 1)) &&
  (q.val != 67 || (h == 1 && l0 == 1 && l1 == 1)) &&
  (q.val != 66 || ((h == 0 && l0 == 1 && l1 == 1) || (h == 1 && l0 == 1))) &&
  (q.val != 65 || ((h == 0 && l0 == 1) || h == 1))

def checkNext (q : Fin 393) (l2 l1 l0 h r0 x : Fin 2) : Bool :=
  match refM.transition q h with
  | none => true
  | some (w, Dir.right, q') => validState q' l1 l0 w r0 x
  | some (w, Dir.left, q') => validState q' x l2 l1 l0 w

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem validState_next (q : Fin 393) (l2 l1 l0 h r0 x : Fin 2) :
    validState q l2 l1 l0 h r0 = true → checkNext q l2 l1 l0 h r0 x = true := by
  revert q l2 l1 l0 h r0 x; decide

def expectedTransition (q : Fin 393) (l1 l0 h r0 : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  match refM.transition q h with
  | none => none
  | some (w, Dir.right, q') => some (w, Dir.right, mapState q' w r0)
  | some (w, Dir.left, q') => some (w, Dir.left, mapState q' l1 l0)

def isThreeStep (q : Fin 393) (l0 h : Fin 2) : Bool :=
  ((q.val == 45 || q.val == 350 || q.val == 272 || q.val == 266 || q.val == 346 ||
    q.val == 356 || q.val == 359 || q.val == 280 || q.val == 322 || q.val == 388 ||
    q.val == 389 || q.val == 341 || q.val == 265 || q.val == 270 || q.val == 80 ||
    q.val == 82 || q.val == 353 || (q.val == 278 && l0.val == 1)) && h.val == 0) ||
  ((q.val == 376 || q.val == 385 || q.val == 334 || q.val == 337 || q.val == 335 ||
    q.val == 280 || q.val == 322 || q.val == 370 || q.val == 371 || q.val == 388 ||
    q.val == 389 || q.val == 344 || q.val == 346 || q.val == 76 || q.val == 365 ||
    q.val == 387 || q.val == 252 || q.val == 347 || q.val == 353) && h.val == 1)

def isFiveStepLRLR (q : Fin 393) (h : Fin 2) : Bool :=
  (q.val == 379 && h.val == 1) || (q.val == 347 && h.val == 0)

def isFiveStepLLRR (q : Fin 393) (l0 h : Fin 2) : Bool :=
  ((q.val == 46 || q.val == 362) && h.val == 0) ||
  ((q.val == 345 || q.val == 80 || q.val == 82 || (q.val == 278 && l0.val == 0)) && h.val == 1)

def isSevenStepLLLRRR (q : Fin 393) (h : Fin 2) : Bool :=
  (q.val == 361 && h.val == 1) || (q.val == 354 && h.val == 0)

def isNineStepLRLLLRRR (q : Fin 393) (h : Fin 2) : Bool :=
  q.val == 355 && h.val == 0

def isMultiStep (q : Fin 393) (l0 h : Fin 2) : Bool :=
  isThreeStep q l0 h || isFiveStepLRLR q h || isFiveStepLLRR q l0 h ||
  isSevenStepLLLRRR q h || isNineStepLRLLLRRR q h

def midP (q : Fin 393) (h : Fin 2) : Fin 380 :=
  if q.val == 45 then renum 342
  else if q.val == 350 then renum 338
  else if q.val == 272 || q.val == 266 then renum 246
  else if q.val == 346 then renum (if h.val == 0 then 154 else 100)
  else if q.val == 356 || q.val == 359 then renum 303
  else if q.val == 280 || q.val == 322 then renum (if h.val == 0 then 209 else 264)
  else if q.val == 376 then renum 84
  else if q.val == 341 then renum 344
  else if q.val == 365 then renum 355
  else if q.val == 76 then renum 365
  else if q.val == 387 then renum 354
  else if q.val == 265 then renum 117
  else if q.val == 270 || q.val == 278 then renum 152
  else if q.val == 252 then renum 265
  else if q.val == 80 && h.val == 0 then renum 101
  else if (q.val == 82 || q.val == 353) && h.val == 0 then renum 102
  else if (q.val == 347 || q.val == 353) && h.val == 1 then renum 347
  else if (q.val == 388 || q.val == 389) && h.val == 0 then renum 290
  else if (q.val == 370 || q.val == 371 || q.val == 388 || q.val == 389) && h.val == 1 then
    renum 370
  else renum 334

def midS (q : Fin 393) (l0 h : Fin 2) : Fin 380 :=
  if q.val == 45 then renum 29
  else if q.val == 350 then renum 339
  else if q.val == 272 || q.val == 266 then
    if l0.val == 0 then renum 268 else renum 279
  else if q.val == 346 then
    if h.val == 0 then renum 351 else renum 342
  else if q.val == 356 || q.val == 359 then
    if l0.val == 0 then renum 357 else renum 368
  else if q.val == 280 || q.val == 322 then
    if h.val == 0 then
      if l0.val == 0 then renum 249 else renum 210
    else
      if l0.val == 0 then renum 321 else renum 287
  else if q.val == 376 then renum 382
  else if q.val == 341 then renum 345
  else if q.val == 365 then renum 340
  else if q.val == 76 then renum 34
  else if q.val == 387 then renum 338
  else if q.val == 265 then renum 257
  else if q.val == 270 || q.val == 278 then
    if l0.val == 0 then renum 271 else renum 153
  else if q.val == 252 then renum 272
  else if q.val == 80 && h.val == 0 then renum 102
  else if (q.val == 82 || q.val == 353) && h.val == 0 then
    if l0.val == 0 then renum 352 else renum 103
  else if (q.val == 347 || q.val == 353) && h.val == 1 then renum 357
  else if (q.val == 388 || q.val == 389) && h.val == 0 then
    if l0.val == 0 then renum 383 else renum 291
  else if (q.val == 370 || q.val == 371 || q.val == 388 || q.val == 389) && h.val == 1 then
    if l0.val == 0 then renum 334 else renum 21
  else
    if l0.val == 0 then renum 44 else renum 333

def validState1 (q : Fin 393) (l1 l0 h r0 : Fin 2) : Bool :=
  validState q 0 l1 l0 h r0 || validState q 1 l1 l0 h r0

theorem validState1_of_validState (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    validState q l2 l1 l0 h r0 = true → validState1 q l1 l0 h r0 = true := by
  intro hv
  rcases l2 with ⟨_ | _ | n, isLt⟩
  · rw [show (⟨0, isLt⟩ : Fin 2) = 0 from rfl] at hv
    simp [validState1, hv]
  · rw [show (⟨1, isLt⟩ : Fin 2) = 1 from rfl] at hv
    simp [validState1, hv]
  · omega

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_oneStep (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isMultiStep q l0 h = false →
    validState1 q l1 l0 h r0 = true →
    candM.transition (mapState q l0 h) h = expectedTransition q l1 l0 h r0 := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_threeStep_1 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isThreeStep q l0 h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (mapState q l0 h) h = some (h, Dir.left, midP q h) := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_threeStep_2 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isThreeStep q l0 h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (midP q h) l0 = some (l0, Dir.right, midS q l0 h) := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_threeStep_3 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isThreeStep q l0 h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (midS q l0 h) h = expectedTransition q l1 l0 h r0 := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem threeStep_not_none (q : Fin 393) (l0 h : Fin 2) :
    isThreeStep q l0 h = true →
    refM.transition q h ≠ none := by
  revert q l0 h; decide

def lrlrP1 (q : Fin 393) : Fin 380 :=
  if q.val == 379 then renum 84 else renum 101

def lrlrS1 (q : Fin 393) : Fin 380 :=
  if q.val == 379 then renum 371 else renum 346

def lrlrP2 (q : Fin 393) : Fin 380 :=
  if q.val == 379 then renum 370 else renum 154

def lrlrS2 (q : Fin 393) : Fin 380 :=
  if q.val == 379 then renum 21 else renum 351

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_1 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (mapState q l0 h) h = some (h, Dir.left, lrlrP1 q) := by
  revert q h l0 l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_2 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (lrlrP1 q) l0 = some (l0, Dir.right, lrlrS1 q) := by
  revert q h l0 l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_3 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (lrlrS1 q) h = some (h, Dir.left, lrlrP2 q) := by
  revert q h l0 l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_4 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (lrlrP2 q) l0 = some (l0, Dir.right, lrlrS2 q) := by
  revert q h l0 l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_5 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (lrlrS2 q) h = expectedTransition q l1 l0 h r0 := by
  revert q h l0 l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem fiveStepLRLR_not_none (q : Fin 393) (h : Fin 2) :
    isFiveStepLRLR q h = true →
    refM.transition q h ≠ none := by
  revert q h; decide

def llrrP1 (q : Fin 393) : Fin 380 :=
  if q.val == 46 then renum 344
  else if q.val == 362 then renum 346
  else if q.val == 345 then renum 354
  else if q.val == 278 then renum 265
  else renum 347

def llrrP2 (q : Fin 393) : Fin 380 :=
  if q.val == 46 then renum 334
  else if q.val == 362 then renum 154
  else if q.val == 278 then renum 117
  else if q.val == 345 then renum 362
  else renum 273

def llrrS1 (q : Fin 393) : Fin 380 :=
  if q.val == 46 then renum 44
  else if q.val == 362 then renum 155
  else if q.val == 345 then renum 363
  else if q.val == 278 then renum 118
  else if q.val == 80 then renum 300
  else renum 302

def llrrS2 (q : Fin 393) : Fin 380 :=
  if q.val == 46 then renum 42
  else if q.val == 362 then renum 364
  else if q.val == 345 then renum 32
  else if q.val == 278 then renum 270
  else if q.val == 80 then renum 301
  else renum 303

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_1 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q l0 h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (mapState q l0 h) h = some (h, Dir.left, llrrP1 q) := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_2 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q l0 h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (llrrP1 q) l0 = some (l0, Dir.left, llrrP2 q) := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_3 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q l0 h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (llrrP2 q) l1 = some (l1, Dir.right, llrrS1 q) := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_4 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q l0 h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (llrrS1 q) l0 = some (l0, Dir.right, llrrS2 q) := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_5 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q l0 h = true →
    validState1 q l1 l0 h r0 = true →
    candM.transition (llrrS2 q) h = expectedTransition q l1 l0 h r0 := by
  revert q l0 h l1 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem fiveStepLLRR_not_none (q : Fin 393) (l0 h : Fin 2) :
    isFiveStepLLRR q l0 h = true →
    refM.transition q h ≠ none := by
  revert q l0 h; decide

def lllrrrP1 (q : Fin 393) : Fin 380 :=
  if q.val == 361 then renum 365 else renum 362

def lllrrrP2 (q : Fin 393) : Fin 380 :=
  if q.val == 361 then renum 355 else renum 346

def lllrrrP3 (q : Fin 393) : Fin 380 :=
  if q.val == 361 then renum 197 else renum 100

def lllrrrS1 (q : Fin 393) : Fin 380 :=
  if q.val == 361 then renum 198 else renum 101

def lllrrrS2 (q : Fin 393) : Fin 380 :=
  if q.val == 361 then renum 366 else renum 102

def lllrrrS3 (q : Fin 393) : Fin 380 :=
  if q.val == 361 then renum 367 else renum 352

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_1 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (mapState q l0 h) h = some (h, Dir.left, lllrrrP1 q) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_2 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (lllrrrP1 q) l0 = some (l0, Dir.left, lllrrrP2 q) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_3 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (lllrrrP2 q) l1 = some (l1, Dir.left, lllrrrP3 q) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_4 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (lllrrrP3 q) l2 = some (l2, Dir.right, lllrrrS1 q) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_5 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (lllrrrS1 q) l1 = some (l1, Dir.right, lllrrrS2 q) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_6 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (lllrrrS2 q) l0 = some (l0, Dir.right, lllrrrS3 q) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_7 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (lllrrrS3 q) h = expectedTransition q l1 l0 h r0 := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem sevenStepLLLRRR_not_none (q : Fin 393) (h : Fin 2) :
    isSevenStepLLLRRR q h = true →
    refM.transition q h ≠ none := by
  revert q h; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_0a (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (mapState q l0 h) h = some (h, Dir.left, renum 197) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_0b (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (renum 197) l0 = some (l0, Dir.right, renum 354) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_1 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (renum 354) h = some (h, Dir.left, renum 362) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_2 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (renum 362) l0 = some (l0, Dir.left, renum 346) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_3 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (renum 346) l1 = some (l1, Dir.left, renum 100) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_4 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (renum 100) l2 = some (l2, Dir.right, renum 101) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_5 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (renum 101) l1 = some (l1, Dir.right, renum 102) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_6 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (renum 102) l0 = some (l0, Dir.right, renum 352) := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_7 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    validState q l2 l1 l0 h r0 = true →
    candM.transition (renum 352) h = expectedTransition q l1 l0 h r0 := by
  revert q h l2 l1 l0 r0; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem nineStepLRLLLRRR_not_none (q : Fin 393) (h : Fin 2) :
    isNineStepLRLLLRRR q h = true →
    refM.transition q h ≠ none := by
  revert q h; decide

theorem step_of_transition_eq {q : Fin 393} {S : Fin 380} (T : Tape (Fin 2))
    (htr : candM.transition S T.head =
      expectedTransition q T.left.tail.head T.left.head T.head T.right.head) :
    step candM ⟨S, T⟩ =
      (step refM ⟨q, T⟩).map fun c =>
        ⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩ := by
  dsimp only [step]
  rw [htr, Zf393.zf393Trans_eq q T.head]
  rcases e : Zf393.zf393Trans q T.head with _ | ⟨w, d, q'⟩
  · simp [expectedTransition, e]
  · cases T; cases d <;> simp [expectedTransition, e, Tape.move, Tape.write]

theorem tape_left_right_self (T : Tape (Fin 2)) :
    (((T.write T.head).move Dir.left).write T.left.head).move Dir.right = T := by
  cases T
  simp [Tape.write, Tape.move]

theorem step_three_left_right {N : ℕ} [NeZero N] {M : Machine N 2}
    {q₁ P S : Fin N} (T : Tape (Fin 2))
    (h1 : M.transition q₁ T.head = some (T.head, Dir.left, P))
    (h2 : M.transition P T.left.head = some (T.left.head, Dir.right, S))
    {c' : Cfg N 2}
    (h3 : step M ⟨S, T⟩ = some c') :
    Reaches₁ (step M) ⟨q₁, T⟩ c' := by
  have hs1 : step M ⟨q₁, T⟩ = some ⟨P, (T.write T.head).move Dir.left⟩ := by
    simp [step, h1]
  have hhead : ((T.write T.head).move Dir.left).head = T.left.head := by
    cases T; rfl
  have hs2 : step M ⟨P, (T.write T.head).move Dir.left⟩ = some ⟨S, T⟩ := by
    dsimp only [step]
    rw [hhead, h2]
    dsimp only [Option.map]
    rw [tape_left_right_self]
  exact Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2) h3

theorem step_five_left_right {N : ℕ} [NeZero N] {M : Machine N 2}
    {q₁ P₁ S₁ P₂ S₂ : Fin N} (T : Tape (Fin 2))
    (h1 : M.transition q₁ T.head = some (T.head, Dir.left, P₁))
    (h2 : M.transition P₁ T.left.head = some (T.left.head, Dir.right, S₁))
    (h3 : M.transition S₁ T.head = some (T.head, Dir.left, P₂))
    (h4 : M.transition P₂ T.left.head = some (T.left.head, Dir.right, S₂))
    {c' : Cfg N 2}
    (h5 : step M ⟨S₂, T⟩ = some c') :
    Reaches₁ (step M) ⟨q₁, T⟩ c' := by
  have hs1 : step M ⟨q₁, T⟩ = some ⟨P₁, (T.write T.head).move Dir.left⟩ := by
    simp [step, h1]
  have hhead : ((T.write T.head).move Dir.left).head = T.left.head := by
    cases T; rfl
  have hs2 : step M ⟨P₁, (T.write T.head).move Dir.left⟩ = some ⟨S₁, T⟩ := by
    dsimp only [step]
    rw [hhead, h2]
    dsimp only [Option.map]
    rw [tape_left_right_self]
  have hs3 : step M ⟨S₁, T⟩ = some ⟨P₂, (T.write T.head).move Dir.left⟩ := by
    simp [step, h3]
  have hs4 : step M ⟨P₂, (T.write T.head).move Dir.left⟩ = some ⟨S₂, T⟩ := by
    dsimp only [step]
    rw [hhead, h4]
    dsimp only [Option.map]
    rw [tape_left_right_self]
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2)
        hs3)
      hs4)
    h5

theorem step_five_left_left_right_right {N : ℕ} [NeZero N] {M : Machine N 2}
    {q₁ P₁ P₂ S₁ S₂ : Fin N} (T : Tape (Fin 2))
    (h1 : M.transition q₁ T.head = some (T.head, Dir.left, P₁))
    (h2 : M.transition P₁ T.left.head = some (T.left.head, Dir.left, P₂))
    (h3 : M.transition P₂ T.left.tail.head = some (T.left.tail.head, Dir.right, S₁))
    (h4 : M.transition S₁ T.left.head = some (T.left.head, Dir.right, S₂))
    {c' : Cfg N 2}
    (h5 : step M ⟨S₂, T⟩ = some c') :
    Reaches₁ (step M) ⟨q₁, T⟩ c' := by
  let T₁ := (T.write T.head).move Dir.left
  have hs1 : step M ⟨q₁, T⟩ = some ⟨P₁, T₁⟩ := by
    simp [T₁, step, h1]
  have hhead1 : T₁.head = T.left.head := by
    cases T; rfl
  have hleft1 : T₁.left.head = T.left.tail.head := by
    cases T; rfl
  have hs2 : step M ⟨P₁, T₁⟩ = some ⟨P₂, (T₁.write T₁.head).move Dir.left⟩ := by
    dsimp only [step]
    rw [hhead1, h2]
    rfl
  have hhead2 : ((T₁.write T₁.head).move Dir.left).head = T.left.tail.head := by
    cases T; rfl
  have hs3 : step M ⟨P₂, (T₁.write T₁.head).move Dir.left⟩ = some ⟨S₁, T₁⟩ := by
    dsimp only [step]
    rw [hhead2, h3]
    dsimp only [Option.map]
    rw [← hleft1, tape_left_right_self T₁]
  have hs4 : step M ⟨S₁, T₁⟩ = some ⟨S₂, T⟩ := by
    dsimp only [step]
    rw [hhead1, h4]
    dsimp only [Option.map]
    rw [tape_left_right_self T]
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2)
        hs3)
      hs4)
    h5

theorem step_seven_left_left_left_right_right_right {N : ℕ} [NeZero N] {M : Machine N 2}
    {q₁ P₁ P₂ P₃ S₁ S₂ S₃ : Fin N} (T : Tape (Fin 2))
    (h1 : M.transition q₁ T.head = some (T.head, Dir.left, P₁))
    (h2 : M.transition P₁ T.left.head = some (T.left.head, Dir.left, P₂))
    (h3 : M.transition P₂ T.left.tail.head = some (T.left.tail.head, Dir.left, P₃))
    (h4 : M.transition P₃ T.left.tail.tail.head = some (T.left.tail.tail.head, Dir.right, S₁))
    (h5 : M.transition S₁ T.left.tail.head = some (T.left.tail.head, Dir.right, S₂))
    (h6 : M.transition S₂ T.left.head = some (T.left.head, Dir.right, S₃))
    {c' : Cfg N 2}
    (h7 : step M ⟨S₃, T⟩ = some c') :
    Reaches₁ (step M) ⟨q₁, T⟩ c' := by
  let T₁ := (T.write T.head).move Dir.left
  let T₂ := (T₁.write T₁.head).move Dir.left
  have hs1 : step M ⟨q₁, T⟩ = some ⟨P₁, T₁⟩ := by
    simp [T₁, step, h1]
  have hhead1 : T₁.head = T.left.head := by
    cases T; rfl
  have hleft1 : T₁.left.head = T.left.tail.head := by
    cases T; rfl
  have hs2 : step M ⟨P₁, T₁⟩ = some ⟨P₂, T₂⟩ := by
    dsimp only [T₂, step]
    rw [hhead1, h2]
    rfl
  have hhead2 : T₂.head = T.left.tail.head := by
    cases T; rfl
  have hleft2 : T₂.left.head = T.left.tail.tail.head := by
    cases T; rfl
  have hs3 : step M ⟨P₂, T₂⟩ = some ⟨P₃, (T₂.write T₂.head).move Dir.left⟩ := by
    dsimp only [step]
    rw [hhead2, h3]
    rfl
  have hhead3 : ((T₂.write T₂.head).move Dir.left).head = T.left.tail.tail.head := by
    cases T; rfl
  have hs4 : step M ⟨P₃, (T₂.write T₂.head).move Dir.left⟩ = some ⟨S₁, T₂⟩ := by
    dsimp only [step]
    rw [hhead3, h4]
    dsimp only [Option.map]
    rw [← hleft2, tape_left_right_self T₂]
  have hs5 : step M ⟨S₁, T₂⟩ = some ⟨S₂, T₁⟩ := by
    dsimp only [step]
    rw [hhead2, h5]
    dsimp only [Option.map]
    rw [← hleft1, tape_left_right_self T₁]
  have hs6 : step M ⟨S₂, T₁⟩ = some ⟨S₃, T⟩ := by
    dsimp only [step]
    rw [hhead1, h6]
    dsimp only [Option.map]
    rw [tape_left_right_self T]
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail
          (Relation.TransGen.tail
            (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2)
            hs3)
          hs4)
        hs5)
      hs6)
    h7

theorem step_nine_left_right_left_left_left_right_right_right {N : ℕ} [NeZero N] {M : Machine N 2}
    {q₁ P₀ q₂ P₁ P₂ P₃ S₁ S₂ S₃ : Fin N} (T : Tape (Fin 2))
    (h0a : M.transition q₁ T.head = some (T.head, Dir.left, P₀))
    (h0b : M.transition P₀ T.left.head = some (T.left.head, Dir.right, q₂))
    (h1 : M.transition q₂ T.head = some (T.head, Dir.left, P₁))
    (h2 : M.transition P₁ T.left.head = some (T.left.head, Dir.left, P₂))
    (h3 : M.transition P₂ T.left.tail.head = some (T.left.tail.head, Dir.left, P₃))
    (h4 : M.transition P₃ T.left.tail.tail.head = some (T.left.tail.tail.head, Dir.right, S₁))
    (h5 : M.transition S₁ T.left.tail.head = some (T.left.tail.head, Dir.right, S₂))
    (h6 : M.transition S₂ T.left.head = some (T.left.head, Dir.right, S₃))
    {c' : Cfg N 2}
    (h7 : step M ⟨S₃, T⟩ = some c') :
    Reaches₁ (step M) ⟨q₁, T⟩ c' := by
  let T₁ := (T.write T.head).move Dir.left
  let T₂ := (T₁.write T₁.head).move Dir.left
  have hs0a : step M ⟨q₁, T⟩ = some ⟨P₀, T₁⟩ := by
    simp [T₁, step, h0a]
  have hhead1 : T₁.head = T.left.head := by
    cases T; rfl
  have hleft1 : T₁.left.head = T.left.tail.head := by
    cases T; rfl
  have hs0b : step M ⟨P₀, T₁⟩ = some ⟨q₂, T⟩ := by
    dsimp only [step]
    rw [hhead1, h0b]
    dsimp only [Option.map]
    rw [tape_left_right_self T]
  have hs1 : step M ⟨q₂, T⟩ = some ⟨P₁, T₁⟩ := by
    simp [T₁, step, h1]
  have hs2 : step M ⟨P₁, T₁⟩ = some ⟨P₂, T₂⟩ := by
    dsimp only [T₂, step]
    rw [hhead1, h2]
    rfl
  have hhead2 : T₂.head = T.left.tail.head := by
    cases T; rfl
  have hleft2 : T₂.left.head = T.left.tail.tail.head := by
    cases T; rfl
  have hs3 : step M ⟨P₂, T₂⟩ = some ⟨P₃, (T₂.write T₂.head).move Dir.left⟩ := by
    dsimp only [step]
    rw [hhead2, h3]
    rfl
  have hhead3 : ((T₂.write T₂.head).move Dir.left).head = T.left.tail.tail.head := by
    cases T; rfl
  have hs4 : step M ⟨P₃, (T₂.write T₂.head).move Dir.left⟩ = some ⟨S₁, T₂⟩ := by
    dsimp only [step]
    rw [hhead3, h4]
    dsimp only [Option.map]
    rw [← hleft2, tape_left_right_self T₂]
  have hs5 : step M ⟨S₁, T₂⟩ = some ⟨S₂, T₁⟩ := by
    dsimp only [step]
    rw [hhead2, h5]
    dsimp only [Option.map]
    rw [← hleft1, tape_left_right_self T₁]
  have hs6 : step M ⟨S₂, T₁⟩ = some ⟨S₃, T⟩ := by
    dsimp only [step]
    rw [hhead1, h6]
    dsimp only [Option.map]
    rw [tape_left_right_self T]
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail
          (Relation.TransGen.tail
            (Relation.TransGen.tail
              (Relation.TransGen.tail
                (Relation.TransGen.tail (Relation.TransGen.single hs0a) hs0b)
                hs1)
              hs2)
            hs3)
          hs4)
        hs5)
      hs6)
    h7

theorem step_preserves_valid (q : Fin 393) (T : Tape (Fin 2))
    (hv : validState q T.left.tail.tail.head T.left.tail.head T.left.head T.head T.right.head =
      true) :
    match step refM ⟨q, T⟩ with
    | none => True
    | some c =>
      validState c.state c.tape.left.tail.tail.head c.tape.left.tail.head
        c.tape.left.head c.tape.head c.tape.right.head = true := by
  have hnext :=
    validState_next q T.left.tail.tail.head T.left.tail.head T.left.head T.head T.right.head
  dsimp only [step]
  rw [Zf393.zf393Trans_eq q T.head]
  rcases e : Zf393.zf393Trans q T.head with _ | ⟨w, d, q'⟩
  · trivial
  · cases d
    · simpa [checkNext, e, Tape.move, Tape.write] using hnext T.left.tail.tail.tail.head hv
    · simpa [checkNext, e, Tape.move, Tape.write] using hnext T.right.tail.head hv

def Rel (c₁ : Cfg 393 2) (c₂ : Cfg 380 2) : Prop :=
  validState c₁.state c₁.tape.left.tail.tail.head c₁.tape.left.tail.head c₁.tape.left.head
    c₁.tape.head c₁.tape.right.head = true ∧
  c₂ = ⟨mapState c₁.state c₁.tape.left.head c₁.tape.head, c₁.tape⟩

theorem respects : Respects (step refM) (step candM) Rel := by
  intro c₁ c₂ ⟨hv, h⟩
  subst h
  obtain ⟨q, T⟩ := c₁
  have hpres := step_preserves_valid q T hv
  have hv1 :=
    validState1_of_validState q T.left.tail.tail.head T.left.tail.head T.left.head T.head
      T.right.head hv
  cases h3 : isThreeStep q T.left.head T.head
  · cases h5a : isFiveStepLRLR q T.head
    · cases h5b : isFiveStepLLRR q T.left.head T.head
      · cases h7 : isSevenStepLLLRRR q T.head
        · cases h9 : isNineStepLRLLLRRR q T.head
          · have hm : isMultiStep q T.left.head T.head = false := by
              simp [isMultiStep, h3, h5a, h5b, h7, h9]
            have hstep := step_of_transition_eq T
              (transition_oneStep q T.left.tail.head T.left.head T.head T.right.head hm hv1)
            rcases e : step refM ⟨q, T⟩ with _ | c
            · simpa [hstep] using e
            · rw [e] at hpres
              exact ⟨⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩,
                ⟨hpres, rfl⟩,
                Relation.TransGen.single (by simp [hstep, e])⟩
          · have h0a := transition_nineStep_0a q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h0b := transition_nineStep_0b q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h1 := transition_nineStep_1 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h2 := transition_nineStep_2 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h3' := transition_nineStep_3 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h4 := transition_nineStep_4 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h5 := transition_nineStep_5 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h6 := transition_nineStep_6 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have hstep9 := step_of_transition_eq T
              (transition_nineStep_7 q T.left.tail.tail.head T.left.tail.head
                T.left.head T.head T.right.head h9 hv)
            rcases e : step refM ⟨q, T⟩ with _ | c
            · exfalso
              apply nineStepLRLLLRRR_not_none q T.head h9
              rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
              · rfl
              · simp only [step, htr, Option.map_some, reduceCtorEq] at e
            · rw [e] at hpres hstep9
              exact ⟨⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩,
                ⟨hpres, rfl⟩,
                step_nine_left_right_left_left_left_right_right_right T h0a h0b h1 h2 h3'
                  h4 h5 h6 hstep9⟩
        · have h1 := transition_sevenStepLLLRRR_1 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h2 := transition_sevenStepLLLRRR_2 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h3' := transition_sevenStepLLLRRR_3 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h4 := transition_sevenStepLLLRRR_4 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h5 := transition_sevenStepLLLRRR_5 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h6 := transition_sevenStepLLLRRR_6 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have hstep7 := step_of_transition_eq T
            (transition_sevenStepLLLRRR_7 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h7 hv)
          rcases e : step refM ⟨q, T⟩ with _ | c
          · exfalso
            apply sevenStepLLLRRR_not_none q T.head h7
            rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
            · rfl
            · simp only [step, htr, Option.map_some, reduceCtorEq] at e
          · rw [e] at hpres hstep7
            exact ⟨⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩,
              ⟨hpres, rfl⟩,
              step_seven_left_left_left_right_right_right T h1 h2 h3' h4 h5 h6 hstep7⟩
      · have h1 := transition_fiveStepLLRR_1 q T.left.tail.head T.left.head T.head
          T.right.head h5b hv1
        have h2 := transition_fiveStepLLRR_2 q T.left.tail.head T.left.head T.head
          T.right.head h5b hv1
        have h3' := transition_fiveStepLLRR_3 q T.left.tail.head T.left.head T.head
          T.right.head h5b hv1
        have h4 := transition_fiveStepLLRR_4 q T.left.tail.head T.left.head T.head
          T.right.head h5b hv1
        have hstep5 := step_of_transition_eq T
          (transition_fiveStepLLRR_5 q T.left.tail.head T.left.head T.head T.right.head h5b hv1)
        rcases e : step refM ⟨q, T⟩ with _ | c
        · exfalso
          apply fiveStepLLRR_not_none q T.left.head T.head h5b
          rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
          · rfl
          · simp only [step, htr, Option.map_some, reduceCtorEq] at e
        · rw [e] at hpres hstep5
          exact ⟨⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩,
            ⟨hpres, rfl⟩,
            step_five_left_left_right_right T h1 h2 h3' h4 hstep5⟩
    · have h1 := transition_fiveStepLRLR_1 q T.left.tail.head T.left.head T.head
        T.right.head h5a hv1
      have h2 := transition_fiveStepLRLR_2 q T.left.tail.head T.left.head T.head
        T.right.head h5a hv1
      have h3' := transition_fiveStepLRLR_3 q T.left.tail.head T.left.head T.head
        T.right.head h5a hv1
      have h4 := transition_fiveStepLRLR_4 q T.left.tail.head T.left.head T.head
        T.right.head h5a hv1
      have hstep5 := step_of_transition_eq T
        (transition_fiveStepLRLR_5 q T.left.tail.head T.left.head T.head T.right.head h5a hv1)
      rcases e : step refM ⟨q, T⟩ with _ | c
      · exfalso
        apply fiveStepLRLR_not_none q T.head h5a
        rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
        · rfl
        · simp only [step, htr, Option.map_some, reduceCtorEq] at e
      · rw [e] at hpres hstep5
        exact ⟨⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩,
          ⟨hpres, rfl⟩,
          step_five_left_right T h1 h2 h3' h4 hstep5⟩
  · have h1 := transition_threeStep_1 q T.left.tail.head T.left.head T.head T.right.head h3 hv1
    have h2 := transition_threeStep_2 q T.left.tail.head T.left.head T.head T.right.head h3 hv1
    have hstep3 := step_of_transition_eq T
      (transition_threeStep_3 q T.left.tail.head T.left.head T.head T.right.head h3 hv1)
    rcases e : step refM ⟨q, T⟩ with _ | c
    · exfalso
      apply threeStep_not_none q T.left.head T.head h3
      rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
      · rfl
      · simp only [step, htr, Option.map_some, reduceCtorEq] at e
    · rw [e] at hpres hstep3
      exact ⟨⟨mapState c.state c.tape.left.head c.tape.head, c.tape⟩,
        ⟨hpres, rfl⟩,
        step_three_left_right T h1 h2 hstep3⟩

theorem rel_boot : Rel (cfgOfFast 64 [] 0 bootR_39753) (cfgOfFast 64 [] 0 bootR_39753) :=
  ⟨by decide, rfl⟩

theorem candidate_equivalent : Halts candidate ↔ Halts reference := by
  unfold BundledMachine.Halts ConjectureMachines.Halts
  rw [nSteps_eval_dom boot_cand, nSteps_eval_dom boot_ref]
  exact StateTransition.tr_eval_dom respects rel_boot
end ConjectureMachines.Zf380
