/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Zf393

/-!
# Layer 1 Backend Verification for `zf393` (`Cryptids.Semantics.Zf393.Backend`)

Formalizes the execution backend of Andrew Wade's 393-state ZF consistency Turing machine `zf393`:
1. Canonical normal-form configuration `zf393RootCfg` at `main().0` (`State 99`) and exact
   bootstrap theorems `boot_reaches_root` (`39,772` steps to `5.root`) and
   `boot_reaches_main0` (`39,773` steps to `zf393RootCfg 19 [] (List.replicate 11 0)`).
2. Unified scanner and return operations (`4.dispatch.1..9`, `5.root`, `6.break.0..2`,
   `6.continue.0..4`), including root overflow into `default`.
3. Moving `00` selector (`1.sel`), self-cleaning register gadgets (`1.inc`, `1.decnz`,
   `3.<reg>.inc/decnz`), abstract call-stack machine `zf393RegStep`, and halting equivalence
   `halts_zf393_iff_zf393RegHalts : ConjectureMachines.Halts zf393 ↔ Zf393RegHalts`.
-/

@[expose] public section

namespace ConjectureMachines.Zf393.Layer1

open Turing StateTransition ConjectureMachines
open ConjectureMachines.Zf393
open ConjectureMachines.Riemann543.Layer1
  (nSteps nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_reaches nSteps_eval_dom nSteps_of_halt mem_eval_iff_nSteps
   mk_append_replicate_zero default_eq_mk_nil
   default_cons_zero append_replicate_zero_default fin2_cases
   Tape.mkL Tape.mkL_cons Tape.mk'_cons Tape.mkL_default
   append_replicate_cons append_cons_snoc append_reverse_cons
   encodeReg encodeReg_length encodeReg_reverse append_encodeReg_reverse append_encodeReg
   encodeRegs encodeRegs_nil encodeRegs_cons encodeRegs_append
   regsTape regsTape_nil regsTape_cons regsTape_append
   list_take_cons_drop list_take_set_drop)

set_option maxRecDepth 200000

/-!
## 2. Normal-Form Configuration (`zf393RootCfg`) & 39,772/39,773-Step Bootstrap
-/

/-- The 190 fixed unary blocks `[0]^132 ++ [1] ++ [0]^57` preceding the 11 active registers. -/
def prefix190 : List ℕ :=
  List.replicate 132 0 ++ [1] ++ List.replicate 57 0

/-- Bit-level encoding (`381` bits, no `00` anywhere) of `prefix190`. -/
def fixedPrefix381 : List (Fin 2) :=
  encodeRegs prefix190

theorem fixedPrefix381_length : fixedPrefix381.length = 381 := by
  decide

/-- Canonical configuration at `main().0` (`State 99`). -/
def rootCfg (pre : List ℕ) (slot : ℕ) (ip : List (Fin 2)) (regs : List ℕ) : Cfg 393 2 :=
  ⟨99, Tape.mk' LB01
    (ListBlank.append (ip ++ List.replicate (slot - ip.length) 0 ++ encodeRegs pre)
      (regsTape regs))⟩

abbrev zf393RootCfg (slot : ℕ) (ip : List (Fin 2)) (regs : List ℕ) : Cfg 393 2 :=
  rootCfg prefix190 slot ip regs

/-- Fast computable configuration encoding `(q, L, h, R)` for `decide`-based execution. -/
def cfgOfFast (q : Fin 393) (L : List (Fin 2)) (h : Fin 2) (R : List (Fin 2)) : Cfg 393 2 :=
  ⟨q, Tape.mk' (ListBlank.append L default) ((ListBlank.append R default).cons h)⟩

def stepFast (q : Fin 393) (L : List (Fin 2)) (h : Fin 2) (R : List (Fin 2)) :
    Option (Fin 393 × List (Fin 2) × Fin 2 × List (Fin 2)) :=
  match zf393Trans q h with
  | none => none
  | some (w, .right, q') =>
    match R with
    | [] => some (q', w :: L, 0, [])
    | r :: rs => some (q', w :: L, r, rs)
  | some (w, .left, q') =>
    match L with
    | [] => some (q', [], 0, w :: R)
    | l :: ls => some (q', ls, l, w :: R)

def runFast : ℕ → Fin 393 → List (Fin 2) → Fin 2 → List (Fin 2) →
    Option (Fin 393 × List (Fin 2) × Fin 2 × List (Fin 2))
  | 0, q, L, h, R => some (q, L, h, R)
  | n + 1, q, L, h, R =>
    match stepFast q L h R with
    | none => none
    | some (q', L', h', R') => runFast n q' L' h' R'

theorem mkL_cons_eq_mk'_cons (l : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mkL (L.cons l) R = Tape.mk' L (R.cons l) := by
  simp [Tape.mkL, Tape.mk']

theorem step_cfgOfFast (q : Fin 393) (L : List (Fin 2)) (h : Fin 2) (R : List (Fin 2)) :
    step zf393 (cfgOfFast q L h R) =
      (stepFast q L h R).map fun x => cfgOfFast x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  dsimp only [stepFast, cfgOfFast]
  rcases htr : zf393Trans q h with _ | ⟨w, d, q'⟩
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

theorem nSteps_of_runFast (n : ℕ) (q : Fin 393) (L : List (Fin 2)) (h : Fin 2)
    (R : List (Fin 2)) :
    nSteps zf393 n (cfgOfFast q L h R) =
      (runFast n q L h R).map fun x => cfgOfFast x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  induction n generalizing q L h R with
  | zero => rfl
  | succ n ih =>
    rw [nSteps_succ, step_cfgOfFast, runFast]
    rcases stepFast q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'

inductive BootState where
  | b0 | b1 | b2 | b3 | b4 | b68
  deriving DecidableEq

def stateOfBoot : BootState → Fin 393
  | .b0 => 0 | .b1 => 1 | .b2 => 2 | .b3 => 3 | .b4 => 4 | .b68 => 68

def bitOfBool : Bool → Fin 2
  | false => 0 | true => 1

def stepBootR (q' : BootState) (w : Bool) (L : List Bool) (R : List Bool) :
    Option (BootState × List Bool × Bool × List Bool) :=
  match R with
  | [] => some (q', w :: L, false, [])
  | r :: rs => some (q', w :: L, r, rs)

def stepBootL (q' : BootState) (w : Bool) (L : List Bool) (R : List Bool) :
    Option (BootState × List Bool × Bool × List Bool) :=
  match L with
  | [] => some (q', [], false, w :: R)
  | l :: ls => some (q', ls, l, w :: R)

def stepBoot (q : BootState) (L : List Bool) (h : Bool) (R : List Bool) :
    Option (BootState × List Bool × Bool × List Bool) :=
  match q, h with
  | .b0, false => stepBootR .b1 true L R
  | .b0, true => stepBootL .b2 false L R
  | .b1, false => stepBootR .b2 false L R
  | .b1, true => stepBootR .b1 false L R
  | .b2, false => stepBootL .b3 true L R
  | .b2, true => stepBootR .b4 false L R
  | .b3, false => stepBootL .b4 false L R
  | .b3, true => stepBootL .b68 false L R
  | .b4, false => stepBootL .b0 true L R
  | .b4, true => stepBootL .b1 false L R
  | .b68, _ => none

def runBoot : ℕ → BootState → List Bool → Bool → List Bool →
    Option (BootState × List Bool × Bool × List Bool)
  | 0, q, L, h, R => some (q, L, h, R)
  | n + 1, q, L, h, R =>
    match stepBoot q L h R with
    | none => none
    | some (q', L', h', R') => runBoot n q' L' h' R'

theorem runBoot_add (m n : ℕ) (q : BootState) (L : List Bool) (h : Bool)
    (R : List Bool) :
    runBoot (m + n) q L h R =
      match runBoot m q L h R with
      | none => none
      | some (q', L', h', R') => runBoot n q' L' h' R' := by
  induction m generalizing q L h R with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.succ_add, runBoot, runBoot]
    rcases stepBoot q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'

theorem stepFast_of_stepBoot {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hs : stepBoot q L h R = some (q', L', h', R')) :
    stepFast (stateOfBoot q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBoot q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  cases q <;> cases h <;> simp only [stepBoot] at hs
  all_goals try cases hs
  all_goals
    cases L <;> cases R <;>
    simp only [stepBootR, stepBootL, Option.some.injEq, Prod.mk.injEq] at hs <;>
    rcases hs with ⟨rfl, rfl, rfl, rfl⟩ <;>
    rfl

theorem runFast_of_runBoot (n : ℕ) {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hr : runBoot n q L h R = some (q', L', h', R')) :
    runFast n (stateOfBoot q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBoot q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
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
      rw [runFast, stepFast_of_stepBoot hst]
      exact ih hr

def bootChkL_0 : List Bool := [
  true, true, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  true]

def bootChkR_0 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true]

theorem boot_chk_0 :
    runBoot 5000 .b0 [] false [] =
      some (.b1, bootChkL_0, true, bootChkR_0) := by
  decide

def bootChkL_1 : List Bool := [
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, true, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, true, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, true, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, true]

def bootChkR_1 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true]

theorem boot_chk_1 :
    runBoot 5000 .b1 bootChkL_0 true bootChkR_0 =
      some (.b4, bootChkL_1, false, bootChkR_1) := by
  decide

def bootChkL_2 : List Bool := [
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, true, true, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, true, true, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, true, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, true]

def bootChkR_2 : List Bool := [
  true, true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true]

theorem boot_chk_2 :
    runBoot 5000 .b4 bootChkL_1 false bootChkR_1 =
      some (.b0, bootChkL_2, false, bootChkR_2) := by
  decide

def bootChkL_3 : List Bool := [
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  true, true, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, true, true, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, true, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, true]

def bootChkR_3 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true]

theorem boot_chk_3 :
    runBoot 5000 .b0 bootChkL_2 false bootChkR_2 =
      some (.b1, bootChkL_3, true, bootChkR_3) := by
  decide

def bootChkL_4 : List Bool := [
  false, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, true, false, true, false, false, false, true, false, false, false, true, false,
  false, true, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, true, true, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, true]

def bootChkR_4 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true]

theorem boot_chk_4 :
    runBoot 5000 .b1 bootChkL_3 true bootChkR_3 =
      some (.b4, bootChkL_4, false, bootChkR_4) := by
  decide

def bootChkL_5 : List Bool := [
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, true, true, false, false, false, true, false, false,
  true, true, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, true]

def bootChkR_5 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true]

theorem boot_chk_5 :
    runBoot 5000 .b4 bootChkL_4 false bootChkR_4 =
      some (.b1, bootChkL_5, true, bootChkR_5) := by
  decide

def bootChkL_6 : List Bool := [
  false, false, false, true, false, false, false, true, false, false, true, true, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, true, true, true,
  false, false, true, true, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, true]

def bootChkR_6 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true]

theorem boot_chk_6 :
    runBoot 5000 .b1 bootChkL_5 true bootChkR_5 =
      some (.b0, bootChkL_6, true, bootChkR_6) := by
  decide

def bootChkL_7 : List Bool := [
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, true]

def bootChkR_7 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true]

theorem boot_chk_7 :
    runBoot 4734 .b0 bootChkL_6 true bootChkR_6 =
      some (.b68, bootChkL_7, false, bootChkR_7) := by
  decide

theorem boot_phase1_39734 :
    runBoot 39734 .b0 [] false [] = some (.b68, bootChkL_7, false, bootChkR_7) := by
  have h : (39734 : ℕ) = 5000 + (5000 + (5000 + (5000 + (5000 + (5000 + (5000 + 4734)))))) := rfl
  simp only [h, runBoot_add, boot_chk_0, boot_chk_1, boot_chk_2, boot_chk_3, boot_chk_4,
    boot_chk_5, boot_chk_6, boot_chk_7]

theorem boot_fast_39734 :
    runFast 39734 0 [] 0 [] =
      some (68, bootChkL_7.map bitOfBool, 0, bootChkR_7.map bitOfBool) :=
  runFast_of_runBoot 39734 (q := .b0) (L := []) (h := false) (R := []) boot_phase1_39734

theorem runFast_add (m n : ℕ) (q : Fin 393) (L : List (Fin 2)) (h : Fin 2)
    (R : List (Fin 2)) :
    runFast (m + n) q L h R =
      match runFast m q L h R with
      | none => none
      | some (q', L', h', R') => runFast n q' L' h' R' := by
  induction m generalizing q L h R with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.succ_add, runFast, runFast]
    rcases stepFast q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'

theorem boot_fast_38 :
    runFast 38 68 (bootChkL_7.map bitOfBool) 0 (bootChkR_7.map bitOfBool) =
      some (60, List.replicate 10 0, 1,
        List.replicate 19 0 ++ fixedPrefix381 ++ encodeRegs (List.replicate 10 0) ++ [1]) := by
  decide

theorem boot_fast_39 :
    runFast 39 68 (bootChkL_7.map bitOfBool) 0 (bootChkR_7.map bitOfBool) =
      some (99, 1 :: List.replicate 10 0, 0,
        List.replicate 18 0 ++ fixedPrefix381 ++ encodeRegs (List.replicate 10 0) ++ [1]) := by
  decide

theorem prefix190_ne_nil : prefix190 ≠ [] := by decide
instance prefix190_ne_nil_fact : Fact (prefix190 ≠ []) := ⟨prefix190_ne_nil⟩

theorem fixedPrefix381_eq_encodeRegs : fixedPrefix381 = encodeRegs prefix190 := rfl

attribute [irreducible] prefix190 fixedPrefix381

theorem boot_fast_39772 :
    runFast 39772 0 [] 0 [] =
      some (60, List.replicate 10 0, 1,
        List.replicate 19 0 ++ fixedPrefix381 ++ encodeRegs (List.replicate 10 0) ++ [1]) := by
  have hadd : (39772 : ℕ) = 39734 + 38 := rfl
  have h34 : runFast 39734 0 [] 0 [] =
      some (68, bootChkL_7.map bitOfBool, 0, bootChkR_7.map bitOfBool) := boot_fast_39734
  rw [hadd, runFast_add, h34]
  exact boot_fast_38

theorem boot_fast_39773 :
    runFast 39773 0 [] 0 [] =
      some (99, 1 :: List.replicate 10 0, 0,
        List.replicate 18 0 ++ fixedPrefix381 ++ encodeRegs (List.replicate 10 0) ++ [1]) := by
  have hadd : (39773 : ℕ) = 39734 + 39 := rfl
  have h34 : runFast 39734 0 [] 0 [] =
      some (68, bootChkL_7.map bitOfBool, 0, bootChkR_7.map bitOfBool) := boot_fast_39734
  rw [hadd, runFast_add, h34]
  exact boot_fast_39

theorem init_eq_cfgOfFast : (init : Cfg 393 2) = cfgOfFast 0 [] 0 [] := by
  simp only [init, cfgOfFast, ListBlank.append, default_cons_zero]
  rfl

theorem regs10_snoc_one_eq_regsTape11 :
    ListBlank.append (encodeRegs (List.replicate 10 0)) LB01 =
      regsTape (List.replicate 11 0) := by
  have h10 : encodeRegs (List.replicate 11 0) =
      encodeRegs (List.replicate 10 0) ++ [1, 0] := rfl
  rw [regsTape, h10, ListBlank.append_assoc]
  simp only [ListBlank.append, default_cons_zero]

/-- In `39,772` steps from `init`, `zf393` reaches `5.root` (`State 60`) standing on `[1]`
immediately before `zf393RootCfg 19 [] (List.replicate 11 0)`. -/
theorem boot_reaches_root :
    nSteps zf393 39772 init =
      some ⟨60, Tape.mk' default
        ((ListBlank.append (List.replicate 19 0 ++ fixedPrefix381)
          (regsTape (List.replicate 11 0))).cons 1)⟩ := by
  rw [init_eq_cfgOfFast, nSteps_of_runFast, boot_fast_39772, Option.map_some]
  simp only [cfgOfFast, ListBlank.append, append_replicate_zero_default, List.append_assoc,
    ListBlank.append_assoc, regs10_snoc_one_eq_regsTape11]

/-- In `39,773` steps (`39,772` steps to `5.root` + 1 step into `main().0`), `zf393` reaches
`zf393RootCfg 19 [] (List.replicate 11 0)`. -/
theorem boot_reaches_main0 :
    nSteps zf393 39773 init = some (zf393RootCfg 19 [] (List.replicate 11 0)) := by
  rw [init_eq_cfgOfFast, nSteps_of_runFast, boot_fast_39773, Option.map_some]
  unfold zf393RootCfg rootCfg
  rw [← fixedPrefix381_eq_encodeRegs]
  simp only [cfgOfFast, ListBlank.append, append_replicate_zero_default, List.nil_append,
    List.length_nil, Nat.sub_zero, List.append_assoc, ListBlank.append_assoc,
    regs10_snoc_one_eq_regsTape11]
  rfl

/-!
## 3. Return Scans (`4.dispatch.1..9`, `5.root`) & Call-Stack Operations (`6.break`, `6.continue`)
-/

section GenericPrefix

variable {pre : List ℕ} [hpre : Fact (pre ≠ [])]


/-- Unified 10-state return scanner (`0 ↦ 6.continue.0 = 64`, `1..9 ↦ 4.dispatch.1..9 = 51..59`). -/
def zfScanState : ℕ → Fin 393
  | 0 => 64
  | 1 => 51
  | 2 => 52
  | 3 => 53
  | 4 => 54
  | 5 => 55
  | 6 => 56
  | 7 => 57
  | 8 => 58
  | 9 => 59
  | _ => 64

/-- Boolean check that scanning `rev` from `zfScanState z` (`z ∈ 0..9`) never sees 10 zeros. -/
def scanZerosOk (z : ℕ) : List (Fin 2) → Bool
  | [] => true
  | b :: xs =>
    if b == 0 then (if 9 ≤ z then false else scanZerosOk (z + 1) xs) else scanZerosOk 0 xs

/-- `NoNineZeros bits`: scanning `bits` from `4.dispatch.1` (`zfScanState 1`) never sees 9 zeros. -/
def NoNineZeros (bits : List (Fin 2)) : Prop :=
  scanZerosOk 1 bits.reverse = true

instance (bits : List (Fin 2)) : Decidable (NoNineZeros bits) :=
  inferInstanceAs (Decidable (scanZerosOk 1 bits.reverse = true))

theorem scanZerosOk_mono {z₁ z₂ : ℕ} (hz : z₁ ≤ z₂) :
    ∀ rev : List (Fin 2), scanZerosOk z₂ rev = true → scanZerosOk z₁ rev = true
  | [], _ => rfl
  | b :: xs, h => by
    rcases fin2_cases b with rfl | rfl
    · simp only [scanZerosOk] at h ⊢
      by_cases hz2 : 9 ≤ z₂
      · simp [hz2] at h
      · have hz1 : ¬ (9 ≤ z₁) := by omega
        simp only [Fin.isValue, BEq.rfl, ↓reduceIte, Bool.ite_false_left, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le] at h ⊢
        exact ⟨by omega, scanZerosOk_mono (by omega) xs h.2⟩
    · exact h

theorem scanZerosOk_tail {z : ℕ} {b : Fin 2} {xs : List (Fin 2)}
    (h : scanZerosOk z (b :: xs) = true) : scanZerosOk 0 xs = true := by
  rcases fin2_cases b with rfl | rfl
  · simp only [scanZerosOk] at h
    by_cases hz9 : 9 ≤ z
    · simp [hz9] at h
    · simp only [Fin.isValue, BEq.rfl, ↓reduceIte, Bool.ite_false_left, Bool.and_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le] at h
      exact scanZerosOk_mono (Nat.zero_le _) xs h.2
  · exact h

/-- Scanning left across `rev` from `zfScanState z` (`z ≤ 9`) when `scanZerosOk z rev = true`. -/
theorem zfScan_rev (rev : List (Fin 2)) (z : ℕ) (hz : z ≤ 9)
    (hok : scanZerosOk z rev = true) (R : ListBlank (Fin 2)) :
    ∃ z', z' ≤ 9 ∧
      nSteps zf393 rev.length ⟨zfScanState z, Tape.mkL (ListBlank.append rev default) R⟩ =
        some ⟨zfScanState z', Tape.mkL default (ListBlank.append rev.reverse R)⟩ := by
  induction rev generalizing z R with
  | nil => exact ⟨z, hz, rfl⟩
  | cons a xs ih =>
    rcases fin2_cases a with rfl | rfl
    · simp only [scanZerosOk] at hok
      by_cases hz9 : 9 ≤ z
      · simp [hz9] at hok
      · simp only [Fin.isValue, BEq.rfl, ↓reduceIte, Bool.ite_false_left, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le] at hok
        have hz8 : z ≤ 8 := by omega
        have htr0 : zf393Trans (zfScanState z) 0 = some (0, .left, zfScanState (z + 1)) := by
          match z with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl | _ + 9 => omega
        have hstep : step zf393 ⟨zfScanState z, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨zfScanState (z + 1), Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left htr0 _ _
        obtain ⟨z', hz', hrest⟩ := ih (z + 1) (by omega) hok.2 (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at hrest
        exact ⟨z', hz', step_nSteps hstep hrest⟩
    · have htr1 : zf393Trans (zfScanState z) 1 = some (1, .left, zfScanState 0) := by
        match z with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl | _ + 10 => omega
      have hstep : step zf393 ⟨zfScanState z, Tape.mkL ((ListBlank.append xs default).cons 1) R⟩ =
          some ⟨zfScanState 0, Tape.mkL (ListBlank.append xs default) (R.cons 1)⟩ :=
        step_mkL_left htr1 _ _
      obtain ⟨z', hz', hrest⟩ := ih 0 (by decide) hok (R.cons 1)
      rw [append_cons_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', step_nSteps hstep hrest⟩

/-- Bouncing off `default` from `zfScanState z` (`z ≤ 9`) into `5.root` (`State 60`). -/
theorem zfScan_bounce_default (z : ℕ) (hz : z ≤ 9) (R : ListBlank (Fin 2)) :
    nSteps zf393 (2 * (9 - z) + 1) ⟨zfScanState z, Tape.mkL default R⟩ =
      some ⟨60, Tape.mk' default R⟩ := by
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  generalize hd : 9 - z = d
  induction d generalizing z R with
  | zero =>
    have hz9 : z = 9 := by omega
    subst hz9
    apply step_one
    conv_lhs => rw [hdef]
    rw [step_mkL_right (by rfl), default_cons_zero]
  | succ d ih =>
    have hz8 : z ≤ 8 := by omega
    have htr0 : zf393Trans (zfScanState z) 0 = some (0, .left, zfScanState (z + 1)) := by
      match z with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl | _ + 9 => omega
    have h1 : step zf393 ⟨zfScanState z, Tape.mkL default R⟩ =
        some ⟨zfScanState (z + 1), Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left htr0 default R
    have h2 := ih (z + 1) (by omega) (R.cons 0) (by omega)
    have h3 : step zf393 ⟨60, Tape.mk' default (R.cons 0)⟩ =
        some ⟨60, Tape.mk' default R⟩ := by
      rw [step_mk'_right (by rfl), default_cons_zero]
    have hcomb := step_nSteps h1 (nSteps_bind_eq h2 (step_one h3))
    have hlen : 2 * d + 1 + 1 + 1 = 2 * (d + 1) + 1 := by omega
    rwa [hlen] at hcomb

/-- From `5.root` (`State 60`) on `1 :: R`, `zf393` steps onto `main().0` (`State 99`). -/
theorem root_scan_to_main0 (R : ListBlank (Fin 2)) :
    step zf393 ⟨60, Tape.mk' default (R.cons 1)⟩ =
      some ⟨99, Tape.mk' LB01 R⟩ :=
  step_mk'_right (by rfl) default R

/-- Unified return scan from `zfScanState z` (`z ≤ 9`) across `ip.reverse` on `default.cons 1`. -/
theorem scan_reaches_main0 (z : ℕ) (hz : z ≤ 9) (ip : List (Fin 2))
    (hok : scanZerosOk z (ip.reverse ++ [1]) = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧
      nSteps zf393 s ⟨zfScanState z, Tape.mkL (ListBlank.append ip.reverse LB01) R⟩ =
        some ⟨99, Tape.mk' LB01 (ListBlank.append ip R)⟩ := by
  have hL : ListBlank.append ip.reverse LB01 =
      ListBlank.append (ip.reverse ++ [1]) default := by
    rw [ListBlank.append_assoc]; rfl
  rw [hL]
  obtain ⟨z', hz', hscan⟩ := zfScan_rev (ip.reverse ++ [1]) z hz hok R
  have hrev : (ip.reverse ++ [1]).reverse = 1 :: ip := by
    simp [List.reverse_append]
  rw [hrev, ListBlank.append] at hscan
  have hbounce := zfScan_bounce_default z' hz' ((ListBlank.append ip R).cons 1)
  have hroot := step_one (root_scan_to_main0 (ListBlank.append ip R))
  exact ⟨_, by omega, nSteps_bind_eq hscan (nSteps_bind_eq hbounce hroot)⟩

/-- `4.dispatch.1` (`State 51`) scanning left across `L` (`NoNineZeros L`) on `default.cons 1`
reaches `main().0` (`State 99`) with `Tape.left = default.cons 1`. -/
theorem dispatch1_reaches_main0 (L : List (Fin 2)) (hok : NoNineZeros L)
    (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧
      nSteps zf393 s ⟨51, Tape.mkL (ListBlank.append L.reverse LB01) R⟩ =
        some ⟨99, Tape.mk' LB01 (ListBlank.append L R)⟩ := by
  have hok1 : scanZerosOk 1 (L.reverse ++ [1]) = true := by
    unfold NoNineZeros at hok
    have aux : ∀ z rev, scanZerosOk z rev = true → scanZerosOk z (rev ++ [1]) = true := by
      intro z rev h
      induction rev generalizing z with
      | nil => rfl
      | cons b xs ih =>
        rcases fin2_cases b with rfl | rfl
        · simp only [List.cons_append, scanZerosOk] at h ⊢
          by_cases hz9 : 9 ≤ z
          · simp [hz9] at h
          · simp only [Fin.isValue, BEq.rfl, ↓reduceIte, Bool.ite_false_left, Bool.and_eq_true,
              Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le] at h ⊢
            exact ⟨h.1, ih (z + 1) h.2⟩
        · exact ih 0 h
    exact aux 1 L.reverse hok
  exact scan_reaches_main0 1 (by decide) L hok1 R

def breakState : ℕ → Fin 393
  | 0 => 61
  | 1 => 62
  | _ => 63

def continueState : ℕ → Fin 393
  | 0 => 64
  | 1 => 65
  | 2 => 66
  | 3 => 67
  | _ => 68

theorem popBreakRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (popBreakRev k rev).length ≤ rev.length := by
  induction rev generalizing k with
  | nil => simp [popBreakRev]
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => simp [popBreakRev]
      | succ k' => have := ih k'; simp [popBreakRev]; omega
    · have := ih k; simp [popBreakRev]; omega

theorem popContinueRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (popContinueRev k rev).length ≤ rev.length := by
  induction rev generalizing k with
  | nil => simp [popContinueRev]
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · have := ih k; simp [popContinueRev]; omega
    · cases k with
      | zero => simp [popContinueRev]
      | succ k' => have := ih k'; simp [popContinueRev]; omega

theorem scanZerosOk_popBreakRev (k : ℕ) (rev : List (Fin 2))
    (hok : scanZerosOk 0 (rev ++ [1]) = true) :
    scanZerosOk 0 (popBreakRev k rev ++ [1]) = true := by
  induction rev generalizing k with
  | nil => exact hok
  | cons b xs ih =>
    have hxs : scanZerosOk 0 (xs ++ [1]) = true := scanZerosOk_tail hok
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => exact hxs
      | succ k' => exact ih k' hxs
    · exact ih k hxs

theorem scanZerosOk_popContinueRev (k : ℕ) (rev : List (Fin 2))
    (hok : scanZerosOk 0 (rev ++ [1]) = true) :
    scanZerosOk 0 (popContinueRev k rev ++ [1]) = true := by
  induction rev generalizing k with
  | nil => exact hok
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · exact ih k (scanZerosOk_tail hok)
    · cases k with
      | zero => exact hok
      | succ k' => exact ih k' (scanZerosOk_tail hok)

theorem popContinueRev_append_one (k : ℕ) (rev : List (Fin 2)) (hk : k ≤ rev.count 1) :
    popContinueRev k (rev ++ [1]) = popContinueRev k rev ++ [1] := by
  induction rev generalizing k with
  | nil =>
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0; rfl
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · exact ih k (by simpa using hk)
    · cases k with
      | zero => rfl
      | succ k' => exact ih k' (by rw [List.count_cons_self] at hk; omega)

def rawContinueRev (k : ℕ) : List (Fin 2) → List (Fin 2)
  | [] => []
  | b :: rest =>
    match k with
    | 0 => b :: rest
    | k' + 1 => if b == 0 then rawContinueRev (k' + 1) rest else rawContinueRev k' rest

theorem rawContinueRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (rawContinueRev k rev).length ≤ rev.length := by
  induction rev generalizing k with
  | nil => cases k <;> rfl
  | cons b xs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      rcases fin2_cases b with rfl | rfl
      · have := ih (k' + 1); simp [rawContinueRev]; omega
      · have := ih k'; simp [rawContinueRev]; omega

theorem popContinueRev_eq_zero_rawContinueRev (k : ℕ) (rev : List (Fin 2)) :
    popContinueRev k rev = popContinueRev 0 (rawContinueRev k rev) := by
  induction rev generalizing k with
  | nil => cases k <;> rfl
  | cons b xs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      rcases fin2_cases b with rfl | rfl
      · exact ih (k' + 1)
      · exact ih k'

theorem popContinueRev_zero_pad (rev : List (Fin 2)) :
    rev.reverse =
      (popContinueRev 0 rev).reverse ++
        List.replicate (rev.length - (popContinueRev 0 rev).length) 0 := by
  induction rev with
  | nil => rfl
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · have hsub : (0 :: xs).length - (popContinueRev 0 (0 :: xs)).length =
          (xs.length - (popContinueRev 0 xs).length) + 1 := by
        have := popContinueRev_length_le 0 xs
        simp [popContinueRev]; omega
      rw [List.reverse_cons, ih, hsub, List.replicate_succ', List.append_assoc]
      rfl
    · simp [popContinueRev]

theorem continueState_step0 (k : Fin 4) :
    zf393Trans (continueState (k.val + 1)) 0 = some (0, .left, continueState (k.val + 1)) := by
  revert k; decide

theorem continueState_step1 (k : Fin 4) :
    zf393Trans (continueState (k.val + 1)) 1 = some (0, .left, continueState k.val) := by
  revert k; decide

theorem continue_scan_to_64 (k : ℕ) (hk4 : k ≤ 4) (rev : List (Fin 2))
    (h1 : k ≤ rev.count 1) (L R : ListBlank (Fin 2)) :
    let w' := (rawContinueRev k rev).reverse
    ∃ s, nSteps zf393 s ⟨continueState k, Tape.mkL (ListBlank.append rev L) R⟩ =
      some ⟨64, Tape.mkL (ListBlank.append w'.reverse L)
        (ListBlank.append (List.replicate (rev.length - w'.length) 0) R)⟩ := by
  induction rev generalizing k R with
  | nil =>
    intro w'
    have hk0 : k = 0 := by simp at h1; omega
    subst hk0
    exact ⟨0, rfl⟩
  | cons b xs ih =>
    intro w'
    cases k with
    | zero =>
      have hsub : (b :: xs).length - w'.length = 0 := by
        simp [w', rawContinueRev]
      refine ⟨0, ?_⟩
      rw [hsub, List.replicate_zero, ListBlank.append, List.reverse_reverse]
      rfl
    | succ k' =>
      have hk'3 : k' < 4 := by omega
      rcases fin2_cases b with rfl | rfl
      · have htr0 := continueState_step0 ⟨k', hk'3⟩
        have hstep : step zf393
            ⟨continueState (k' + 1), Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
            some ⟨continueState (k' + 1), Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
          step_mkL_left htr0 _ _
        obtain ⟨s, hs⟩ := ih (k' + 1) hk4 (by simpa using h1) (R.cons 0)
        have hw'_eq : (rawContinueRev (k' + 1) xs).reverse = w' := rfl
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]; exact rawContinueRev_length_le (k' + 1) xs
        have hsub : (0 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by simp; omega
        rw [hw'_eq, append_replicate_cons, ← hsub] at hs
        exact ⟨s + 1, step_nSteps hstep hs⟩
      · have htr1 := continueState_step1 ⟨k', hk'3⟩
        have hstep : step zf393
            ⟨continueState (k' + 1), Tape.mkL ((ListBlank.append xs L).cons 1) R⟩ =
            some ⟨continueState k', Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
          step_mkL_left htr1 _ _
        obtain ⟨s, hs⟩ := ih k' (by omega) (by rw [List.count_cons_self] at h1; omega) (R.cons 0)
        have hw'_eq : (rawContinueRev k' xs).reverse = w' := rfl
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]; exact rawContinueRev_length_le k' xs
        have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by simp; omega
        rw [hw'_eq, append_replicate_cons, ← hsub] at hs
        exact ⟨s + 1, step_nSteps hstep hs⟩

theorem scanZerosOk_rawContinueRev (m : ℕ) (rev : List (Fin 2))
    (h : scanZerosOk 0 (rev ++ [1]) = true) :
    scanZerosOk 0 (rawContinueRev m rev ++ [1]) = true := by
  induction rev generalizing m with
  | nil => cases m <;> exact h
  | cons b xs ih =>
    cases m with
    | zero => exact h
    | succ m' =>
      rcases fin2_cases b with rfl | rfl
      · exact ih (m' + 1) (scanZerosOk_tail h)
      · exact ih m' (scanZerosOk_tail h)

omit hpre in
theorem continue_k_reaches_main0 (k : ℕ) (hk4 : k ≤ 4) (slot : ℕ) (P : List (Fin 2))
    (h1 : k ≤ P.count 1) (hsl : P.length ≤ slot)
    (hok : scanZerosOk 0 (P.reverse ++ [1]) = true) (regs : List ℕ) :
    let ip' := (popContinueRev k P.reverse).reverse
    ∃ s, 1 ≤ s ∧
      nSteps zf393 s ⟨continueState k, Tape.mkL (ListBlank.append P.reverse LB01)
        (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
          (regsTape regs))⟩ =
      some (@rootCfg pre slot ip' regs) := by
  intro ip'
  have h1_rev : k ≤ P.reverse.count 1 := by rwa [List.count_reverse]
  obtain ⟨s₁, hs₁⟩ := continue_scan_to_64 k hk4 P.reverse h1_rev LB01
    (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre) (regsTape regs))
  let raw := rawContinueRev k P.reverse
  have hlen_raw : raw.length ≤ P.length := by
    rw [← P.length_reverse]; exact rawContinueRev_length_le k P.reverse
  have hlen_ip' : ip'.length ≤ raw.length := by
    dsimp only [ip', raw]
    rw [popContinueRev_eq_zero_rawContinueRev, List.length_reverse]
    exact popContinueRev_length_le 0 _
  have hok_raw : scanZerosOk 0 (raw.reverse.reverse ++ [1]) = true := by
    rw [List.reverse_reverse]
    exact scanZerosOk_rawContinueRev k P.reverse hok
  obtain ⟨s₂, hs₂_pos, hs₂⟩ := scan_reaches_main0 0 (by decide) raw.reverse hok_raw
    (ListBlank.append (List.replicate (P.reverse.length - raw.reverse.length) 0)
      (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
        (regsTape regs)))
  have hraw_pad : raw.reverse = ip' ++ List.replicate (raw.length - ip'.length) 0 := by
    dsimp only [ip', raw]
    rw [popContinueRev_eq_zero_rawContinueRev, List.length_reverse]
    exact popContinueRev_zero_pad _
  have htot : (raw.length - ip'.length) + (P.reverse.length - raw.reverse.length) +
      (slot - P.length) = slot - ip'.length := by
    simp only [List.length_reverse]; omega
  have hR : ListBlank.append raw.reverse
      (ListBlank.append (List.replicate (P.reverse.length - raw.reverse.length) 0)
        (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
          (regsTape regs))) =
      ListBlank.append (ip' ++ List.replicate (slot - ip'.length) 0 ++ encodeRegs pre)
        (regsTape regs) := by
    conv_lhs => arg 1; rw [hraw_pad]
    rw [← ListBlank.append_assoc, List.append_assoc ip', ← List.replicate_add,
      ← ListBlank.append_assoc, ← List.append_assoc, List.append_assoc ip', ← List.replicate_add,
      htot]
  rw [hR] at hs₂
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem break_scan_to_64 (k : ℕ) (hk2 : k ≤ 2) (rev : List (Fin 2))
    (h0 : k + 1 ≤ rev.count 0) (L R : ListBlank (Fin 2)) :
    let w' := (popBreakRev k rev).reverse
    ∃ s, 1 ≤ s ∧ nSteps zf393 s ⟨breakState k, Tape.mkL (ListBlank.append rev L) R⟩ =
      some ⟨64, Tape.mkL (ListBlank.append (w'.reverse.tail) L)
        ((ListBlank.append (List.replicate (rev.length - w'.length) 0) R).cons 1)⟩ := by
  induction rev generalizing k R with
  | nil => simp at h0
  | cons b xs ih =>
    intro w'
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero =>
        have hstep : step zf393 ⟨61, Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
            some ⟨64, Tape.mkL (ListBlank.append xs L) (R.cons 1)⟩ :=
          step_mkL_left (by rfl) _ _
        have hw'_rev : w'.reverse = 1 :: xs := by simp [w', popBreakRev]
        have hsub : (0 :: xs).length - w'.length = 0 := by
          have : w'.length = (0 :: xs).length := by rw [← List.length_reverse, hw'_rev]; rfl
          omega
        refine ⟨1, le_refl 1, ?_⟩
        rw [hw'_rev, List.tail_cons, hsub, List.replicate_zero, ListBlank.append]
        exact step_one hstep
      | succ k' =>
        have hk'1 : k' ≤ 1 := by omega
        have htr0 : zf393Trans (breakState (k' + 1)) 0 = some (0, .left, breakState k') := by
          match k' with | 0 | 1 => rfl | _ + 2 => omega
        have hstep : step zf393
            ⟨breakState (k' + 1), Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
            some ⟨breakState k', Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
          step_mkL_left htr0 _ _
        obtain ⟨s, hs1, hs⟩ := ih k' (by omega) (by rw [List.count_cons_self] at h0; omega)
          (R.cons 0)
        have hw'_eq : (popBreakRev k' xs).reverse = w' := rfl
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]; exact popBreakRev_length_le k' xs
        have hsub : (0 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by simp; omega
        rw [hw'_eq, append_replicate_cons, ← hsub] at hs
        exact ⟨s + 1, by omega, step_nSteps hstep hs⟩
    · have htr1 : zf393Trans (breakState k) 1 = some (0, .left, breakState k) := by
        match k with | 0 | 1 | 2 => rfl | _ + 3 => omega
      have hstep : step zf393 ⟨breakState k, Tape.mkL ((ListBlank.append xs L).cons 1) R⟩ =
          some ⟨breakState k, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
        step_mkL_left htr1 _ _
      obtain ⟨s, hs1, hs⟩ := ih k hk2 (by simpa using h0) (R.cons 0)
      have hw'_eq : (popBreakRev k xs).reverse = w' := rfl
      have hlen_le : w'.length ≤ xs.length := by
        rw [← hw'_eq, List.length_reverse]; exact popBreakRev_length_le k xs
      have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by simp; omega
      rw [hw'_eq, append_replicate_cons, ← hsub] at hs
      exact ⟨s + 1, by omega, step_nSteps hstep hs⟩

/-- Slot size after `6.break.k` (`k ∈ {0..2}`) on `P` (`slot` if `k + 1 ≤ P.count 0`,
or `slot + (k - P.count 0) + 1` when `P` overflows past the root `1`!). -/
def breakSlot (k slot : ℕ) (P : List (Fin 2)) : ℕ :=
  if k + 1 ≤ P.count 0 then slot else slot + (k - P.count 0) + 1

theorem breakSlot_ge (k slot : ℕ) (P : List (Fin 2)) : slot ≤ breakSlot k slot P := by
  unfold breakSlot; split <;> omega

theorem popBreakRev_append_of_le (k : ℕ) (rev tail : List (Fin 2)) (h : k + 1 ≤ rev.count 0) :
    popBreakRev k (rev ++ tail) = popBreakRev k rev ++ tail := by
  induction rev generalizing k with
  | nil => simp at h
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => rfl
      | succ k' => exact ih k' (by rw [List.count_cons_self] at h; omega)
    · exact ih k (by simpa using h)

theorem popBreakRev_head_one (k : ℕ) (rev : List (Fin 2)) (h : k + 1 ≤ rev.count 0) :
    popBreakRev k rev = 1 :: (popBreakRev k rev).tail := by
  induction rev generalizing k with
  | nil => simp at h
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => rfl
      | succ k' => exact ih k' (by rw [List.count_cons_self] at h; omega)
    · exact ih k (by simpa using h)

theorem popBreakRev_overflow (k : ℕ) (rev : List (Fin 2)) (h : rev.count 0 ≤ k) :
    popBreakRev k rev = [] ∧
      popBreakRev k (rev ++ [1] ++ List.replicate (k + 1) 0) =
        1 :: List.replicate (rev.count 0) 0 := by
  induction rev generalizing k with
  | nil =>
    simp only [List.count_nil, List.nil_append] at *
    have aux : ∀ m : ℕ, popBreakRev m (List.replicate (m + 1) 0) = [1] := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => exact ih
    exact ⟨rfl, aux k⟩
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => simp [List.count_cons_self] at h
      | succ k' =>
        have hxs : xs.count 0 ≤ k' := by rw [List.count_cons_self] at h; omega
        obtain ⟨h1, h2⟩ := ih k' hxs
        refine ⟨h1, ?_⟩
        have hstep0 :
            popBreakRev (k' + 1) ((0 :: xs) ++ [1] ++ List.replicate (k' + 1 + 1) 0) =
            popBreakRev k' (xs ++ [1] ++ List.replicate (k' + 2) 0) := rfl
        have hcnt0 : (0 :: xs).count 0 = xs.count 0 + 1 := List.count_cons_self
        rw [hstep0, hcnt0]
        have hrep : List.replicate (k' + 2) (0 : Fin 2) = List.replicate (k' + 1) 0 ++ [0] :=
          List.replicate_succ'
        have hcnt : k' + 1 ≤ (xs ++ [1] ++ List.replicate (k' + 1) 0).count 0 := by
          simp
        rw [hrep, ← List.append_assoc, popBreakRev_append_of_le k' _ [0] hcnt, h2,
          List.cons_append, ← List.replicate_succ']
    · obtain ⟨h1, h2⟩ := ih k (by simpa using h)
      exact ⟨h1, h2⟩

omit hpre in
/-- Unified return lemma for `6.break.k` (`k ∈ {0..2}`) starting left across `P.reverse`
on `default.cons 1`, handling both normal break and root overflow (`slot' = breakSlot k slot P`)! -/
theorem break_k_reaches_main0 (k : ℕ) (hk2 : k ≤ 2) (slot : ℕ) (P : List (Fin 2))
    (hsl : P.length ≤ slot) (hok : scanZerosOk 0 (P.reverse ++ [1]) = true) (regs : List ℕ) :
    let ip' := (popBreakRev k P.reverse).reverse
    ∃ s, 1 ≤ s ∧
      nSteps zf393 s ⟨breakState k, Tape.mkL (ListBlank.append P.reverse LB01)
        (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
          (regsTape regs))⟩ =
      some (@rootCfg pre (breakSlot k slot P) ip' regs) := by
  intro ip'
  by_cases hlt : k + 1 ≤ P.count 0
  · have hlt_rev : k + 1 ≤ P.reverse.count 0 := by rwa [List.count_reverse]
    obtain ⟨s₁, hs₁_pos, hs₁⟩ := break_scan_to_64 k hk2 P.reverse hlt_rev LB01
      (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre) (regsTape regs))
    have hhead := popBreakRev_head_one k P.reverse hlt_rev
    have hip'_rev : ip'.reverse = 1 :: ip'.reverse.tail := by simpa [ip'] using hhead
    have hok' : scanZerosOk 0 (ip'.reverse.tail ++ [1]) = true := by
      have hfull : scanZerosOk 0 (ip'.reverse ++ [1]) = true := by
        simpa [ip'] using scanZerosOk_popBreakRev k P.reverse hok
      rw [hip'_rev] at hfull
      exact scanZerosOk_tail hfull
    obtain ⟨s₂, hs₂_pos, hs₂⟩ := scan_reaches_main0 0 (by decide) ip'.reverse.tail.reverse
      (by simpa [List.reverse_reverse] using hok')
      ((ListBlank.append (List.replicate (P.reverse.length - ip'.length) 0)
        (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
          (regsTape regs))).cons 1)
    rw [List.reverse_reverse] at hs₂
    have hlen_le : ip'.length ≤ P.length := by
      have := popBreakRev_length_le k P.reverse; simpa [ip'] using this
    have hpad : P.reverse.length - ip'.length + (slot - P.length) = slot - ip'.length := by
      simp; omega
    have hR : ListBlank.append ip'.reverse.tail.reverse
        ((ListBlank.append (List.replicate (P.reverse.length - ip'.length) 0)
          (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
            (regsTape regs))).cons 1) =
        ListBlank.append (ip' ++ List.replicate (slot - ip'.length) 0 ++ encodeRegs pre)
          (regsTape regs) := by
      have hip'_snoc : ip'.reverse.tail.reverse ++ [1] = ip' := by
        conv_rhs => rw [← List.reverse_reverse ip', hip'_rev]
        simp
      rw [append_cons_snoc, ← ListBlank.append_assoc, hip'_snoc, ← ListBlank.append_assoc,
        ← List.append_assoc, List.append_assoc ip', ← List.replicate_add, hpad]
    rw [hR] at hs₂
    have hbs : breakSlot k slot P = slot := by unfold breakSlot; simp [hlt]
    rw [hbs]
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩
  · have hle : P.reverse.count 0 ≤ k := by rw [List.count_reverse]; omega
    obtain ⟨hpop_nil, hpop_full⟩ := popBreakRev_overflow k P.reverse hle
    have hip'_nil : ip' = [] := by simp [ip', hpop_nil]
    set full_rev := P.reverse ++ [1] ++ List.replicate (k + 1) 0
    have hL_eq : ListBlank.append P.reverse LB01 =
        ListBlank.append full_rev default := by
      unfold full_rev
      rw [ListBlank.append_assoc, ListBlank.append_assoc]
      simp only [ListBlank.append, append_replicate_zero_default]
    have hfull0 : k + 1 ≤ full_rev.count 0 := by
      unfold full_rev; simp
    rw [hL_eq]
    obtain ⟨s₁, hs₁_pos, hs₁⟩ := break_scan_to_64 k hk2 full_rev hfull0 default
      (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre) (regsTape regs))
    have hw_rev : (popBreakRev k full_rev).reverse.reverse.tail =
        List.replicate (P.reverse.count 0) 0 := by
      rw [List.reverse_reverse, hpop_full, List.tail_cons]
    have hw_len : (popBreakRev k full_rev).reverse.length = P.count 0 + 1 := by
      rw [List.length_reverse, hpop_full, List.length_cons, List.length_replicate,
        List.count_reverse]
    have hfull_len : full_rev.length - (popBreakRev k full_rev).reverse.length =
        P.length + (k - P.count 0) + 1 := by
      rw [hw_len]; unfold full_rev; simp; omega
    rw [hw_rev, hfull_len, append_replicate_zero_default] at hs₁
    have hbounce := zfScan_bounce_default 0 (by decide)
      ((ListBlank.append (List.replicate (P.length + (k - P.count 0) + 1) 0)
        (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
           (regsTape regs))).cons 1)
    have hroot := step_one (root_scan_to_main0
      (ListBlank.append (List.replicate (P.length + (k - P.count 0) + 1) 0)
        (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
          (regsTape regs))))
    have hbs : breakSlot k slot P = slot + (k - P.count 0) + 1 := by
      unfold breakSlot; simp [hlt]
    have hpad : P.length + (k - P.count 0) + 1 + (slot - P.length) =
        slot + (k - P.count 0) + 1 := by omega
    rw [hip'_nil, hbs]
    have hR : ListBlank.append (List.replicate (P.length + (k - P.count 0) + 1) 0)
        (ListBlank.append (List.replicate (slot - P.length) 0 ++ encodeRegs pre)
          (regsTape regs)) =
        ListBlank.append (([] : List (Fin 2)) ++
          List.replicate (slot + (k - P.count 0) + 1 - ([] : List (Fin 2)).length) 0 ++
          encodeRegs pre) (regsTape regs) := by
      dsimp only [List.nil_append, List.length_nil, Nat.sub_zero]
      rw [← ListBlank.append_assoc, ← List.append_assoc, ← List.replicate_add, hpad]
    have htot := nSteps_bind_eq hs₁ (nSteps_bind_eq hbounce hroot)
    rw [hR] at htot
    exact ⟨_, by omega, htot⟩

/-!
## 4. Moving `00` Selector (`zf393SelRight`, `1.sel`), `1.inc`, `1.decnz`, & Leaf Gadgets
-/

/-- Selector tape suffix with `m` registers (`0 ≤ m ≤ 11`) shifted to the right of `00`:
`encodeRegs (pre ++ regs.take (11 - m))` followed by `(regsTape (regs.drop (11 - m))).cons 0`.
When `m = 0` (`regs.length = 11`), this equals
`ListBlank.append (encodeRegs pre) (regsTape regs)`. -/
def zf393SelRight (pre : List ℕ) (m : ℕ) (regs : List ℕ) : ListBlank (Fin 2) :=
  ListBlank.append (encodeRegs (pre ++ regs.take (11 - m)))
    ((regsTape (regs.drop (11 - m))).cons 0)

theorem zf393SelRight_zero (pre : List ℕ) (regs : List ℕ) (h : regs.length = 11) :
    zf393SelRight pre 0 regs = ListBlank.append (encodeRegs pre) (regsTape regs) := by
  unfold zf393SelRight
  rw [Nat.sub_zero, List.take_of_length_le (by omega), List.drop_of_length_le (by omega),
    regsTape_nil, default_cons_zero, encodeRegs_append, ListBlank.append_assoc]
  rfl

theorem ret1_scan_reg (u : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 (u + 2) ⟨23, Tape.mkL (ListBlank.append (encodeReg u).reverse L) R⟩ =
      some ⟨23, Tape.mkL L (ListBlank.append (encodeReg u) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step zf393
      ⟨23, Tape.mkL (((ListBlank.append (List.replicate u 1) L).cons 1).cons 0) R⟩ =
      some ⟨24, Tape.mkL ((ListBlank.append (List.replicate u 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step zf393
      ⟨24, Tape.mkL ((ListBlank.append (List.replicate u 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨23, Tape.mkL (ListBlank.append (List.replicate u 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 23) (a := 1) (b := 1) (by rfl) u L
    ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  have hlen : u + 1 + 1 = u + 2 := rfl
  rw [hlen, append_replicate_cons, append_cons_snoc] at hcomb
  exact hcomb

theorem append_replicate_inner_cons {n : ℕ} {a : Fin 2} {L : ListBlank (Fin 2)} :
    ListBlank.append (List.replicate n a) (L.cons a) =
      (ListBlank.append (List.replicate n a) L).cons a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, ListBlank.append, ih]

theorem ret1_scan_regs (rs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 (encodeRegs rs).length
      ⟨23, Tape.mkL (ListBlank.append (encodeRegs rs).reverse L) R⟩ =
      some ⟨23, Tape.mkL L (ListBlank.append (encodeRegs rs) R)⟩ := by
  induction rs using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton rs u ih =>
    rw [encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil, List.reverse_append,
      ListBlank.append_assoc, ListBlank.append_assoc]
    have h1 := ret1_scan_reg u (ListBlank.append (encodeRegs rs).reverse L) R
    have h2 := ih (ListBlank.append (encodeReg u) R)
    have hcomb := nSteps_bind_eq h1 h2
    have hlen : u + 2 + (encodeRegs rs).length =
        (encodeRegs rs ++ encodeReg u).length := by
      rw [List.length_append, encodeReg_length]; omega
    rwa [hlen] at hcomb

theorem ret1_finish (rs : List ℕ) (z : ℕ) (L R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨23, Tape.mkL (ListBlank.append (encodeRegs rs).reverse
        (ListBlank.append (List.replicate (z + 2) 0) (L.cons 1))) R⟩ =
      some ⟨61, Tape.mkL L
        (ListBlank.append (List.replicate (z + 3) 0) (ListBlank.append (encodeRegs rs) R))⟩ := by
  have h1 := ret1_scan_regs rs (ListBlank.append (List.replicate (z + 2) 0) (L.cons 1)) R
  set R₁ := ListBlank.append (encodeRegs rs) R
  have hz1 : step zf393
      ⟨23, Tape.mkL (((ListBlank.append (List.replicate z 0) (L.cons 1)).cons 0).cons 0) R₁⟩ =
      some ⟨24, Tape.mkL ((ListBlank.append (List.replicate z 0) (L.cons 1)).cons 0)
        (R₁.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hz2 : step zf393
      ⟨24, Tape.mkL ((ListBlank.append (List.replicate z 0) (L.cons 1)).cons 0) (R₁.cons 0)⟩ =
      some ⟨25, Tape.mkL (ListBlank.append (List.replicate z 0) (L.cons 1))
        ((R₁.cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 25) (a := 0) (b := 0) (by rfl) z (L.cons 1)
    ((R₁.cons 0).cons 0)
  have hm1 : step zf393
      ⟨25, Tape.mkL (L.cons 1) (ListBlank.append (List.replicate z 0) ((R₁.cons 0).cons 0))⟩ =
      some ⟨61, Tape.mkL L
        ((ListBlank.append (List.replicate z 0) ((R₁.cons 0).cons 0)).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq h1 (step_nSteps hz1 (step_nSteps hz2
    (nSteps_bind_eq hscan (step_one hm1))))
  have hrep : ((ListBlank.append (List.replicate z 0) ((R₁.cons 0).cons 0)).cons 0) =
      ListBlank.append (List.replicate (z + 3) 0) R₁ := by
    rw [append_replicate_cons, append_replicate_cons]; rfl
  rw [hrep] at hcomb
  exact ⟨_, by omega, hcomb⟩

theorem ret2_scan_reg (u : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 (u + 2) ⟨26, Tape.mkL (ListBlank.append (encodeReg u).reverse L) R⟩ =
      some ⟨26, Tape.mkL L (ListBlank.append (encodeReg u) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step zf393
      ⟨26, Tape.mkL (((ListBlank.append (List.replicate u 1) L).cons 1).cons 0) R⟩ =
      some ⟨27, Tape.mkL ((ListBlank.append (List.replicate u 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step zf393
      ⟨27, Tape.mkL ((ListBlank.append (List.replicate u 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨26, Tape.mkL (ListBlank.append (List.replicate u 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 26) (a := 1) (b := 1) (by rfl) u L
    ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  have hlen : u + 1 + 1 = u + 2 := rfl
  rw [hlen, append_replicate_cons, append_cons_snoc] at hcomb
  exact hcomb

theorem ret2_scan_regs (rs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 (encodeRegs rs).length
      ⟨26, Tape.mkL (ListBlank.append (encodeRegs rs).reverse L) R⟩ =
      some ⟨26, Tape.mkL L (ListBlank.append (encodeRegs rs) R)⟩ := by
  induction rs using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton rs u ih =>
    rw [encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil, List.reverse_append,
      ListBlank.append_assoc, ListBlank.append_assoc]
    have h1 := ret2_scan_reg u (ListBlank.append (encodeRegs rs).reverse L) R
    have h2 := ih (ListBlank.append (encodeReg u) R)
    have hcomb := nSteps_bind_eq h1 h2
    have hlen : u + 2 + (encodeRegs rs).length =
        (encodeRegs rs ++ encodeReg u).length := by
      rw [List.length_append, encodeReg_length]; omega
    rwa [hlen] at hcomb

theorem ret2_finish (rs : List ℕ) (z : ℕ) (L R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨26, Tape.mkL (ListBlank.append (encodeRegs rs).reverse
        (ListBlank.append (List.replicate (z + 2) 0) (L.cons 1))) R⟩ =
      some ⟨62, Tape.mkL L
        (ListBlank.append (List.replicate (z + 3) 0) (ListBlank.append (encodeRegs rs) R))⟩ := by
  have h1 := ret2_scan_regs rs (ListBlank.append (List.replicate (z + 2) 0) (L.cons 1)) R
  set R₁ := ListBlank.append (encodeRegs rs) R
  have hz1 : step zf393
      ⟨26, Tape.mkL (((ListBlank.append (List.replicate z 0) (L.cons 1)).cons 0).cons 0) R₁⟩ =
      some ⟨27, Tape.mkL ((ListBlank.append (List.replicate z 0) (L.cons 1)).cons 0)
        (R₁.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hz2 : step zf393
      ⟨27, Tape.mkL ((ListBlank.append (List.replicate z 0) (L.cons 1)).cons 0) (R₁.cons 0)⟩ =
      some ⟨28, Tape.mkL (ListBlank.append (List.replicate z 0) (L.cons 1))
        ((R₁.cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 28) (a := 0) (b := 0) (by rfl) z (L.cons 1)
    ((R₁.cons 0).cons 0)
  have hm1 : step zf393
      ⟨28, Tape.mkL (L.cons 1) (ListBlank.append (List.replicate z 0) ((R₁.cons 0).cons 0))⟩ =
      some ⟨62, Tape.mkL L
        ((ListBlank.append (List.replicate z 0) ((R₁.cons 0).cons 0)).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq h1 (step_nSteps hz1 (step_nSteps hz2
    (nSteps_bind_eq hscan (step_one hm1))))
  have hrep : ((ListBlank.append (List.replicate z 0) ((R₁.cons 0).cons 0)).cons 0) =
      ListBlank.append (List.replicate (z + 3) 0) R₁ := by
    rw [append_replicate_cons, append_replicate_cons]; rfl
  rw [hrep] at hcomb
  exact ⟨_, by omega, hcomb⟩

theorem sel_scan_reg (u : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 (u + 2) ⟨20, Tape.mk' L (ListBlank.append (encodeReg u) R)⟩ =
      some ⟨20, Tape.mk' (ListBlank.append (encodeReg u).reverse L) R⟩ := by
  rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step zf393
      ⟨20, Tape.mk' L ((ListBlank.append (List.replicate u 1) (R.cons 0)).cons 1)⟩ =
      some ⟨19, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate u 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 19) (a := 1) (b := 1) (by rfl) u (L.cons 1)
    (R.cons 0)
  have h2 : step zf393
      ⟨19, Tape.mk' (ListBlank.append (List.replicate u 1) (L.cons 1)) (R.cons 0)⟩ =
      some ⟨20, Tape.mk' ((ListBlank.append (List.replicate u 1) (L.cons 1)).cons 0) R⟩ :=
    step_mk'_right (by rfl) _ _
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  have henc : ((ListBlank.append (List.replicate u 1) (L.cons 1)).cons 0) =
      ListBlank.append (encodeReg u).reverse L := by
    rw [append_replicate_cons, append_encodeReg_reverse]
  have hlen : u + 1 + 1 = u + 2 := rfl
  rwa [hlen, henc] at hcomb

theorem sel_scan_regs (rs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 (encodeRegs rs).length ⟨20, Tape.mk' L (ListBlank.append (encodeRegs rs) R)⟩ =
      some ⟨20, Tape.mk' (ListBlank.append (encodeRegs rs).reverse L) R⟩ := by
  induction rs generalizing L with
  | nil => rfl
  | cons u rs ih =>
    rw [encodeRegs_cons, ListBlank.append_assoc]
    have h1 := sel_scan_reg u L (ListBlank.append (encodeRegs rs) R)
    have h2 := ih (ListBlank.append (encodeReg u).reverse L)
    have hcomb := nSteps_bind_eq h1 h2
    have hrev : ListBlank.append (encodeRegs rs).reverse
        (ListBlank.append (encodeReg u).reverse L) =
        ListBlank.append (encodeReg u ++ encodeRegs rs).reverse L := by
      rw [← ListBlank.append_assoc, ← List.reverse_append]
    have hlen : u + 2 + (encodeRegs rs).length =
        (encodeReg u ++ encodeRegs rs).length := by
      rw [List.length_append, encodeReg_length]
    rw [hlen, hrev] at hcomb
    exact hcomb

/-- One pass of `1.sel` (`State 17`) on `zf393SelRight pre m regs` (`m < 11`) shifts one register
across `00` (`m ↦ m + 1`) and returns to `6.break.0` (`State 61`). -/
theorem sel_pass_to_61 (m : ℕ) (hm : m < 11) (z : ℕ) (regs : List ℕ) (hregs : regs.length = 11)
    (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨17, Tape.mk' L
        (ListBlank.append (List.replicate (z + 3) 0) (zf393SelRight pre m regs))⟩ =
      some ⟨61, Tape.mkL L
        (ListBlank.append (List.replicate (z + 3) 0) (zf393SelRight pre (m + 1) regs))⟩ := by
  have htake : regs.take (11 - m) = regs.take (10 - m) ++ [regs[10 - m]] := by
    have h11 : 11 - m = (10 - m) + 1 := by omega
    rw [h11, List.take_add_one, getElem?_pos regs (10 - m) (by omega), Option.toList_some]
  set v := regs[10 - m]
  set rs_pre := pre ++ regs.take (10 - m)
  have hrs_ne : rs_pre ≠ [] := by simp [rs_pre, hpre.out]
  have hrs_split : pre ++ regs.take (11 - m) = rs_pre ++ [v] := by
    rw [htake, List.append_assoc]
  unfold zf393SelRight
  rw [hrs_split, encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil,
    ListBlank.append_assoc]
  set R_tail := regsTape (regs.drop (11 - m))
  have hs1 : step zf393
      ⟨17, Tape.mk' L ((ListBlank.append (List.replicate (z + 2) 0)
        (ListBlank.append (encodeRegs rs_pre)
          (ListBlank.append (encodeReg v) (R_tail.cons 0)))).cons 0)⟩ =
      some ⟨18, Tape.mk' (L.cons 1)
        (ListBlank.append (List.replicate (z + 2) 0)
          (ListBlank.append (encodeRegs rs_pre)
            (ListBlank.append (encodeReg v) (R_tail.cons 0))))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan0 := nSteps_mk'_right_scan (q := 18) (a := 0) (b := 0) (by rfl) (z + 2) (L.cons 1)
    (ListBlank.append (encodeRegs rs_pre) (ListBlank.append (encodeReg v) (R_tail.cons 0)))
  set L_z := ListBlank.append (List.replicate (z + 2) 0) (L.cons 1)
  obtain ⟨u₀, rs_rest, hpre_cons⟩ : ∃ u₀ rs_rest, rs_pre = u₀ :: rs_rest := by
    rcases h : rs_pre with _ | ⟨u₀, rs_rest⟩
    · exact absurd h hrs_ne
    · exact ⟨u₀, rs_rest, rfl⟩
  have h18_to_20 : nSteps zf393 (encodeRegs rs_pre).length
      ⟨18, Tape.mk' L_z
        (ListBlank.append (encodeRegs rs_pre)
          (ListBlank.append (encodeReg v) (R_tail.cons 0)))⟩ =
      some ⟨20, Tape.mk' (ListBlank.append (encodeRegs rs_pre).reverse L_z)
        (ListBlank.append (encodeReg v) (R_tail.cons 0))⟩ := by
    rw [hpre_cons, encodeRegs_cons, ListBlank.append_assoc]
    have hfirst : nSteps zf393 (u₀ + 2)
        ⟨18, Tape.mk' L_z
          (ListBlank.append (encodeReg u₀)
            (ListBlank.append (encodeRegs rs_rest)
              (ListBlank.append (encodeReg v) (R_tail.cons 0))))⟩ =
        some ⟨20, Tape.mk' (ListBlank.append (encodeReg u₀).reverse L_z)
          (ListBlank.append (encodeRegs rs_rest)
            (ListBlank.append (encodeReg v) (R_tail.cons 0)))⟩ := by
      rw [append_encodeReg, List.replicate_succ, ListBlank.append]
      set R_u0 := ListBlank.append (encodeRegs rs_rest)
        (ListBlank.append (encodeReg v) (R_tail.cons 0))
      have ha1 := step_mk'_right (q := 18) (q' := 19) (a := 1) (b := 1) (by rfl) L_z
        (ListBlank.append (List.replicate u₀ 1) (R_u0.cons 0))
      have hasc := nSteps_mk'_right_scan (q := 19) (a := 1) (b := 1) (by rfl) u₀ (L_z.cons 1)
        (R_u0.cons 0)
      have ha2 := step_mk'_right (q := 19) (q' := 20) (a := 0) (b := 0) (by rfl)
        (ListBlank.append (List.replicate u₀ 1) (L_z.cons 1)) R_u0
      have hc := step_nSteps ha1 (nSteps_bind_eq hasc (step_one ha2))
      have henc : ((ListBlank.append (List.replicate u₀ 1) (L_z.cons 1)).cons 0) =
          ListBlank.append (encodeReg u₀).reverse L_z := by
        rw [append_replicate_cons, append_encodeReg_reverse]
      have hlen : u₀ + 1 + 1 = u₀ + 2 := rfl
      rwa [hlen, henc] at hc
    have hrest := sel_scan_regs rs_rest (ListBlank.append (encodeReg u₀).reverse L_z)
      (ListBlank.append (encodeReg v) (R_tail.cons 0))
    have hc := nSteps_bind_eq hfirst hrest
    have hrev : ListBlank.append (encodeRegs rs_rest).reverse
        (ListBlank.append (encodeReg u₀).reverse L_z) =
        ListBlank.append (encodeReg u₀ ++ encodeRegs rs_rest).reverse L_z := by
      rw [← ListBlank.append_assoc, ← List.reverse_append]
    have hlen : u₀ + 2 + (encodeRegs rs_rest).length =
        (encodeReg u₀ ++ encodeRegs rs_rest).length := by
      rw [List.length_append, encodeReg_length]
    rw [hlen, hrev] at hc
    exact hc
  set L_pre := ListBlank.append (encodeRegs rs_pre).reverse L_z
  have hv_scan := sel_scan_reg v L_pre (R_tail.cons 0)
  rw [append_encodeReg_reverse] at hv_scan
  set L_ones := ListBlank.append (List.replicate (v + 1) 1) L_pre
  have hd0 : step zf393 ⟨20, Tape.mk' (L_ones.cons 0) (R_tail.cons 0)⟩ =
      some ⟨21, Tape.mkL (L_ones.cons 0) (R_tail.cons 0)⟩ :=
    step_mk'_left (by rfl) _ _
  have he0 : step zf393 ⟨21, Tape.mkL (L_ones.cons 0) (R_tail.cons 0)⟩ =
      some ⟨22, Tape.mkL L_ones ((R_tail.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hf_ones := nSteps_mkL_left_scan (q := 22) (a := 1) (b := 1) (by rfl) (v + 1) L_pre
    ((R_tail.cons 0).cons 1)
  have henc_v : ListBlank.append (List.replicate (v + 1) 1) ((R_tail.cons 0).cons 1) =
      ((ListBlank.append (encodeReg v) R_tail).cons 1) := by
    rw [append_replicate_inner_cons, append_encodeReg]
  rw [henc_v] at hf_ones
  obtain ⟨rs_init, u_last, hpre_snoc⟩ : ∃ rs_init u_last, rs_pre = rs_init ++ [u_last] := by
    rcases rs_pre.eq_nil_or_concat with hnil | ⟨rs_init, u_last, hcat⟩
    · exact absurd hnil hrs_ne
    · exact ⟨rs_init, u_last, by rw [hcat, List.concat_eq_append]⟩
  have hL_pre_0 : L_pre = (ListBlank.append (List.replicate (u_last + 1) 1)
      (ListBlank.append (encodeRegs rs_init).reverse L_z)).cons 0 := by
    simp only [L_pre, hpre_snoc, encodeRegs_append, encodeRegs_cons, encodeRegs_nil,
      List.append_nil, List.reverse_append, ListBlank.append_assoc, append_encodeReg_reverse]
  have hf0 : step zf393 ⟨22, Tape.mkL L_pre ((ListBlank.append (encodeReg v) R_tail).cons 1)⟩ =
      some ⟨21, Tape.mk' L_pre ((ListBlank.append (encodeReg v) R_tail).cons 1)⟩ := by
    rw [hL_pre_0]
    exact step_mkL_right (by rfl) _ _
  have he1 : step zf393 ⟨21, Tape.mk' L_pre ((ListBlank.append (encodeReg v) R_tail).cons 1)⟩ =
      some ⟨23, Tape.mkL L_pre ((ListBlank.append (encodeReg v) R_tail).cons 0)⟩ :=
    step_mk'_left (by rfl) _ _
  obtain ⟨s_ret, _, hret⟩ := ret1_finish rs_pre z L ((ListBlank.append (encodeReg v) R_tail).cons 0)
  have hdrop : regs.drop (11 - (m + 1)) = v :: regs.drop (11 - m) := by
    have hsub1 : 11 - (m + 1) = 10 - m := by omega
    have hsub2 : 11 - m = (10 - m) + 1 := by omega
    rw [hsub1, hsub2]
    exact (List.getElem_cons_drop (by omega)).symm
  have hsub_take : 11 - (m + 1) = 10 - m := by omega
  rw [hdrop, hsub_take, regsTape_cons]
  exact ⟨_, by omega, step_nSteps hs1 (nSteps_bind_eq hscan0 (nSteps_bind_eq h18_to_20
    (nSteps_bind_eq hv_scan (step_nSteps hd0 (step_nSteps he0 (nSteps_bind_eq hf_ones
      (step_nSteps hf0 (step_nSteps he1 hret))))))))⟩

/-- Complete single selector pass (`1.sel` + `2.ret1` + `6.break.0`): shifts `m ↦ m + 1`
and appends `[1]` to `walked ++ List.replicate m 1`. -/
theorem sel_step_reaches_main0 (m : ℕ) (hm : m < 11) (slot : ℕ) (walked : List (Fin 2))
    (hsl : walked.length + m + 4 ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs : List ℕ) (hregs : regs.length = 11) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨17, Tape.mk' (ListBlank.append (walked ++ List.replicate m 1 ++ [0]).reverse
        LB01)
        (ListBlank.append (List.replicate (slot - (walked.length + m + 1)) 0)
          (zf393SelRight pre m regs))⟩ =
      some ⟨99, Tape.mk' LB01
        (ListBlank.append ((walked ++ List.replicate (m + 1) 1) ++
          List.replicate (slot - (walked.length + m + 1)) 0)
          (zf393SelRight pre (m + 1) regs))⟩ := by
  set P := walked ++ List.replicate m 1 ++ [0]
  set z := slot - (walked.length + m + 1) - 3
  have hz_eq : slot - (walked.length + m + 1) = z + 3 := by omega
  rw [hz_eq]
  obtain ⟨s₁, _, hs₁⟩ := @sel_pass_to_61 pre hpre m hm z regs hregs
    (ListBlank.append P.reverse LB01)
  set R_sel := ListBlank.append (List.replicate (z + 3) 0) (zf393SelRight pre (m + 1) regs)
  have hP_rev : ListBlank.append P.reverse LB01 =
      (ListBlank.append (walked ++ List.replicate m 1).reverse LB01).cons 0 := by
    simp [P, List.reverse_append]
  have hb0 : step zf393 ⟨61, Tape.mkL (ListBlank.append P.reverse LB01) R_sel⟩ =
      some ⟨64, Tape.mkL (ListBlank.append (walked ++ List.replicate m 1).reverse
        LB01) (R_sel.cons 1)⟩ := by
    rw [hP_rev]
    exact step_mkL_left (by rfl) _ _
  have hscan_ones : ∀ n xs, scanZerosOk 0 (List.replicate n (1 : Fin 2) ++ xs) =
      scanZerosOk 0 xs := by
    intro n xs; induction n with
    | zero => rfl
    | succ n ih => exact ih
  have hok_ones : scanZerosOk 0 ((walked ++ List.replicate m 1).reverse ++ [1]) = true := by
    rw [List.reverse_append, List.reverse_replicate, List.append_assoc, hscan_ones m]
    exact hok
  obtain ⟨s₂, _, hs₂⟩ := scan_reaches_main0 0 (by decide) (walked ++ List.replicate m 1) hok_ones
    (R_sel.cons 1)
  have hR : ListBlank.append (walked ++ List.replicate m 1) (R_sel.cons 1) =
      ListBlank.append ((walked ++ List.replicate (m + 1) 1) ++ List.replicate (z + 3) 0)
        (zf393SelRight pre (m + 1) regs) := by
    rw [append_cons_snoc, List.append_assoc walked, ← List.replicate_succ']
    simp only [R_sel, ← ListBlank.append_assoc]
  rw [hR] at hs₂
  exact ⟨_, by omega, nSteps_bind_eq hs₁ (step_nSteps hb0 hs₂)⟩

theorem inc_scan_reg (u : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 (u + 2) ⟨16, Tape.mk' L (ListBlank.append (encodeReg u) R)⟩ =
      some ⟨16, Tape.mk' (ListBlank.append (encodeReg u).reverse L) R⟩ := by
  rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step zf393
      ⟨16, Tape.mk' L ((ListBlank.append (List.replicate u 1) (R.cons 0)).cons 1)⟩ =
      some ⟨15, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate u 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 15) (a := 1) (b := 1) (by rfl) u (L.cons 1)
    (R.cons 0)
  have h2 : step zf393
      ⟨15, Tape.mk' (ListBlank.append (List.replicate u 1) (L.cons 1)) (R.cons 0)⟩ =
      some ⟨16, Tape.mk' ((ListBlank.append (List.replicate u 1) (L.cons 1)).cons 0) R⟩ :=
    step_mk'_right (by rfl) _ _
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  have henc : ((ListBlank.append (List.replicate u 1) (L.cons 1)).cons 0) =
      ListBlank.append (encodeReg u).reverse L := by
    rw [append_replicate_cons, append_encodeReg_reverse]
  have hlen : u + 1 + 1 = u + 2 := rfl
  rwa [hlen, henc] at hcomb

theorem inc_scan_regs (rs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 (encodeRegs rs).length ⟨16, Tape.mk' L (ListBlank.append (encodeRegs rs) R)⟩ =
      some ⟨16, Tape.mk' (ListBlank.append (encodeRegs rs).reverse L) R⟩ := by
  induction rs generalizing L with
  | nil => rfl
  | cons u rs ih =>
    rw [encodeRegs_cons, ListBlank.append_assoc]
    have h1 := inc_scan_reg u L (ListBlank.append (encodeRegs rs) R)
    have h2 := ih (ListBlank.append (encodeReg u).reverse L)
    have hcomb := nSteps_bind_eq h1 h2
    have hrev : ListBlank.append (encodeRegs rs).reverse
        (ListBlank.append (encodeReg u).reverse L) =
        ListBlank.append (encodeReg u ++ encodeRegs rs).reverse L := by
      rw [← ListBlank.append_assoc, ← List.reverse_append]
    have hlen : u + 2 + (encodeRegs rs).length =
        (encodeReg u ++ encodeRegs rs).length := by
      rw [List.length_append, encodeReg_length]
    rw [hlen, hrev] at hcomb
    exact hcomb

/-- `1.inc` (`State 13`) on `zf393SelRight pre (11 - r.val) regs` increments `regs[r.val]`
and returns to `6.break.0` (`State 61`). -/
theorem inc_pass_to_61 (r : Fin 11) (z : ℕ) (regs : List ℕ) (hregs : regs.length = 11)
    (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨13, Tape.mk' L
        (ListBlank.append (List.replicate (z + 3) 0) (zf393SelRight pre (11 - r.val) regs))⟩ =
      some ⟨61, Tape.mkL L
        (ListBlank.append (List.replicate (z + 3) 0)
          (ListBlank.append (encodeRegs pre) (regsTape (regs.set r.val (regs[r.val] + 1)))))⟩ := by
  have hsub : 11 - (11 - r.val) = r.val := by omega
  unfold zf393SelRight
  rw [hsub]
  set rs_pre := pre ++ regs.take r.val
  set R_after := regsTape (regs.drop r.val)
  have hs1 : step zf393
      ⟨13, Tape.mk' L ((ListBlank.append (List.replicate (z + 2) 0)
        (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0))).cons 0)⟩ =
      some ⟨14, Tape.mk' (L.cons 1)
        (ListBlank.append (List.replicate (z + 2) 0)
          (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0)))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan0 := nSteps_mk'_right_scan (q := 14) (a := 0) (b := 0) (by rfl) (z + 2) (L.cons 1)
    (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0))
  set L_z := ListBlank.append (List.replicate (z + 2) 0) (L.cons 1)
  have hpre_ne : rs_pre ≠ [] := by simp [rs_pre, hpre.out]
  obtain ⟨u₀, rs_rest, hpre_cons⟩ : ∃ u₀ rs_rest, rs_pre = u₀ :: rs_rest := by
    rcases h : rs_pre with _ | ⟨u₀, rs_rest⟩
    · exact absurd h hpre_ne
    · exact ⟨u₀, rs_rest, rfl⟩
  have h14_to_16 : nSteps zf393 (encodeRegs rs_pre).length
      ⟨14, Tape.mk' L_z (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0))⟩ =
      some ⟨16, Tape.mk' (ListBlank.append (encodeRegs rs_pre).reverse L_z) (R_after.cons 0)⟩ := by
    rw [hpre_cons, encodeRegs_cons, ListBlank.append_assoc]
    have hfirst : nSteps zf393 (u₀ + 2)
        ⟨14, Tape.mk' L_z
          (ListBlank.append (encodeReg u₀) (ListBlank.append (encodeRegs rs_rest)
            (R_after.cons 0)))⟩ =
        some ⟨16, Tape.mk' (ListBlank.append (encodeReg u₀).reverse L_z)
          (ListBlank.append (encodeRegs rs_rest) (R_after.cons 0))⟩ := by
      rw [append_encodeReg, List.replicate_succ, ListBlank.append]
      set R_u0 := ListBlank.append (encodeRegs rs_rest) (R_after.cons 0)
      have ha1 := step_mk'_right (q := 14) (q' := 15) (a := 1) (b := 1) (by rfl) L_z
        (ListBlank.append (List.replicate u₀ 1) (R_u0.cons 0))
      have hasc := nSteps_mk'_right_scan (q := 15) (a := 1) (b := 1) (by rfl) u₀ (L_z.cons 1)
        (R_u0.cons 0)
      have ha2 := step_mk'_right (q := 15) (q' := 16) (a := 0) (b := 0) (by rfl)
        (ListBlank.append (List.replicate u₀ 1) (L_z.cons 1)) R_u0
      have hc := step_nSteps ha1 (nSteps_bind_eq hasc (step_one ha2))
      have henc : ((ListBlank.append (List.replicate u₀ 1) (L_z.cons 1)).cons 0) =
          ListBlank.append (encodeReg u₀).reverse L_z := by
        rw [append_replicate_cons, append_encodeReg_reverse]
      have hlen : u₀ + 1 + 1 = u₀ + 2 := rfl
      rwa [hlen, henc] at hc
    have hrest := inc_scan_regs rs_rest (ListBlank.append (encodeReg u₀).reverse L_z)
      (R_after.cons 0)
    have hc := nSteps_bind_eq hfirst hrest
    have hrev : ListBlank.append (encodeRegs rs_rest).reverse
        (ListBlank.append (encodeReg u₀).reverse L_z) =
        ListBlank.append (encodeReg u₀ ++ encodeRegs rs_rest).reverse L_z := by
      rw [← ListBlank.append_assoc, ← List.reverse_append]
    have hlen : u₀ + 2 + (encodeRegs rs_rest).length =
        (encodeReg u₀ ++ encodeRegs rs_rest).length := by
      rw [List.length_append, encodeReg_length]
    rw [hlen, hrev] at hc
    exact hc
  have hd0 : step zf393
      ⟨16, Tape.mk' (ListBlank.append (encodeRegs rs_pre).reverse L_z) (R_after.cons 0)⟩ =
      some ⟨23, Tape.mkL (ListBlank.append (encodeRegs rs_pre).reverse L_z) (R_after.cons 1)⟩ :=
    step_mk'_left (by rfl) _ _
  obtain ⟨s_ret, _, hret⟩ := ret1_finish rs_pre z L (R_after.cons 1)
  have hset : ListBlank.append (encodeRegs rs_pre) (R_after.cons 1) =
      ListBlank.append (encodeRegs pre) (regsTape (regs.set r.val (regs[r.val] + 1))) := by
    have hdrop : regs.drop r.val = regs[r.val] :: regs.drop (r.val + 1) :=
      (List.getElem_cons_drop (by omega)).symm
    have henc1 : (regsTape (regs[r.val] :: regs.drop (r.val + 1))).cons 1 =
        regsTape ((regs[r.val] + 1) :: regs.drop (r.val + 1)) := by
      rw [regsTape_cons, regsTape_cons, append_encodeReg, append_encodeReg]
      rfl
    simp only [R_after, rs_pre, hdrop, henc1, encodeRegs_append,
      ListBlank.append_assoc]
    rw [← regsTape_append, ← list_take_set_drop regs r.val (regs[r.val] + 1) (by omega)]
  rw [hset] at hret
  exact ⟨_, by omega, step_nSteps hs1 (nSteps_bind_eq hscan0
    (nSteps_bind_eq h14_to_16 (step_nSteps hd0 hret)))⟩

theorem popBreakRev_replicate_one_append (k n : ℕ) (xs : List (Fin 2)) :
    popBreakRev k (List.replicate n 1 ++ xs) = popBreakRev k xs := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem breakSlot_append_ones (k s m : ℕ) (walked : List (Fin 2)) :
    breakSlot k s (walked ++ List.replicate m 1) = breakSlot k s walked := by
  unfold breakSlot
  rw [List.count_append, List.count_replicate]
  simp

/-- Complete `inc_step_reaches_main0` on `m = 11 - r.val`: increments `regs[r.val]` and
erases all `11 - r.val` temporary selector `1`s via `6.break.0`. -/
theorem inc_step_reaches_main0 (r : Fin 11) (slot : ℕ) (walked : List (Fin 2))
    (hsl : walked.length + (11 - r.val) + 3 ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs : List ℕ) (hregs : regs.length = 11) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨13, Tape.mk' (ListBlank.append (walked ++ List.replicate (11 - r.val) 1).reverse
        LB01)
        (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
          (zf393SelRight pre (11 - r.val) regs))⟩ =
      some (@rootCfg pre (breakSlot 0 slot walked) (retStack walked)
        (regs.set r.val (regs[r.val] + 1))) := by
  set m := 11 - r.val
  set z := slot - (walked.length + m) - 3
  have hz_eq : slot - (walked.length + m) = z + 3 := by omega
  rw [hz_eq]
  obtain ⟨s₁, _, hs₁⟩ := @inc_pass_to_61 pre hpre r z regs hregs
    (ListBlank.append (walked ++ List.replicate m 1).reverse LB01)
  have hscan_ones : ∀ n xs, scanZerosOk 0 (List.replicate n (1 : Fin 2) ++ xs) =
      scanZerosOk 0 xs := by
    intro n xs; induction n with
    | zero => rfl
    | succ n ih => exact ih
  have hok_m : scanZerosOk 0 ((walked ++ List.replicate m 1).reverse ++ [1]) = true := by
    rw [List.reverse_append, List.reverse_replicate, List.append_assoc, hscan_ones m]
    exact hok
  have hlen_m : (walked ++ List.replicate m 1).length ≤ slot := by simp; omega
  obtain ⟨s₂, _, hs₂⟩ := @break_k_reaches_main0 pre 0 (by decide) slot
    (walked ++ List.replicate m 1) hlen_m hok_m (regs.set r.val (regs[r.val] + 1))
  have hsub_m : slot - (walked ++ List.replicate m 1).length = z + 3 := by
    rw [List.length_append, List.length_replicate]; exact hz_eq
  rw [← ListBlank.append_assoc] at hs₁
  rw [hsub_m] at hs₂
  have hpop : (popBreakRev 0 (walked ++ List.replicate m 1).reverse).reverse = retStack walked := by
    rw [List.reverse_append, List.reverse_replicate, popBreakRev_replicate_one_append]
    rfl
  rw [hpop, breakSlot_append_ones] at hs₂
  exact ⟨_, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem decnz_shift_right (rs : List ℕ) (L R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨8, Tape.mk' L (ListBlank.append (encodeRegs rs) (R.cons 0))⟩ =
      some ⟨9, Tape.mk' (ListBlank.append (encodeRegs rs).reverse (L.cons 0)) R⟩ := by
  induction rs generalizing L with
  | nil =>
    exact ⟨1, le_refl 1, step_one (step_mk'_right (by rfl) L R)⟩
  | cons u rs ih =>
    rw [encodeRegs_cons, ListBlank.append_assoc]
    set R_rs := ListBlank.append (encodeRegs rs) (R.cons 0)
    have h1 : nSteps zf393 (u + 2)
        ⟨8, Tape.mk' L (ListBlank.append (encodeReg u) R_rs)⟩ =
        some ⟨8, Tape.mk' (ListBlank.append (List.replicate (u + 1) 1) (L.cons 0)) R_rs⟩ := by
      rw [append_encodeReg, List.replicate_succ, ListBlank.append]
      have ha1 := step_mk'_right (q := 8) (q' := 7) (a := 1) (b := 0) (by rfl) L
        (ListBlank.append (List.replicate u 1) (R_rs.cons 0))
      have hasc := nSteps_mk'_right_scan (q := 7) (a := 1) (b := 1) (by rfl) u (L.cons 0)
        (R_rs.cons 0)
      have ha2 := step_mk'_right (q := 7) (q' := 8) (a := 0) (b := 1) (by rfl)
        (ListBlank.append (List.replicate u 1) (L.cons 0)) R_rs
      have hc := step_nSteps ha1 (nSteps_bind_eq hasc (step_one ha2))
      have hlen : u + 1 + 1 = u + 2 := rfl
      have hrep1 : ((ListBlank.append (List.replicate u 1) (L.cons 0)).cons 1) =
          ListBlank.append (List.replicate (u + 1) 1) (L.cons 0) := by
        rw [List.replicate_succ, ListBlank.append]
      rwa [hlen, hrep1] at hc
    obtain ⟨s₂, _, hs₂⟩ := ih (ListBlank.append (List.replicate (u + 1) 1) (L.cons 0))
    have hL_eq : ((ListBlank.append (List.replicate (u + 1) 1) (L.cons 0)).cons 0) =
        ListBlank.append (encodeReg u).reverse (L.cons 0) := by
      rw [append_encodeReg_reverse]
    rw [hL_eq, ← ListBlank.append_assoc, ← List.reverse_append] at hs₂
    exact ⟨_, by omega, nSteps_bind_eq h1 hs₂⟩

theorem decnz_shift_left (rs : List ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s ⟨11, Tape.mk' L ((regsTape rs).cons 0)⟩ =
      some ⟨23, Tape.mkL (ListBlank.append (encodeRegs rs).reverse L) default⟩ := by
  induction rs generalizing L with
  | nil =>
    have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
      default_cons_zero.symm
    have h1 : step zf393 ⟨11, Tape.mk' L ((regsTape []).cons 0)⟩ =
        some ⟨12, Tape.mk' (L.cons 1) default⟩ :=
      step_mk'_right (by rfl) L default
    have h2 : step zf393 ⟨12, Tape.mk' (L.cons 1) default⟩ =
        some ⟨17, Tape.mkL (L.cons 1) default⟩ := by
      conv_lhs => rw [hdef]
      rw [step_mk'_left (by rfl), default_cons_zero]
    have h3 : step zf393 ⟨17, Tape.mkL (L.cons 1) default⟩ =
        some ⟨23, Tape.mkL L default⟩ := by
      rw [step_mkL_left (by rfl), default_cons_zero]
    exact ⟨3, by decide, step_nSteps h1 (step_nSteps h2 (step_one h3))⟩
  | cons u rs ih =>
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    set R_u := (regsTape rs).cons 0
    have h1 : step zf393
        ⟨11, Tape.mk' L (((ListBlank.append (List.replicate u 1) R_u).cons 1).cons 0)⟩ =
        some ⟨12, Tape.mk' (L.cons 1) ((ListBlank.append (List.replicate u 1) R_u).cons 1)⟩ :=
      step_mk'_right (by rfl) _ _
    have h2 : step zf393
        ⟨12, Tape.mk' (L.cons 1) ((ListBlank.append (List.replicate u 1) R_u).cons 1)⟩ =
        some ⟨9, Tape.mk' ((L.cons 1).cons 1) (ListBlank.append (List.replicate u 1) R_u)⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 9) (a := 1) (b := 1) (by rfl) u ((L.cons 1).cons 1)
      R_u
    set L_u := ListBlank.append (List.replicate u 1) ((L.cons 1).cons 1)
    have hL_u_eq : L_u = ((ListBlank.append (List.replicate u 1) L).cons 1).cons 1 := by
      dsimp only [L_u]
      rw [append_replicate_inner_cons, append_replicate_inner_cons]
    have h3 : step zf393 ⟨9, Tape.mk' L_u R_u⟩ =
        some ⟨5, Tape.mkL L_u R_u⟩ :=
      step_mk'_left (by rfl) _ _
    have h4 : step zf393 ⟨5, Tape.mkL (((ListBlank.append (List.replicate u 1) L).cons 1).cons 1)
        R_u⟩ =
        some ⟨10, Tape.mkL ((ListBlank.append (List.replicate u 1) L).cons 1) (R_u.cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have h5 : step zf393
        ⟨10, Tape.mkL ((ListBlank.append (List.replicate u 1) L).cons 1) (R_u.cons 1)⟩ =
        some ⟨11, Tape.mk' ((ListBlank.append (List.replicate u 1) L).cons 1) (R_u.cons 1)⟩ :=
      step_mkL_right (by rfl) _ _
    have h6 : step zf393
        ⟨11, Tape.mk' ((ListBlank.append (List.replicate u 1) L).cons 1) (R_u.cons 1)⟩ =
        some ⟨11, Tape.mk' (((ListBlank.append (List.replicate u 1) L).cons 1).cons 0) R_u⟩ :=
      step_mk'_right (by rfl) _ _
    rw [hL_u_eq] at hscan h3
    obtain ⟨s_rest, _, hrest⟩ := ih (((ListBlank.append (List.replicate u 1) L).cons 1).cons 0)
    have henc_u : (((ListBlank.append (List.replicate u 1) L).cons 1).cons 0) =
        ListBlank.append (encodeReg u).reverse L := by
      rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
    rw [henc_u] at h6
    rw [henc_u, ← ListBlank.append_assoc, ← List.reverse_append, ← encodeRegs_cons] at hrest
    exact ⟨_, by omega, step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan
      (step_nSteps h3 (step_nSteps h4 (step_nSteps h5 (step_nSteps h6 hrest))))))⟩

/-- `1.decnz` (`State 5`) on `zf393SelRight pre (11 - r.val) regs` shifts `slot` right by `+ 1`,
returning to `62` (`6.break.1`) with `regs` when `regs[r.val] = 0`, or to `61` (`6.break.0`)
with `regs.set r.val (regs[r.val] - 1)` when `0 < regs[r.val]`. -/
theorem decnz_pass_to_break (r : Fin 11) (z : ℕ) (regs : List ℕ) (hregs : regs.length = 11)
    (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨5, Tape.mk' L
        (ListBlank.append (List.replicate (z + 3) 0) (zf393SelRight pre (11 - r.val) regs))⟩ =
      some (if regs[r.val] = 0 then
        ⟨62, Tape.mkL L
          (ListBlank.append (List.replicate (z + 4) 0)
            (ListBlank.append (encodeRegs pre) (regsTape regs)))⟩
      else
        ⟨61, Tape.mkL L
          (ListBlank.append (List.replicate (z + 4) 0)
            (ListBlank.append (encodeRegs pre)
              (regsTape (regs.set r.val (regs[r.val] - 1)))))⟩) := by
  have hsub : 11 - (11 - r.val) = r.val := by omega
  unfold zf393SelRight
  rw [hsub]
  set rs_pre := pre ++ regs.take r.val
  set R_after := regsTape (regs.drop r.val)
  have hs1 : step zf393
      ⟨5, Tape.mk' L ((ListBlank.append (List.replicate (z + 2) 0)
        (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0))).cons 0)⟩ =
      some ⟨6, Tape.mk' (L.cons 1)
        (ListBlank.append (List.replicate (z + 2) 0)
          (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0)))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan0 := nSteps_mk'_right_scan (q := 6) (a := 0) (b := 0) (by rfl) (z + 2) (L.cons 1)
    (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0))
  set L_z := ListBlank.append (List.replicate (z + 2) 0) (L.cons 1)
  have hrs_ne : rs_pre ≠ [] := by simp [rs_pre, hpre.out]
  obtain ⟨u₀, rs_rest, hpre_cons⟩ : ∃ u₀ rs_rest, rs_pre = u₀ :: rs_rest := by
    rcases h : rs_pre with _ | ⟨u₀, rs_rest⟩
    · exact absurd h hrs_ne
    · exact ⟨u₀, rs_rest, rfl⟩
  have h6_eq_8 : step zf393
      ⟨6, Tape.mk' L_z (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0))⟩ =
      step zf393
      ⟨8, Tape.mk' L_z (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0))⟩ := by
    rw [hpre_cons, encodeRegs_cons, ListBlank.append_assoc, append_encodeReg,
      List.replicate_succ, ListBlank.append]
    rw [step_mk'_right (q := 6) (q' := 7) (a := 1) (b := 0) (by rfl),
      step_mk'_right (q := 8) (q' := 7) (a := 1) (b := 0) (by rfl)]
  obtain ⟨s_sh, hs_sh_pos, hshift⟩ := decnz_shift_right rs_pre L_z R_after
  have h6_shift : nSteps zf393 s_sh
      ⟨6, Tape.mk' L_z (ListBlank.append (encodeRegs rs_pre) (R_after.cons 0))⟩ =
      some ⟨9, Tape.mk' (ListBlank.append (encodeRegs rs_pre).reverse (L_z.cons 0)) R_after⟩ := by
    obtain ⟨k, rfl⟩ : ∃ k, s_sh = k + 1 := ⟨s_sh - 1, by omega⟩
    rw [nSteps_succ, h6_eq_8, ← nSteps_succ]
    exact hshift
  set L_pre := ListBlank.append (encodeRegs rs_pre).reverse (L_z.cons 0)
  have hdrop : regs.drop r.val = regs[r.val] :: regs.drop (r.val + 1) :=
    (List.getElem_cons_drop (by omega)).symm
  set v := regs[r.val]
  set rs_tail := regs.drop (r.val + 1)
  have hR_after : R_after =
      ListBlank.append (List.replicate (v + 1) 1) ((regsTape rs_tail).cons 0) := by
    rw [← append_encodeReg]
    simp only [R_after, hdrop, regsTape_cons]
  set R_t0 := (regsTape rs_tail).cons 0
  have hscan_v := nSteps_mk'_right_scan (q := 9) (a := 1) (b := 1) (by rfl) (v + 1) L_pre R_t0
  rw [← hR_after] at hscan_v
  have he0 : step zf393
      ⟨9, Tape.mk' (ListBlank.append (List.replicate (v + 1) 1) L_pre) R_t0⟩ =
      some ⟨5, Tape.mkL (ListBlank.append (List.replicate (v + 1) 1) L_pre) R_t0⟩ :=
    step_mk'_left (by rfl) _ _
  have hd1 : step zf393
      ⟨5, Tape.mkL ((ListBlank.append (List.replicate v 1) L_pre).cons 1) R_t0⟩ =
      some ⟨10, Tape.mkL (ListBlank.append (List.replicate v 1) L_pre)
        (R_t0.cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  cases hv : v with
  | zero =>
    simp only [hv, ↓reduceIte, List.replicate_zero, ListBlank.append] at *
    obtain ⟨rs_init, u_last, hpre_snoc⟩ : ∃ rs_init u_last, rs_pre = rs_init ++ [u_last] := by
      rcases rs_pre.eq_nil_or_concat with hnil | ⟨rs_init, u_last, hcat⟩
      · exact absurd hnil hrs_ne
      · exact ⟨rs_init, u_last, by rw [hcat, List.concat_eq_append]⟩
    have hL_pre_0 : L_pre = (ListBlank.append (List.replicate (u_last + 1) 1)
        (ListBlank.append (encodeRegs rs_init).reverse (L_z.cons 0))).cons 0 := by
      simp only [L_pre, hpre_snoc, encodeRegs_append, encodeRegs_cons, encodeRegs_nil,
        List.append_nil, List.reverse_append, ListBlank.append_assoc, append_encodeReg_reverse]
    have hg0 : step zf393 ⟨10, Tape.mkL L_pre (R_t0.cons 1)⟩ =
        some ⟨26, Tape.mkL (ListBlank.append (List.replicate (u_last + 1) 1)
          (ListBlank.append (encodeRegs rs_init).reverse (L_z.cons 0)))
          ((R_t0.cons 1).cons 0)⟩ := by
      rw [hL_pre_0]; exact step_mkL_left (by rfl) _ _
    have hscan_last := nSteps_mkL_left_scan (q := 26) (a := 1) (b := 1) (by rfl) (u_last + 1)
      (ListBlank.append (encodeRegs rs_init).reverse (L_z.cons 0)) ((R_t0.cons 1).cons 0)
    have hL_z_cons : L_z.cons 0 = ListBlank.append (List.replicate ((z + 1) + 2) 0) (L.cons 1) := by
      rfl
    rw [hL_z_cons] at hscan_last
    obtain ⟨s_ret, _, hret⟩ := ret2_finish rs_init (z + 1) L
      (ListBlank.append (List.replicate (u_last + 1) 1) ((R_t0.cons 1).cons 0))
    have hR_eq : ListBlank.append (encodeRegs rs_init)
        (ListBlank.append (List.replicate (u_last + 1) 1) ((R_t0.cons 1).cons 0)) =
        ListBlank.append (encodeRegs pre) (regsTape regs) := by
      have henc0 : (R_t0.cons 1) = regsTape (0 :: rs_tail) := rfl
      have henc_u : ListBlank.append (List.replicate (u_last + 1) 1)
          ((regsTape (0 :: rs_tail)).cons 0) =
          ListBlank.append (encodeReg u_last) (regsTape (0 :: rs_tail)) := by
        rw [append_encodeReg]
      have henc_cat : encodeRegs rs_init ++ encodeReg u_last =
          encodeRegs (rs_init ++ [u_last]) := by
        simp [encodeRegs_append, encodeRegs_cons, encodeRegs_nil]
      have hr_list : rs_init ++ [u_last] ++ (0 :: rs_tail) = pre ++ regs := by
        rw [← hpre_snoc, ← hdrop]
        dsimp only [rs_pre]
        rw [List.append_assoc, List.take_append_drop]
      rw [henc0, henc_u, ← ListBlank.append_assoc, henc_cat, ← regsTape_append, hr_list,
        regsTape_append]
    rw [hR_eq] at hret
    exact ⟨_, by omega, step_nSteps hs1 (nSteps_bind_eq hscan0 (nSteps_bind_eq h6_shift
      (nSteps_bind_eq hscan_v (step_nSteps he0 (step_nSteps hd1
        (step_nSteps hg0 (nSteps_bind_eq hscan_last hret)))))))⟩
  | succ v' =>
    have hpos : ¬ (v' + 1 = 0) := by omega
    simp only [hv, hpos, ↓reduceIte] at *
    have hg1 : step zf393
        ⟨10, Tape.mkL ((ListBlank.append (List.replicate v' 1) L_pre).cons 1)
          (R_t0.cons 1)⟩ =
        some ⟨11, Tape.mk' ((ListBlank.append (List.replicate v' 1) L_pre).cons 1)
          (R_t0.cons 1)⟩ :=
      step_mkL_right (by rfl) _ _
    have hh1 : step zf393
        ⟨11, Tape.mk' ((ListBlank.append (List.replicate v' 1) L_pre).cons 1)
          (R_t0.cons 1)⟩ =
        some ⟨11, Tape.mk' (ListBlank.append (encodeReg v').reverse L_pre)
          R_t0⟩ := by
      have h := step_mk'_right (q := 11) (q' := 11) (a := 1) (b := 0) (by rfl)
        ((ListBlank.append (List.replicate v' 1) L_pre).cons 1) R_t0
      have henc : (((ListBlank.append (List.replicate v' 1) L_pre).cons 1).cons 0) =
          ListBlank.append (encodeReg v').reverse L_pre := by
        rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
      rwa [henc] at h
    obtain ⟨s_left, _, hleft⟩ := decnz_shift_left rs_tail
      (ListBlank.append (encodeReg v').reverse L_pre)
    have hL_all : ListBlank.append (encodeRegs rs_tail).reverse
        (ListBlank.append (encodeReg v').reverse L_pre) =
        ListBlank.append (encodeRegs (rs_pre ++ [v'] ++ rs_tail)).reverse
          (ListBlank.append (List.replicate ((z + 1) + 2) 0) (L.cons 1)) := by
      simp only [L_pre, L_z, encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil,
        List.reverse_append, ListBlank.append_assoc]
      rfl
    rw [hL_all] at hleft
    obtain ⟨s_ret, _, hret⟩ := ret1_finish (rs_pre ++ [v'] ++ rs_tail) (z + 1) L default
    have hR_eq : ListBlank.append (encodeRegs (rs_pre ++ [v'] ++ rs_tail)) default =
        ListBlank.append (encodeRegs pre) (regsTape (regs.set r.val v')) := by
      change regsTape (rs_pre ++ [v'] ++ rs_tail) = _
      have hr_eq : rs_pre ++ [v'] ++ rs_tail = pre ++ regs.set r.val v' := by
        simp only [rs_pre, rs_tail, List.append_assoc, List.singleton_append]
        rw [← list_take_set_drop regs r.val v' (by omega)]
      rw [hr_eq, regsTape_append]
    rw [hR_eq] at hret
    exact ⟨_, by omega, step_nSteps hs1 (nSteps_bind_eq hscan0 (nSteps_bind_eq h6_shift
      (nSteps_bind_eq hscan_v (step_nSteps he0 (step_nSteps hd1
        (step_nSteps hg1 (step_nSteps hh1 (nSteps_bind_eq hleft hret))))))))⟩

/-- Complete `decnz_step_reaches_main0` on `m = 11 - r.val`: shifts `slot` right by `+ 1`,
erases all selector `1`s, and updates stack & registers for both `regs[r.val] = 0` (`break.1`)
and `0 < regs[r.val]` (`break.0` with `regs[r.val] - 1`). -/
theorem decnz_step_reaches_main0 (r : Fin 11) (slot : ℕ) (walked : List (Fin 2))
    (hsl : walked.length + (11 - r.val) + 3 ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs : List ℕ) (hregs : regs.length = 11) :
    ∃ s, 1 ≤ s ∧ nSteps zf393 s
      ⟨5, Tape.mk' (ListBlank.append (walked ++ List.replicate (11 - r.val) 1).reverse
        LB01)
        (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
          (zf393SelRight pre (11 - r.val) regs))⟩ =
      some (if regs[r.val] = 0 then
        @rootCfg pre (breakSlot 1 (slot + 1) walked) ((popBreakRev 1 walked.reverse).reverse) regs
      else
        @rootCfg pre (breakSlot 0 (slot + 1) walked) (retStack walked)
          (regs.set r.val (regs[r.val] - 1))) := by
  set m := 11 - r.val
  set z := slot - (walked.length + m) - 3
  have hz_eq : slot - (walked.length + m) = z + 3 := by omega
  rw [hz_eq]
  obtain ⟨s₁, _, hs₁⟩ := @decnz_pass_to_break pre hpre r z regs hregs
    (ListBlank.append (walked ++ List.replicate m 1).reverse LB01)
  have hscan_ones : ∀ n xs, scanZerosOk 0 (List.replicate n (1 : Fin 2) ++ xs) =
      scanZerosOk 0 xs := by
    intro n xs; induction n with
    | zero => rfl
    | succ n ih => exact ih
  have hok_m : scanZerosOk 0 ((walked ++ List.replicate m 1).reverse ++ [1]) = true := by
    rw [List.reverse_append, List.reverse_replicate, List.append_assoc, hscan_ones m]
    exact hok
  have hlen_m : (walked ++ List.replicate m 1).length ≤ slot + 1 := by simp; omega
  have hsub_m : (slot + 1) - (walked ++ List.replicate m 1).length = z + 4 := by
    rw [List.length_append, List.length_replicate]; omega
  by_cases hv : regs[r.val] = 0
  · simp only [hv, ↓reduceIte] at hs₁ ⊢
    obtain ⟨s₂, _, hs₂⟩ := @break_k_reaches_main0 pre 1 (by decide) (slot + 1)
      (walked ++ List.replicate m 1) hlen_m hok_m regs
    rw [← ListBlank.append_assoc] at hs₁
    rw [hsub_m] at hs₂
    have hpop : (popBreakRev 1 (walked ++ List.replicate m 1).reverse).reverse =
        (popBreakRev 1 walked.reverse).reverse := by
      rw [List.reverse_append, List.reverse_replicate, popBreakRev_replicate_one_append]
    rw [hpop, breakSlot_append_ones] at hs₂
    exact ⟨_, by omega, nSteps_bind_eq hs₁ hs₂⟩
  · simp only [hv, ↓reduceIte] at hs₁ ⊢
    obtain ⟨s₂, _, hs₂⟩ := @break_k_reaches_main0 pre 0 (by decide) (slot + 1)
      (walked ++ List.replicate m 1) hlen_m hok_m (regs.set r.val (regs[r.val] - 1))
    rw [← ListBlank.append_assoc] at hs₁
    rw [hsub_m] at hs₂
    have hpop : (popBreakRev 0 (walked ++ List.replicate m 1).reverse).reverse =
        retStack walked := by
      rw [List.reverse_append, List.reverse_replicate, popBreakRev_replicate_one_append]
      rfl
    rw [hpop, breakSlot_append_ones] at hs₂
    exact ⟨_, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-- Stage-3 `inc` leaf state for tape register `r : Fin 11` (`0=scratch3 .. 10=prooflist`). -/
def regIncStage3 : Fin 11 → Fin 393
  | 0 => 46
  | 1 => 44
  | 2 => 42
  | 3 => 38
  | 4 => 36
  | 5 => 34
  | 6 => 30
  | 7 => 50
  | 8 => 48
  | 9 => 32
  | 10 => 40

/-- Stage-3 `decnz` leaf state for tape register `r : Fin 11` (`0=scratch3 .. 10=prooflist`). -/
def regDecnzStage3 : Fin 11 → Fin 393
  | 0 => 45
  | 1 => 43
  | 2 => 41
  | 3 => 37
  | 4 => 35
  | 5 => 33
  | 6 => 29
  | 7 => 49
  | 8 => 47
  | 9 => 31
  | 10 => 39

theorem isLeafState_iff (q : Fin 393) :
    (29 ≤ q.val ∧ q.val ≤ 50) ↔
      (∃ r : Fin 11, q = regIncStage3 r) ∨ (∃ r : Fin 11, q = regDecnzStage3 r) := by
  revert q; decide

theorem regIncStage3_step1 (r : Fin 10) :
    zf393Trans (regIncStage3 ⟨r.val, by omega⟩) 1 =
      some (1, .right, regIncStage3 ⟨r.val + 1, by omega⟩) := by
  revert r; decide

theorem regDecnzStage3_step1 (r : Fin 10) :
    zf393Trans (regDecnzStage3 ⟨r.val, by omega⟩) 1 =
      some (1, .right, regDecnzStage3 ⟨r.val + 1, by omega⟩) := by
  revert r; decide

theorem regIncStage3_step0 (q : Fin 11) :
    zf393Trans (regIncStage3 q) 0 = some (0, .right, 17) := by
  revert q; decide

theorem regDecnzStage3_step0 (q : Fin 11) :
    zf393Trans (regDecnzStage3 q) 0 = some (0, .right, 17) := by
  revert q; decide

theorem stage3_walk_ones_inc (r : Fin 11) (j : ℕ) (hj : r.val + j ≤ 10)
    (L R : ListBlank (Fin 2)) :
    nSteps zf393 j ⟨regIncStage3 r, Tape.mk' L (ListBlank.append (List.replicate j 1) R)⟩ =
      some ⟨regIncStage3 ⟨r.val + j, by omega⟩,
        Tape.mk' (ListBlank.append (List.replicate j 1) L) R⟩ := by
  induction j generalizing r L with
  | zero =>
    simp only [Nat.add_zero, Fin.eta, List.replicate_zero, ListBlank.append]
    rfl
  | succ j ih =>
    have htr1 : zf393Trans (regIncStage3 r) 1 =
        some (1, .right, regIncStage3 ⟨r.val + 1, by omega⟩) :=
      regIncStage3_step1 ⟨r.val, by omega⟩
    rw [List.replicate_succ, ListBlank.append]
    have hs1 := step_mk'_right htr1 L (ListBlank.append (List.replicate j 1) R)
    have hj' : (⟨r.val + 1, by omega⟩ : Fin 11).val + j ≤ 10 := by dsimp; omega
    have hrest := ih ⟨r.val + 1, by omega⟩ hj' (L.cons 1)
    have hcomb := step_nSteps hs1 hrest
    have hidx : (⟨(⟨r.val + 1, by omega⟩ : Fin 11).val + j, by omega⟩ : Fin 11) =
        ⟨r.val + (j + 1), by omega⟩ := by
      ext; dsimp; omega
    rwa [append_replicate_cons, hidx] at hcomb

theorem stage3_walk_ones_decnz (r : Fin 11) (j : ℕ) (hj : r.val + j ≤ 10)
    (L R : ListBlank (Fin 2)) :
    nSteps zf393 j ⟨regDecnzStage3 r, Tape.mk' L (ListBlank.append (List.replicate j 1) R)⟩ =
      some ⟨regDecnzStage3 ⟨r.val + j, by omega⟩,
        Tape.mk' (ListBlank.append (List.replicate j 1) L) R⟩ := by
  induction j generalizing r L with
  | zero =>
    simp only [Nat.add_zero, Fin.eta, List.replicate_zero, ListBlank.append]
    rfl
  | succ j ih =>
    have htr1 : zf393Trans (regDecnzStage3 r) 1 =
        some (1, .right, regDecnzStage3 ⟨r.val + 1, by omega⟩) :=
      regDecnzStage3_step1 ⟨r.val, by omega⟩
    rw [List.replicate_succ, ListBlank.append]
    have hs1 := step_mk'_right htr1 L (ListBlank.append (List.replicate j 1) R)
    have hj' : (⟨r.val + 1, by omega⟩ : Fin 11).val + j ≤ 10 := by dsimp; omega
    have hrest := ih ⟨r.val + 1, by omega⟩ hj' (L.cons 1)
    have hcomb := step_nSteps hs1 hrest
    have hidx : (⟨(⟨r.val + 1, by omega⟩ : Fin 11).val + j, by omega⟩ : Fin 11) =
        ⟨r.val + (j + 1), by omega⟩ := by
      ext; dsimp; omega
    rwa [append_replicate_cons, hidx] at hcomb

/-!
## 5. Decision-Tree Dispatcher, Abstract Machine (`zf393RegStep`), & `Halts zf393 ↔ Zf393RegHalts`
-/

theorem leafReg_inc_spec (q : Fin 393) (hl : isLeafState q = true) (hi : isLeafInc q = true) :
    q = regIncStage3 (leafReg q) := by
  revert q hl hi; decide

theorem leafReg_decnz_spec (q : Fin 393) (hl : isLeafState q = true) (hi : isLeafInc q = false) :
    q = regDecnzStage3 (leafReg q) := by
  revert q hl hi; decide

def treeWalkCfg (q : Fin 393) (walked rem : List (Fin 2))
    (L₀ R_tail : ListBlank (Fin 2)) : Cfg 393 2 :=
  ⟨q, Tape.mk' (ListBlank.append walked.reverse L₀) (ListBlank.append rem R_tail)⟩

theorem walkTape_sound (q : Fin 393) (walked rem : List (Fin 2))
    (L₀ R_tail : ListBlank (Fin 2)) :
    match walkTape q walked rem with
    | .halt q_h walked_h rem_h =>
      ∃ s, walked_h.length = walked.length + s ∧
        nSteps zf393 s (treeWalkCfg q walked rem L₀ R_tail) =
          some (treeWalkCfg q_h walked_h rem_h L₀ R_tail) ∧
        step zf393 (treeWalkCfg q_h walked_h rem_h L₀ R_tail) = none
    | .jumpLeft q' walked_j rem' =>
      (∃ b, walked_j ++ (b :: rem') = walked ++ rem) ∧
      ∃ s, 1 ≤ s ∧
        nSteps zf393 s (treeWalkCfg q walked rem L₀ R_tail) =
          some ⟨q', Tape.mkL (ListBlank.append walked_j.reverse L₀)
            (ListBlank.append (0 :: rem') R_tail)⟩
    | .regLeaf q' walked_l rem' =>
      walked_l ++ rem' = walked ++ rem ∧
      ∃ s, 1 ≤ s ∧
        nSteps zf393 s (treeWalkCfg q walked rem L₀ R_tail) =
          some (treeWalkCfg q' walked_l rem' L₀ R_tail)
    | .outOfFuel => True := by
  induction rem generalizing q walked with
  | nil => trivial
  | cons b rem' ih =>
    simp only [walkTape]
    rcases htr : zf393Trans q b with _ | ⟨w, d, q'⟩
    · refine ⟨0, Nat.add_zero _, rfl, ?_⟩
      exact step_mk'_none htr (ListBlank.append walked.reverse L₀)
        (ListBlank.append rem' R_tail)
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp only [hw, ↓reduceIte]
          have hw0 : w = 0 := beq_iff_eq.mp hw
          subst hw0
          refine ⟨⟨b, rfl⟩, 1, le_refl 1, ?_⟩
          exact step_one (step_mk'_left htr (ListBlank.append walked.reverse L₀)
            (ListBlank.append rem' R_tail))
        · simp [hw]
      | right =>
        by_cases hw : (w == b) = true
        · simp only [hw, ↓reduceIte]
          have hwb : w = b := beq_iff_eq.mp hw
          subst hwb
          have hstep1 : step zf393 (treeWalkCfg q walked (w :: rem') L₀ R_tail) =
              some (treeWalkCfg q' (walked ++ [w]) rem' L₀ R_tail) := by
            simpa [treeWalkCfg, append_reverse_cons] using
              step_mk'_right htr (ListBlank.append walked.reverse L₀)
                (ListBlank.append rem' R_tail)
          by_cases hleaf : isLeafState q' = true
          · simp only [hleaf, ↓reduceIte]
            exact ⟨by simp, 1, le_refl 1, step_one hstep1⟩
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            have hrec := ih q' (walked ++ [w])
            rcases hout : walkTape q' (walked ++ [w]) rem' with
              ⟨q_h, w_h, r_h⟩ | ⟨q_j, w_j, r_j⟩ | ⟨q_l, w_l, r_l⟩ | _
            · rw [hout] at hrec
              obtain ⟨s, hlen, hs, hnone⟩ := hrec
              refine ⟨s + 1, ?_, step_nSteps hstep1 hs, hnone⟩
              rw [List.length_append, List.length_singleton] at hlen; omega
            · rw [hout] at hrec
              obtain ⟨⟨b', heq⟩, s, _, hs⟩ := hrec
              exact ⟨⟨b', by simpa using heq⟩, s + 1, by omega, step_nSteps hstep1 hs⟩
            · rw [hout] at hrec
              obtain ⟨heq, s, _, hs⟩ := hrec
              exact ⟨by simpa using heq, s + 1, by omega, step_nSteps hstep1 hs⟩
            · trivial
        · simp [hw]

/-- Combined multi-pass `3.<reg_r>.inc` leaf execution from `main().0` (`State 99`):
runs all `(11 - r.val)` passes of `1.sel` (`m = 0 ↦ 1 ↦ ... ↦ 11 - r.val`) followed by
`1.inc`, landing at `@rootCfg pre (breakSlot 0 slot walked) (retStack walked)
(regs.set r.val (regs[r.val] + 1))`. -/
theorem inc_leaf_reaches_main0 (r : Fin 11) (slot : ℕ) (walked : List (Fin 2))
    (hwalk : walkTape 99 [] walked = .regLeaf (regIncStage3 r) walked [])
    (hsl : walked.length + (11 - r.val) + 3 ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs : List ℕ) (hregs : regs.length = 11) :
    ∃ s, 1 ≤ s ∧
      nSteps zf393 s
        ⟨99, Tape.mk' LB01
          (ListBlank.append (walked ++ List.replicate (slot - walked.length) 0 ++
            encodeRegs pre) (regsTape regs))⟩ =
      some (@rootCfg pre (breakSlot 0 slot walked) (retStack walked)
        (regs.set r.val (regs[r.val] + 1))) := by
  have walk_exact : ∀ (R_rem : ListBlank (Fin 2)),
      ∃ sw, 1 ≤ sw ∧ nSteps zf393 sw
        ⟨99, Tape.mk' LB01 (ListBlank.append walked R_rem)⟩ =
        some ⟨regIncStage3 r, Tape.mk' (ListBlank.append walked.reverse LB01)
          R_rem⟩ := by
    intro R_rem
    have hws := walkTape_sound 99 [] walked LB01 R_rem
    rw [hwalk] at hws
    obtain ⟨_, sw, hsw_pos, hs⟩ := hws
    exact ⟨sw, hsw_pos, hs⟩
  have loop : ∀ m k : ℕ, m + k = 11 - r.val →
      ∃ s, 1 ≤ s ∧ nSteps zf393 s
        ⟨99, Tape.mk' LB01
          (ListBlank.append walked
            (ListBlank.append (List.replicate m 1)
              (ListBlank.append (List.replicate (slot - (walked.length + m)) 0)
                (zf393SelRight pre m regs))))⟩ =
        some (@rootCfg pre (breakSlot 0 slot walked) (retStack walked)
          (regs.set r.val (regs[r.val] + 1))) := by
    intro m k hmk
    induction k generalizing m with
    | zero =>
      have hm_eq : m = 11 - r.val := by omega
      subst hm_eq
      have hrep_split : List.replicate (11 - r.val) (1 : Fin 2) =
          List.replicate (10 - r.val) 1 ++ [1] := by
        have h11 : 11 - r.val = (10 - r.val) + 1 := by omega
        rw [h11, List.replicate_succ']
      rw [hrep_split, ListBlank.append_assoc]
      obtain ⟨sw, _, hsw⟩ := walk_exact
        (ListBlank.append (List.replicate (10 - r.val) 1)
          (ListBlank.append [1]
            (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
              (zf393SelRight pre (11 - r.val) regs))))
      have hones := stage3_walk_ones_inc r (10 - r.val) (by omega)
        (ListBlank.append walked.reverse LB01)
        (ListBlank.append [1]
          (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
            (zf393SelRight pre (11 - r.val) regs)))
      have hr10 : (⟨r.val + (10 - r.val), by omega⟩ : Fin 11) = 10 := by ext; dsimp; omega
      rw [hr10] at hones
      have hs10 : step zf393
          ⟨regIncStage3 10, Tape.mk'
            (ListBlank.append (List.replicate (10 - r.val) 1)
              (ListBlank.append walked.reverse LB01))
            (ListBlank.append [1]
              (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
                (zf393SelRight pre (11 - r.val) regs)))⟩ =
          some ⟨13, Tape.mk'
            (ListBlank.append (walked ++ List.replicate (11 - r.val) 1).reverse
              LB01)
            (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
              (zf393SelRight pre (11 - r.val) regs))⟩ := by
        have h := step_mk'_right (q := regIncStage3 10) (q' := 13) (a := 1) (b := 1) (by rfl)
          (ListBlank.append (List.replicate (10 - r.val) 1)
            (ListBlank.append walked.reverse LB01))
          (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
            (zf393SelRight pre (11 - r.val) regs))
        have hL_eq : ((ListBlank.append (List.replicate (10 - r.val) 1)
            (ListBlank.append walked.reverse LB01)).cons 1) =
            ListBlank.append (walked ++ List.replicate (11 - r.val) 1).reverse
              LB01 := by
          rw [hrep_split, List.reverse_append, List.reverse_append, List.reverse_replicate,
            ListBlank.append_assoc, ListBlank.append_assoc]
          rfl
        rwa [hL_eq] at h
      obtain ⟨sinc, _, hinc⟩ := @inc_step_reaches_main0 pre hpre r slot walked hsl hok regs hregs
      exact ⟨_, by omega, nSteps_bind_eq hsw (nSteps_bind_eq hones (step_nSteps hs10 hinc))⟩
    | succ k' ih =>
      have hrm : r.val + m < 11 := by omega
      obtain ⟨sw, _, hsw⟩ := walk_exact
        (ListBlank.append (List.replicate m 1)
          (ListBlank.append (List.replicate (slot - (walked.length + m)) 0)
            (zf393SelRight pre m regs)))
      have hones := stage3_walk_ones_inc r m (by omega)
        (ListBlank.append walked.reverse LB01)
        (ListBlank.append (List.replicate (slot - (walked.length + m)) 0)
          (zf393SelRight pre m regs))
      have hsub_z : slot - (walked.length + m) =
          (slot - (walked.length + m + 1)) + 1 := by omega
      rw [hsub_z, List.replicate_succ, ListBlank.append] at hsw hones ⊢
      have htr0 : zf393Trans (regIncStage3 ⟨r.val + m, hrm⟩) 0 =
          some (0, .right, 17) :=
        regIncStage3_step0 ⟨r.val + m, hrm⟩
      have hs0 : step zf393
          ⟨regIncStage3 ⟨r.val + m, hrm⟩,
            Tape.mk' (ListBlank.append (List.replicate m 1)
              (ListBlank.append walked.reverse LB01))
              ((ListBlank.append (List.replicate (slot - (walked.length + m + 1)) 0)
                (zf393SelRight pre m regs)).cons 0)⟩ =
          some ⟨17, Tape.mk'
            (ListBlank.append (walked ++ List.replicate m 1 ++ [0]).reverse LB01)
            (ListBlank.append (List.replicate (slot - (walked.length + m + 1)) 0)
              (zf393SelRight pre m regs))⟩ := by
        have h := step_mk'_right htr0
          (ListBlank.append (List.replicate m 1)
            (ListBlank.append walked.reverse LB01))
          (ListBlank.append (List.replicate (slot - (walked.length + m + 1)) 0)
            (zf393SelRight pre m regs))
        have hL_eq : ((ListBlank.append (List.replicate m 1)
            (ListBlank.append walked.reverse LB01)).cons 0) =
            ListBlank.append (walked ++ List.replicate m 1 ++ [0]).reverse
              LB01 := by
          simp [List.reverse_append, ListBlank.append_assoc]
        rwa [hL_eq] at h
      obtain ⟨ssel, _, hsel⟩ := @sel_step_reaches_main0 pre hpre m (by omega) slot walked
        (by omega) hok regs hregs
      obtain ⟨srest, _, hrest⟩ := ih (m + 1) (by omega)
      rw [ListBlank.append_assoc, ListBlank.append_assoc] at hsel
      have hadd_assoc : walked.length + (m + 1) = walked.length + m + 1 := by omega
      rw [hadd_assoc] at hrest
      exact ⟨_, by omega, nSteps_bind_eq hsw (nSteps_bind_eq hones
        (step_nSteps hs0 (nSteps_bind_eq hsel hrest)))⟩
  obtain ⟨s, hs1, hs⟩ := loop 0 (11 - r.val) (Nat.zero_add _)
  simp only [List.replicate_zero, Nat.add_zero, zf393SelRight_zero pre regs hregs,
    ListBlank.append, List.append_assoc, ListBlank.append_assoc] at hs ⊢
  exact ⟨s, hs1, hs⟩

/-- Combined multi-pass `3.<reg_r>.decnz` leaf execution from `main().0` (`State 99`). -/
theorem decnz_leaf_reaches_main0 (r : Fin 11) (slot : ℕ) (walked : List (Fin 2))
    (hwalk : walkTape 99 [] walked = .regLeaf (regDecnzStage3 r) walked [])
    (hsl : walked.length + (11 - r.val) + 3 ≤ slot)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true)
    (regs : List ℕ) (hregs : regs.length = 11) :
    ∃ s, 1 ≤ s ∧
      nSteps zf393 s
        ⟨99, Tape.mk' LB01
          (ListBlank.append (walked ++ List.replicate (slot - walked.length) 0 ++
            encodeRegs pre) (regsTape regs))⟩ =
      some (if regs[r.val] = 0 then
        @rootCfg pre (breakSlot 1 (slot + 1) walked) ((popBreakRev 1 walked.reverse).reverse) regs
      else
        @rootCfg pre (breakSlot 0 (slot + 1) walked) (retStack walked)
          (regs.set r.val (regs[r.val] - 1))) := by
  have walk_exact : ∀ (R_rem : ListBlank (Fin 2)),
      ∃ sw, 1 ≤ sw ∧ nSteps zf393 sw
        ⟨99, Tape.mk' LB01 (ListBlank.append walked R_rem)⟩ =
        some ⟨regDecnzStage3 r, Tape.mk' (ListBlank.append walked.reverse LB01)
          R_rem⟩ := by
    intro R_rem
    have hws := walkTape_sound 99 [] walked LB01 R_rem
    rw [hwalk] at hws
    obtain ⟨_, sw, hsw_pos, hs⟩ := hws
    exact ⟨sw, hsw_pos, hs⟩
  have loop : ∀ m k : ℕ, m + k = 11 - r.val →
      ∃ s, 1 ≤ s ∧ nSteps zf393 s
        ⟨99, Tape.mk' LB01
          (ListBlank.append walked
            (ListBlank.append (List.replicate m 1)
              (ListBlank.append (List.replicate (slot - (walked.length + m)) 0)
                (zf393SelRight pre m regs))))⟩ =
        some (if regs[r.val] = 0 then
          @rootCfg pre (breakSlot 1 (slot + 1) walked)
            ((popBreakRev 1 walked.reverse).reverse) regs
        else
          @rootCfg pre (breakSlot 0 (slot + 1) walked) (retStack walked)
            (regs.set r.val (regs[r.val] - 1))) := by
    intro m k hmk
    induction k generalizing m with
    | zero =>
      have hm_eq : m = 11 - r.val := by omega
      subst hm_eq
      have hrep_split : List.replicate (11 - r.val) (1 : Fin 2) =
          List.replicate (10 - r.val) 1 ++ [1] := by
        have h11 : 11 - r.val = (10 - r.val) + 1 := by omega
        rw [h11, List.replicate_succ']
      rw [hrep_split, ListBlank.append_assoc]
      obtain ⟨sw, _, hsw⟩ := walk_exact
        (ListBlank.append (List.replicate (10 - r.val) 1)
          (ListBlank.append [1]
            (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
              (zf393SelRight pre (11 - r.val) regs))))
      have hones := stage3_walk_ones_decnz r (10 - r.val) (by omega)
        (ListBlank.append walked.reverse LB01)
        (ListBlank.append [1]
          (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
            (zf393SelRight pre (11 - r.val) regs)))
      have hr10 : (⟨r.val + (10 - r.val), by omega⟩ : Fin 11) = 10 := by ext; dsimp; omega
      rw [hr10] at hones
      have hs10 : step zf393
          ⟨regDecnzStage3 10, Tape.mk'
            (ListBlank.append (List.replicate (10 - r.val) 1)
              (ListBlank.append walked.reverse LB01))
            (ListBlank.append [1]
              (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
                (zf393SelRight pre (11 - r.val) regs)))⟩ =
          some ⟨5, Tape.mk'
            (ListBlank.append (walked ++ List.replicate (11 - r.val) 1).reverse
              LB01)
            (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
              (zf393SelRight pre (11 - r.val) regs))⟩ := by
        have h := step_mk'_right (q := regDecnzStage3 10) (q' := 5) (a := 1) (b := 1) (by rfl)
          (ListBlank.append (List.replicate (10 - r.val) 1)
            (ListBlank.append walked.reverse LB01))
          (ListBlank.append (List.replicate (slot - (walked.length + (11 - r.val))) 0)
            (zf393SelRight pre (11 - r.val) regs))
        have hL_eq : ((ListBlank.append (List.replicate (10 - r.val) 1)
            (ListBlank.append walked.reverse LB01)).cons 1) =
            ListBlank.append (walked ++ List.replicate (11 - r.val) 1).reverse
              LB01 := by
          rw [hrep_split, List.reverse_append, List.reverse_append, List.reverse_replicate,
            ListBlank.append_assoc, ListBlank.append_assoc]
          rfl
        rwa [hL_eq] at h
      obtain ⟨sdec, _, hdec⟩ := @decnz_step_reaches_main0 pre hpre r slot walked hsl hok regs hregs
      exact ⟨_, by omega, nSteps_bind_eq hsw (nSteps_bind_eq hones (step_nSteps hs10 hdec))⟩
    | succ k' ih =>
      have hrm : r.val + m < 11 := by omega
      obtain ⟨sw, _, hsw⟩ := walk_exact
        (ListBlank.append (List.replicate m 1)
          (ListBlank.append (List.replicate (slot - (walked.length + m)) 0)
            (zf393SelRight pre m regs)))
      have hones := stage3_walk_ones_decnz r m (by omega)
        (ListBlank.append walked.reverse LB01)
        (ListBlank.append (List.replicate (slot - (walked.length + m)) 0)
          (zf393SelRight pre m regs))
      have hsub_z : slot - (walked.length + m) =
          (slot - (walked.length + m + 1)) + 1 := by omega
      rw [hsub_z, List.replicate_succ, ListBlank.append] at hsw hones ⊢
      have htr0 : zf393Trans (regDecnzStage3 ⟨r.val + m, hrm⟩) 0 =
          some (0, .right, 17) :=
        regDecnzStage3_step0 ⟨r.val + m, hrm⟩
      have hs0 : step zf393
          ⟨regDecnzStage3 ⟨r.val + m, hrm⟩,
            Tape.mk' (ListBlank.append (List.replicate m 1)
              (ListBlank.append walked.reverse LB01))
              ((ListBlank.append (List.replicate (slot - (walked.length + m + 1)) 0)
                (zf393SelRight pre m regs)).cons 0)⟩ =
          some ⟨17, Tape.mk'
            (ListBlank.append (walked ++ List.replicate m 1 ++ [0]).reverse LB01)
            (ListBlank.append (List.replicate (slot - (walked.length + m + 1)) 0)
              (zf393SelRight pre m regs))⟩ := by
        have h := step_mk'_right htr0
          (ListBlank.append (List.replicate m 1)
            (ListBlank.append walked.reverse LB01))
          (ListBlank.append (List.replicate (slot - (walked.length + m + 1)) 0)
            (zf393SelRight pre m regs))
        have hL_eq : ((ListBlank.append (List.replicate m 1)
            (ListBlank.append walked.reverse LB01)).cons 0) =
            ListBlank.append (walked ++ List.replicate m 1 ++ [0]).reverse
              LB01 := by
          simp [List.reverse_append, ListBlank.append_assoc]
        rwa [hL_eq] at h
      obtain ⟨ssel, _, hsel⟩ := @sel_step_reaches_main0 pre hpre m (by omega) slot walked
        (by omega) hok regs hregs
      obtain ⟨srest, _, hrest⟩ := ih (m + 1) (by omega)
      rw [ListBlank.append_assoc, ListBlank.append_assoc] at hsel
      have hadd_assoc : walked.length + (m + 1) = walked.length + m + 1 := by omega
      rw [hadd_assoc] at hrest
      exact ⟨_, by omega, nSteps_bind_eq hsw (nSteps_bind_eq hones
        (step_nSteps hs0 (nSteps_bind_eq hsel hrest)))⟩
  obtain ⟨s, hs1, hs⟩ := loop 0 (11 - r.val) (Nat.zero_add _)
  simp only [List.replicate_zero, Nat.add_zero, zf393SelRight_zero pre regs hregs,
    ListBlank.append, List.append_assoc, ListBlank.append_assoc] at hs ⊢
  exact ⟨s, hs1, hs⟩

def dagInfo_0 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 12 then
    if q.val < 6 then
      if q.val < 3 then
        if q.val < 1 then
          (99, 0, 0, 1)
        else
          if q.val < 2 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 4 then
          (99, 0, 0, 1)
        else
          if q.val < 5 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
    else
      if q.val < 9 then
        if q.val < 7 then
          (99, 0, 0, 1)
        else
          if q.val < 8 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 10 then
          (99, 0, 0, 1)
        else
          if q.val < 11 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
  else
    if q.val < 18 then
      if q.val < 15 then
        if q.val < 13 then
          (99, 0, 0, 1)
        else
          if q.val < 14 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 16 then
          (99, 0, 0, 1)
        else
          if q.val < 17 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
    else
      if q.val < 21 then
        if q.val < 19 then
          (99, 0, 0, 1)
        else
          if q.val < 20 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 22 then
          (99, 0, 0, 1)
        else
          if q.val < 23 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)

def dagInfo_1 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 36 then
    if q.val < 30 then
      if q.val < 27 then
        if q.val < 25 then
          (99, 0, 0, 1)
        else
          if q.val < 26 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 28 then
          (99, 0, 0, 1)
        else
          if q.val < 29 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
    else
      if q.val < 33 then
        if q.val < 31 then
          (99, 0, 0, 1)
        else
          if q.val < 32 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 34 then
          (99, 0, 0, 1)
        else
          if q.val < 35 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
  else
    if q.val < 42 then
      if q.val < 39 then
        if q.val < 37 then
          (99, 0, 0, 1)
        else
          if q.val < 38 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 40 then
          (99, 0, 0, 1)
        else
          if q.val < 41 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
    else
      if q.val < 45 then
        if q.val < 43 then
          (99, 0, 0, 1)
        else
          if q.val < 44 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 47 then
          if q.val < 46 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
        else
          if q.val < 48 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)

def dagInfo_2 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 61 then
    if q.val < 55 then
      if q.val < 52 then
        if q.val < 50 then
          (99, 0, 0, 1)
        else
          if q.val < 51 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 53 then
          (99, 0, 0, 1)
        else
          if q.val < 54 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
    else
      if q.val < 58 then
        if q.val < 56 then
          (99, 0, 0, 1)
        else
          if q.val < 57 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 59 then
          (99, 0, 0, 1)
        else
          if q.val < 60 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
  else
    if q.val < 67 then
      if q.val < 64 then
        if q.val < 62 then
          (99, 0, 0, 1)
        else
          if q.val < 63 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
      else
        if q.val < 65 then
          (99, 0, 0, 1)
        else
          if q.val < 66 then
            (99, 0, 0, 1)
          else
            (99, 0, 0, 1)
    else
      if q.val < 70 then
        if q.val < 68 then
          (99, 0, 0, 1)
        else
          if q.val < 69 then
            (99, 0, 0, 1)
          else
            (6, 18, 127, 3)
      else
        if q.val < 71 then
          (0, 19, 128, 3)
        else
          if q.val < 72 then
            (2, 94, 104, 2)
          else
            (3, 94, 105, 1)

def dagInfo_3 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 85 then
    if q.val < 79 then
      if q.val < 76 then
        if q.val < 74 then
          (0, 95, 106, 2)
        else
          if q.val < 75 then
            (1, 95, 107, 1)
          else
            (0, 96, 108, 2)
      else
        if q.val < 77 then
          (1, 96, 109, 1)
        else
          if q.val < 78 then
            (0, 96, 107, 2)
          else
            (1, 96, 108, 1)
    else
      if q.val < 82 then
        if q.val < 80 then
          (1, 94, 95, 3)
        else
          if q.val < 81 then
            (0, 95, 96, 2)
          else
            (0, 94, 103, 3)
      else
        if q.val < 83 then
          (0, 95, 104, 2)
        else
          if q.val < 84 then
            (1, 33, 127, 1)
          else
            (0, 34, 128, 2)
  else
    if q.val < 91 then
      if q.val < 88 then
        if q.val < 86 then
          (2, 59, 102, 2)
        else
          if q.val < 87 then
            (3, 59, 103, 1)
          else
            (0, 60, 104, 2)
      else
        if q.val < 89 then
          (1, 60, 105, 1)
        else
          if q.val < 90 then
            (0, 61, 105, 2)
          else
            (0, 60, 103, 1)
    else
      if q.val < 94 then
        if q.val < 92 then
          (0, 61, 104, 2)
        else
          if q.val < 93 then
            (0, 59, 63, 3)
          else
            (1, 100, 101, 3)
      else
        if q.val < 96 then
          if q.val < 95 then
            (0, 101, 102, 2)
          else
            (1, 0, 1, 2)
        else
          if q.val < 97 then
            (2, 0, 2, 1)
          else
            (0, 1, 2, 2)

def dagInfo_4 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 110 then
    if q.val < 104 then
      if q.val < 101 then
        if q.val < 99 then
          (0, 2, 3, 2)
        else
          if q.val < 100 then
            (0, 0, 0, 3)
          else
            (0, 1, 1, 2)
      else
        if q.val < 102 then
          (0, 2, 2, 2)
        else
          if q.val < 103 then
            (0, 3, 3, 2)
          else
            (0, 4, 4, 2)
    else
      if q.val < 107 then
        if q.val < 105 then
          (0, 5, 5, 3)
        else
          if q.val < 106 then
            (0, 6, 6, 2)
          else
            (0, 7, 7, 3)
      else
        if q.val < 108 then
          (0, 8, 8, 2)
        else
          if q.val < 109 then
            (0, 9, 9, 3)
          else
            (0, 10, 10, 2)
  else
    if q.val < 116 then
      if q.val < 113 then
        if q.val < 111 then
          (0, 11, 11, 3)
        else
          if q.val < 112 then
            (0, 12, 12, 2)
          else
            (0, 13, 13, 4)
      else
        if q.val < 114 then
          (0, 14, 14, 6)
        else
          if q.val < 115 then
            (0, 15, 15, 6)
          else
            (0, 16, 16, 6)
    else
      if q.val < 119 then
        if q.val < 117 then
          (0, 17, 17, 5)
        else
          if q.val < 118 then
            (0, 18, 18, 6)
          else
            (0, 19, 19, 6)
      else
        if q.val < 120 then
          (0, 20, 20, 5)
        else
          if q.val < 121 then
            (0, 21, 21, 5)
          else
            (0, 22, 22, 6)

def dagInfo_5 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 134 then
    if q.val < 128 then
      if q.val < 125 then
        if q.val < 123 then
          (0, 23, 23, 7)
        else
          if q.val < 124 then
            (0, 24, 24, 5)
          else
            (0, 25, 25, 7)
      else
        if q.val < 126 then
          (0, 26, 26, 7)
        else
          if q.val < 127 then
            (0, 27, 27, 8)
          else
            (0, 28, 28, 6)
    else
      if q.val < 131 then
        if q.val < 129 then
          (0, 29, 29, 8)
        else
          if q.val < 130 then
            (0, 30, 30, 6)
          else
            (0, 31, 31, 5)
      else
        if q.val < 132 then
          (0, 32, 32, 6)
        else
          if q.val < 133 then
            (0, 33, 33, 6)
          else
            (0, 34, 34, 8)
  else
    if q.val < 140 then
      if q.val < 137 then
        if q.val < 135 then
          (0, 35, 35, 7)
        else
          if q.val < 136 then
            (0, 36, 36, 5)
          else
            (0, 37, 37, 6)
      else
        if q.val < 138 then
          (0, 38, 38, 8)
        else
          if q.val < 139 then
            (0, 39, 39, 6)
          else
            (0, 40, 40, 6)
    else
      if q.val < 143 then
        if q.val < 141 then
          (0, 41, 41, 9)
        else
          if q.val < 142 then
            (0, 42, 42, 8)
          else
            (0, 43, 43, 5)
      else
        if q.val < 145 then
          if q.val < 144 then
            (0, 44, 44, 7)
          else
            (0, 45, 45, 5)
        else
          if q.val < 146 then
            (0, 46, 46, 9)
          else
            (0, 47, 47, 5)

def dagInfo_6 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 159 then
    if q.val < 153 then
      if q.val < 150 then
        if q.val < 148 then
          (0, 48, 48, 5)
        else
          if q.val < 149 then
            (0, 49, 49, 6)
          else
            (0, 50, 50, 7)
      else
        if q.val < 151 then
          (0, 51, 51, 5)
        else
          if q.val < 152 then
            (0, 52, 52, 7)
          else
            (0, 53, 53, 6)
    else
      if q.val < 156 then
        if q.val < 154 then
          (0, 54, 54, 8)
        else
          if q.val < 155 then
            (0, 55, 55, 2)
          else
            (0, 56, 56, 2)
      else
        if q.val < 157 then
          (0, 57, 57, 3)
        else
          if q.val < 158 then
            (0, 58, 58, 2)
          else
            (0, 59, 59, 2)
  else
    if q.val < 165 then
      if q.val < 162 then
        if q.val < 160 then
          (0, 60, 60, 3)
        else
          if q.val < 161 then
            (0, 61, 61, 6)
          else
            (0, 62, 62, 5)
      else
        if q.val < 163 then
          (0, 63, 63, 8)
        else
          if q.val < 164 then
            (0, 64, 64, 5)
          else
            (0, 65, 65, 6)
    else
      if q.val < 168 then
        if q.val < 166 then
          (0, 66, 66, 6)
        else
          if q.val < 167 then
            (0, 67, 67, 5)
          else
            (0, 68, 68, 7)
      else
        if q.val < 169 then
          (0, 69, 69, 8)
        else
          if q.val < 170 then
            (0, 70, 70, 5)
          else
            (0, 71, 71, 6)

def dagInfo_7 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 183 then
    if q.val < 177 then
      if q.val < 174 then
        if q.val < 172 then
          (0, 72, 72, 5)
        else
          if q.val < 173 then
            (0, 73, 73, 9)
          else
            (0, 74, 74, 5)
      else
        if q.val < 175 then
          (0, 75, 75, 5)
        else
          if q.val < 176 then
            (0, 76, 76, 5)
          else
            (0, 77, 77, 6)
    else
      if q.val < 180 then
        if q.val < 178 then
          (0, 78, 78, 5)
        else
          if q.val < 179 then
            (0, 79, 79, 6)
          else
            (0, 80, 80, 6)
      else
        if q.val < 181 then
          (0, 81, 81, 5)
        else
          if q.val < 182 then
            (0, 82, 82, 5)
          else
            (0, 83, 83, 6)
  else
    if q.val < 189 then
      if q.val < 186 then
        if q.val < 184 then
          (0, 84, 84, 5)
        else
          if q.val < 185 then
            (0, 85, 85, 6)
          else
            (0, 86, 86, 5)
      else
        if q.val < 187 then
          (0, 87, 87, 7)
        else
          if q.val < 188 then
            (0, 88, 88, 6)
          else
            (0, 89, 89, 6)
    else
      if q.val < 192 then
        if q.val < 190 then
          (0, 90, 90, 6)
        else
          if q.val < 191 then
            (0, 91, 91, 4)
          else
            (0, 92, 92, 6)
      else
        if q.val < 194 then
          if q.val < 193 then
            (0, 93, 93, 4)
          else
            (0, 94, 94, 4)
        else
          if q.val < 195 then
            (0, 95, 95, 6)
          else
            (0, 96, 96, 5)

def dagInfo_8 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 208 then
    if q.val < 202 then
      if q.val < 199 then
        if q.val < 197 then
          (0, 97, 97, 2)
        else
          if q.val < 198 then
            (0, 98, 98, 2)
          else
            (0, 99, 99, 2)
      else
        if q.val < 200 then
          (0, 100, 100, 4)
        else
          if q.val < 201 then
            (0, 101, 101, 4)
          else
            (0, 102, 102, 7)
    else
      if q.val < 205 then
        if q.val < 203 then
          (0, 103, 103, 6)
        else
          if q.val < 204 then
            (0, 104, 104, 6)
          else
            (0, 105, 105, 5)
      else
        if q.val < 206 then
          (0, 106, 106, 7)
        else
          if q.val < 207 then
            (0, 107, 107, 5)
          else
            (0, 108, 108, 4)
  else
    if q.val < 214 then
      if q.val < 211 then
        if q.val < 209 then
          (0, 109, 109, 5)
        else
          if q.val < 210 then
            (0, 110, 110, 6)
          else
            (0, 111, 111, 5)
      else
        if q.val < 212 then
          (0, 112, 112, 6)
        else
          if q.val < 213 then
            (0, 113, 113, 5)
          else
            (0, 114, 114, 6)
    else
      if q.val < 217 then
        if q.val < 215 then
          (0, 115, 115, 5)
        else
          if q.val < 216 then
            (0, 116, 116, 6)
          else
            (0, 117, 117, 6)
      else
        if q.val < 219 then
          if q.val < 218 then
            (0, 118, 118, 6)
          else
            (0, 119, 119, 9)
        else
          if q.val < 220 then
            (0, 120, 120, 6)
          else
            (0, 121, 121, 9)

def dagInfo_9 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 233 then
    if q.val < 227 then
      if q.val < 224 then
        if q.val < 222 then
          (0, 122, 122, 3)
        else
          if q.val < 223 then
            (0, 123, 123, 1)
          else
            (0, 124, 124, 2)
      else
        if q.val < 225 then
          (1, 124, 125, 1)
        else
          if q.val < 226 then
            (0, 125, 126, 2)
          else
            (1, 46, 74, 8)
    else
      if q.val < 230 then
        if q.val < 228 then
          (0, 47, 75, 5)
        else
          if q.val < 229 then
            (0, 48, 76, 6)
          else
            (0, 49, 77, 6)
      else
        if q.val < 231 then
          (0, 50, 78, 5)
        else
          if q.val < 232 then
            (1, 61, 104, 5)
          else
            (0, 62, 105, 5)
  else
    if q.val < 239 then
      if q.val < 236 then
        if q.val < 234 then
          (0, 63, 106, 5)
        else
          if q.val < 235 then
            (0, 64, 107, 5)
          else
            (0, 65, 108, 7)
      else
        if q.val < 237 then
          (0, 66, 109, 6)
        else
          if q.val < 238 then
            (0, 67, 110, 4)
          else
            (1, 23, 26, 6)
    else
      if q.val < 242 then
        if q.val < 240 then
          (0, 24, 27, 7)
        else
          if q.val < 241 then
            (0, 25, 28, 6)
          else
            (1, 34, 43, 7)
      else
        if q.val < 243 then
          (0, 35, 44, 6)
        else
          if q.val < 244 then
            (2, 46, 75, 7)
          else
            (1, 49, 78, 5)

def dagInfo_10 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 257 then
    if q.val < 251 then
      if q.val < 248 then
        if q.val < 246 then
          (1, 29, 39, 7)
        else
          if q.val < 247 then
            (3, 46, 79, 6)
          else
            (1, 32, 41, 5)
      else
        if q.val < 249 then
          (2, 26, 88, 6)
        else
          if q.val < 250 then
            (1, 22, 111, 5)
          else
            (1, 90, 119, 5)
    else
      if q.val < 254 then
        if q.val < 252 then
          (0, 91, 120, 5)
        else
          if q.val < 253 then
            (0, 92, 121, 8)
          else
            (2, 61, 105, 4)
      else
        if q.val < 255 then
          (1, 50, 53, 6)
        else
          if q.val < 256 then
            (1, 57, 61, 2)
          else
            (0, 58, 62, 2)
  else
    if q.val < 263 then
      if q.val < 260 then
        if q.val < 258 then
          (1, 18, 93, 5)
        else
          if q.val < 259 then
            (0, 19, 94, 5)
          else
            (1, 65, 109, 6)
      else
        if q.val < 261 then
          (1, 107, 110, 4)
        else
          if q.val < 262 then
            (1, 114, 117, 5)
          else
            (0, 115, 118, 4)
    else
      if q.val < 266 then
        if q.val < 264 then
          (3, 23, 112, 5)
        else
          if q.val < 265 then
            (1, 24, 42, 6)
          else
            (1, 16, 29, 5)
      else
        if q.val < 268 then
          if q.val < 267 then
            (0, 17, 30, 5)
          else
            (2, 29, 107, 6)
        else
          if q.val < 269 then
            (4, 46, 84, 5)
          else
            (1, 5, 12, 2)

def dagInfo_11 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 282 then
    if q.val < 276 then
      if q.val < 273 then
        if q.val < 271 then
          (1, 19, 105, 5)
        else
          if q.val < 272 then
            (1, 49, 110, 5)
          else
            (1, 33, 121, 5)
      else
        if q.val < 274 then
          (1, 48, 106, 5)
        else
          if q.val < 275 then
            (1, 37, 81, 5)
          else
            (1, 85, 90, 5)
    else
      if q.val < 279 then
        if q.val < 277 then
          (1, 93, 102, 3)
        else
          if q.val < 278 then
            (1, 15, 118, 5)
          else
            (1, 26, 122, 8)
      else
        if q.val < 280 then
          (2, 47, 111, 5)
        else
          if q.val < 281 then
            (0, 24, 113, 5)
          else
            (3, 29, 108, 5)
  else
    if q.val < 288 then
      if q.val < 285 then
        if q.val < 283 then
          (1, 51, 96, 5)
        else
          if q.val < 284 then
            (3, 36, 111, 3)
          else
            (2, 48, 110, 5)
      else
        if q.val < 286 then
          (1, 30, 40, 5)
        else
          if q.val < 287 then
            (0, 47, 76, 5)
          else
            (0, 25, 43, 4)
    else
      if q.val < 291 then
        if q.val < 289 then
          (1, 15, 129, 1)
        else
          if q.val < 290 then
            (7, 18, 128, 2)
          else
            (7, 13, 130, 2)
      else
        if q.val < 292 then
          (0, 14, 131, 1)
        else
          if q.val < 293 then
            (0, 15, 132, 2)
          else
            (1, 15, 133, 1)

def dagInfo_12 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 306 then
    if q.val < 300 then
      if q.val < 297 then
        if q.val < 295 then
          (1, 19, 129, 2)
        else
          if q.val < 296 then
            (0, 20, 130, 1)
          else
            (0, 21, 131, 2)
      else
        if q.val < 298 then
          (1, 21, 132, 1)
        else
          if q.val < 299 then
            (3, 17, 112, 4)
          else
            (0, 18, 113, 2)
    else
      if q.val < 303 then
        if q.val < 301 then
          (2, 45, 112, 4)
        else
          if q.val < 302 then
            (0, 46, 113, 2)
          else
            (2, 49, 111, 4)
      else
        if q.val < 304 then
          (0, 50, 112, 2)
        else
          if q.val < 305 then
            (6, 13, 129, 3)
          else
            (4, 30, 123, 2)
  else
    if q.val < 312 then
      if q.val < 309 then
        if q.val < 307 then
          (0, 31, 124, 2)
        else
          if q.val < 308 then
            (0, 32, 125, 2)
          else
            (0, 33, 126, 2)
      else
        if q.val < 310 then
          (1, 7, 132, 1)
        else
          if q.val < 311 then
            (0, 6, 130, 1)
          else
            (0, 7, 131, 2)
    else
      if q.val < 315 then
        if q.val < 313 then
          (0, 8, 132, 2)
        else
          if q.val < 314 then
            (2, 5, 13, 1)
          else
            (8, 18, 129, 1)
      else
        if q.val < 317 then
          if q.val < 316 then
            (1, 31, 125, 1)
          else
            (0, 32, 126, 1)
        else
          if q.val < 318 then
            (0, 33, 127, 2)
          else
            (0, 34, 128, 2)

def dagInfo_13 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 331 then
    if q.val < 325 then
      if q.val < 322 then
        if q.val < 320 then
          (5, 14, 127, 4)
        else
          if q.val < 321 then
            (4, 16, 128, 4)
          else
            (4, 14, 126, 5)
      else
        if q.val < 323 then
          (1, 19, 127, 5)
        else
          if q.val < 324 then
            (2, 26, 123, 7)
          else
            (0, 27, 124, 5)
    else
      if q.val < 328 then
        if q.val < 326 then
          (2, 18, 125, 4)
        else
          if q.val < 327 then
            (0, 19, 126, 6)
          else
            (2, 25, 120, 4)
      else
        if q.val < 329 then
          (0, 26, 121, 5)
        else
          if q.val < 330 then
            (1, 19, 119, 4)
          else
            (0, 20, 120, 4)
  else
    if q.val < 337 then
      if q.val < 334 then
        if q.val < 332 then
          (1, 20, 123, 7)
        else
          if q.val < 333 then
            (0, 21, 124, 5)
          else
            (0, 9, 134, 1)
      else
        if q.val < 335 then
          (0, 15, 131, 1)
        else
          if q.val < 336 then
            (0, 17, 135, 1)
          else
            (0, 19, 115, 2)
    else
      if q.val < 340 then
        if q.val < 338 then
          (1, 19, 116, 1)
        else
          if q.val < 339 then
            (0, 58, 100, 2)
          else
            (1, 58, 101, 1)
      else
        if q.val < 341 then
          (0, 56, 60, 2)
        else
          if q.val < 342 then
            (1, 56, 61, 1)
          else
            (1, 1, 2, 1)

def dagInfo_14 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 355 then
    if q.val < 349 then
      if q.val < 346 then
        if q.val < 344 then
          (1, 1, 3, 1)
        else
          if q.val < 345 then
            (0, 2, 4, 2)
          else
            (1, 2, 5, 1)
      else
        if q.val < 347 then
          (1, 2, 3, 1)
        else
          if q.val < 348 then
            (1, 18, 114, 1)
          else
            (1, 101, 103, 1)
    else
      if q.val < 352 then
        if q.val < 350 then
          (0, 102, 104, 2)
        else
          if q.val < 351 then
            (1, 102, 105, 1)
          else
            (1, 55, 56, 1)
      else
        if q.val < 353 then
          (1, 3, 97, 1)
        else
          if q.val < 354 then
            (1, 46, 114, 1)
          else
            (1, 98, 99, 1)
  else
    if q.val < 361 then
      if q.val < 358 then
        if q.val < 356 then
          (1, 58, 59, 1)
        else
          if q.val < 357 then
            (1, 4, 105, 1)
          else
            (1, 50, 113, 1)
      else
        if q.val < 359 then
          (2, 57, 62, 1)
        else
          if q.val < 360 then
            (0, 34, 127, 1)
          else
            (1, 6, 7, 1)
    else
      if q.val < 364 then
        if q.val < 362 then
          (0, 7, 8, 1)
        else
          if q.val < 363 then
            (1, 2, 4, 1)
          else
            (0, 3, 5, 1)
      else
        if q.val < 366 then
          if q.val < 365 then
            (1, 8, 114, 1)
          else
            (0, 9, 115, 1)
        else
          if q.val < 367 then
            (1, 10, 114, 1)
          else
            (0, 11, 115, 1)

def dagInfo_15 (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 380 then
    if q.val < 374 then
      if q.val < 371 then
        if q.val < 369 then
          (1, 12, 113, 1)
        else
          if q.val < 370 then
            (0, 13, 114, 1)
          else
            (1, 8, 133, 1)
      else
        if q.val < 372 then
          (0, 35, 129, 1)
        else
          if q.val < 373 then
            (0, 14, 130, 1)
          else
            (2, 19, 130, 1)
    else
      if q.val < 377 then
        if q.val < 375 then
          (0, 20, 131, 2)
        else
          if q.val < 376 then
            (1, 20, 132, 1)
          else
            (1, 61, 106, 1)
      else
        if q.val < 378 then
          (0, 6, 13, 1)
        else
          if q.val < 379 then
            (0, 7, 14, 1)
          else
            (0, 20, 129, 1)
  else
    if q.val < 386 then
      if q.val < 383 then
        if q.val < 381 then
          (1, 19, 129, 1)
        else
          if q.val < 382 then
            (1, 61, 105, 1)
          else
            (1, 34, 129, 1)
      else
        if q.val < 384 then
          (8, 13, 131, 1)
        else
          if q.val < 385 then
            (0, 14, 132, 2)
          else
            (1, 14, 133, 1)
    else
      if q.val < 389 then
        if q.val < 387 then
          (5, 22, 133, 1)
        else
          if q.val < 388 then
            (0, 23, 134, 1)
          else
            (1, 34, 129, 1)
      else
        if q.val < 391 then
          if q.val < 390 then
            (0, 16, 134, 1)
          else
            (5, 20, 125, 4)
        else
          if q.val < 392 then
            (0, 21, 126, 5)
          else
            (3, 20, 125, 6)

def dagInfo (q : Fin 393) : ℕ × ℕ × ℕ × ℕ :=
  if q.val < 196 then
    if q.val < 98 then
      if q.val < 49 then
        if q.val < 24 then
          dagInfo_0 q
        else
          dagInfo_1 q
      else
        if q.val < 73 then
          dagInfo_2 q
        else
          dagInfo_3 q
    else
      if q.val < 147 then
        if q.val < 122 then
          dagInfo_4 q
        else
          dagInfo_5 q
      else
        if q.val < 171 then
          dagInfo_6 q
        else
          dagInfo_7 q
  else
    if q.val < 294 then
      if q.val < 245 then
        if q.val < 221 then
          dagInfo_8 q
        else
          dagInfo_9 q
      else
        if q.val < 270 then
          dagInfo_10 q
        else
          dagInfo_11 q
    else
      if q.val < 343 then
        if q.val < 319 then
          dagInfo_12 q
        else
          dagInfo_13 q
      else
        if q.val < 368 then
          dagInfo_14 q
        else
          dagInfo_15 q

inductive SlotTrie where
  | leaf (val : Option ℕ)
  | branch (val : Option ℕ) (zero one : SlotTrie)

def SlotTrie.get : SlotTrie → List (Fin 2) → Option ℕ
  | .leaf v, [] => v
  | .leaf _, _ :: _ => none
  | .branch v _ _, [] => v
  | .branch _ l r, b :: bs => (if b == 0 then l else r).get bs

def trieNode_0 : SlotTrie :=
  (.branch (some 20)
    (.branch none
    (.leaf none)
    (.branch (some 21)
    (.branch none
    (.leaf none)
    (.leaf (some 21)))
    (.leaf (some 21))))
    (.branch (some 21)
    (.branch none
    (.leaf none)
    (.branch (some 22)
    (.leaf none)
    (.leaf (some 22))))
    (.leaf (some 22))))

def trieNode_1 : SlotTrie :=
  (.branch (some 25)
    (.leaf none)
    (.branch (some 25)
    (.branch none
    (.leaf none)
    (.leaf (some 26)))
    (.branch (some 26)
    (.branch none
    (.leaf none)
    (.branch (some 27)
    (.leaf none)
    (.leaf (some 27))))
    (.leaf (some 27)))))

def trieNode_2 : SlotTrie :=
  (.branch (some 28)
    (.leaf none)
    (.branch (some 28)
    (.branch none
    (.leaf none)
    (.leaf (some 29)))
    (.branch (some 29)
    (.branch none
    (.leaf none)
    (.branch (some 30)
    (.leaf none)
    (.leaf (some 30))))
    (.leaf (some 30)))))

def trieNode_3 : SlotTrie :=
  (.branch (some 31)
    (.leaf none)
    (.branch (some 31)
    (.branch none
    (.leaf none)
    (.leaf (some 32)))
    (.branch (some 32)
    (.branch none
    (.leaf none)
    (.branch (some 33)
    (.leaf none)
    (.leaf (some 33))))
    (.leaf (some 33)))))

def trieNode_4 : SlotTrie :=
  (.branch (some 34)
    (.leaf none)
    (.branch (some 34)
    (.branch none
    (.leaf none)
    (.leaf (some 35)))
    (.branch (some 35)
    (.branch none
    (.leaf none)
    (.branch (some 36)
    (.leaf none)
    (.leaf (some 36))))
    (.leaf (some 36)))))

def trieNode_5 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 37)
    (.branch none
    (.leaf none)
    (.leaf (some 37)))
    (.leaf (some 37))))
    (.branch (some 37)
    (.leaf none)
    (.branch (some 38)
    (.branch none
    (.leaf none)
    (.branch (some 38)
    (.leaf none)
    (.branch (some 39)
    (.leaf none)
    (.leaf (some 39)))))
    (.leaf (some 39)))))

def trieNode_6 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 40)
    (.branch none
    (.leaf none)
    (.leaf (some 40)))
    (.leaf (some 40))))
    (.branch (some 40)
    (.leaf none)
    (.branch (some 41)
    (.branch none
    (.leaf none)
    (.branch (some 41)
    (.leaf none)
    (.branch (some 42)
    (.leaf none)
    (.leaf (some 42)))))
    (.leaf (some 42)))))

def trieNode_7 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 43)
    (.branch none
    (.leaf none)
    (.leaf (some 43)))
    (.leaf (some 43))))
    (.branch (some 43)
    (.leaf none)
    (.branch (some 44)
    (.branch none
    (.leaf none)
    (.branch (some 44)
    (.leaf none)
    (.branch (some 45)
    (.leaf none)
    (.leaf (some 45)))))
    (.leaf (some 45)))))

def trieNode_8 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 46)
    (.branch none
    (.leaf none)
    (.leaf (some 46)))
    (.leaf (some 46))))
    (.branch (some 46)
    (.leaf none)
    (.branch (some 47)
    (.branch none
    (.leaf none)
    (.branch (some 47)
    (.leaf none)
    (.branch (some 48)
    (.leaf none)
    (.leaf (some 48)))))
    (.leaf (some 48)))))

def trieNode_9 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 49)
    (.branch none
    (.leaf none)
    (.leaf (some 49)))
    (.leaf (some 49))))
    (.branch (some 49)
    (.leaf none)
    (.branch (some 50)
    (.branch none
    (.leaf none)
    (.branch (some 50)
    (.leaf none)
    (.branch (some 51)
    (.leaf none)
    (.leaf (some 51)))))
    (.leaf (some 51)))))

def trieNode_10 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 52)
    (.branch none
    (.leaf none)
    (.leaf (some 52)))
    (.leaf (some 52))))
    (.branch (some 52)
    (.leaf none)
    (.branch (some 53)
    (.branch none
    (.leaf none)
    (.branch (some 53)
    (.leaf none)
    (.branch (some 54)
    (.leaf none)
    (.leaf (some 54)))))
    (.leaf (some 54)))))

def trieNode_11 : SlotTrie :=
  (.branch (some 54)
    (.branch none
    (.leaf none)
    (.branch (some 55)
    (.branch none
    (.leaf none)
    (.leaf (some 55)))
    (.leaf (some 55))))
    (.branch (some 55)
    (.leaf none)
    (.branch (some 56)
    (.leaf none)
    (.leaf (some 56)))))

def trieNode_12 : SlotTrie :=
  (.branch (some 57)
    (.leaf none)
    (.branch (some 57)
    (.branch none
    (.leaf none)
    (.leaf (some 58)))
    (.branch (some 58)
    (.branch none
    (.leaf none)
    (.branch (some 59)
    (.leaf none)
    (.leaf (some 59))))
    (.leaf (some 59)))))

def trieNode_13 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 59)
    (.branch none
    (.leaf none)
    (.leaf (some 59)))
    (.leaf (some 59))))
    (.branch (some 59)
    (.leaf none)
    (.branch (some 60)
    (.branch none
    (.leaf none)
    (.branch (some 60)
    (.leaf none)
    (.branch (some 61)
    (.leaf none)
    (.leaf (some 61)))))
    (.leaf (some 61)))))

def trieNode_14 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 62)
    (.branch none
    (.leaf none)
    (.leaf (some 62)))
    (.leaf (some 62))))
    (.branch (some 62)
    (.leaf none)
    (.branch (some 63)
    (.branch none
    (.leaf none)
    (.branch (some 63)
    (.leaf none)
    (.branch (some 64)
    (.leaf none)
    (.leaf (some 64)))))
    (.leaf (some 64)))))

def trieNode_15 : SlotTrie :=
  (.branch (some 65)
    (.leaf none)
    (.branch (some 65)
    (.branch none
    (.leaf none)
    (.leaf (some 66)))
    (.branch (some 66)
    (.branch none
    (.leaf none)
    (.branch (some 67)
    (.leaf none)
    (.leaf (some 67))))
    (.leaf (some 67)))))

def trieNode_16 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 67)
    (.branch none
    (.leaf none)
    (.leaf (some 67)))
    (.leaf (some 67))))
    (.branch (some 67)
    (.leaf none)
    (.branch (some 68)
    (.branch none
    (.leaf none)
    (.branch (some 68)
    (.leaf none)
    (.branch (some 69)
    (.leaf none)
    (.leaf (some 69)))))
    (.leaf (some 69)))))

def trieNode_17 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    trieNode_14
    (.branch (some 63)
    (.leaf none)
    (.branch (some 64)
    (.leaf none)
    (.leaf (some 64)))))
    (.branch (some 64)
    (.leaf none)
    (.leaf (some 64))))
    (.branch (some 64)
    (.leaf none)
    (.leaf (some 64))))

def trieNode_18 : SlotTrie :=
  (.branch (some 64)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_15)
    (.branch (some 65)
    (.leaf none)
    (.branch (some 66)
    (.leaf none)
    (.leaf (some 66)))))
    (.branch (some 66)
    trieNode_16
    (.branch (some 68)
    (.leaf none)
    (.branch (some 69)
    (.leaf none)
    (.leaf (some 69))))))

def trieNode_19 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_12)
    (.branch (some 57)
    (.leaf none)
    (.branch (some 58)
    (.leaf none)
    (.leaf (some 58)))))
    (.branch (some 58)
    trieNode_13
    (.branch (some 60)
    (.leaf none)
    (.branch (some 61)
    (.leaf none)
    (.leaf (some 61))))))

def trieNode_20 : SlotTrie :=
  (.branch (some 51)
    (.branch none
    (.branch none
    trieNode_10
    (.branch (some 53)
    (.leaf none)
    (.branch (some 54)
    (.leaf none)
    (.leaf (some 54)))))
    trieNode_11)
    (.branch (some 56)
    trieNode_19
    (.branch (some 61)
    trieNode_17
    trieNode_18)))

def trieNode_21 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 70)
    (.branch none
    (.leaf none)
    (.leaf (some 70)))
    (.leaf (some 70))))
    (.branch (some 70)
    (.leaf none)
    (.branch (some 71)
    (.branch none
    (.leaf none)
    (.branch (some 71)
    (.leaf none)
    (.branch (some 72)
    (.leaf none)
    (.leaf (some 72)))))
    (.leaf (some 72)))))

def trieNode_22 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 73)
    (.branch none
    (.leaf none)
    (.leaf (some 73)))
    (.leaf (some 73))))
    (.branch (some 73)
    (.leaf none)
    (.branch (some 74)
    (.branch none
    (.leaf none)
    (.branch (some 74)
    (.leaf none)
    (.branch (some 75)
    (.leaf none)
    (.leaf (some 75)))))
    (.leaf (some 75)))))

def trieNode_23 : SlotTrie :=
  (.branch (some 76)
    (.leaf none)
    (.branch (some 76)
    (.branch none
    (.leaf none)
    (.leaf (some 77)))
    (.branch (some 77)
    (.branch none
    (.leaf none)
    (.branch (some 78)
    (.leaf none)
    (.leaf (some 78))))
    (.leaf (some 78)))))

def trieNode_24 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 78)
    (.branch none
    (.leaf none)
    (.leaf (some 78)))
    (.leaf (some 78))))
    (.branch (some 78)
    (.leaf none)
    (.branch (some 79)
    (.branch none
    (.leaf none)
    (.branch (some 79)
    (.leaf none)
    (.branch (some 80)
    (.leaf none)
    (.leaf (some 80)))))
    (.leaf (some 80)))))

def trieNode_25 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 81)
    (.branch none
    (.leaf none)
    (.leaf (some 81)))
    (.leaf (some 81))))
    (.branch (some 81)
    (.leaf none)
    (.branch (some 82)
    (.branch none
    (.leaf none)
    (.branch (some 82)
    (.leaf none)
    (.branch (some 83)
    (.leaf none)
    (.leaf (some 83)))))
    (.leaf (some 83)))))

def trieNode_26 : SlotTrie :=
  (.branch (some 84)
    (.leaf none)
    (.branch (some 84)
    (.branch none
    (.leaf none)
    (.leaf (some 85)))
    (.branch (some 85)
    (.branch none
    (.leaf none)
    (.branch (some 86)
    (.leaf none)
    (.leaf (some 86))))
    (.leaf (some 86)))))

def trieNode_27 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 86)
    (.branch none
    (.leaf none)
    (.leaf (some 86)))
    (.leaf (some 86))))
    (.branch (some 86)
    (.leaf none)
    (.branch (some 87)
    (.branch none
    (.leaf none)
    (.branch (some 87)
    (.leaf none)
    (.branch (some 88)
    (.leaf none)
    (.leaf (some 88)))))
    (.leaf (some 88)))))

def trieNode_28 : SlotTrie :=
  (.branch (some 83)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_26)
    (.branch (some 84)
    (.leaf none)
    (.branch (some 85)
    (.leaf none)
    (.leaf (some 85)))))
    (.branch (some 85)
    trieNode_27
    (.branch (some 87)
    (.leaf none)
    (.branch (some 88)
    (.leaf none)
    (.leaf (some 88))))))

def trieNode_29 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_23)
    (.branch (some 76)
    (.leaf none)
    (.branch (some 77)
    (.leaf none)
    (.leaf (some 77)))))
    (.branch (some 77)
    trieNode_24
    (.branch (some 79)
    (.leaf none)
    (.branch (some 80)
    (.leaf none)
    (.leaf (some 80))))))

def trieNode_30 : SlotTrie :=
  (.branch (some 89)
    (.leaf none)
    (.branch (some 89)
    (.branch none
    (.leaf none)
    (.leaf (some 90)))
    (.branch (some 90)
    (.branch none
    (.leaf none)
    (.branch (some 91)
    (.leaf none)
    (.leaf (some 91))))
    (.leaf (some 91)))))

def trieNode_31 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 91)
    (.branch none
    (.leaf none)
    (.leaf (some 91)))
    (.leaf (some 91))))
    (.branch (some 91)
    (.leaf none)
    (.branch (some 92)
    (.branch none
    (.leaf none)
    (.branch (some 92)
    (.leaf none)
    (.branch (some 93)
    (.leaf none)
    (.leaf (some 93)))))
    (.leaf (some 93)))))

def trieNode_32 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 94)
    (.branch none
    (.leaf none)
    (.leaf (some 94)))
    (.leaf (some 94))))
    (.branch (some 94)
    (.leaf none)
    (.branch (some 95)
    (.branch none
    (.leaf none)
    (.branch (some 95)
    (.leaf none)
    (.branch (some 96)
    (.leaf none)
    (.leaf (some 96)))))
    (.leaf (some 96)))))

def trieNode_33 : SlotTrie :=
  (.branch (some 97)
    (.leaf none)
    (.branch (some 97)
    (.branch none
    (.leaf none)
    (.leaf (some 98)))
    (.branch (some 98)
    (.branch none
    (.leaf none)
    (.branch (some 99)
    (.leaf none)
    (.leaf (some 99))))
    (.leaf (some 99)))))

def trieNode_34 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 99)
    (.branch none
    (.leaf none)
    (.leaf (some 99)))
    (.leaf (some 99))))
    (.branch (some 99)
    (.leaf none)
    (.branch (some 100)
    (.branch none
    (.leaf none)
    (.branch (some 100)
    (.leaf none)
    (.branch (some 101)
    (.leaf none)
    (.leaf (some 101)))))
    (.leaf (some 101)))))

def trieNode_35 : SlotTrie :=
  (.branch (some 96)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_33)
    (.branch (some 97)
    (.leaf none)
    (.branch (some 98)
    (.leaf none)
    (.leaf (some 98)))))
    (.branch (some 98)
    trieNode_34
    (.branch (some 100)
    (.leaf none)
    (.branch (some 101)
    (.leaf none)
    (.leaf (some 101))))))

def trieNode_36 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_30)
    (.branch (some 89)
    (.leaf none)
    (.branch (some 90)
    (.leaf none)
    (.leaf (some 90)))))
    (.branch (some 90)
    trieNode_31
    (.branch (some 92)
    (.leaf none)
    (.branch (some 93)
    (.leaf none)
    (.leaf (some 93))))))

def trieNode_37 : SlotTrie :=
  (.branch (some 93)
    (.branch none
    (.branch none
    trieNode_32
    (.branch (some 95)
    (.leaf none)
    (.branch (some 96)
    (.leaf none)
    (.leaf (some 96)))))
    (.branch (some 96)
    (.leaf none)
    (.leaf (some 96))))
    trieNode_35)

def trieNode_38 : SlotTrie :=
  (.branch (some 75)
    (.branch none
    trieNode_29
    (.branch (some 80)
    (.branch none
    trieNode_25
    (.branch (some 82)
    (.leaf none)
    (.branch (some 83)
    (.leaf none)
    (.leaf (some 83)))))
    trieNode_28))
    (.branch (some 88)
    trieNode_36
    trieNode_37))

def trieNode_39 : SlotTrie :=
  (.branch (some 102)
    (.leaf none)
    (.branch (some 102)
    (.branch none
    (.leaf none)
    (.leaf (some 103)))
    (.branch (some 103)
    (.branch none
    (.leaf none)
    (.branch (some 104)
    (.leaf none)
    (.leaf (some 104))))
    (.leaf (some 104)))))

def trieNode_40 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 104)
    (.branch none
    (.leaf none)
    (.leaf (some 104)))
    (.leaf (some 104))))
    (.branch (some 104)
    (.leaf none)
    (.branch (some 105)
    (.branch none
    (.leaf none)
    (.branch (some 105)
    (.leaf none)
    (.branch (some 106)
    (.leaf none)
    (.leaf (some 106)))))
    (.leaf (some 106)))))

def trieNode_41 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 107)
    (.branch none
    (.leaf none)
    (.leaf (some 107)))
    (.leaf (some 107))))
    (.branch (some 107)
    (.leaf none)
    (.branch (some 108)
    (.branch none
    (.leaf none)
    (.branch (some 108)
    (.leaf none)
    (.branch (some 109)
    (.leaf none)
    (.leaf (some 109)))))
    (.leaf (some 109)))))

def trieNode_42 : SlotTrie :=
  (.branch (some 110)
    (.leaf none)
    (.branch (some 110)
    (.branch none
    (.leaf none)
    (.leaf (some 111)))
    (.branch (some 111)
    (.branch none
    (.leaf none)
    (.branch (some 112)
    (.leaf none)
    (.leaf (some 112))))
    (.leaf (some 112)))))

def trieNode_43 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 112)
    (.branch none
    (.leaf none)
    (.leaf (some 112)))
    (.leaf (some 112))))
    (.branch (some 112)
    (.leaf none)
    (.branch (some 113)
    (.branch none
    (.leaf none)
    (.branch (some 113)
    (.leaf none)
    (.branch (some 114)
    (.leaf none)
    (.leaf (some 114)))))
    (.leaf (some 114)))))

def trieNode_44 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    trieNode_41
    (.branch (some 108)
    (.leaf none)
    (.branch (some 109)
    (.leaf none)
    (.leaf (some 109)))))
    (.branch (some 109)
    (.leaf none)
    (.leaf (some 109))))
    (.branch (some 109)
    (.leaf none)
    (.leaf (some 109))))

def trieNode_45 : SlotTrie :=
  (.branch (some 109)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_42)
    (.branch (some 110)
    (.leaf none)
    (.branch (some 111)
    (.leaf none)
    (.leaf (some 111)))))
    (.branch (some 111)
    trieNode_43
    (.branch (some 113)
    (.leaf none)
    (.branch (some 114)
    (.leaf none)
    (.leaf (some 114))))))

def trieNode_46 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_39)
    (.branch (some 102)
    (.leaf none)
    (.branch (some 103)
    (.leaf none)
    (.leaf (some 103)))))
    (.branch (some 103)
    trieNode_40
    (.branch (some 105)
    (.leaf none)
    (.branch (some 106)
    (.leaf none)
    (.leaf (some 106))))))

def trieNode_47 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 115)
    (.branch none
    (.leaf none)
    (.leaf (some 115)))
    (.leaf (some 115))))
    (.branch (some 115)
    (.leaf none)
    (.branch (some 116)
    (.branch none
    (.leaf none)
    (.branch (some 116)
    (.leaf none)
    (.branch (some 117)
    (.leaf none)
    (.leaf (some 117)))))
    (.leaf (some 117)))))

def trieNode_48 : SlotTrie :=
  (.branch (some 118)
    (.leaf none)
    (.branch (some 118)
    (.branch none
    (.leaf none)
    (.leaf (some 119)))
    (.branch (some 119)
    (.branch none
    (.leaf none)
    (.branch (some 120)
    (.leaf none)
    (.leaf (some 120))))
    (.leaf (some 120)))))

def trieNode_49 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 120)
    (.branch none
    (.leaf none)
    (.leaf (some 120)))
    (.leaf (some 120))))
    (.branch (some 120)
    (.leaf none)
    (.branch (some 121)
    (.branch none
    (.leaf none)
    (.branch (some 121)
    (.leaf none)
    (.branch (some 122)
    (.leaf none)
    (.leaf (some 122)))))
    (.leaf (some 122)))))

def trieNode_50 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    trieNode_47
    (.branch (some 116)
    (.leaf none)
    (.branch (some 117)
    (.leaf none)
    (.leaf (some 117)))))
    (.leaf (some 117)))
    (.branch (some 117)
    (.leaf none)
    (.leaf (some 117))))

def trieNode_51 : SlotTrie :=
  (.branch (some 117)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_48)
    (.branch (some 118)
    (.leaf none)
    (.branch (some 119)
    (.leaf none)
    (.leaf (some 119)))))
    (.branch (some 119)
    trieNode_49
    (.branch (some 121)
    (.leaf none)
    (.branch (some 122)
    (.leaf none)
    (.leaf (some 122))))))

def trieNode_52 : SlotTrie :=
  (.branch (some 123)
    (.leaf none)
    (.branch (some 123)
    (.branch none
    (.leaf none)
    (.leaf (some 124)))
    (.branch (some 124)
    (.branch none
    (.leaf none)
    (.branch (some 125)
    (.leaf none)
    (.leaf (some 125))))
    (.leaf (some 125)))))

def trieNode_53 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 125)
    (.branch none
    (.leaf none)
    (.leaf (some 125)))
    (.leaf (some 125))))
    (.branch (some 125)
    (.leaf none)
    (.branch (some 126)
    (.branch none
    (.leaf none)
    (.branch (some 126)
    (.leaf none)
    (.branch (some 127)
    (.leaf none)
    (.leaf (some 127)))))
    (.leaf (some 127)))))

def trieNode_54 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 128)
    (.branch none
    (.leaf none)
    (.leaf (some 128)))
    (.leaf (some 128))))
    (.branch (some 128)
    (.leaf none)
    (.branch (some 129)
    (.branch none
    (.leaf none)
    (.branch (some 129)
    (.leaf none)
    (.branch (some 130)
    (.leaf none)
    (.leaf (some 130)))))
    (.leaf (some 130)))))

def trieNode_55 : SlotTrie :=
  (.branch (some 131)
    (.leaf none)
    (.branch (some 131)
    (.branch none
    (.leaf none)
    (.leaf (some 132)))
    (.branch (some 132)
    (.branch none
    (.leaf none)
    (.branch (some 133)
    (.leaf none)
    (.leaf (some 133))))
    (.leaf (some 133)))))

def trieNode_56 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 133)
    (.branch none
    (.leaf none)
    (.leaf (some 133)))
    (.leaf (some 133))))
    (.branch (some 133)
    (.leaf none)
    (.branch (some 134)
    (.branch none
    (.leaf none)
    (.branch (some 134)
    (.leaf none)
    (.branch (some 135)
    (.leaf none)
    (.leaf (some 135)))))
    (.leaf (some 135)))))

def trieNode_57 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    trieNode_54
    (.branch (some 129)
    (.leaf none)
    (.branch (some 130)
    (.leaf none)
    (.leaf (some 130)))))
    (.branch (some 130)
    (.leaf none)
    (.leaf (some 130))))
    (.branch (some 130)
    (.leaf none)
    (.leaf (some 130))))

def trieNode_58 : SlotTrie :=
  (.branch (some 130)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_55)
    (.branch (some 131)
    (.leaf none)
    (.branch (some 132)
    (.leaf none)
    (.leaf (some 132)))))
    (.branch (some 132)
    trieNode_56
    (.branch (some 134)
    (.leaf none)
    (.branch (some 135)
    (.leaf none)
    (.leaf (some 135))))))

def trieNode_59 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_52)
    (.branch (some 123)
    (.leaf none)
    (.branch (some 124)
    (.leaf none)
    (.leaf (some 124)))))
    (.branch (some 124)
    trieNode_53
    (.branch (some 126)
    (.leaf none)
    (.branch (some 127)
    (.leaf none)
    (.leaf (some 127))))))

def trieNode_60 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 136)
    (.branch none
    (.leaf none)
    (.leaf (some 136)))
    (.leaf (some 136))))
    (.branch (some 136)
    (.leaf none)
    (.branch (some 137)
    (.branch none
    (.leaf none)
    (.branch (some 137)
    (.leaf none)
    (.branch (some 138)
    (.leaf none)
    (.leaf (some 138)))))
    (.leaf (some 138)))))

def trieNode_61 : SlotTrie :=
  (.branch (some 139)
    (.leaf none)
    (.branch (some 139)
    (.branch none
    (.leaf none)
    (.leaf (some 140)))
    (.branch (some 140)
    (.branch none
    (.leaf none)
    (.branch (some 141)
    (.leaf none)
    (.leaf (some 141))))
    (.leaf (some 141)))))

def trieNode_62 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 141)
    (.branch none
    (.leaf none)
    (.leaf (some 141)))
    (.leaf (some 141))))
    (.branch (some 141)
    (.leaf none)
    (.branch (some 142)
    (.branch none
    (.leaf none)
    (.branch (some 142)
    (.leaf none)
    (.branch (some 143)
    (.leaf none)
    (.leaf (some 143)))))
    (.leaf (some 143)))))

def trieNode_63 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    trieNode_60
    (.branch (some 137)
    (.leaf none)
    (.branch (some 138)
    (.leaf none)
    (.leaf (some 138)))))
    (.leaf (some 138)))
    (.branch (some 138)
    (.leaf none)
    (.leaf (some 138))))

def trieNode_64 : SlotTrie :=
  (.branch (some 138)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_61)
    (.branch (some 139)
    (.leaf none)
    (.branch (some 140)
    (.leaf none)
    (.leaf (some 140)))))
    (.branch (some 140)
    trieNode_62
    (.branch (some 142)
    (.leaf none)
    (.branch (some 143)
    (.leaf none)
    (.leaf (some 143))))))

def trieNode_65 : SlotTrie :=
  (.branch (some 114)
    (.branch none
    trieNode_50
    trieNode_51)
    (.branch (some 122)
    (.branch none
    trieNode_59
    (.branch (some 127)
    trieNode_57
    trieNode_58))
    (.branch (some 135)
    trieNode_63
    trieNode_64)))

def trieNode_66 : SlotTrie :=
  (.branch (some 144)
    (.leaf none)
    (.branch (some 144)
    (.branch none
    (.leaf none)
    (.leaf (some 145)))
    (.branch (some 145)
    (.branch none
    (.leaf none)
    (.branch (some 146)
    (.leaf none)
    (.leaf (some 146))))
    (.leaf (some 146)))))

def trieNode_67 : SlotTrie :=
  (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 146)
    (.branch none
    (.leaf none)
    (.leaf (some 146)))
    (.leaf (some 146))))
    (.branch (some 146)
    (.leaf none)
    (.branch (some 147)
    (.branch none
    (.leaf none)
    (.branch (some 147)
    (.leaf none)
    (.branch (some 148)
    (.leaf none)
    (.leaf (some 148)))))
    (.leaf (some 148)))))

def trieNode_68 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    (.branch none
    (.leaf none)
    (.branch (some 149)
    (.branch none
    (.leaf none)
    (.leaf (some 149)))
    (.leaf (some 149))))
    (.leaf (some 149)))
    (.leaf none))
    (.leaf none))

def trieNode_69 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_66)
    (.branch (some 144)
    (.leaf none)
    (.branch (some 145)
    (.leaf none)
    (.leaf (some 145)))))
    (.branch (some 145)
    trieNode_67
    (.branch (some 147)
    (.leaf none)
    (.branch (some 148)
    (.leaf none)
    (.leaf (some 148))))))

def trieNode_70 : SlotTrie :=
  (.branch (some 101)
    (.branch none
    (.branch none
    trieNode_46
    (.branch (some 106)
    trieNode_44
    trieNode_45))
    trieNode_65)
    (.branch (some 143)
    (.branch none
    trieNode_69
    (.branch (some 148)
    (.branch none
    trieNode_68
    (.leaf none))
    (.leaf none)))
    (.leaf none)))

def trieNode_71 : SlotTrie :=
  (.branch (some 72)
    (.branch none
    (.branch none
    (.branch none
    trieNode_22
    (.branch (some 74)
    (.leaf none)
    (.branch (some 75)
    (.leaf none)
    (.leaf (some 75)))))
    (.leaf (some 75)))
    trieNode_38)
    trieNode_70)

def trieNode_72 : SlotTrie :=
  (.branch (some 69)
    (.branch none
    (.branch none
    trieNode_21
    (.branch (some 71)
    (.leaf none)
    (.branch (some 72)
    (.leaf none)
    (.leaf (some 72)))))
    (.branch (some 72)
    (.leaf none)
    (.leaf (some 72))))
    trieNode_71)

def trieNode_73 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    trieNode_7
    (.branch (some 44)
    (.leaf none)
    (.branch (some 45)
    (.leaf none)
    (.leaf (some 45)))))
    (.leaf (some 45)))
    (.branch (some 45)
    (.branch none
    trieNode_8
    (.branch (some 47)
    (.leaf none)
    (.branch (some 48)
    (.leaf none)
    (.leaf (some 48)))))
    (.branch (some 48)
    (.leaf none)
    (.leaf (some 48)))))

def trieNode_74 : SlotTrie :=
  (.branch (some 48)
    (.branch none
    (.branch none
    (.branch none
    trieNode_9
    (.branch (some 50)
    (.leaf none)
    (.branch (some 51)
    (.leaf none)
    (.leaf (some 51)))))
    (.leaf (some 51)))
    trieNode_20)
    trieNode_72)

def trieNode_75 : SlotTrie :=
  (.branch none
    (.branch none
    (.branch none
    trieNode_6
    (.branch (some 41)
    (.leaf none)
    (.branch (some 42)
    (.leaf none)
    (.leaf (some 42)))))
    (.leaf (some 42)))
    (.branch (some 42)
    (.leaf none)
    (.leaf (some 42))))

def trieNode_76 : SlotTrie :=
  (.branch (some 36)
    (.branch none
    trieNode_5
    (.branch (some 38)
    (.leaf none)
    (.branch (some 39)
    (.leaf none)
    (.leaf (some 39)))))
    (.branch (some 39)
    trieNode_75
    (.branch (some 42)
    trieNode_73
    trieNode_74)))

def trieNode_77 : SlotTrie :=
  (.branch (some 33)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_4)
    (.branch (some 34)
    (.leaf none)
    (.branch (some 35)
    (.leaf none)
    (.leaf (some 35)))))
    (.branch (some 35)
    (.branch none
    (.leaf none)
    (.branch (some 36)
    (.leaf none)
    (.leaf (some 36))))
    trieNode_76))

def trieNode_78 : SlotTrie :=
  (.branch (some 30)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_3)
    (.branch (some 31)
    (.leaf none)
    (.branch (some 32)
    (.leaf none)
    (.leaf (some 32)))))
    (.branch (some 32)
    (.branch none
    (.leaf none)
    (.branch (some 33)
    (.leaf none)
    (.leaf (some 33))))
    trieNode_77))

def trieNode_79 : SlotTrie :=
  (.branch (some 27)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_2)
    (.branch (some 28)
    (.leaf none)
    (.branch (some 29)
    (.leaf none)
    (.leaf (some 29)))))
    (.branch (some 29)
    (.branch none
    (.leaf none)
    (.branch (some 30)
    (.leaf none)
    (.leaf (some 30))))
    trieNode_78))

def trieNode_80 : SlotTrie :=
  (.branch (some 24)
    (.branch none
    (.branch none
    (.leaf none)
    trieNode_1)
    (.branch (some 25)
    (.leaf none)
    (.branch (some 26)
    (.leaf none)
    (.leaf (some 26)))))
    (.branch (some 26)
    (.branch none
    (.leaf none)
    (.branch (some 27)
    (.leaf none)
    (.leaf (some 27))))
    trieNode_79))

def trieNode_81 : SlotTrie :=
  (.branch (some 21)
    (.branch none
    (.leaf none)
    (.leaf (some 22)))
    (.branch (some 22)
    (.branch none
    (.leaf none)
    (.leaf (some 23)))
    (.branch (some 23)
    (.branch none
    (.leaf none)
    (.leaf (some 24)))
    trieNode_80)))

def smallTrie : SlotTrie :=
  (.branch (some 19)
    (.branch none
    (.branch none
    (.leaf none)
    (.leaf (some 20)))
    trieNode_0)
    (.branch (some 20)
    (.branch none
    (.leaf none)
    (.leaf (some 21)))
    trieNode_81))

def lookupSmall (ip : List (Fin 2)) : Option ℕ :=
  smallTrie.get ip

def minSlot (ip : List (Fin 2)) : ℕ :=
  (lookupSmall ip).getD 150


/-- Trail-zero count at the start of `rev` (number of trailing `0`s at the end of `walked`). -/
def trailZeros : List (Fin 2) → ℕ
  | 0 :: xs => trailZeros xs + 1
  | _ => 0

theorem scanZerosOk_of_trailZeros (rev : List (Fin 2)) (hok : scanZerosOk 0 (rev ++ [1]) = true)
    (b : Fin 2) (htz : b = 0 → trailZeros rev ≤ 8) :
    scanZerosOk 0 ((b :: rev) ++ [1]) = true := by
  rcases fin2_cases b with rfl | rfl
  · have h8 : trailZeros rev ≤ 8 := htz rfl
    have aux : ∀ z xs, z ≤ 8 → trailZeros xs ≤ 8 - z →
        scanZerosOk 0 (xs ++ [1]) = true → scanZerosOk (z + 1) (xs ++ [1]) = true := by
      intro z xs hz htr h0
      induction xs generalizing z with
      | nil => rfl
      | cons a rest ih =>
        rcases fin2_cases a with rfl | rfl
        · have htr' : trailZeros rest + 1 ≤ 8 - z := htr
          have hlt : ¬ (9 ≤ z + 1) := by omega
          simp only [List.cons_append, scanZerosOk, hlt, ↓reduceIte]
          exact ih (z + 1) (by omega) (by omega) (scanZerosOk_tail h0)
        · exact scanZerosOk_tail h0
    exact aux 0 rev (by decide) (by omega) hok
  · exact hok

/-- True iff every bit in `p` steps `.right` with `w == b` to a non-leaf state. -/
def staysInDag : Fin 393 → List (Fin 2) → Bool
  | _, [] => true
  | q, b :: xs =>
    match zf393Trans q b with
    | some (w, .right, q') => (w == b) && (!isLeafState q') && staysInDag q' xs
    | _ => false

theorem staysInDag_prefix (q : Fin 393) {p w : List (Fin 2)}
    (hpw : p <+: w) (hw : staysInDag q w = true) :
    staysInDag q p = true := by
  induction p generalizing q w with
  | nil => rfl
  | cons b ps ih =>
    rcases w with _ | ⟨b', ws⟩
    · obtain ⟨t, ht⟩ := hpw; cases ht
    · obtain ⟨t, ht⟩ := hpw
      injection ht with hb hps
      subst hb
      simp only [staysInDag] at hw ⊢
      rcases htr : zf393Trans q b with _ | ⟨w0, d, q'⟩
      · rw [htr] at hw; cases hw
      · rw [htr] at hw
        cases d with
        | left => cases hw
        | right =>
          simp only [Bool.and_eq_true] at hw ⊢
          exact ⟨hw.1, ih q' ⟨t, hps⟩ hw.2⟩

theorem walkTape_staysInDag (q : Fin 393) (walked p rest : List (Fin 2))
    (hp : staysInDag q p = true) :
    ∃ q', walkTape q walked (p ++ rest) = walkTape q' (walked ++ p) rest := by
  induction p generalizing q walked with
  | nil => exact ⟨q, by simp⟩
  | cons b ps ih =>
    simp only [staysInDag] at hp
    rcases htr : zf393Trans q b with _ | ⟨w, d, q₁⟩
    · rw [htr] at hp; cases hp
    · rw [htr] at hp
      cases d with
      | left => cases hp
      | right =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
        have hwb : w = b := beq_iff_eq.mp hp.1.1
        subst hwb
        simp only [List.cons_append, walkTape, htr, beq_self_eq_true, hp.1.2,
          Bool.false_eq_true, ↓reduceIte]
        obtain ⟨q', hq'⟩ := ih q₁ (walked ++ [w]) hp.2
        refine ⟨q', ?_⟩
        rw [hq', List.append_assoc]
        rfl

theorem walkTape_zeros_tail (q : Fin 393) (walked : List (Fin 2)) (n : ℕ) :
    match walkTape q walked (List.replicate n 0) with
    | .outOfFuel => True
    | .halt _ _ _ => True
    | .jumpLeft _ w_j r_j =>
      r_j = List.replicate (walked.length + n - (w_j.length + 1)) 0
    | .regLeaf _ w_l r_l =>
      r_l = List.replicate (walked.length + n - w_l.length) 0 := by
  induction n generalizing q walked with
  | zero => simp [walkTape]
  | succ m ih =>
    simp only [List.replicate_succ, walkTape]
    rcases zf393Trans q 0 with _ | ⟨w, d, q'⟩
    · trivial
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp only [hw, ↓reduceIte]; simp; omega
        · simp [hw]
      | right =>
        by_cases hw : (w == 0) = true
        · simp only [hw, ↓reduceIte]
          by_cases hleaf : isLeafState q' = true
          · simp only [hleaf, ↓reduceIte]; simp; omega
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            have h := ih q' (walked ++ [w])
            have hlen : (walked ++ [w]).length + m = walked.length + (m + 1) := by
              simp; omega
            rw [hlen] at h
            exact h
        · simp [hw]

theorem walkTape_slot_tail {slot : ℕ} {ip : List (Fin 2)}
    (hsl : ip.length ≤ slot) (hdag : staysInDag 99 ip.dropLast = true) :
    match walkTape 99 [] (ip ++ List.replicate (slot - ip.length) 0) with
    | .outOfFuel => True
    | .halt _ _ _ => True
    | .jumpLeft _ w_j r_j =>
      r_j = List.replicate (slot - (w_j.length + 1)) 0
    | .regLeaf _ w_l r_l =>
      r_l = List.replicate (slot - w_l.length) 0 := by
  by_cases hnil : ip = []
  · subst hnil
    have h := walkTape_zeros_tail 99 [] slot
    simpa using h
  · have hsplit : ip ++ List.replicate (slot - ip.length) 0 =
        ip.dropLast ++ ([ip.getLast hnil] ++ List.replicate (slot - ip.length) 0) := by
      rw [← List.append_assoc, List.dropLast_append_getLast]
    rw [hsplit]
    obtain ⟨q₁, hq₁⟩ := walkTape_staysInDag 99 [] ip.dropLast _ hdag
    rw [hq₁, List.nil_append]
    have hlen_dl : ip.dropLast.length + 1 = ip.length := by
      have := List.length_dropLast (xs := ip)
      have hpos : 1 ≤ ip.length := List.length_pos_of_ne_nil hnil
      omega
    simp only [List.singleton_append, walkTape]
    rcases zf393Trans q₁ (ip.getLast hnil) with _ | ⟨w, d, q₂⟩
    · trivial
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp only [hw, ↓reduceIte, hlen_dl]
        · simp [hw]
      | right =>
        by_cases hw : (w == ip.getLast hnil) = true
        · simp only [hw, ↓reduceIte]
          by_cases hleaf : isLeafState q₂ = true
          · simp only [hleaf, ↓reduceIte, List.length_append, List.length_singleton, hlen_dl]
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            have h := walkTape_zeros_tail q₂ (ip.dropLast ++ [w]) (slot - ip.length)
            have htot : (ip.dropLast ++ [w]).length + (slot - ip.length) = slot := by
              rw [List.length_append, List.length_singleton, hlen_dl]; omega
            rw [htot] at h
            exact h
        · simp [hw]

theorem popBreakRev_suffix_one (k : ℕ) (rev : List (Fin 2)) :
    popBreakRev k rev = [] ∨ ∃ t, popBreakRev k rev = 1 :: t ∧ t <:+ rev.tail := by
  induction rev generalizing k with
  | nil => exact Or.inl rfl
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => exact Or.inr ⟨xs, rfl, List.suffix_refl xs⟩
      | succ k' =>
        rcases ih k' with hnil | ⟨t, ht, hsuf⟩
        · exact Or.inl hnil
        · exact Or.inr ⟨t, ht, hsuf.trans xs.tail_suffix⟩
    · rcases ih k with hnil | ⟨t, ht, hsuf⟩
      · exact Or.inl hnil
      · exact Or.inr ⟨t, ht, hsuf.trans xs.tail_suffix⟩

theorem popBreakRev_dropLast_prefix (k : ℕ) (w : List (Fin 2)) :
    (popBreakRev k w.reverse).reverse.dropLast <+: w.dropLast := by
  rcases popBreakRev_suffix_one k w.reverse with hnil | ⟨t, ht, hsuf⟩
  · simp [hnil]
  · have hdl : (popBreakRev k w.reverse).reverse.dropLast = t.reverse := by
      rw [ht, List.reverse_cons, List.dropLast_concat]
    rw [hdl]
    have hw_dl : w.dropLast = w.reverse.tail.reverse := by
      rcases w.eq_nil_or_concat with rfl | ⟨w', x, rfl⟩
      · rfl
      · simp
    rw [hw_dl]
    obtain ⟨u, hu⟩ := hsuf
    refine ⟨u.reverse, ?_⟩
    rw [← List.reverse_append, hu]

theorem popContinueRev_suffix (k : ℕ) (rev : List (Fin 2)) :
    popContinueRev k rev <:+ rev := by
  induction rev generalizing k with
  | nil => exact List.suffix_refl []
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · exact (ih k).trans (List.suffix_cons 0 xs)
    · cases k with
      | zero => exact List.suffix_refl (1 :: xs)
      | succ k' => exact (ih k').trans (List.suffix_cons 1 xs)

theorem popContinueRev_prefix (k : ℕ) (w : List (Fin 2)) :
    (popContinueRev k w.reverse).reverse <+: w := by
  obtain ⟨u, hu⟩ := popContinueRev_suffix k w.reverse
  refine ⟨u.reverse, ?_⟩
  rw [← List.reverse_append, hu, List.reverse_reverse]

theorem staysInDag_of_walkTape (q : Fin 393) (walked rem : List (Fin 2)) :
    match walkTape q walked rem with
    | .outOfFuel => True
    | .halt _ _ _ => True
    | .jumpLeft _ w_j _ =>
      ∃ u, w_j = walked ++ u ∧ staysInDag q u = true
    | .regLeaf _ w_l _ =>
      ∃ u, w_l = walked ++ u ∧ staysInDag q u.dropLast = true := by
  induction rem generalizing q walked with
  | nil => simp [walkTape]
  | cons b rem' ih =>
    simp only [walkTape]
    rcases htr : zf393Trans q b with _ | ⟨w, d, q'⟩
    · trivial
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp only [hw, ↓reduceIte]
          exact ⟨[], by simp, rfl⟩
        · simp [hw]
      | right =>
        by_cases hwb : (w == b) = true
        · simp only [hwb, ↓reduceIte]
          have hwb_eq : w = b := beq_iff_eq.mp hwb
          subst hwb_eq
          by_cases hleaf : isLeafState q' = true
          · simp only [hleaf, ↓reduceIte]
            exact ⟨[w], rfl, rfl⟩
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            have h := ih q' (walked ++ [w])
            have hnot_leaf : (!isLeafState q') = true := by simpa using hleaf
            rcases hout : walkTape q' (walked ++ [w]) rem' with
              ⟨_, _, _⟩ | ⟨_, w_j, _⟩ | ⟨_, w_l, _⟩ | _
            · trivial
            · rw [hout] at h
              obtain ⟨u, rfl, hu⟩ := h
              refine ⟨w :: u, by simp, ?_⟩
              simp [staysInDag, htr, hnot_leaf, hu]
            · rw [hout] at h
              obtain ⟨u, rfl, hu⟩ := h
              refine ⟨w :: u, by simp, ?_⟩
              cases u with
              | nil => rfl
              | cons u0 us =>
                simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil u0 us),
                  staysInDag, htr, beq_self_eq_true, hnot_leaf, Bool.and_self, Bool.true_and]
                exact hu
            · trivial
        · simp [hwb]

/-- Local edge invariant checker on every reachable state `q` of the 324-node DAG (`69 ≤ q.val`). -/
def checkDagEdge (q : Fin 393) (b : Fin 2) : Bool :=
  let (tz, ones, ln, fwd) := dagInfo q
  if tz > 8 then true
  else
    (1 ≤ fwd) && (fwd ≤ 9) &&
    match zf393Trans q b with
    | none => ln ≤ 135
    | some (w, .right, q') =>
      let ntz := if w == 1 then 0 else tz + 1
      let nones := ones + (if w == 1 then 1 else 0)
      (w == b) &&
      if 69 ≤ q'.val then
        let (tz', ones', ln', fwd') := dagInfo q'
        (tz' ≤ 8) && (ntz ≤ tz') && (ones' ≤ nones) && (ln + 1 ≤ ln') && (ln' ≤ 135) &&
        (1 ≤ fwd') && (fwd' ≤ 9) && (if b == 0 then fwd' + 1 ≤ fwd else true)
      else
        isLeafState q' && (ntz ≤ 9) && (ln + 1 ≤ 136)
    | some (w, .left, q') =>
      (w == 0) && (ln ≤ 135) &&
      match q'.val with
      | 61 | 62 | 63 => true
      | 64 => true
      | 65 => 1 ≤ ones
      | 66 => 2 ≤ ones
      | 67 => 3 ≤ ones
      | 68 => 4 ≤ ones
      | _ => false

set_option maxHeartbeats 0 in
-- Finite exhaustive check over all 393 states and 2 tape symbols
theorem checkDagEdge_ok (q : Fin 393) (b : Fin 2) :
    checkDagEdge q b = true := by
  revert q b; decide

/-- Termination & invariant preservation of `walkTape q walked (List.replicate k 0)`
from any DAG node `q` (`(dagInfo q).1 ≤ 8` and `(dagInfo q).2.2.2 ≤ k`). -/
theorem walkTape_zeros_props (q : Fin 393) (walked : List (Fin 2)) (k : ℕ)
    (hq : (dagInfo q).1 ≤ 8)
    (hfwd : (dagInfo q).2.2.2 ≤ k)
    (htz : trailZeros walked.reverse ≤ (dagInfo q).1)
    (hones : (dagInfo q).2.1 ≤ walked.count 1)
    (hlen : walked.length ≤ (dagInfo q).2.2.1)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true) :
    match walkTape q walked (List.replicate k 0) with
    | .outOfFuel => False
    | .halt _ w_h _ => w_h.length ≤ 135
    | .jumpLeft q' w_j _ =>
      w_j.length ≤ 135 ∧ scanZerosOk 0 (w_j.reverse ++ [1]) = true ∧
      ((q'.val = 61 ∨ q'.val = 62 ∨ q'.val = 63) ∨
       (q'.val = 64 ∧ 0 ≤ w_j.count 1) ∨
       (q'.val = 65 ∧ 1 ≤ w_j.count 1) ∨
       (q'.val = 66 ∧ 2 ≤ w_j.count 1) ∨
       (q'.val = 67 ∧ 3 ≤ w_j.count 1) ∨
       (q'.val = 68 ∧ 4 ≤ w_j.count 1))
    | .regLeaf q' w_l _ =>
      isLeafState q' = true ∧ w_l.length ≤ 136 ∧
      scanZerosOk 0 (w_l.reverse ++ [1]) = true := by
  induction k generalizing q walked with
  | zero =>
    have hedge := checkDagEdge_ok q 0
    dsimp only [checkDagEdge] at hedge
    have htz_f : ¬ ((dagInfo q).1 > 8) := by omega
    simp only [htz_f, ↓reduceIte, Bool.and_eq_true] at hedge
    have h1 : 1 ≤ (dagInfo q).2.2.2 := of_decide_eq_true hedge.1.1
    omega
  | succ k' ih =>
    have hedge := checkDagEdge_ok q 0
    dsimp only [checkDagEdge] at hedge
    have htz_f : ¬ ((dagInfo q).1 > 8) := by omega
    simp only [htz_f, ↓reduceIte, Bool.and_eq_true] at hedge
    have hedge2 := hedge.2
    simp only [List.replicate_succ, walkTape]
    rcases htr : zf393Trans q 0 with _ | ⟨w, d, q'⟩
    · rw [htr] at hedge2
      have hln : (dagInfo q).2.2.1 ≤ 135 := of_decide_eq_true hedge2
      omega
    · rw [htr] at hedge2
      cases d with
      | left =>
        simp only [Bool.and_eq_true] at hedge2
        simp only [hedge2.1.1, ↓reduceIte]
        have hln : (dagInfo q).2.2.1 ≤ 135 := of_decide_eq_true hedge2.1.2
        refine ⟨by omega, hok, ?_⟩
        revert hedge2
        generalize q'.val = n
        match n with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
        | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29
        | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 | 43
        | 44 | 45 | 46 | 47 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57
        | 58 | 59 | 60 => intro h; cases h.2
        | 61 => intro _; exact Or.inl (Or.inl rfl)
        | 62 => intro _; exact Or.inl (Or.inr (Or.inl rfl))
        | 63 => intro _; exact Or.inl (Or.inr (Or.inr rfl))
        | 64 => intro _; exact Or.inr (Or.inl ⟨rfl, Nat.zero_le _⟩)
        | 65 =>
          intro h; exact Or.inr (Or.inr (Or.inl ⟨rfl, le_trans (of_decide_eq_true h.2) hones⟩))
        | 66 =>
          intro h
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, le_trans (of_decide_eq_true h.2) hones⟩)))
        | 67 =>
          intro h
          exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨rfl, le_trans (of_decide_eq_true h.2) hones⟩))))
        | 68 =>
          intro h
          exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr ⟨rfl, le_trans (of_decide_eq_true h.2) hones⟩))))
        | _ + 69 => intro h; cases h.2
      | right =>
        simp only [Bool.and_eq_true] at hedge2
        simp only [hedge2.1, ↓reduceIte]
        have hwb : w = 0 := beq_iff_eq.mp hedge2.1
        subst hwb
        have hok' : scanZerosOk 0 ((walked ++ [0]).reverse ++ [1]) = true := by
          rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
          exact scanZerosOk_of_trailZeros walked.reverse hok 0 (fun _ => by omega)
        by_cases h69 : 69 ≤ q'.val
        · simp only [h69, ↓reduceIte, Bool.and_eq_true, beq_self_eq_true] at hedge2
          have hleaf_f : isLeafState q' = false := by
            unfold isLeafState; simp; omega
          simp only [hleaf_f, Bool.false_eq_true, ↓reduceIte]
          have hnt : (dagInfo q).1 + 1 ≤ (dagInfo q').1 :=
            of_decide_eq_true hedge2.2.1.1.1.1.1.1.2
          have htz' : trailZeros (walked ++ [0]).reverse ≤ (dagInfo q').1 := by
            rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
            simp only [trailZeros]; omega
          have hones' : (dagInfo q').2.1 ≤ (walked ++ [0]).count 1 := by
            rw [List.count_append]
            have hno : (dagInfo q').2.1 ≤ (dagInfo q).2.1 :=
              of_decide_eq_true hedge2.2.1.1.1.1.1.2
            simp; omega
          have hlen' : (walked ++ [0]).length ≤ (dagInfo q').2.2.1 := by
            have hl1 : (dagInfo q).2.2.1 + 1 ≤ (dagInfo q').2.2.1 :=
              of_decide_eq_true hedge2.2.1.1.1.1.2
            simp; omega
          have hfwd' : (dagInfo q').2.2.2 + 1 ≤ (dagInfo q).2.2.2 :=
            of_decide_eq_true hedge2.2.2
          exact ih q' (walked ++ [0]) (of_decide_eq_true hedge2.2.1.1.1.1.1.1.1)
            (by omega) htz' hones' hlen' hok'
        · simp only [h69, ↓reduceIte, Bool.and_eq_true] at hedge2
          rw [hedge2.2.1.1]; simp only [↓reduceIte]
          have hl1 : (dagInfo q).2.2.1 + 1 ≤ 136 := of_decide_eq_true hedge2.2.2
          exact ⟨hedge2.2.1.1, by simp; omega, hok'⟩

/-- Universal property of `walkTape q walked (ip ++ List.replicate 10 0)` starting from any
DAG node `q` (`(dagInfo q).1 ≤ 8`). -/
theorem walkTape_dag_props (q : Fin 393) (walked ip : List (Fin 2))
    (hq : (dagInfo q).1 ≤ 8)
    (htz : trailZeros walked.reverse ≤ (dagInfo q).1)
    (hones : (dagInfo q).2.1 ≤ walked.count 1)
    (hlen : walked.length ≤ (dagInfo q).2.2.1)
    (hok : scanZerosOk 0 (walked.reverse ++ [1]) = true) :
    match walkTape q walked (ip ++ List.replicate 10 0) with
    | .outOfFuel => False
    | .halt _ w_h _ => w_h.length ≤ 135
    | .jumpLeft q' w_j _ =>
      w_j.length ≤ 135 ∧ scanZerosOk 0 (w_j.reverse ++ [1]) = true ∧
      ((q'.val = 61 ∨ q'.val = 62 ∨ q'.val = 63) ∨
       (q'.val = 64 ∧ 0 ≤ w_j.count 1) ∨
       (q'.val = 65 ∧ 1 ≤ w_j.count 1) ∨
       (q'.val = 66 ∧ 2 ≤ w_j.count 1) ∨
       (q'.val = 67 ∧ 3 ≤ w_j.count 1) ∨
       (q'.val = 68 ∧ 4 ≤ w_j.count 1))
    | .regLeaf q' w_l _ =>
      isLeafState q' = true ∧ w_l.length ≤ 136 ∧
      scanZerosOk 0 (w_l.reverse ++ [1]) = true := by
  induction ip generalizing q walked with
  | nil =>
    have hedge := checkDagEdge_ok q 0
    dsimp only [checkDagEdge] at hedge
    have htz_f : ¬ ((dagInfo q).1 > 8) := by omega
    simp only [htz_f, ↓reduceIte, Bool.and_eq_true] at hedge
    have hfwd9 : (dagInfo q).2.2.2 ≤ 9 := of_decide_eq_true hedge.1.2
    exact walkTape_zeros_props q walked 10 hq (by omega) htz hones hlen hok
  | cons b ip' ih =>
    have hedge := checkDagEdge_ok q b
    dsimp only [checkDagEdge] at hedge
    have htz_f : ¬ ((dagInfo q).1 > 8) := by omega
    simp only [htz_f, ↓reduceIte, Bool.and_eq_true] at hedge
    have hedge2 := hedge.2
    simp only [List.cons_append, walkTape]
    rcases htr : zf393Trans q b with _ | ⟨w, d, q'⟩
    · rw [htr] at hedge2
      have hln : (dagInfo q).2.2.1 ≤ 135 := of_decide_eq_true hedge2
      omega
    · rw [htr] at hedge2
      cases d with
      | left =>
        simp only [Bool.and_eq_true] at hedge2
        simp only [hedge2.1.1, ↓reduceIte]
        have hln : (dagInfo q).2.2.1 ≤ 135 := of_decide_eq_true hedge2.1.2
        refine ⟨by omega, hok, ?_⟩
        revert hedge2
        generalize q'.val = n
        match n with
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
        | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29
        | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 | 43
        | 44 | 45 | 46 | 47 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57
        | 58 | 59 | 60 => intro h; cases h.2
        | 61 => intro _; exact Or.inl (Or.inl rfl)
        | 62 => intro _; exact Or.inl (Or.inr (Or.inl rfl))
        | 63 => intro _; exact Or.inl (Or.inr (Or.inr rfl))
        | 64 => intro _; exact Or.inr (Or.inl ⟨rfl, Nat.zero_le _⟩)
        | 65 =>
          intro h; exact Or.inr (Or.inr (Or.inl ⟨rfl, le_trans (of_decide_eq_true h.2) hones⟩))
        | 66 =>
          intro h
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, le_trans (of_decide_eq_true h.2) hones⟩)))
        | 67 =>
          intro h
          exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨rfl, le_trans (of_decide_eq_true h.2) hones⟩))))
        | 68 =>
          intro h
          exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr ⟨rfl, le_trans (of_decide_eq_true h.2) hones⟩))))
        | _ + 69 => intro h; cases h.2
      | right =>
        simp only [Bool.and_eq_true] at hedge2
        simp only [hedge2.1, ↓reduceIte]
        have hwb : w = b := beq_iff_eq.mp hedge2.1
        subst hwb
        have hok' : scanZerosOk 0 ((walked ++ [w]).reverse ++ [1]) = true := by
          rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
          exact scanZerosOk_of_trailZeros walked.reverse hok w (fun _ => by omega)
        by_cases h69 : 69 ≤ q'.val
        · simp only [h69, ↓reduceIte, Bool.and_eq_true] at hedge2
          have hleaf_f : isLeafState q' = false := by
            unfold isLeafState; simp; omega
          simp only [hleaf_f, Bool.false_eq_true, ↓reduceIte]
          have hnt : (if w == 1 then 0 else (dagInfo q).1 + 1) ≤ (dagInfo q').1 :=
            of_decide_eq_true hedge2.2.1.1.1.1.1.1.2
          have htz' : trailZeros (walked ++ [w]).reverse ≤ (dagInfo q').1 := by
            rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
            rcases fin2_cases w with rfl | rfl
            · simp only [trailZeros]; simp at hnt; omega
            · simp only [trailZeros]; omega
          have hones' : (dagInfo q').2.1 ≤ (walked ++ [w]).count 1 := by
            rw [List.count_append]
            have hno : (dagInfo q').2.1 ≤ (dagInfo q).2.1 + (if w == 1 then 1 else 0) :=
              of_decide_eq_true hedge2.2.1.1.1.1.1.2
            rcases fin2_cases w with rfl | rfl <;> simp at hno ⊢ <;> omega
          have hlen' : (walked ++ [w]).length ≤ (dagInfo q').2.2.1 := by
            have hl1 : (dagInfo q).2.2.1 + 1 ≤ (dagInfo q').2.2.1 :=
              of_decide_eq_true hedge2.2.1.1.1.1.2
            simp; omega
          exact ih q' (walked ++ [w]) (of_decide_eq_true hedge2.2.1.1.1.1.1.1.1)
            htz' hones' hlen' hok'
        · simp only [h69, ↓reduceIte, Bool.and_eq_true] at hedge2
          rw [hedge2.2.1.1]; simp only [↓reduceIte]
          have hl1 : (dagInfo q).2.2.1 + 1 ≤ 136 := of_decide_eq_true hedge2.2.2
          exact ⟨hedge2.2.1.1, by simp; omega, hok'⟩

theorem walkTape_extend_zeros (q : Fin 393) (walked rem : List (Fin 2)) (n : ℕ) :
    match walkTape q walked rem with
    | .outOfFuel => True
    | .halt q_h w_h r_h =>
      walkTape q walked (rem ++ List.replicate n 0) =
        .halt q_h w_h (r_h ++ List.replicate n 0)
    | .jumpLeft q' w_j r_j =>
      walkTape q walked (rem ++ List.replicate n 0) =
        .jumpLeft q' w_j (r_j ++ List.replicate n 0)
    | .regLeaf q' w_l r_l =>
      walkTape q walked (rem ++ List.replicate n 0) =
        .regLeaf q' w_l (r_l ++ List.replicate n 0) := by
  induction rem generalizing q walked with
  | nil => trivial
  | cons b rem' ih =>
    simp only [List.cons_append, walkTape]
    rcases zf393Trans q b with _ | ⟨w, d, q'⟩
    · rfl
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp [hw]
        · simp [hw]
      | right =>
        by_cases hw : (w == b) = true
        · simp only [hw, ↓reduceIte]
          by_cases hleaf : isLeafState q' = true
          · simp [hleaf]
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            exact ih q' (walked ++ [w])
        · simp [hw]

theorem walkTape_self_on_regLeaf (q : Fin 393) (walked rem : List (Fin 2)) (q' : Fin 393)
    (w_l r_l : List (Fin 2))
    (h : walkTape q walked rem = .regLeaf q' (walked ++ w_l) r_l) :
    walkTape q walked w_l = .regLeaf q' (walked ++ w_l) [] := by
  induction rem generalizing q walked w_l with
  | nil => simp [walkTape] at h
  | cons b rem' ih =>
    simp only [walkTape] at h
    rcases htr : zf393Trans q b with _ | ⟨w, d, q_next⟩
    · rw [htr] at h; cases h
    · rw [htr] at h
      cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp [hw] at h
        · simp [hw] at h
      | right =>
        by_cases hwb : (w == b) = true
        · simp only [hwb, ↓reduceIte] at h
          have hwb_eq : w = b := beq_iff_eq.mp hwb
          subst hwb_eq
          by_cases hleaf : isLeafState q_next = true
          · simp only [hleaf, ↓reduceIte] at h
            injection h with hq hwl hrl
            have hw_singleton : w_l = [w] := by
              have happ : walked ++ [w] = walked ++ w_l := hwl
              exact (List.append_cancel_left happ).symm
            subst hw_singleton hq
            simp [walkTape, htr, hleaf]
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte] at h
            have hprefix : ∀ q₀ w₀ r₀ q₁ w₁ r₁,
                walkTape q₀ w₀ r₀ = .regLeaf q₁ w₁ r₁ →
                  w₀.length < w₁.length ∧ w₁.take w₀.length = w₀ := by
              intro q₀ w₀ r₀
              induction r₀ generalizing q₀ w₀ with
              | nil => intro _ _ _ hx; simp [walkTape] at hx
              | cons x xs ihx =>
                intro q₁ w₁ r₁ hx
                simp only [walkTape] at hx
                rcases htrx : zf393Trans q₀ x with _ | ⟨wx, dx, qx⟩
                · rw [htrx] at hx; cases hx
                · rw [htrx] at hx
                  cases dx with
                  | left =>
                    by_cases hwx : (wx == 0) = true
                    · simp only [hwx, ↓reduceIte] at hx; cases hx
                    · simp only [hwx, Bool.false_eq_true, ↓reduceIte] at hx; cases hx
                  | right =>
                    by_cases hwx : (wx == x) = true
                    · simp only [hwx, ↓reduceIte] at hx
                      by_cases hlx : isLeafState qx = true
                      · simp only [hlx, ↓reduceIte] at hx
                        injection hx with _ hwx_eq _
                        exact ⟨by rw [← hwx_eq]; simp, by rw [← hwx_eq, List.take_left]⟩
                      · simp only [hlx, Bool.false_eq_true, ↓reduceIte] at hx
                        obtain ⟨hlt1, htk1⟩ := ihx qx (w₀ ++ [wx]) q₁ w₁ r₁ hx
                        refine ⟨by simp at hlt1; omega, ?_⟩
                        have h1 := congrArg (List.take w₀.length) htk1
                        rw [List.take_take, Nat.min_eq_left (by simp), List.take_left] at h1
                        exact h1
                    · simp only [hwx, Bool.false_eq_true, ↓reduceIte] at hx; cases hx
            obtain ⟨hlt, htk⟩ := hprefix q_next (walked ++ [w]) rem' q' (walked ++ w_l) r_l h
            cases w_l with
            | nil => simp at hlt
            | cons b0 ws =>
              have hcons : walked ++ (b0 :: ws) = (walked ++ [b0]) ++ ws := by simp
              have hlen_eq : (walked ++ [w]).length = (walked ++ [b0]).length := by simp
              rw [hcons, hlen_eq, List.take_left] at htk
              have hb0 : w = b0 := (List.cons.inj (List.append_cancel_left htk).symm).1
              subst hb0
              simp only [walkTape, htr, hwb, hleaf, Bool.false_eq_true, ↓reduceIte]
              rw [hcons] at h ⊢
              exact ih q_next (walked ++ [w]) ws h
        · simp [hwb] at h

/-- Fast tail-recursive DAG walker accumulating `revWalked` in `O(1)` per step. -/
def fastWalk (q : Fin 393) (revWalked : List (Fin 2)) : List (Fin 2) → TreeOutcome
  | [] => .outOfFuel
  | b :: rem =>
    match zf393Trans q b with
    | none => .halt q revWalked.reverse (b :: rem)
    | some (w, .left, q') =>
      if w == 0 then .jumpLeft q' revWalked.reverse rem else .outOfFuel
    | some (w, .right, q') =>
      if w == b then
        let nw := w :: revWalked
        if isLeafState q' then .regLeaf q' nw.reverse rem
        else fastWalk q' nw rem
      else .outOfFuel

theorem fastWalk_eq_walkTape (q : Fin 393) (revWalked rem : List (Fin 2)) :
    fastWalk q revWalked rem = walkTape q revWalked.reverse rem := by
  induction rem generalizing q revWalked with
  | nil => rfl
  | cons b rem' ih =>
    simp only [fastWalk, walkTape]
    rcases zf393Trans q b with _ | ⟨w, d, q'⟩
    · rfl
    · cases d with
      | left => rfl
      | right =>
        by_cases hwb : (w == b) = true
        · simp only [hwb, ↓reduceIte]
          by_cases hl : isLeafState q' = true
          · simp [hl]
          · simp only [hl, Bool.false_eq_true, ↓reduceIte]
            simpa [List.reverse_cons] using ih q' (w :: revWalked)
        · simp [hwb]

/-- Decidable check covering all small stacks `(ip, sl)` in `smallTrie` (`sl < 150`)
using a single `O(|ip|)` call to `fastWalk` on `m = min 10 (sl - ip.length)`. -/
def checkSmallStackEntry (entry : List (Fin 2) × ℕ) : Bool :=
  let (ip, sl) := entry
  let m := Nat.min 10 (sl - ip.length)
  (sl < 150) && (ip.length ≤ sl) &&
  match fastWalk 99 [] (ip ++ List.replicate m 0) with
  | .halt _ _ _ => true
  | .jumpLeft q1 w_j _ =>
    (w_j.length + 1 ≤ sl) &&
    match q1.val with
    | 61 => minSlot ((popBreakRev 0 w_j.reverse).reverse) ≤ breakSlot 0 sl w_j
    | 62 => minSlot ((popBreakRev 1 w_j.reverse).reverse) ≤ breakSlot 1 sl w_j
    | 63 => minSlot ((popBreakRev 2 w_j.reverse).reverse) ≤ breakSlot 2 sl w_j
    | 64 => minSlot ((popContinueRev 0 w_j.reverse).reverse) ≤ sl
    | 65 => minSlot ((popContinueRev 1 w_j.reverse).reverse) ≤ sl
    | 66 => minSlot ((popContinueRev 2 w_j.reverse).reverse) ≤ sl
    | 67 => minSlot ((popContinueRev 3 w_j.reverse).reverse) ≤ sl
    | 68 => minSlot ((popContinueRev 4 w_j.reverse).reverse) ≤ sl
    | _ => false
  | .regLeaf q1 w_l _ =>
    let r := leafReg q1
    (w_l.length + (11 - r.val) + 3 ≤ sl) &&
    if isLeafInc q1 then
      minSlot (retStack w_l) ≤ breakSlot 0 sl w_l
    else
      (minSlot ((popBreakRev 1 w_l.reverse).reverse) ≤ breakSlot 1 (sl + 1) w_l) &&
      (minSlot (retStack w_l) ≤ breakSlot 0 (sl + 1) w_l)
  | .outOfFuel => false

def SlotTrie.allEntries (revPrefix : List (Fin 2)) : SlotTrie → Bool
  | .leaf none => true
  | .leaf (some sl) => checkSmallStackEntry (revPrefix.reverse, sl)
  | .branch none l r =>
    l.allEntries (0 :: revPrefix) && r.allEntries (1 :: revPrefix)
  | .branch (some sl) l r =>
    checkSmallStackEntry (revPrefix.reverse, sl) &&
    l.allEntries (0 :: revPrefix) && r.allEntries (1 :: revPrefix)

theorem trieNode_0_ok :
    trieNode_0.allEntries [
        1, 0] = true := by
  unfold trieNode_0
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_1_ok :
    trieNode_1.allEntries [
        1, 0, 0, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_1
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_2_ok :
    trieNode_2.allEntries [
        1, 0, 0, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_2
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_3_ok :
    trieNode_3.allEntries [
        1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_3
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_4_ok :
    trieNode_4.allEntries [
        1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_4
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_5_ok :
    trieNode_5.allEntries [
        0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_5
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_6_ok :
    trieNode_6.allEntries [
        0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_6
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_7_ok :
    trieNode_7.allEntries [
        0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_7
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_8_ok :
    trieNode_8.allEntries [
        0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_8
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_9_ok :
    trieNode_9.allEntries [
        0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_9
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_10_ok :
    trieNode_10.allEntries [
        0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_10
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_11_ok :
    trieNode_11.allEntries [
        1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_11
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_12_ok :
    trieNode_12.allEntries [
        1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_12
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_13_ok :
    trieNode_13.allEntries [
        0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_13
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_14_ok :
    trieNode_14.allEntries [
        0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_14
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_15_ok :
    trieNode_15.allEntries [
        1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_15
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_16_ok :
    trieNode_16.allEntries [
        0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_16
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_17_ok :
    trieNode_17.allEntries [
        0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_17
  simp only [
    SlotTrie.allEntries, trieNode_14_ok]
  decide

theorem trieNode_18_ok :
    trieNode_18.allEntries [
        1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_18
  simp only [
    SlotTrie.allEntries, trieNode_15_ok, trieNode_16_ok]
  decide

theorem trieNode_19_ok :
    trieNode_19.allEntries [
        0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_19
  simp only [
    SlotTrie.allEntries, trieNode_12_ok, trieNode_13_ok]
  decide

theorem trieNode_20_ok :
    trieNode_20.allEntries [
        1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_20
  simp only [
    SlotTrie.allEntries, trieNode_10_ok, trieNode_11_ok, trieNode_19_ok,
    trieNode_17_ok, trieNode_18_ok]
  decide

theorem trieNode_21_ok :
    trieNode_21.allEntries [
        0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_21
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_22_ok :
    trieNode_22.allEntries [
        0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_22
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_23_ok :
    trieNode_23.allEntries [
        1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_23
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_24_ok :
    trieNode_24.allEntries [
        0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_24
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_25_ok :
    trieNode_25.allEntries [
        0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_25
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_26_ok :
    trieNode_26.allEntries [
        1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1] = true := by
  unfold trieNode_26
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_27_ok :
    trieNode_27.allEntries [
        0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_27
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_28_ok :
    trieNode_28.allEntries [
        1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_28
  simp only [
    SlotTrie.allEntries, trieNode_26_ok, trieNode_27_ok]
  decide

theorem trieNode_29_ok :
    trieNode_29.allEntries [
        0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_29
  simp only [
    SlotTrie.allEntries, trieNode_23_ok, trieNode_24_ok]
  decide

theorem trieNode_30_ok :
    trieNode_30.allEntries [
        1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_30
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_31_ok :
    trieNode_31.allEntries [
        0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_31
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_32_ok :
    trieNode_32.allEntries [
        0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_32
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_33_ok :
    trieNode_33.allEntries [
        1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1] = true := by
  unfold trieNode_33
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_34_ok :
    trieNode_34.allEntries [
        0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_34
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_35_ok :
    trieNode_35.allEntries [
        1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_35
  simp only [
    SlotTrie.allEntries, trieNode_33_ok, trieNode_34_ok]
  decide

theorem trieNode_36_ok :
    trieNode_36.allEntries [
        0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_36
  simp only [
    SlotTrie.allEntries, trieNode_30_ok, trieNode_31_ok]
  decide

theorem trieNode_37_ok :
    trieNode_37.allEntries [
        1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_37
  simp only [
    SlotTrie.allEntries, trieNode_32_ok, trieNode_35_ok]
  decide

theorem trieNode_38_ok :
    trieNode_38.allEntries [
        1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_38
  simp only [
    SlotTrie.allEntries, trieNode_29_ok, trieNode_25_ok, trieNode_28_ok,
    trieNode_36_ok, trieNode_37_ok]
  decide

theorem trieNode_39_ok :
    trieNode_39.allEntries [
        1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_39
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_40_ok :
    trieNode_40.allEntries [
        0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_40
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_41_ok :
    trieNode_41.allEntries [
        0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1] = true := by
  unfold trieNode_41
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_42_ok :
    trieNode_42.allEntries [
        1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1] = true := by
  unfold trieNode_42
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_43_ok :
    trieNode_43.allEntries [
        0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_43
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_44_ok :
    trieNode_44.allEntries [
        0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_44
  simp only [
    SlotTrie.allEntries, trieNode_41_ok]
  decide

theorem trieNode_45_ok :
    trieNode_45.allEntries [
        1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_45
  simp only [
    SlotTrie.allEntries, trieNode_42_ok, trieNode_43_ok]
  decide

theorem trieNode_46_ok :
    trieNode_46.allEntries [
        0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_46
  simp only [
    SlotTrie.allEntries, trieNode_39_ok, trieNode_40_ok]
  decide

theorem trieNode_47_ok :
    trieNode_47.allEntries [
        0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1] = true := by
  unfold trieNode_47
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_48_ok :
    trieNode_48.allEntries [
        1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1] = true := by
  unfold trieNode_48
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_49_ok :
    trieNode_49.allEntries [
        0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_49
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_50_ok :
    trieNode_50.allEntries [
        0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_50
  simp only [
    SlotTrie.allEntries, trieNode_47_ok]
  decide

theorem trieNode_51_ok :
    trieNode_51.allEntries [
        1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_51
  simp only [
    SlotTrie.allEntries, trieNode_48_ok, trieNode_49_ok]
  decide

theorem trieNode_52_ok :
    trieNode_52.allEntries [
        1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1] = true := by
  unfold trieNode_52
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_53_ok :
    trieNode_53.allEntries [
        0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1] = true := by
  unfold trieNode_53
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_54_ok :
    trieNode_54.allEntries [
        0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1] = true := by
  unfold trieNode_54
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_55_ok :
    trieNode_55.allEntries [
        1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1] = true := by
  unfold trieNode_55
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_56_ok :
    trieNode_56.allEntries [
        0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1] = true := by
  unfold trieNode_56
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_57_ok :
    trieNode_57.allEntries [
        0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_57
  simp only [
    SlotTrie.allEntries, trieNode_54_ok]
  decide

theorem trieNode_58_ok :
    trieNode_58.allEntries [
        1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_58
  simp only [
    SlotTrie.allEntries, trieNode_55_ok, trieNode_56_ok]
  decide

theorem trieNode_59_ok :
    trieNode_59.allEntries [
        0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_59
  simp only [
    SlotTrie.allEntries, trieNode_52_ok, trieNode_53_ok]
  decide

theorem trieNode_60_ok :
    trieNode_60.allEntries [
        0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1] = true := by
  unfold trieNode_60
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_61_ok :
    trieNode_61.allEntries [
        1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1] = true := by
  unfold trieNode_61
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_62_ok :
    trieNode_62.allEntries [
        0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1] = true := by
  unfold trieNode_62
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_63_ok :
    trieNode_63.allEntries [
        0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_63
  simp only [
    SlotTrie.allEntries, trieNode_60_ok]
  decide

theorem trieNode_64_ok :
    trieNode_64.allEntries [
        1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_64
  simp only [
    SlotTrie.allEntries, trieNode_61_ok, trieNode_62_ok]
  decide

theorem trieNode_65_ok :
    trieNode_65.allEntries [
        1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_65
  simp only [
    SlotTrie.allEntries, trieNode_50_ok, trieNode_51_ok, trieNode_59_ok,
    trieNode_57_ok, trieNode_58_ok, trieNode_63_ok, trieNode_64_ok]
  decide

theorem trieNode_66_ok :
    trieNode_66.allEntries [
        1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1] = true := by
  unfold trieNode_66
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_67_ok :
    trieNode_67.allEntries [
        0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_67
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_68_ok :
    trieNode_68.allEntries [
        0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_68
  simp only [
    SlotTrie.allEntries]
  decide

theorem trieNode_69_ok :
    trieNode_69.allEntries [
        0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_69
  simp only [
    SlotTrie.allEntries, trieNode_66_ok, trieNode_67_ok]
  decide

theorem trieNode_70_ok :
    trieNode_70.allEntries [
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_70
  simp only [
    SlotTrie.allEntries, trieNode_46_ok, trieNode_44_ok, trieNode_45_ok,
    trieNode_65_ok, trieNode_69_ok, trieNode_68_ok]
  decide

theorem trieNode_71_ok :
    trieNode_71.allEntries [
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_71
  simp only [
    SlotTrie.allEntries, trieNode_22_ok, trieNode_38_ok, trieNode_70_ok]
  decide

theorem trieNode_72_ok :
    trieNode_72.allEntries [
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_72
  simp only [
    SlotTrie.allEntries, trieNode_21_ok, trieNode_71_ok]
  decide

theorem trieNode_73_ok :
    trieNode_73.allEntries [
        0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_73
  simp only [
    SlotTrie.allEntries, trieNode_7_ok, trieNode_8_ok]
  decide

theorem trieNode_74_ok :
    trieNode_74.allEntries [
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_74
  simp only [
    SlotTrie.allEntries, trieNode_9_ok, trieNode_20_ok, trieNode_72_ok]
  decide

theorem trieNode_75_ok :
    trieNode_75.allEntries [
        0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_75
  simp only [
    SlotTrie.allEntries, trieNode_6_ok]
  decide

theorem trieNode_76_ok :
    trieNode_76.allEntries [
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_76
  simp only [
    SlotTrie.allEntries, trieNode_5_ok, trieNode_75_ok, trieNode_73_ok,
    trieNode_74_ok]
  decide

theorem trieNode_77_ok :
    trieNode_77.allEntries [
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_77
  simp only [
    SlotTrie.allEntries, trieNode_4_ok, trieNode_76_ok]
  decide

theorem trieNode_78_ok :
    trieNode_78.allEntries [
        1, 1, 1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_78
  simp only [
    SlotTrie.allEntries, trieNode_3_ok, trieNode_77_ok]
  decide

theorem trieNode_79_ok :
    trieNode_79.allEntries [
        1, 1, 1, 1, 1, 1, 1] = true := by
  unfold trieNode_79
  simp only [
    SlotTrie.allEntries, trieNode_2_ok, trieNode_78_ok]
  decide

theorem trieNode_80_ok :
    trieNode_80.allEntries [
        1, 1, 1, 1, 1] = true := by
  unfold trieNode_80
  simp only [
    SlotTrie.allEntries, trieNode_1_ok, trieNode_79_ok]
  decide

theorem trieNode_81_ok :
    trieNode_81.allEntries [
        1, 1] = true := by
  unfold trieNode_81
  simp only [
    SlotTrie.allEntries, trieNode_80_ok]
  decide

theorem smallTrie_allEntries : smallTrie.allEntries [] = true := by
  unfold smallTrie
  simp only [
    SlotTrie.allEntries, trieNode_0_ok, trieNode_81_ok]
  decide

theorem SlotTrie.allEntries_get (t : SlotTrie) (revPrefix ip : List (Fin 2)) {sl : ℕ}
    (h : t.allEntries revPrefix = true) (hget : t.get ip = some sl) :
    checkSmallStackEntry (revPrefix.reverse ++ ip, sl) = true := by
  induction t generalizing revPrefix ip with
  | leaf v =>
    cases ip with
    | nil =>
      rcases v with _ | val <;>
        simp only [SlotTrie.get, SlotTrie.allEntries, Option.some.injEq] at h hget
      · cases hget
      · subst hget; rw [List.append_nil]; exact h
    | cons _ _ => cases hget
  | branch v l r ihl ihr =>
    cases ip with
    | nil =>
      rcases v with _ | val <;>
        simp only [SlotTrie.get, SlotTrie.allEntries, Bool.and_eq_true, Option.some.injEq] at h hget
      · cases hget
      · subst hget; rw [List.append_nil]; exact h.1.1
    | cons b bs =>
      cases v <;> simp only [SlotTrie.allEntries, Bool.and_eq_true] at h <;>
        rcases fin2_cases b with rfl | rfl <;>
        dsimp only [SlotTrie.get] at hget
      · simpa [List.reverse_cons, List.append_assoc] using ihl _ _ h.1 hget
      · simpa [List.reverse_cons, List.append_assoc] using ihr _ _ h.2 hget
      · simpa [List.reverse_cons, List.append_assoc] using ihl _ _ h.1.2 hget
      · simpa [List.reverse_cons, List.append_assoc] using ihr _ _ h.2 hget

theorem checkSmallStackEntry_of_lookup {ip : List (Fin 2)} {sl : ℕ}
    (hlk : lookupSmall ip = some sl) :
    checkSmallStackEntry (ip, sl) = true :=
  SlotTrie.allEntries_get smallTrie [] ip smallTrie_allEntries hlk

theorem minSlot_le_150 (ip : List (Fin 2)) : minSlot ip ≤ 150 := by
  unfold minSlot
  cases h : lookupSmall ip with
  | none => decide
  | some sl =>
    dsimp only [Option.getD]
    have hall := checkSmallStackEntry_of_lookup h
    simp only [checkSmallStackEntry, Bool.and_eq_true] at hall
    have hsl : sl < 150 := of_decide_eq_true hall.1.1
    omega

/-- Invariant relating a TM slot size `slot : ℕ` and an abstract configuration `c : Zf393RegCfg`:
`c.regs.length = 11`, `c.ip.length ≤ 136`, `staysInDag 99 c.ip.dropLast = true`,
and `minSlot c.ip ≤ slot`. -/
def Zf393Inv (slot : ℕ) (c : Zf393RegCfg) : Prop :=
  c.regs.length = 11 ∧ c.ip.length ≤ 136 ∧
  staysInDag 99 c.ip.dropLast = true ∧ minSlot c.ip ≤ slot

theorem zf393Inv_init : Zf393Inv 19 zf393RegInit :=
  ⟨by decide, by decide, by decide, by decide⟩

attribute [irreducible] smallTrie

theorem breakSlot_mono (k : ℕ) {s1 s2 : ℕ} (hs : s1 ≤ s2) (w : List (Fin 2)) :
    breakSlot k s1 w ≤ breakSlot k s2 w := by
  unfold breakSlot; split <;> omega

/-- Forward 1-step simulation: from any `@rootCfg pre slot c.ip c.regs` satisfying
`Zf393Inv slot c`, the Turing machine `zf393` simulates `zf393RegStep c` in `s ≥ 1` steps! -/
theorem tm_simulates_zf393RegStep {slot : ℕ} {c : Zf393RegCfg} (hinv : Zf393Inv slot c) :
    match zf393RegStep c with
    | none =>
      ∃ s ch, nSteps zf393 s (@rootCfg pre slot c.ip c.regs) = some ch ∧ step zf393 ch = none
    | some c' =>
      ∃ slot' s, 1 ≤ s ∧ Zf393Inv slot' c' ∧
        nSteps zf393 s (@rootCfg pre slot c.ip c.regs) =
          some (@rootCfg pre slot' c'.ip c'.regs) := by
  obtain ⟨hregs, hip136, hdag_in, hmin⟩ := hinv
  have hdag_walk := walkTape_dag_props 99 [] c.ip (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hstays_walk := staysInDag_of_walkTape 99 [] (c.ip ++ List.replicate 10 0)
  have hsl_ge_ip : c.ip.length ≤ slot := by
    unfold minSlot at hmin
    cases hlk : lookupSmall c.ip with
    | none =>
      simp [hlk] at hmin; omega
    | some sl =>
      simp [hlk] at hmin
      have hall := checkSmallStackEntry_of_lookup hlk
      simp only [checkSmallStackEntry, Bool.and_eq_true] at hall
      have hip_sl : c.ip.length ≤ sl := of_decide_eq_true hall.1.2
      omega
  have hslot_match :
      match walkTape 99 [] (c.ip ++ List.replicate 10 0) with
      | .outOfFuel => False
      | .halt q_h w_h _ =>
        ∃ r_s, walkTape 99 [] (c.ip ++ List.replicate (slot - c.ip.length) 0) =
          .halt q_h w_h r_s
      | .jumpLeft q' w_j _ =>
        (∃ r_s, walkTape 99 [] (c.ip ++ List.replicate (slot - c.ip.length) 0) =
          .jumpLeft q' w_j r_s) ∧
        w_j.length + 1 ≤ slot ∧
        match q'.val with
        | 61 => minSlot ((popBreakRev 0 w_j.reverse).reverse) ≤ breakSlot 0 slot w_j
        | 62 => minSlot ((popBreakRev 1 w_j.reverse).reverse) ≤ breakSlot 1 slot w_j
        | 63 => minSlot ((popBreakRev 2 w_j.reverse).reverse) ≤ breakSlot 2 slot w_j
        | 64 => minSlot ((popContinueRev 0 w_j.reverse).reverse) ≤ slot
        | 65 => minSlot ((popContinueRev 1 w_j.reverse).reverse) ≤ slot
        | 66 => minSlot ((popContinueRev 2 w_j.reverse).reverse) ≤ slot
        | 67 => minSlot ((popContinueRev 3 w_j.reverse).reverse) ≤ slot
        | 68 => minSlot ((popContinueRev 4 w_j.reverse).reverse) ≤ slot
        | _ => False
      | .regLeaf q' w_l _ =>
        let r := leafReg q'
        (∃ r_s, walkTape 99 [] (c.ip ++ List.replicate (slot - c.ip.length) 0) =
          .regLeaf q' w_l r_s) ∧
        w_l.length + (11 - r.val) + 3 ≤ slot ∧
        (if isLeafInc q' then
          minSlot (retStack w_l) ≤ breakSlot 0 slot w_l
        else
          minSlot ((popBreakRev 1 w_l.reverse).reverse) ≤ breakSlot 1 (slot + 1) w_l ∧
          minSlot (retStack w_l) ≤ breakSlot 0 (slot + 1) w_l) := by
    unfold minSlot at hmin
    cases hlk : lookupSmall c.ip with
    | none =>
      simp [hlk] at hmin
      have hsub10 : slot - c.ip.length = 10 + (slot - c.ip.length - 10) := by omega
      have hext := walkTape_extend_zeros 99 [] (c.ip ++ List.replicate 10 0)
        (slot - c.ip.length - 10)
      have hrep_eq : (c.ip ++ List.replicate 10 0) ++ List.replicate (slot - c.ip.length - 10) 0 =
          c.ip ++ List.replicate (slot - c.ip.length) 0 := by
        rw [List.append_assoc, ← List.replicate_add, ← hsub10]
      rw [hrep_eq] at hext
      rcases h10 : walkTape 99 [] (c.ip ++ List.replicate 10 0) with
        ⟨q_h, w_h, r_h⟩ | ⟨q', w_j, r_j⟩ | ⟨q', w_l, r_l⟩ | _
      · rw [h10] at hext; exact ⟨_, hext⟩
      · rw [h10] at hdag_walk hext
        obtain ⟨hwj135, _, hqv⟩ := hdag_walk
        refine ⟨⟨_, hext⟩, by omega, ?_⟩
        rcases hqv with (hq61 | hq62 | hq63) | ⟨hq64, _⟩ | ⟨hq65, _⟩ |
            ⟨hq66, _⟩ | ⟨hq67, _⟩ | ⟨hq68, _⟩
        · rw [hq61]
          exact le_trans (minSlot_le_150 _) (le_trans (by omega) (breakSlot_ge 0 slot w_j))
        · rw [hq62]
          exact le_trans (minSlot_le_150 _) (le_trans (by omega) (breakSlot_ge 1 slot w_j))
        · rw [hq63]
          exact le_trans (minSlot_le_150 _) (le_trans (by omega) (breakSlot_ge 2 slot w_j))
        · rw [hq64]; exact le_trans (minSlot_le_150 _) (by omega)
        · rw [hq65]; exact le_trans (minSlot_le_150 _) (by omega)
        · rw [hq66]; exact le_trans (minSlot_le_150 _) (by omega)
        · rw [hq67]; exact le_trans (minSlot_le_150 _) (by omega)
        · rw [hq68]; exact le_trans (minSlot_le_150 _) (by omega)
      · rw [h10] at hdag_walk hext
        obtain ⟨_, hwl136, _⟩ := hdag_walk
        refine ⟨⟨_, hext⟩, by omega, ?_⟩
        split
        · exact le_trans (minSlot_le_150 _) (le_trans (by omega) (breakSlot_ge 0 slot w_l))
        · exact ⟨le_trans (minSlot_le_150 _) (le_trans (by omega) (breakSlot_ge 1 (slot + 1) w_l)),
            le_trans (minSlot_le_150 _) (le_trans (by omega) (breakSlot_ge 0 (slot + 1) w_l))⟩
      · rw [h10] at hdag_walk; exact hdag_walk
    | some sl =>
      rw [hlk] at hmin; dsimp only [Option.getD] at hmin
      have hall := checkSmallStackEntry_of_lookup hlk
      simp only [checkSmallStackEntry, Bool.and_eq_true] at hall
      let m := Nat.min 10 (sl - c.ip.length)
      have hm10 : m ≤ 10 := Nat.min_le_left _ _
      have hmsl : m ≤ sl - c.ip.length := Nat.min_le_right _ _
      have hip_sl : c.ip.length ≤ sl := of_decide_eq_true hall.1.2
      have hext10 := walkTape_extend_zeros 99 [] (c.ip ++ List.replicate m 0) (10 - m)
      have hrep10 :
          (c.ip ++ List.replicate m 0) ++ List.replicate (10 - m) 0 =
          c.ip ++ List.replicate 10 0 := by
        rw [List.append_assoc, ← List.replicate_add]
        congr 2; omega
      rw [hrep10] at hext10
      have hext_slot := walkTape_extend_zeros 99 [] (c.ip ++ List.replicate m 0)
        (slot - c.ip.length - m)
      have hrep_slot :
          (c.ip ++ List.replicate m 0) ++ List.replicate (slot - c.ip.length - m) 0 =
          c.ip ++ List.replicate (slot - c.ip.length) 0 := by
        rw [List.append_assoc, ← List.replicate_add]
        congr 2; omega
      rw [hrep_slot] at hext_slot
      have hall2 := hall.2
      rw [fastWalk_eq_walkTape, List.reverse_nil] at hall2
      rcases hm : walkTape 99 [] (c.ip ++ List.replicate m 0) with
        ⟨q_h, w_h, r_h⟩ | ⟨q', w_j, r_j⟩ | ⟨q', w_l, r_l⟩ | _
      · rw [hm] at hext10 hext_slot
        rw [hext10]
        exact ⟨_, hext_slot⟩
      · rw [hm] at hall2 hext10 hext_slot
        rw [hext10] at hdag_walk ⊢
        simp only [Bool.and_eq_true] at hall2
        have hwj_sl : w_j.length + 1 ≤ sl := of_decide_eq_true hall2.1
        refine ⟨⟨_, hext_slot⟩, by omega, ?_⟩
        have hms := hall2.2
        rcases hdag_walk.2.2 with (hq61 | hq62 | hq63) | ⟨hq64, _⟩ | ⟨hq65, _⟩ |
            ⟨hq66, _⟩ | ⟨hq67, _⟩ | ⟨hq68, _⟩
        · rw [hq61] at hms ⊢
          exact le_trans (of_decide_eq_true hms) (breakSlot_mono 0 hmin w_j)
        · rw [hq62] at hms ⊢
          exact le_trans (of_decide_eq_true hms) (breakSlot_mono 1 hmin w_j)
        · rw [hq63] at hms ⊢
          exact le_trans (of_decide_eq_true hms) (breakSlot_mono 2 hmin w_j)
        · rw [hq64] at hms ⊢; exact le_trans (of_decide_eq_true hms) hmin
        · rw [hq65] at hms ⊢; exact le_trans (of_decide_eq_true hms) hmin
        · rw [hq66] at hms ⊢; exact le_trans (of_decide_eq_true hms) hmin
        · rw [hq67] at hms ⊢; exact le_trans (of_decide_eq_true hms) hmin
        · rw [hq68] at hms ⊢; exact le_trans (of_decide_eq_true hms) hmin
      · rw [hm] at hall2 hext10 hext_slot
        rw [hext10]
        simp only [Bool.and_eq_true] at hall2
        have hwl_sl : w_l.length + (11 - (leafReg q').val) + 3 ≤ sl :=
          of_decide_eq_true hall2.1
        refine ⟨⟨_, hext_slot⟩, by omega, ?_⟩
        have hms := hall2.2
        by_cases hinc_q : isLeafInc q' = true <;>
          simp only [hinc_q, ↓reduceIte, Bool.false_eq_true] at hms ⊢
        · exact le_trans (of_decide_eq_true hms) (breakSlot_mono 0 hmin w_l)
        · simp only [Bool.and_eq_true] at hms
          exact ⟨le_trans (of_decide_eq_true hms.1) (breakSlot_mono 1 (by omega) w_l),
            le_trans (of_decide_eq_true hms.2) (breakSlot_mono 0 (by omega) w_l)⟩
      · rw [hm] at hall2; cases hall2
  have htail := walkTape_slot_tail hsl_ge_ip hdag_in
  have hreach := walkTape_sound 99 [] (c.ip ++ List.replicate (slot - c.ip.length) 0)
    LB01 (ListBlank.append (encodeRegs pre) (regsTape c.regs))
  have hroot_eq : @rootCfg pre slot c.ip c.regs =
      treeWalkCfg 99 [] (c.ip ++ List.replicate (slot - c.ip.length) 0)
        LB01 (ListBlank.append (encodeRegs pre) (regsTape c.regs)) := by
    unfold rootCfg treeWalkCfg
    simp only [List.reverse_nil, ListBlank.append, ← ListBlank.append_assoc]
  unfold zf393RegStep
  rcases h10 : walkTape 99 [] (c.ip ++ List.replicate 10 0) with
    ⟨q_h, w_h, r_h⟩ | ⟨q', w_j, r_j⟩ | ⟨q', w_l, r_l⟩ | _
  · dsimp only
    rw [h10] at hslot_match
    obtain ⟨r_s, hr_s⟩ := hslot_match
    rw [hr_s] at hreach
    obtain ⟨s, _, hs, hnone⟩ := hreach
    exact ⟨s, _, by rwa [hroot_eq], hnone⟩
  · dsimp only
    rw [h10] at hdag_walk hstays_walk hslot_match
    obtain ⟨hwj135, hok_j, hqv⟩ := hdag_walk
    obtain ⟨_, hw_eq, hstays_wj⟩ := hstays_walk
    rw [List.nil_append] at hw_eq
    rw [← hw_eq] at hstays_wj
    obtain ⟨⟨r_s, hr_s⟩, hwj_sl, hms⟩ := hslot_match
    rw [hr_s] at hreach htail
    subst htail
    obtain ⟨_, s₁, _, hs₁⟩ := hreach
    have hR_eq :
        ListBlank.append (0 :: List.replicate (slot - (w_j.length + 1)) 0)
          (ListBlank.append (encodeRegs pre) (regsTape c.regs)) =
        ListBlank.append (List.replicate (slot - w_j.length) 0 ++ encodeRegs pre)
          (regsTape c.regs) := by
      have hsub : slot - w_j.length = (slot - (w_j.length + 1)) + 1 := by omega
      rw [hsub, List.replicate_succ, ListBlank.append_assoc]
    rw [hR_eq] at hs₁
    rcases hqv with (hq61 | hq62 | hq63) | ⟨hq64, hc0⟩ | ⟨hq65, hc1⟩ |
        ⟨hq66, hc2⟩ | ⟨hq67, hc3⟩ | ⟨hq68, hc4⟩
    · have hq'_eq : q' = breakState 0 := by ext; exact hq61
      simp only [hq61] at hms ⊢
      rw [hq'_eq] at hs₁
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := break_k_reaches_main0 (pre := pre) 0 (by decide) slot w_j
        (by omega) hok_j c.regs
      have hip_len : (popBreakRev 0 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popBreakRev_length_le 0 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popBreakRev 0 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99 ((popBreakRev_dropLast_prefix 0 w_j).trans w_j.dropLast_prefix)
          hstays_wj
      exact ⟨_, s₁ + s₂, by omega, ⟨hregs, hip_len, hdag', hms⟩,
        by rw [hroot_eq]; exact nSteps_bind_eq hs₁ hs₂⟩
    · have hq'_eq : q' = breakState 1 := by ext; exact hq62
      simp only [hq62] at hms ⊢
      rw [hq'_eq] at hs₁
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := break_k_reaches_main0 (pre := pre) 1 (by decide) slot w_j
        (by omega) hok_j c.regs
      have hip_len : (popBreakRev 1 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popBreakRev_length_le 1 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popBreakRev 1 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99 ((popBreakRev_dropLast_prefix 1 w_j).trans w_j.dropLast_prefix)
          hstays_wj
      exact ⟨_, s₁ + s₂, by omega, ⟨hregs, hip_len, hdag', hms⟩,
        by rw [hroot_eq]; exact nSteps_bind_eq hs₁ hs₂⟩
    · have hq'_eq : q' = breakState 2 := by ext; exact hq63
      simp only [hq63] at hms ⊢
      rw [hq'_eq] at hs₁
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := break_k_reaches_main0 (pre := pre) 2 (by decide) slot w_j
        (by omega) hok_j c.regs
      have hip_len : (popBreakRev 2 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popBreakRev_length_le 2 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popBreakRev 2 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99 ((popBreakRev_dropLast_prefix 2 w_j).trans w_j.dropLast_prefix)
          hstays_wj
      exact ⟨_, s₁ + s₂, by omega, ⟨hregs, hip_len, hdag', hms⟩,
        by rw [hroot_eq]; exact nSteps_bind_eq hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 0 := by ext; exact hq64
      simp only [hq64] at hms ⊢
      rw [hq'_eq] at hs₁
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := continue_k_reaches_main0 (pre := pre) 0 (by decide) slot w_j
        hc0 (by omega) hok_j c.regs
      have hip_len : (popContinueRev 0 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 0 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 0 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 0 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 0 w_j))
          hstays_wj
      exact ⟨slot, s₁ + s₂, by omega, ⟨hregs, hip_len, hdag', hms⟩,
        by rw [hroot_eq]; exact nSteps_bind_eq hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 1 := by ext; exact hq65
      simp only [hq65] at hms ⊢
      rw [hq'_eq] at hs₁
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := continue_k_reaches_main0 (pre := pre) 1 (by decide) slot w_j
        hc1 (by omega) hok_j c.regs
      have hip_len : (popContinueRev 1 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 1 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 1 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 1 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 1 w_j))
          hstays_wj
      exact ⟨slot, s₁ + s₂, by omega, ⟨hregs, hip_len, hdag', hms⟩,
        by rw [hroot_eq]; exact nSteps_bind_eq hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 2 := by ext; exact hq66
      simp only [hq66] at hms ⊢
      rw [hq'_eq] at hs₁
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := continue_k_reaches_main0 (pre := pre) 2 (by decide) slot w_j
        hc2 (by omega) hok_j c.regs
      have hip_len : (popContinueRev 2 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 2 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 2 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 2 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 2 w_j))
          hstays_wj
      exact ⟨slot, s₁ + s₂, by omega, ⟨hregs, hip_len, hdag', hms⟩,
        by rw [hroot_eq]; exact nSteps_bind_eq hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 3 := by ext; exact hq67
      simp only [hq67] at hms ⊢
      rw [hq'_eq] at hs₁
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := continue_k_reaches_main0 (pre := pre) 3 (by decide) slot w_j
        hc3 (by omega) hok_j c.regs
      have hip_len : (popContinueRev 3 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 3 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 3 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 3 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 3 w_j))
          hstays_wj
      exact ⟨slot, s₁ + s₂, by omega, ⟨hregs, hip_len, hdag', hms⟩,
        by rw [hroot_eq]; exact nSteps_bind_eq hs₁ hs₂⟩
    · have hq'_eq : q' = continueState 4 := by ext; exact hq68
      simp only [hq68] at hms ⊢
      rw [hq'_eq] at hs₁
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := continue_k_reaches_main0 (pre := pre) 4 (by decide) slot w_j
        hc4 (by omega) hok_j c.regs
      have hip_len : (popContinueRev 4 w_j.reverse).reverse.length ≤ 136 := by
        rw [List.length_reverse]
        exact (popContinueRev_length_le 4 w_j.reverse).trans (by rw [List.length_reverse]; omega)
      have hdag' : staysInDag 99 (popContinueRev 4 w_j.reverse).reverse.dropLast = true :=
        staysInDag_prefix 99
          ((popContinueRev 4 w_j.reverse).reverse.dropLast_prefix.trans
            (popContinueRev_prefix 4 w_j))
          hstays_wj
      exact ⟨slot, s₁ + s₂, by omega, ⟨hregs, hip_len, hdag', hms⟩,
        by rw [hroot_eq]; exact nSteps_bind_eq hs₁ hs₂⟩
  · dsimp only
    rw [h10] at hdag_walk hstays_walk hslot_match
    obtain ⟨hleaf_q, hwl136, hok_l⟩ := hdag_walk
    obtain ⟨_, hw_eq, hstays_wl⟩ := hstays_walk
    rw [List.nil_append] at hw_eq
    rw [← hw_eq] at hstays_wl
    obtain ⟨⟨r_s, hr_s⟩, hwl_sl, hms⟩ := hslot_match
    rw [hr_s] at hreach htail
    subst htail
    obtain ⟨hu_eq, _, _, _⟩ := hreach
    rw [List.nil_append] at hu_eq
    have hroot_wl : @rootCfg pre slot c.ip c.regs =
        ⟨99, Tape.mk' LB01
          (ListBlank.append (w_l ++ List.replicate (slot - w_l.length) 0 ++ encodeRegs pre)
            (regsTape c.regs))⟩ := by
      unfold rootCfg
      rw [← hu_eq]
    have hself := walkTape_self_on_regLeaf 99 [] (c.ip ++ List.replicate 10 0) q' w_l r_l
      (by simpa using h10)
    rw [List.nil_append] at hself
    have hgetD : c.regs.getD (leafReg q').val 0 = c.regs[(leafReg q').val] := by
      simp [List.getD, getElem?_pos c.regs (leafReg q').val (by omega)]
    have hip0_len : (retStack w_l).length ≤ 136 := by
      unfold retStack; rw [List.length_reverse]
      exact (popBreakRev_length_le 0 w_l.reverse).trans (by rw [List.length_reverse]; omega)
    have hdag0 : staysInDag 99 (retStack w_l).dropLast = true := by
      unfold retStack
      exact staysInDag_prefix 99 (popBreakRev_dropLast_prefix 0 w_l) hstays_wl
    by_cases hinc : isLeafInc q' = true
    · simp only [hinc, ↓reduceIte] at hms ⊢
      have hq_inc := leafReg_inc_spec q' hleaf_q hinc
      rw [hq_inc] at hself
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := inc_leaf_reaches_main0 (pre := pre) (leafReg q') slot w_l hself
        hwl_sl hok_l c.regs hregs
      rw [← hroot_wl, ← hgetD] at hs₂
      have hset_len : (c.regs.set (leafReg q').val (c.regs.getD (leafReg q').val 0 + 1)).length =
          11 := by rw [List.length_set, hregs]
      exact ⟨_, s₂, hs₂_pos, ⟨hset_len, hip0_len, hdag0, hms⟩, hs₂⟩
    · simp only [Bool.not_eq_true] at hinc
      simp only [hinc, Bool.false_eq_true, ↓reduceIte] at hms ⊢
      have hq_dec := leafReg_decnz_spec q' hleaf_q hinc
      rw [hq_dec] at hself
      obtain ⟨s₂, hs₂_pos, hs₂⟩ := decnz_leaf_reaches_main0 (pre := pre) (leafReg q') slot w_l
        hself hwl_sl hok_l c.regs hregs
      rw [← hroot_wl, ← hgetD] at hs₂
      by_cases hv : c.regs.getD (leafReg q').val 0 = 0
      · simp only [hv, beq_self_eq_true, ↓reduceIte] at hs₂ ⊢
        have hip1_len : (popBreakRev 1 w_l.reverse).reverse.length ≤ 136 := by
          rw [List.length_reverse]
          exact (popBreakRev_length_le 1 w_l.reverse).trans (by rw [List.length_reverse]; omega)
        have hdag1 : staysInDag 99 (popBreakRev 1 w_l.reverse).reverse.dropLast = true :=
          staysInDag_prefix 99 (popBreakRev_dropLast_prefix 1 w_l) hstays_wl
        exact ⟨_, s₂, hs₂_pos, ⟨hregs, hip1_len, hdag1, hms.1⟩, hs₂⟩
      · have hvf : (c.regs.getD (leafReg q').val 0 == 0) = false := beq_eq_false_iff_ne.mpr hv
        simp only [hv, hvf, Bool.false_eq_true, ↓reduceIte] at hs₂ ⊢
        have hset_len :
            (c.regs.set (leafReg q').val (c.regs.getD (leafReg q').val 0 - 1)).length = 11 := by
          rw [List.length_set, hregs]
        exact ⟨_, s₂, hs₂_pos, ⟨hset_len, hip0_len, hdag0, hms.2⟩, hs₂⟩
  · rw [h10] at hslot_match; exact False.elim hslot_match

theorem tm_simulates_zf393RegNSteps_from (m : ℕ) (slot : ℕ) (c₀ c : Zf393RegCfg)
    (hinv : Zf393Inv slot c₀) (hm : zf393RegNSteps m c₀ = some c) :
    ∃ slot' ds, Zf393Inv slot' c ∧
      nSteps zf393 ds (@rootCfg pre slot c₀.ip c₀.regs) =
        some (@rootCfg pre slot' c.ip c.regs) := by
  induction m generalizing slot c₀ with
  | zero =>
    obtain rfl : c₀ = c := Option.some.inj hm
    exact ⟨slot, 0, hinv, rfl⟩
  | succ m' ih =>
    simp only [zf393RegNSteps] at hm
    have hsim := tm_simulates_zf393RegStep (pre := pre) hinv
    rcases hst : zf393RegStep c₀ with _ | c₁
    · rw [hst] at hm; cases hm
    · rw [hst] at hm hsim
      obtain ⟨slot₁, s₁, _, hinv₁, hs₁⟩ := hsim
      obtain ⟨slot', ds, hinv', hds⟩ := ih slot₁ c₁ hinv₁ hm
      exact ⟨slot', s₁ + ds, hinv', nSteps_bind_eq hs₁ hds⟩

theorem zf393RegNSteps_snoc (n : ℕ) (c₀ c c' : Zf393RegCfg)
    (h1 : zf393RegNSteps n c₀ = some c) (h2 : zf393RegStep c = some c') :
    zf393RegNSteps (n + 1) c₀ = some c' := by
  induction n generalizing c₀ with
  | zero =>
    obtain rfl : c₀ = c := Option.some.inj h1
    simp [zf393RegNSteps, h2]
  | succ m ih =>
    simp only [zf393RegNSteps] at h1 ⊢
    rcases hst : zf393RegStep c₀ with _ | c₁
    · rw [hst] at h1; cases h1
    · rw [hst] at h1; exact ih c₁ h1

theorem halts_from_rootCfg_iff :
    (∃ ch T, nSteps zf393 T (@rootCfg pre 19 [] (List.replicate 11 0)) = some ch ∧
      step zf393 ch = none) ↔ Zf393RegHalts := by
  constructor
  · rintro ⟨ch, T, hT, hhalt⟩
    by_contra hnot
    have hinf : ∀ n : ℕ, ∃ slot s c, n ≤ s ∧
        zf393RegNSteps n zf393RegInit = some c ∧ Zf393Inv slot c ∧
        nSteps zf393 s (@rootCfg pre 19 [] (List.replicate 11 0)) =
          some (@rootCfg pre slot c.ip c.regs) := by
      intro n
      induction n with
      | zero =>
        exact ⟨19, 0, zf393RegInit, le_refl 0, rfl, zf393Inv_init, rfl⟩
      | succ n ih =>
        obtain ⟨slot, s, c, hns, hreg, hinv, hsteps⟩ := ih
        have hsim := tm_simulates_zf393RegStep (pre := pre) hinv
        rcases hst : zf393RegStep c with _ | c'
        · exact False.elim (hnot ⟨n, c, hreg, hst⟩)
        · rw [hst] at hsim
          obtain ⟨slot', ds, hds1, hinv', hds⟩ := hsim
          exact ⟨slot', s + ds, c', by omega,
            zf393RegNSteps_snoc n zf393RegInit c c' hreg hst,
            hinv', nSteps_bind_eq hsteps hds⟩
    obtain ⟨slot, s, c, hTs, _, _, hsteps⟩ := hinf (T + 1)
    have hsplit : s = T + (s - T) := by omega
    rw [hsplit, nSteps_add, hT, Option.bind_some, nSteps_of_halt hhalt (by omega)] at hsteps
    cases hsteps
  · rintro ⟨n, c, hn, hnone⟩
    obtain ⟨slot, s₁, hinv, hs₁⟩ :=
      tm_simulates_zf393RegNSteps_from (pre := pre) n 19 zf393RegInit c zf393Inv_init hn
    have hsim := tm_simulates_zf393RegStep (pre := pre) hinv
    rw [hnone] at hsim
    obtain ⟨s₂, ch, hs₂, hch⟩ := hsim
    exact ⟨ch, s₁ + s₂, nSteps_bind_eq hs₁ hs₂, hch⟩

end GenericPrefix

/-- Layer 1 master theorem: `zf393` halts from blank tape iff the 11-register call-stack machine
`zf393RegStep` halts from `zf393RegInit` (`⟨[], List.replicate 11 0⟩`). -/
theorem halts_zf393_iff_zf393RegHalts : ConjectureMachines.Halts zf393 ↔ Zf393RegHalts := by
  rw [ConjectureMachines.Halts, Part.dom_iff_mem]
  simp_rw [mem_eval_iff_nSteps]
  constructor
  · rintro ⟨ch, T, hT, hhalt⟩
    by_cases hlt : T < 39773
    · have h39773 : 39773 = T + (39773 - T) := by omega
      have hb := boot_reaches_main0
      rw [h39773, nSteps_add, hT, Option.bind_some, nSteps_of_halt hhalt (by omega)] at hb
      cases hb
    · have h39773 : T = 39773 + (T - 39773) := by omega
      rw [h39773, nSteps_add, boot_reaches_main0, Option.bind_some] at hT
      exact (halts_from_rootCfg_iff (pre := prefix190)).mp ⟨ch, T - 39773, hT, hhalt⟩
  · intro hreg
    obtain ⟨ch, s, hs, hch⟩ := (halts_from_rootCfg_iff (pre := prefix190)).mpr hreg
    exact ⟨ch, 39773 + s, nSteps_bind_eq boot_reaches_main0 hs, hch⟩

end ConjectureMachines.Zf393.Layer1

end
