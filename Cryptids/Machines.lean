/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.SetTheory.ZFC.Basic
meta import Lean.Elab.Term

/-!
# Turing Machine Definitions (`Cryptids.Machines`)

Machines with `states` states and `symbols` symbols, over Mathlib's tape, together with the
elaboration-time table loader `load_machine_rows%` and all baseline and candidate machines in
`ConjectureMachines.Machines`.
-/

meta section
namespace ConjectureMachines.Machines
open Lean Elab Term

private def parseCellStx (cell : String) : TermElabM (TSyntax `term) := do
  if cell == "---" then `(none)
  else match cell.toList with
    | wChar :: dChar :: rest =>
      if rest.isEmpty then throwError "Malformed transition cell: {cell}"
      let wLit := Syntax.mkNumLit (String.singleton wChar)
      let dirStx ← match dChar with
        | 'L' => `(Turing.Dir.left) | 'R' => `(Turing.Dir.right)
        | _ => throwError "Invalid direction in transition cell: {cell}"
      `(some ($wLit, $dirStx, $(Syntax.mkNumLit (String.ofList rest))))
    | _ => throwError "Malformed transition cell: {cell}"

elab "load_machine_rows% " path:str : term <= expectedType? => do
  let contents ← liftM (m := IO) (IO.FS.readFile path.getString)
  let mut rowStxs : Array (TSyntax `term) := #[]
  for rawLine in contents.splitOn "\n" do
    let line := ((rawLine.splitOn "#").headD "").trimAscii.toString
    if !line.isEmpty then
      match (line.splitOn " ").filter (fun s => !s.isEmpty) with
      | [c0, c1] => rowStxs := rowStxs.push (← `([$(← parseCellStx c0), $(← parseCellStx c1)]))
      | _ => throwError "Expected 2 columns in transition table line: {rawLine}"
  elabTerm (← `([$rowStxs,*])) expectedType?
end ConjectureMachines.Machines
end

@[expose] public section
namespace ConjectureMachines
open Turing StateTransition

/-- A transition table: for a state and the symbol under the head, either the
symbol to write, the direction to move and the state to enter, or `none` to
halt. -/
structure Machine (states symbols : ℕ) where
  transition : Fin states → Fin symbols → Option (Fin symbols × Dir × Fin states)

variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- A configuration: the current state and the tape, whose `head` is the
symbol under the head. -/
structure Cfg (states symbols : ℕ) [NeZero symbols] where
  state : Fin states
  tape : Tape (Fin symbols)

/-- One step, or `none` when the transition is missing. -/
def step (M : Machine states symbols) : Cfg states symbols → Option (Cfg states symbols)
  | ⟨q, T⟩ => (M.transition q T.head).map fun ⟨a, d, q'⟩ => ⟨q', (T.write a).move d⟩

/-- The start state on the all-blank tape. -/
def init : Cfg states symbols := ⟨0, Tape.mk₁ []⟩

/-- `M` halts when started in state `0` on the all-blank tape. -/
def Halts (M : Machine states symbols) : Prop := (StateTransition.eval (step M) init).Dom

/-- Build a `Machine states symbols` from a list of per-state transition rows. -/
def Machine.ofRows (rows : List (List (Option (Fin symbols × Dir × Fin states)))) :
    Machine states symbols := ⟨fun q a => (rows.getD q.val []).getD a.val none⟩

/-- A Turing machine over `symbols` tape symbols bundled with its non-zero state count. -/
structure BundledMachine (symbols : ℕ) where
  states : ℕ
  [neZeroStates : NeZero states]
  toMachine : Machine states symbols

attribute [instance] BundledMachine.neZeroStates

/-- Bundle a `Machine (states + 1) symbols` into a `BundledMachine symbols`. -/
abbrev Machine.bundle {states symbols : ℕ} (M : Machine (states + 1) symbols) :
    BundledMachine symbols := ⟨states + 1, M⟩

/-- `M` halts when started in state `0` on the all-blank tape. -/
abbrev BundledMachine.Halts {symbols : ℕ} [NeZero symbols] (M : BundledMachine symbols) : Prop :=
  ConjectureMachines.Halts M.toMachine

export BundledMachine (Halts)

namespace Machines
/-- Rows of `goldbach25`. -/ def goldbach25Rows : List (List (Option (Fin 2 × Dir × Fin 25))) :=
  load_machine_rows% "baselines/tables/goldbach_25.txt"
/-- 25-state Goldbach baseline. -/ def goldbach25 : Machine 25 2 := Machine.ofRows goldbach25Rows
/-- Rows of `goldbach24`. -/ def goldbach24Rows : List (List (Option (Fin 2 × Dir × Fin 24))) :=
  load_machine_rows% "artifacts/goldbach_24/machine.txt"
/-- 24-state Goldbach candidate. -/ def goldbach24 : Machine 24 2 := Machine.ofRows goldbach24Rows
/-- Rows of `zf432`. -/ def zf432Rows : List (List (Option (Fin 2 × Dir × Fin 432))) :=
  load_machine_rows% "baselines/tables/zf_432.txt"
/-- 432-state ZF baseline. -/ def zf432 : Machine 432 2 := Machine.ofRows zf432Rows
/-- Rows of `zf431`. -/ def zf431Rows : List (List (Option (Fin 2 × Dir × Fin 431))) :=
  load_machine_rows% "artifacts/zf_431/machine.txt"
/-- 431-state ZF candidate. -/ def zf431 : Machine 431 2 := Machine.ofRows zf431Rows
/-- Rows of `zf430`. -/ def zf430Rows : List (List (Option (Fin 2 × Dir × Fin 430))) :=
  load_machine_rows% "artifacts/zf_430/machine.txt"
/-- 430-state ZF candidate. -/ def zf430 : Machine 430 2 := Machine.ofRows zf430Rows
/-- Rows of `zf429`. -/ def zf429Rows : List (List (Option (Fin 2 × Dir × Fin 429))) :=
  load_machine_rows% "artifacts/zf_429/machine.txt"
/-- 429-state ZF candidate. -/ def zf429 : Machine 429 2 := Machine.ofRows zf429Rows
/-- Rows of `riemann744`. -/ def riemann744Rows : List (List (Option (Fin 2 × Dir × Fin 744))) :=
  load_machine_rows% "baselines/tables/riemann_744.txt"
/-- 744-state RH baseline. -/ def riemann744 : Machine 744 2 := Machine.ofRows riemann744Rows
/-- Rows of `riemann543`. -/ def riemann543Rows : List (List (Option (Fin 2 × Dir × Fin 543))) :=
  load_machine_rows% "artifacts/riemann_543/machine.txt"
/-- 543-state RH candidate. -/ def riemann543 : Machine 543 2 := Machine.ofRows riemann543Rows
end Machines

/-- The configuration `n` steps in from `init`, or `none` once `M` has halted. -/
def run (M : Machine states symbols) (n : ℕ) : Option (Cfg states symbols) :=
  (fun c => c.bind (step M))^[n] (some init)

/-- `M`, started in state `0` on the all-blank tape, has not halted within `n` steps. -/
def Runs (M : Machine states symbols) (n : ℕ) : Prop := (run M n).isSome

instance (M : Machine states symbols) (n : ℕ) : Decidable (Runs M n) :=
  inferInstanceAs (Decidable ((run M n).isSome = true))

end ConjectureMachines
