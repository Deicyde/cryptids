/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Turing Machine Definitions

Machines with `states` states and `symbols` symbols, over Mathlib's tape. The
table sends a state and the symbol under the head to the symbol to write, the
direction to move and the state to enter, or to nothing: a missing transition
halts the machine. The step function, the tape and the notion of evaluation are
Mathlib's, so Mathlib's simulation machinery (`StateTransition.Respects`,
`StateTransition.tr_eval_dom`) applies to these machines unchanged.
-/

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

/-- The configuration `n` steps in from `init`, or `none` once `M` has halted. -/
def run (M : Machine states symbols) (n : ℕ) : Option (Cfg states symbols) :=
  (fun c => c.bind (step M))^[n] (some init)

/-- `M`, started in state `0` on the all-blank tape, has not halted within `n`
steps. -/
def Runs (M : Machine states symbols) (n : ℕ) : Prop := (run M n).isSome

/-- `Runs M n` is a computation, so `decide` settles it by running `M` for `n`
steps; the recursion depth of the elaborator, not the kernel, is what bounds
`n`. -/
instance (M : Machine states symbols) (n : ℕ) : Decidable (Runs M n) :=
  inferInstanceAs (Decidable ((run M n).isSome = true))

/-- A machine from its rows, one per state and one entry per symbol; an entry
the rows do not have halts. -/
def Machine.ofRows (rows : List (List (Option (Fin symbols × Dir × Fin states)))) :
    Machine states symbols :=
  ⟨fun q a => (rows.getD q.val []).getD a.val none⟩

/-- A Turing machine over `symbols` tape symbols with its non-zero state count bundled as a
structure field, allowing machines with different numbers of states to share the same type
`BundledMachine symbols`. -/
structure BundledMachine (symbols : ℕ) where
  states : ℕ
  [neZeroStates : NeZero states]
  toMachine : Machine states symbols

attribute [instance] BundledMachine.neZeroStates

/-- Bundle a `Machine states symbols` into a `BundledMachine symbols`. -/
abbrev Machine.bundle {states symbols : ℕ} [NeZero states] (M : Machine states symbols) :
    BundledMachine symbols :=
  ⟨states, M⟩

/-- `M` halts when started in state `0` on the all-blank tape. -/
abbrev BundledMachine.Halts {symbols : ℕ} [NeZero symbols] (M : BundledMachine symbols) : Prop :=
  ConjectureMachines.Halts M.toMachine

export BundledMachine (Halts)

end ConjectureMachines
