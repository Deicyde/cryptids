/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Turing Machine Definitions

Machines with `states` states and `symbols` symbols, over Mathlib's tape. The
table sends a state and the symbol under the head to the symbol to write, the
direction to move and the state to enter, or to nothing: a missing transition
halts the machine. The step function, the tape and the notion of evaluation are
Mathlib's, so Mathlib's simulation machinery (`StateTransition.Respects`,
`StateTransition.tr_eval_dom`) applies to these machines unchanged.
-/

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

end ConjectureMachines
