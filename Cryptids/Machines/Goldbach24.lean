/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.FromFile

/-!
# 24-State Goldbach Candidate Turing Machine (`goldbach_24`)

The 24-state, 2-symbol Turing machine for Goldbach's conjecture discovered by
Maxence Faldor and Moritz Firsching using Gemini Argon (2026), obtained from `goldbach_25` via a
`+1` unary tape-encoding shift and 4 transition edits that make bootstrap state `8` unreachable:
- **Details**: `artifacts/goldbach_24/README.md`
- **Canonical table**: `artifacts/goldbach_24/machine.txt`
- **Canonical SHA-256**: `9b8b92a609ca9ae891856957b21a4d5ff9ba4317c27835e31265a249d236b2dc`
-/

@[expose] public section

namespace ConjectureMachines.Machines

open Turing

/-- Transition rows of `goldbach24` (24 states, 2 symbols), loaded from
`artifacts/goldbach_24/machine.txt`. -/
def goldbach24Rows : List (List (Option (Fin 2 × Dir × Fin 24))) :=
  load_machine_rows% "artifacts/goldbach_24/machine.txt"

/-- `goldbach24` (24 states, 2 symbols,
SHA-256 `9b8b92a609ca9ae891856957b21a4d5ff9ba4317c27835e31265a249d236b2dc`). -/
def goldbach24 : Machine 24 2 := Machine.ofRows goldbach24Rows

end ConjectureMachines.Machines
