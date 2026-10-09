/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines

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

/-- Transition rows of `goldbach24` (24 states, 2 symbols). -/
def goldbach24Rows : List (List (Option (Fin 2 × Dir × Fin 24))) := [
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

/-- `goldbach24` (24 states, 2 symbols,
SHA-256 `9b8b92a609ca9ae891856957b21a4d5ff9ba4317c27835e31265a249d236b2dc`). -/
def goldbach24 : Machine 24 2 := Machine.ofRows goldbach24Rows

end ConjectureMachines.Machines
