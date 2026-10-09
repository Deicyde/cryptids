/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.FromFile

/-!
# 430-State ZF Consistency Candidate Turing Machine (`zf_430`)

The 430-state, 2-symbol Turing machine for ZF set theory consistency discovered by
Maxence Faldor and Moritz Firsching using Gemini Argon (2026), obtained from `zf_432` via Moore
merge (`42 -> 13`) and reachable head-symbol merge (`95 -> 331`):
- **Details**: `artifacts/zf_430/README.md`
- **Canonical table**: `artifacts/zf_430/machine.txt`
- **Canonical SHA-256**: `9a4829d0f084177b045612e444b6cd63070168a55d7b582e1f34b10b3daca26c`
-/

@[expose] public section

namespace ConjectureMachines.Machines

open Turing

/-- Transition rows of `zf430` (430 states, 2 symbols), loaded from
`artifacts/zf_430/machine.txt`. -/
def zf430Rows : List (List (Option (Fin 2 × Dir × Fin 430))) :=
  load_machine_rows% "artifacts/zf_430/machine.txt"

/-- `zf430` (430 states, 2 symbols,
SHA-256 `9a4829d0f084177b045612e444b6cd63070168a55d7b582e1f34b10b3daca26c`). -/
def zf430 : Machine 430 2 := Machine.ofRows zf430Rows

end ConjectureMachines.Machines
