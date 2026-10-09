/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.FromFile

/-!
# 429-State ZF Consistency Candidate Turing Machine (`zf_429`)

The 429-state, 2-symbol Turing machine for ZF set theory consistency discovered by
Maxence Faldor and Moritz Firsching using Gemini Argon (2026), obtained from `zf_432` via Moore
merge (`42 -> 13`), head-symbol merge (`95 -> 331`), and 4-cell window contextual split
(`91 -> {46, 93, 94}`):
- **Details**: `artifacts/zf_429/README.md`
- **Canonical table**: `artifacts/zf_429/machine.txt`
- **Canonical SHA-256**: `041919e91a6a5cb2afee60ecdf97975a57811c0c8e0cff52c771d66501f7f730`
-/

@[expose] public section

namespace ConjectureMachines.Machines

open Turing

/-- Transition rows of `zf429` (429 states, 2 symbols), loaded from
`artifacts/zf_429/machine.txt`. -/
def zf429Rows : List (List (Option (Fin 2 × Dir × Fin 429))) :=
  load_machine_rows% "artifacts/zf_429/machine.txt"

/-- `zf429` (429 states, 2 symbols,
SHA-256 `041919e91a6a5cb2afee60ecdf97975a57811c0c8e0cff52c771d66501f7f730`). -/
def zf429 : Machine 429 2 := Machine.ofRows zf429Rows

end ConjectureMachines.Machines
