/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.FromFile

/-!
# 431-State ZF Consistency Candidate Turing Machine (`zf_431`)

The 431-state, 2-symbol Turing machine for ZF set theory consistency discovered by
Maxence Faldor and Moritz Firsching using Gemini Argon (2026), obtained from `zf_432` via an exact
Moore merge of state `42 -> 13`:
- **Details**: `artifacts/zf_431/README.md`
- **Canonical table**: `artifacts/zf_431/machine.txt`
- **Canonical SHA-256**: `6414d9a1a4bebd72761483505a7581e936dbeb5e4790e39436080f0b0bd302ca`
-/

@[expose] public section

namespace ConjectureMachines.Machines

open Turing

/-- Transition rows of `zf431` (431 states, 2 symbols), loaded from
`artifacts/zf_431/machine.txt`. -/
def zf431Rows : List (List (Option (Fin 2 × Dir × Fin 431))) :=
  load_machine_rows% "artifacts/zf_431/machine.txt"

/-- `zf431` (431 states, 2 symbols,
SHA-256 `6414d9a1a4bebd72761483505a7581e936dbeb5e4790e39436080f0b0bd302ca`). -/
def zf431 : Machine 431 2 := Machine.ofRows zf431Rows

end ConjectureMachines.Machines
