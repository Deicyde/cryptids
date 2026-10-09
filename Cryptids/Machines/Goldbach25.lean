/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.FromFile

/-!
# 25-State Goldbach Reference Turing Machine (`goldbach_25`)

The 25-state, 2-symbol Turing machine for Goldbach's conjecture constructed by
Andrew Yao and Yijun Leng (2024):
- **Authors**: Andrew Yao and Yijun Leng (`lengyijun/goldbach_tm`, `bbchallenge` Cryptids wiki).
- **Upstream source**: `baselines/sources/goldbach_25_bbchallenge.txt`
- **Canonical table**: `baselines/tables/goldbach_25.txt`
- **Canonical SHA-256**: `da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67`
-/

@[expose] public section

namespace ConjectureMachines.Machines

open Turing

/-- Transition rows of `goldbach25` (25 states, 2 symbols), loaded from
`baselines/tables/goldbach_25.txt`. -/
def goldbach25Rows : List (List (Option (Fin 2 × Dir × Fin 25))) :=
  load_machine_rows% "baselines/tables/goldbach_25.txt"

/-- `goldbach25` (25 states, 2 symbols,
SHA-256 `da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67`). -/
def goldbach25 : Machine 25 2 := Machine.ofRows goldbach25Rows

end ConjectureMachines.Machines
