/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines

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

/-- Transition rows of `goldbach25` (25 states, 2 symbols). -/
def goldbach25Rows : List (List (Option (Fin 2 × Dir × Fin 25))) := [
  [some (1, .right, 1), some (1, .right, 3)],
  [some (1, .left, 2), some (1, .right, 1)],
  [some (0, .right, 0), some (1, .left, 2)],
  [some (0, .left, 16), some (1, .right, 4)],
  [some (0, .left, 5), some (1, .right, 6)],
  [some (0, .left, 2), some (1, .left, 5)],
  [some (0, .left, 5), some (0, .left, 7)],
  [some (1, .left, 16), some (1, .left, 8)],
  [some (0, .right, 9), some (0, .left, 8)],
  [some (1, .right, 10), some (0, .left, 9)],
  [some (0, .right, 11), some (0, .right, 18)],
  [some (1, .right, 11), some (0, .right, 12)],
  [some (1, .right, 13), some (1, .right, 12)],
  [some (0, .left, 14), some (0, .left, 20)],
  [some (0, .left, 15), some (1, .left, 14)],
  [some (1, .right, 7), some (1, .left, 23)],
  [some (1, .left, 17), some (1, .left, 16)],
  [some (0, .right, 10), some (0, .left, 19)],
  [some (1, .left, 17), some (1, .right, 18)],
  [none, some (1, .right, 2)],
  [some (1, .left, 21), some (1, .left, 20)],
  [some (0, .left, 22), some (0, .left, 9)],
  [some (0, .right, 10), some (0, .left, 22)],
  [some (1, .right, 24), some (1, .left, 23)],
  [some (1, .right, 4), some (1, .right, 24)]]

/-- `goldbach25` (25 states, 2 symbols,
SHA-256 `da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67`). -/
def goldbach25 : Machine 25 2 := Machine.ofRows goldbach25Rows

end ConjectureMachines.Machines
