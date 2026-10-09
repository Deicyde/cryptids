/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.FromFile

/-!
# 432-State ZF Consistency Reference Turing Machine (`zf_432`)

The 432-state, 2-symbol Turing machine for Zermelo–Fraenkel set theory consistency
constructed by Andrew Wade (2025), compiling Stefan O'Rear's Tarski-style minimal first-order ZF
encoding (`zf2.nql`):
- **Author**: Andrew Wade (`ajwade/turing_machine_explorer`, `zf2.py` / `zf_432_wade.tm`), based on
  Stefan O'Rear's `zf2.nql` (`sorear/metamath-turing-machines`).
- **Upstream source**: `baselines/sources/zf_432_wade.tm`
- **Canonical table**: `baselines/tables/zf_432.txt`
- **Canonical SHA-256**: `cb9ffd320f7360b5e0e49181a6201286b408d1f8c168d61fafc51d1ca8b86702`
-/

@[expose] public section

namespace ConjectureMachines.Machines

open Turing

/-- Transition rows of `zf432` (432 states, 2 symbols), loaded from
`baselines/tables/zf_432.txt`. -/
def zf432Rows : List (List (Option (Fin 2 × Dir × Fin 432))) :=
  load_machine_rows% "baselines/tables/zf_432.txt"

/-- `zf432` (432 states, 2 symbols,
SHA-256 `cb9ffd320f7360b5e0e49181a6201286b408d1f8c168d61fafc51d1ca8b86702`). -/
def zf432 : Machine 432 2 := Machine.ofRows zf432Rows

end ConjectureMachines.Machines
