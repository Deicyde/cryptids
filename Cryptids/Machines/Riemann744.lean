/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.FromFile

/-!
# 744-State Riemann Hypothesis Reference Turing Machine (`riemann_744`)

The 744-state, 2-symbol Turing machine for the Riemann Hypothesis constructed by
Yuri Matiyasevich, Martin Davis, and Stefan O'Rear (2016), compiled from `riemann.nql` to test
Matiyasevich's harmonic-LCM inequality equivalent to the Riemann Hypothesis:
- **Authors**: Yuri Matiyasevich, Martin Davis, and Stefan O'Rear
  (`sorear/metamath-turing-machines`, `riemann.nql` / `riemann_744_sorear.tm`).
- **Upstream source**: `baselines/sources/riemann_744_sorear.tm`
- **Canonical table**: `baselines/tables/riemann_744.txt`
- **Canonical SHA-256**: `4f629ed5be1715747f3d467dbb35bded647a25dc740a80b5208c14f65d7d5f44`
-/

@[expose] public section

namespace ConjectureMachines.Machines

open Turing

/-- Transition rows of `riemann744` (744 states, 2 symbols), loaded from
`baselines/tables/riemann_744.txt`. -/
def riemann744Rows : List (List (Option (Fin 2 × Dir × Fin 744))) :=
  load_machine_rows% "baselines/tables/riemann_744.txt"

/-- `riemann744` (744 states, 2 symbols,
SHA-256 `4f629ed5be1715747f3d467dbb35bded647a25dc740a80b5208c14f65d7d5f44`). -/
def riemann744 : Machine 744 2 := Machine.ofRows riemann744Rows

end ConjectureMachines.Machines
