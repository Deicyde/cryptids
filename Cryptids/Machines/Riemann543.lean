/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.FromFile

/-!
# 543-State Riemann Hypothesis Candidate Turing Machine (`riemann_543`)

The 543-state, 2-symbol Turing machine for the Riemann Hypothesis discovered by
Maxence Faldor and Moritz Firsching using Gemini Argon (2026), obtained from `riemann_744` via a
25-cell window invariant (`m0Nat`/`m1Nat`), pass-bounce macro-step elimination (`140` bounces), and
`52` multi-step `SyncCountdown` chains:
- **Details**: `artifacts/riemann_543/README.md`
- **Canonical table**: `artifacts/riemann_543/machine.txt`
- **Canonical SHA-256**: `14c7d827a8ef5ff7671f4642fe31d956c4880a0ce8270c74286b453313f4824e`
-/

@[expose] public section

namespace ConjectureMachines.Machines

open Turing

/-- Transition rows of `riemann543` (543 states, 2 symbols), loaded from
`artifacts/riemann_543/machine.txt`. -/
def riemann543Rows : List (List (Option (Fin 2 × Dir × Fin 543))) :=
  load_machine_rows% "artifacts/riemann_543/machine.txt"

/-- `riemann543` (543 states, 2 symbols,
SHA-256 `14c7d827a8ef5ff7671f4642fe31d956c4880a0ce8270c74286b453313f4824e`). -/
def riemann543 : Machine 543 2 := Machine.ofRows riemann543Rows

end ConjectureMachines.Machines
