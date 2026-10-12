/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Zf380
public import Cryptids.Semantics.Zf393.Backend
public import Cryptids.Semantics.Zf393.Program

/-!
# End-to-End Semantics of `zf_393` and `zf_380` (`Cryptids.Semantics.Zf393`)

Combines:
1. [`Cryptids.Zf393`](./../Zf393.lean), [`Cryptids.Zf380`](./../Zf380.lean), and
   [`Cryptids.Semantics.Zf393.Backend`](./Zf393/Backend.lean): the 39,773-step bootstrap,
   moving `00` register-selection invariant, self-cleaning register gadgets, and exact simulation
   equivalence `ConjectureMachines.Halts zf393 ↔ Zf393RegHalts`; and
2. [`Cryptids.Semantics.Zf393.Program`](./Zf393/Program.lean): evaluation of all 324 control-DAG
   states (`69..392`), the 125-step `main()` spine (`99..223`), and soundness & completeness of
   `zf393MainStep` against O'Rear's `ZFProvable` (`Zf393RegHalts ↔ ZFInconsistent`).

Together with `Cryptids.Semantics.Zf.not_zfInconsistent` (soundness of `ZFProvable` in Mathlib's
`ZFSet.{0}`) and `ConjectureMachines.Zf380.candidate_equivalent`, this establishes:
- `halts_zf393_iff_zfInconsistent : ConjectureMachines.Halts zf393 ↔ ZFInconsistent`
- `not_halts_zf393 : ¬ ConjectureMachines.Halts zf393`
- `halts_candidate_iff_zfInconsistent : Halts ConjectureMachines.Zf380.candidate ↔ ZFInconsistent`
- `not_halts_candidate : ¬ Halts ConjectureMachines.Zf380.candidate`.
-/

@[expose] public section

namespace ConjectureMachines.Zf393

open Turing ConjectureMachines ConjectureMachines.Semantics.Zf

/-- **Main Theorem for `zf_393`**: Andrew Wade's 393-state Turing machine `zf393` halts from the
blank tape if and only if O'Rear's `zf2.nql` Hilbert system proves `v₀ ∈ v₀` (`ZFInconsistent`). -/
theorem halts_zf393_iff_zfInconsistent :
    ConjectureMachines.Halts zf393 ↔ ZFInconsistent :=
  Layer1.halts_zf393_iff_zf393RegHalts.trans Layer2.zf393RegHalts_iff_zfInconsistent

/-- **Unconditional Non-Halting of `zf_393`**: Since `ZFProvable` is sound in Mathlib's
`ZFSet.{0}` (`not_zfInconsistent`), `zf393` never halts on the blank tape. -/
theorem not_halts_zf393 : ¬ ConjectureMachines.Halts zf393 := by
  rw [halts_zf393_iff_zfInconsistent]
  exact not_zfInconsistent

end ConjectureMachines.Zf393

namespace ConjectureMachines.Zf380.Semantics

open ConjectureMachines ConjectureMachines.Semantics.Zf

/-- The 380-state record machine `zf_380` (`ConjectureMachines.Zf380.candidate`) halts on the
blank tape if and only if O'Rear's `zf2.nql` Hilbert system proves `v₀ ∈ v₀` (`ZFInconsistent`). -/
theorem halts_candidate_iff_zfInconsistent :
    Halts ConjectureMachines.Zf380.candidate ↔ ZFInconsistent :=
  ConjectureMachines.Zf380.candidate_equivalent.trans
    ConjectureMachines.Zf393.halts_zf393_iff_zfInconsistent

/-- Since `ZFProvable` is sound in Mathlib's `ZFSet.{0}` (`not_zfInconsistent`), the 380-state
record machine `zf_380` (`ConjectureMachines.Zf380.candidate`) never halts on the blank tape. -/
theorem not_halts_candidate : ¬ Halts ConjectureMachines.Zf380.candidate := by
  rw [halts_candidate_iff_zfInconsistent]
  exact not_zfInconsistent

end ConjectureMachines.Zf380.Semantics

end
