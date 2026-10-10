/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Zf393.Backend
public import Cryptids.Semantics.Zf393.Program

/-!
# End-to-End Semantics of Wade's 393-State ZF Machine (`Cryptids.Semantics.Zf393`)

Combines:
1. [`Cryptids.Zf393`](./../Zf393.lean) and
   [`Cryptids.Semantics.Zf393.Backend`](./Zf393/Backend.lean): the 39,773-step bootstrap,
   moving `00` register-selection invariant, self-cleaning register gadgets, and exact simulation
   equivalence `ConjectureMachines.Halts zf393 ↔ Layer1.Zf393RegHalts`; and
2. [`Cryptids.Semantics.Zf393.Program`](./Zf393/Program.lean): evaluation of all 324 control-DAG
   states (`69..392`), the 125-step `main()` spine (`99..223`), and soundness & completeness of
   `zf393MainStep` against O'Rear's `ZFProvable` (`Layer2.Zf393RegHalts ↔ ZFInconsistent`).

Together with `Cryptids.Semantics.Zf.not_zfInconsistent` (soundness of `ZFProvable` in Mathlib's
`ZFSet.{0}`), this establishes both:
- `halts_zf393_iff_zfInconsistent : ConjectureMachines.Halts zf393 ↔ ZFInconsistent`
- `not_halts_zf393 : ¬ ConjectureMachines.Halts zf393`.
-/

@[expose] public section

namespace ConjectureMachines.Zf393

open Turing ConjectureMachines ConjectureMachines.Semantics.Zf

set_option maxRecDepth 200000

/-- Isomorphism between the identical `Layer1.TreeOutcome` and `Layer2.TreeOutcome` types. -/
def toL2Outcome : Layer1.TreeOutcome → Layer2.TreeOutcome
  | .halt q w r => .halt q w r
  | .jumpLeft q w r => .jumpLeft q w r
  | .regLeaf q w r => .regLeaf q w r
  | .outOfFuel => .outOfFuel

theorem layer1_zf393Trans_eq_layer2 (q : Fin 393) (a : Fin 2) :
    zf393Trans q a = Layer2.zf393Trans q a := by
  revert q a; decide

theorem layer1_walkTape_eq_layer2 (q : Fin 393) (walked rem : List (Fin 2)) :
    toL2Outcome (Layer1.walkTape q walked rem) = Layer2.walkTape q walked rem := by
  induction rem generalizing q walked with
  | nil => rfl
  | cons b bs ih =>
    unfold Layer1.walkTape Layer2.walkTape
    rw [layer1_zf393Trans_eq_layer2]
    rcases Layer2.zf393Trans q b with _ | ⟨w, d, q'⟩
    · rfl
    · cases d with
      | left =>
        dsimp only
        split <;> rfl
      | right =>
        dsimp only
        split
        · have hl : Layer1.isLeafState q' = Layer2.isLeafState q' := rfl
          rw [hl]
          split
          · rfl
          · exact ih q' (walked ++ [w])
        · rfl

/-- Bijection between `Layer1.Zf393RegCfg` and `Layer2.Zf393RegCfg`. -/
def toL2Cfg (c : Layer1.Zf393RegCfg) : Layer2.Zf393RegCfg :=
  ⟨c.ip, c.regs⟩

theorem toL2Cfg_step (c : Layer1.Zf393RegCfg) :
    Option.map toL2Cfg (Layer1.zf393RegStep c) = Layer2.zf393RegStep (toL2Cfg c) := by
  unfold Layer1.zf393RegStep Layer2.zf393RegStep toL2Cfg
  have hw := layer1_walkTape_eq_layer2 99 [] (c.ip ++ List.replicate 10 0)
  rw [← hw]
  rcases Layer1.walkTape 99 [] (c.ip ++ List.replicate 10 0) with
    ⟨q, w, r⟩ | ⟨q, w, r⟩ | ⟨q, w, r⟩ | _
  · rfl
  · dsimp only [toL2Outcome]
    have hpb : ∀ k, Layer1.popBreakRev k w.reverse = Layer2.popBreakRev k w.reverse := by
      intro k
      induction w.reverse generalizing k with
      | nil => rfl
      | cons x xs ih =>
        unfold Layer1.popBreakRev Layer2.popBreakRev
        rcases ConjectureMachines.Riemann543.Layer1.fin2_cases x with rfl | rfl
        · cases k with
          | zero => rfl
          | succ k' => exact ih k'
        · exact ih k
    have hpc : ∀ k, Layer1.popContinueRev k w.reverse = Layer2.popContinueRev k w.reverse := by
      intro k
      induction w.reverse generalizing k with
      | nil => rfl
      | cons x xs ih =>
        unfold Layer1.popContinueRev Layer2.popContinueRev
        rcases ConjectureMachines.Riemann543.Layer1.fin2_cases x with rfl | rfl
        · exact ih k
        · cases k with
          | zero => rfl
          | succ k' => exact ih k'
    simp only [hpb, hpc]
    split <;> simp_all
  · dsimp only [toL2Outcome]
    have hlr : Layer1.leafReg q = Layer2.leafReg q := rfl
    have hli : Layer1.isLeafInc q = Layer2.isLeafInc q := rfl
    have hpb : ∀ k, Layer1.popBreakRev k w.reverse = Layer2.popBreakRev k w.reverse := by
      intro k
      induction w.reverse generalizing k with
      | nil => rfl
      | cons x xs ih =>
        unfold Layer1.popBreakRev Layer2.popBreakRev
        rcases ConjectureMachines.Riemann543.Layer1.fin2_cases x with rfl | rfl
        · cases k with
          | zero => rfl
          | succ k' => exact ih k'
        · exact ih k
    have hret : Layer1.retStack w = Layer2.retStack w := by
      unfold Layer1.retStack Layer2.retStack
      rw [hpb]
    rw [hlr, hli, hret, hpb]
    split
    · rfl
    · split <;> rfl
  · rfl

theorem toL2Cfg_nSteps (n : ℕ) (c : Layer1.Zf393RegCfg) :
    Option.map toL2Cfg (Layer1.zf393RegNSteps n c) =
      Layer2.zf393RegNSteps n (toL2Cfg c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [Layer1.zf393RegNSteps, Layer2.zf393RegNSteps]
    rw [← toL2Cfg_step c]
    cases Layer1.zf393RegStep c with
    | none => rfl
    | some c' => exact ih c'

theorem layer1_regHalts_iff_layer2_regHalts :
    Layer1.Zf393RegHalts ↔ Layer2.Zf393RegHalts := by
  constructor
  · rintro ⟨n, c, hn, hst⟩
    have hn2 := toL2Cfg_nSteps n Layer1.zf393RegInit
    rw [hn] at hn2
    have hst2 := toL2Cfg_step c
    rw [hst] at hst2
    exact ⟨n, toL2Cfg c, hn2.symm, hst2.symm⟩
  · rintro ⟨n, c2, hn2, hst2⟩
    have hn1 := toL2Cfg_nSteps n Layer1.zf393RegInit
    change _ = Layer2.zf393RegNSteps n Layer2.zf393RegInit at hn1
    rw [hn2] at hn1
    cases h : Layer1.zf393RegNSteps n Layer1.zf393RegInit with
    | none => rw [h] at hn1; cases hn1
    | some c1 =>
      rw [h] at hn1
      injection hn1 with hc
      have hst1 := toL2Cfg_step c1
      rw [hc, hst2] at hst1
      cases hs : Layer1.zf393RegStep c1 with
      | none => exact ⟨n, c1, h, hs⟩
      | some c1' => rw [hs] at hst1; cases hst1

/-- **Main Theorem for `zf_393`**: Andrew Wade's 393-state Turing machine `zf393` halts from the
blank tape if and only if O'Rear's `zf2.nql` Hilbert system proves `v₀ ∈ v₀` (`ZFInconsistent`). -/
theorem halts_zf393_iff_zfInconsistent :
    ConjectureMachines.Halts zf393 ↔ ZFInconsistent :=
  Layer1.halts_zf393_iff_zf393RegHalts.trans
    (layer1_regHalts_iff_layer2_regHalts.trans Layer2.zf393RegHalts_iff_zfInconsistent)

/-- **Unconditional Non-Halting of `zf_393`**: Since `ZFProvable` is sound in Mathlib's
`ZFSet.{0}` (`not_zfInconsistent`), `zf393` never halts on the blank tape. -/
theorem not_halts_zf393 : ¬ ConjectureMachines.Halts zf393 := by
  rw [halts_zf393_iff_zfInconsistent]
  exact not_zfInconsistent

end ConjectureMachines.Zf393

end
