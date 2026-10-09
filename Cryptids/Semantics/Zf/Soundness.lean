/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Propositions
public import Mathlib.Tactic.Ring

/-!
# Gödel Numbering, Hilbert System, and Soundness of `zf2.nql` in Mathlib's `ZFSet`

This module formalizes the logical core of Stefan O'Rear's `zf2.nql` ZF proof enumerator:

1. **Cantor Unpairing**: the inverse `cantorUnpair` of `cantorPair` (`Cryptids.Propositions`), with
   bijection theorems `cantorUnpair_cantorPair` and `cantorPair_cantorUnpair`.
2. **Total Tarski Truth Predicate `zfHolds`**: a well-founded satisfaction relation on *all*
   natural numbers `n : ℕ` under valuations `v : ℕ → ZFSet.{u}`, with `[simp]` Tarski equations
   for every constructor and agreement with the structural `ZFFormula.Holds`.
3. **Soundness**: `zfProvable_zfHolds`, `zfProvable_sound_zfSet`, and
   `not_zfInconsistent : ¬ ZFInconsistent`, derived from Mathlib's `ZFSet.{0}` model
   (`ZFSet.ext`, `ZFSet.powerset`, `ZFSet.sUnion`, `ZFSet.sep`/`ZFSet.image` for Replacement,
   and an explicit singleton-closed witness for Infinity).
-/

@[expose] public section

namespace ConjectureMachines.Semantics.Zf

/-! ## Section 1: Basic `[simp]` Lemmas for Formula Encodings -/

@[simp]
theorem cantorPair_zero_zero : cantorPair 0 0 = 0 := rfl

@[simp]
theorem cantorPair_zero_one : cantorPair 0 1 = 1 := rfl

@[simp]
theorem zfEq_zero_zero : zfEq 0 0 = 0 := rfl

@[simp]
theorem zfMem_zero_zero : zfMem 0 0 = 1 := rfl

/-! ## Section 1b: Cantor Unpairing and Bounds -/

/-- One step along the Cantor diagonal enumeration of `ℕ × ℕ`. -/
def cantorStep (p : ℕ × ℕ) : ℕ × ℕ :=
  match p.2 with
  | 0 => (0, p.1 + 1)
  | y + 1 => (p.1 + 1, y)

/-- Inverse of `cantorPair`, defined by iterating `cantorStep` from `(0, 0)`. -/
def cantorUnpair : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | z + 1 => cantorStep (cantorUnpair z)

@[simp]
theorem cantorUnpair_zero : cantorUnpair 0 = (0, 0) := rfl

@[simp]
theorem cantorUnpair_succ (z : ℕ) : cantorUnpair (z + 1) = cantorStep (cantorUnpair z) := rfl

private theorem tri_succ (n : ℕ) :
    (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
  rw [h, Nat.add_mul_div_right _ _ (by decide : 0 < 2)]

private theorem le_tri (n : ℕ) : n ≤ n * (n + 1) / 2 := by
  cases n with
  | zero => omega
  | succ m =>
    have := tri_succ m
    omega

theorem add_le_cantorPair (x y : ℕ) : x + y ≤ cantorPair x y := by
  unfold cantorPair
  have := le_tri (x + y)
  omega

theorem le_cantorPair_left (x y : ℕ) : x ≤ cantorPair x y := by
  have := add_le_cantorPair x y
  omega

theorem le_cantorPair_right (x y : ℕ) : y ≤ cantorPair x y := by
  have := add_le_cantorPair x y
  omega

theorem lt_cantorPair_left_of_pos (x y : ℕ) (hy : 0 < y) : x < cantorPair x y := by
  have := add_le_cantorPair x y
  omega

theorem cantorPair_zero_succ (x : ℕ) : cantorPair 0 (x + 1) = cantorPair x 0 + 1 := by
  unfold cantorPair
  simp only [Nat.zero_add, Nat.add_zero]
  have := tri_succ x
  omega

theorem cantorPair_succ_left (x y : ℕ) : cantorPair (x + 1) y = cantorPair x (y + 1) + 1 := by
  unfold cantorPair
  have h1 : x + 1 + y = x + (y + 1) := by omega
  rw [h1]
  omega

theorem cantorPair_cantorStep (p : ℕ × ℕ) :
    cantorPair (cantorStep p).1 (cantorStep p).2 = cantorPair p.1 p.2 + 1 := by
  rcases p with ⟨x, _ | y⟩
  · exact cantorPair_zero_succ x
  · exact cantorPair_succ_left x y

@[simp]
theorem cantorPair_cantorUnpair (z : ℕ) :
    cantorPair (cantorUnpair z).1 (cantorUnpair z).2 = z := by
  induction z with
  | zero => rfl
  | succ z ih =>
    unfold cantorUnpair
    rw [cantorPair_cantorStep, ih]

private theorem cantorUnpair_cantorPair_aux (s : ℕ) :
    ∀ x y, x + y = s → cantorUnpair (cantorPair x y) = (x, y) := by
  induction s with
  | zero =>
    intro x y h
    obtain ⟨rfl, rfl⟩ : x = 0 ∧ y = 0 := by omega
    rfl
  | succ s ihs =>
    intro x
    induction x with
    | zero =>
      intro y hy
      obtain rfl : y = s + 1 := by omega
      rw [cantorPair_zero_succ, cantorUnpair, ihs s 0 (by omega)]
      rfl
    | succ x ihx =>
      intro y hy
      rw [cantorPair_succ_left, cantorUnpair, ihx (y + 1) (by omega)]
      rfl

@[simp]
theorem cantorUnpair_cantorPair (x y : ℕ) :
    cantorUnpair (cantorPair x y) = (x, y) :=
  cantorUnpair_cantorPair_aux (x + y) x y rfl

theorem cantorUnpair_fst_lt_of_snd_pos {n : ℕ} (h : 0 < (cantorUnpair n).2) :
    (cantorUnpair n).1 < n := by
  have h1 := lt_cantorPair_left_of_pos (cantorUnpair n).1 (cantorUnpair n).2 h
  rwa [cantorPair_cantorUnpair] at h1

theorem cantorUnpair_fst_le (m : ℕ) : (cantorUnpair m).1 ≤ m := by
  have h1 := le_cantorPair_left (cantorUnpair m).1 (cantorUnpair m).2
  rwa [cantorPair_cantorUnpair] at h1

theorem cantorUnpair_snd_le (m : ℕ) : (cantorUnpair m).2 ≤ m := by
  have h1 := le_cantorPair_right (cantorUnpair m).1 (cantorUnpair m).2
  rwa [cantorPair_cantorUnpair] at h1

/-! ## Section 1c: Total Tarski Truth Predicate on `ℕ` -/

/-- Total Tarski satisfaction predicate on Gödel numbers `n : ℕ` under valuation
`v : ℕ → ZFSet.{u}`. -/
def zfHolds (n : ℕ) (v : ℕ → ZFSet.{u}) : Prop :=
  let m := (cantorUnpair n).1
  let op := (cantorUnpair n).2
  if h0 : op = 0 then
    v (cantorUnpair m).1 = v (cantorUnpair m).2
  else if h1 : op = 1 then
    v (cantorUnpair m).1 ∈ v (cantorUnpair m).2
  else if h2 : op = 2 then
    have hm : m < n := cantorUnpair_fst_lt_of_snd_pos (by omega)
    have hp : (cantorUnpair m).1 < n := Nat.lt_of_le_of_lt (cantorUnpair_fst_le m) hm
    have hq : (cantorUnpair m).2 < n := Nat.lt_of_le_of_lt (cantorUnpair_snd_le m) hm
    zfHolds (cantorUnpair m).1 v → zfHolds (cantorUnpair m).2 v
  else if h3 : op = 3 then
    have hm : m < n := cantorUnpair_fst_lt_of_snd_pos (by omega)
    ¬ zfHolds m v
  else if h4 : op = 4 then
    have hm : m < n := cantorUnpair_fst_lt_of_snd_pos (by omega)
    have hp : (cantorUnpair m).2 < n := Nat.lt_of_le_of_lt (cantorUnpair_snd_le m) hm
    ∀ s : ZFSet.{u}, zfHolds (cantorUnpair m).2 (Function.update v (cantorUnpair m).1 s)
  else
    True
termination_by n

@[simp]
theorem zfHolds_zfEq (x y : ℕ) (v : ℕ → ZFSet.{u}) :
    zfHolds (zfEq x y) v ↔ v x = v y := by
  rw [zfHolds]
  simp [zfEq]

@[simp]
theorem zfHolds_zfMem (x y : ℕ) (v : ℕ → ZFSet.{u}) :
    zfHolds (zfMem x y) v ↔ v x ∈ v y := by
  rw [zfHolds]
  simp [zfMem]

@[simp]
theorem zfHolds_zfImp (φ ψ : ℕ) (v : ℕ → ZFSet.{u}) :
    zfHolds (zfImp φ ψ) v ↔ (zfHolds φ v → zfHolds ψ v) := by
  rw [zfHolds]
  simp [zfImp]

@[simp]
theorem zfHolds_zfNot (φ : ℕ) (v : ℕ → ZFSet.{u}) :
    zfHolds (zfNot φ) v ↔ ¬ zfHolds φ v := by
  rw [zfHolds]
  simp [zfNot]

@[simp]
theorem zfHolds_zfAll (x φ : ℕ) (v : ℕ → ZFSet.{u}) :
    zfHolds (zfAll x φ) v ↔ ∀ s : ZFSet.{u}, zfHolds φ (Function.update v x s) := by
  rw [zfHolds]
  simp [zfAll]

@[simp]
theorem zfHolds_zfEx (x φ : ℕ) (v : ℕ → ZFSet.{u}) :
    zfHolds (zfEx x φ) v ↔ ∃ s : ZFSet.{u}, zfHolds φ (Function.update v x s) := by
  simp [zfEx]

@[simp]
theorem zfHolds_zfAnd (φ ψ : ℕ) (v : ℕ → ZFSet.{u}) :
    zfHolds (zfAnd φ ψ) v ↔ (zfHolds φ v ∧ zfHolds ψ v) := by
  simp [zfAnd, Classical.not_imp]

/-! ## Section 2: Agreement of `zfHolds` with `ZFFormula.Holds` -/

open ZFFormula in
@[simp]
theorem code_ex (x : ℕ) (φ : ZFFormula) : (ex x φ).code = zfEx x φ.code := rfl

open ZFFormula in
@[simp]
theorem code_and (φ ψ : ZFFormula) : (and φ ψ).code = zfAnd φ.code ψ.code := rfl

open ZFFormula in
@[simp]
theorem holds_ex (v : ℕ → ZFSet.{u}) (x : ℕ) (φ : ZFFormula) :
    (ex x φ).Holds v ↔ ∃ s : ZFSet.{u}, φ.Holds (Function.update v x s) := by
  simp [ex, Holds]

@[simp]
theorem holds_and (v : ℕ → ZFSet.{u}) (φ ψ : ZFFormula) :
    (ZFFormula.and φ ψ).Holds v ↔ φ.Holds v ∧ ψ.Holds v := by
  simp [ZFFormula.and, ZFFormula.Holds, Classical.not_imp]

/-- `zfHolds` on the Gödel code of any `ZFFormula` agrees with `ZFFormula.Holds`. -/
@[simp]
theorem zfHolds_code (φ : ZFFormula) (v : ℕ → ZFSet.{u}) :
    zfHolds φ.code v ↔ φ.Holds v := by
  induction φ generalizing v with
  | eq x y => simp [ZFFormula.code, ZFFormula.Holds]
  | mem x y => simp [ZFFormula.code, ZFFormula.Holds]
  | imp φ ψ ihφ ihψ => simp [ZFFormula.code, ZFFormula.Holds, ihφ, ihψ]
  | not φ ihφ => simp [ZFFormula.code, ZFFormula.Holds, ihφ]
  | all x φ ihφ => simp [ZFFormula.code, ZFFormula.Holds, ihφ]

/-- The contradiction formula $v_0 \in v_0$ is refutable in Mathlib's `ZFSet.{u}` under the
empty-set valuation `fun _ => ∅`. -/
theorem not_holds_mem_zero_zero : ¬ (ZFFormula.mem 0 0).Holds (fun _ => (∅ : ZFSet.{u})) :=
  ZFSet.notMem_empty ∅

/-! ## Section 3b: Soundness of `ZFProvable` in `ZFSet` -/

attribute [local instance] Classical.allZFSetDefinable

private theorem update_rep_lhs (v : ℕ → ZFSet.{u}) (x y z s : ZFSet.{u}) :
    Function.update (Function.update (Function.update (Function.update v 3 x) 1 y) 2 z) 1 s =
      Function.update (Function.update (Function.update v 3 x) 2 z) 1 s := by
  rw [Function.update_comm (by decide : (1 : ℕ) ≠ 2), Function.update_idem]

private theorem update_rep_rhs (v : ℕ → ZFSet.{u}) (B z x s : ZFSet.{u}) :
    Function.update (Function.update (Function.update (Function.update v 1 B) 2 z) 3 x) 1 s =
      Function.update (Function.update (Function.update v 3 x) 2 z) 1 s := by
  rw [Function.update_comm (by decide : (1 : ℕ) ≠ 2),
      Function.update_comm (by decide : (1 : ℕ) ≠ 3),
      Function.update_idem,
      Function.update_comm (by decide : (2 : ℕ) ≠ 3)]

private theorem zfHolds_axRep (φ : ℕ) (v : ℕ → ZFSet.{u}) :
    zfHolds (axRep φ) v := by
  simp only [axRep, axRepRhs, zfHolds_zfImp, zfHolds_zfAll, zfHolds_zfEx,
    zfHolds_zfAnd, zfHolds_zfMem, zfHolds_zfEq, update_rep_lhs, update_rep_rhs]
  intro h
  have h' : ∀ x : ZFSet.{u}, ∃ y : ZFSet.{u}, ∀ z : ZFSet.{u},
      (∀ s : ZFSet.{u},
        zfHolds φ (Function.update (Function.update (Function.update v 3 x) 2 z) 1 s)) →
        z = y := by
    intro x
    obtain ⟨y, hy⟩ := h x
    refine ⟨y, fun z hz => ?_⟩
    have := hy z hz
    simpa using this
  let P (x z : ZFSet.{u}) : Prop :=
    ∀ s : ZFSet.{u}, zfHolds φ (Function.update (Function.update (Function.update v 3 x) 2 z) 1 s)
  let f (x : ZFSet.{u}) : ZFSet.{u} := Classical.choose (h' x)
  have hf (x z : ZFSet.{u}) (hP : P x z) : z = f x := Classical.choose_spec (h' x) z hP
  let B : ZFSet.{u} := (ZFSet.image f (v 0)).sep (fun z => ∃ x ∈ v 0, P x z)
  refine ⟨B, fun z => ?_⟩
  have hB : z ∈ B ↔ ∃ x, x ∈ v 0 ∧ P x z := by
    simp only [B, ZFSet.mem_sep, ZFSet.mem_image]
    refine ⟨fun ⟨_, hx⟩ => hx, fun ⟨x, hx0, hPxz⟩ => ⟨⟨x, hx0, (hf x z hPxz).symm⟩, x, hx0, hPxz⟩⟩
  have hv1 : Function.update (Function.update v 1 B) 2 z 2 = z := by simp
  have hv2 : Function.update (Function.update v 1 B) 2 z 1 = B := by simp
  have hv3 : ∀ x : ZFSet.{u},
      Function.update (Function.update (Function.update v 1 B) 2 z) 3 x 3 = x := by simp
  have hv0 : ∀ x : ZFSet.{u},
      Function.update (Function.update (Function.update v 1 B) 2 z) 3 x 0 = v 0 := by simp
  simp only [hv1, hv2, hv3, hv0]
  exact ⟨hB.mp, hB.mpr⟩

/-- Iterated singleton operation $n \mapsto \{\dots\{a\}\dots\}$ used to witness `axInf`. -/
def iterSingleton (a : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => a
  | n + 1 => {iterSingleton a n}

private theorem zfHolds_axInf (v : ℕ → ZFSet.{0}) :
    zfHolds axInf v := by
  simp only [axInf, axInfSingleton, zfHolds_zfEx, zfHolds_zfAnd, zfHolds_zfMem,
    zfHolds_zfAll, zfHolds_zfImp, zfHolds_zfEq]
  let W : ZFSet.{0} := ZFSet.range (iterSingleton (v 0))
  refine ⟨W, ?_, ?_⟩
  · have h0 : Function.update v 1 W 0 = v 0 := by simp
    have h1 : Function.update v 1 W 1 = W := by simp
    rw [h0, h1, ZFSet.mem_range]
    exact ⟨0, rfl⟩
  · intro x hx
    have hxW : x ∈ W := by simpa using hx
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hxW
    refine ⟨{iterSingleton (v 0) n}, ?_, ?_⟩
    · have h2 : Function.update
          (Function.update (Function.update v 1 W) 0 (iterSingleton (v 0) n)) 2
          {iterSingleton (v 0) n} 2 = {iterSingleton (v 0) n} := by simp
      have h1 : Function.update
          (Function.update (Function.update v 1 W) 0 (iterSingleton (v 0) n)) 2
          {iterSingleton (v 0) n} 1 = W := by simp
      rw [h2, h1, ZFSet.mem_range]
      exact ⟨n + 1, rfl⟩
    · intro z
      have hz1 : Function.update (Function.update (Function.update (Function.update v 1 W) 0
          (iterSingleton (v 0) n)) 2 {iterSingleton (v 0) n}) 1 z 1 = z := by simp
      have hz2 : Function.update (Function.update (Function.update (Function.update v 1 W) 0
          (iterSingleton (v 0) n)) 2 {iterSingleton (v 0) n}) 1 z 2 =
          {iterSingleton (v 0) n} := by simp
      have hz0 : Function.update (Function.update (Function.update (Function.update v 1 W) 0
          (iterSingleton (v 0) n)) 2 {iterSingleton (v 0) n}) 1 z 0 =
          iterSingleton (v 0) n := by simp
      rw [hz1, hz2, hz0, ZFSet.mem_singleton]
      exact ⟨id, id⟩

/-- Soundness of `ZFProvable` with respect to the total Tarski valuation `zfHolds` on
`ZFSet.{0}`. -/
theorem zfProvable_zfHolds {n : ℕ} (h : ZFProvable n) (v : ℕ → ZFSet.{0}) :
    zfHolds n v := by
  induction h generalizing v with
  | moot => exact (zfHolds_zfEq 0 0 v).mpr rfl
  | mp _ _ ih1 ih2 =>
    exact (zfHolds_zfImp _ _ v).mp (ih2 v) (ih1 v)
  | gen x _ ih =>
    rw [zfHolds_zfAll]
    intro s
    exact ih (Function.update v x s)
  | b1 φ ψ χ =>
    simp only [axB1, zfHolds_zfImp]
    intro h1 h2 h3
    exact h2 (h1 h3)
  | b2 φ =>
    simp only [axB2, zfHolds_zfImp, zfHolds_zfNot]
    intro h
    by_cases hφ : zfHolds φ v
    · exact hφ
    · exact h hφ
  | b3 φ ψ =>
    simp only [axB3, zfHolds_zfImp, zfHolds_zfNot]
    intro h1 h2
    exact absurd h1 h2
  | b4 x φ ψ =>
    simp only [axB4, zfHolds_zfImp, zfHolds_zfAll]
    intro h1 h2 s
    exact h1 s (h2 s)
  | b6a x y z hxz hzy =>
    simp [axB6a, hxz, hzy.symm]
  | b6b x y φ =>
    simp only [axB6b, zfHolds_zfImp, zfHolds_zfAll]
    intro h t s
    by_cases hxy : x = y
    · subst hxy
      have := h s s
      rw [Function.update_idem] at this ⊢
      exact this
    · rw [Function.update_comm (Ne.symm hxy)]
      exact h s t
  | b6c x φ =>
    simp only [axB6c, zfHolds_zfImp, zfHolds_zfEx, zfHolds_zfAll]
    rintro ⟨s, hs⟩
    have := hs (v x)
    rwa [Function.update_idem, Function.update_eq_self] at this
  | b7 x y =>
    simp only [axB7, zfHolds_zfEx, zfHolds_zfEq]
    refine ⟨v y, ?_⟩
    by_cases hxy : x = y <;> simp [hxy, Ne.symm]
  | b8a x y z =>
    simp only [axB8a, zfHolds_zfImp, zfHolds_zfEq]
    intro h1 h2
    exact h1.symm.trans h2
  | b8b x y z =>
    simp only [axB8b, zfHolds_zfImp, zfHolds_zfEq, zfHolds_zfMem]
    intro h1 h2
    rwa [← h1]
  | b8c x y z =>
    simp only [axB8c, zfHolds_zfImp, zfHolds_zfEq, zfHolds_zfMem]
    intro h1 h2
    rwa [← h1]
  | ext =>
    simp only [axExt, zfHolds_zfImp, zfHolds_zfAll, zfHolds_zfAnd, zfHolds_zfMem, zfHolds_zfEq]
    intro h
    apply ZFSet.ext
    intro z
    have hz := h z
    simpa using ⟨hz.1, hz.2⟩
  | rep φ =>
    exact zfHolds_axRep φ v
  | pow =>
    simp only [axPow, zfHolds_zfEx, zfHolds_zfAll, zfHolds_zfImp, zfHolds_zfMem]
    refine ⟨ZFSet.powerset (v 0), fun z hz => ?_⟩
    have hz' : z ∈ ZFSet.powerset (v 0) := by
      rw [ZFSet.mem_powerset]
      intro w hw
      have hw' := hz w
      simpa using hw' hw
    simpa using hz'
  | uni =>
    simp only [axUni, zfHolds_zfEx, zfHolds_zfAll, zfHolds_zfImp, zfHolds_zfAnd, zfHolds_zfMem]
    refine ⟨ZFSet.sUnion (v 0), fun z hz => ?_⟩
    rcases hz with ⟨w, hw1, hw2⟩
    have hz' : z ∈ ZFSet.sUnion (v 0) := by
      rw [ZFSet.mem_sUnion]
      exact ⟨w, by simpa using hw2, by simpa using hw1⟩
    simpa using hz'
  | inf =>
    exact zfHolds_axInf v

/-- Soundness of the `ZFProvable` Hilbert system with respect to Mathlib's `ZFSet.{0}`:
any provable well-formed formula holds under every variable assignment `v : ℕ → ZFSet.{0}`. -/
theorem zfProvable_sound_zfSet (φ : ZFFormula) (h : ZFProvable φ.code)
    (v : ℕ → ZFSet.{0}) : φ.Holds v :=
  (zfHolds_code φ v).mp (zfProvable_zfHolds h v)

/-- Relative consistency of `ZFProvable` from Mathlib's `ZFSet.{0}` model of ZFC:
`ZFInconsistent` is false assuming `zfProvable_sound_zfSet`. -/
theorem not_zfInconsistent : ¬ ZFInconsistent := by
  intro h
  have h0 : (ZFFormula.mem 0 0).Holds (fun _ => (∅ : ZFSet.{0})) :=
    zfProvable_sound_zfSet (.mem 0 0) h (fun _ => ∅)
  exact not_holds_mem_zero_zero h0

end ConjectureMachines.Semantics.Zf
