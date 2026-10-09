/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.SetTheory.ZFC.Basic
public import Mathlib.Tactic.Ring

/-!
# Gödel Numbering, Hilbert System, and Soundness of `zf2.nql` in Mathlib's `ZFSet`

This module formalizes the logical core of Stefan O'Rear's `zf2.nql` ZF proof enumerator:

1. **Cantor Pairing & Gödel Numbering**: `cantorPair`, its inverse `cantorUnpair`
   (`cantorUnpair_cantorPair`, `cantorPair_cantorUnpair`), and the formula constructors
   `zfEq`, `zfMem`, `zfImp`, `zfNot`, `zfAll` (with abbreviations `zfEx`, `zfAnd`).
2. **Total Tarski Truth Predicate `zfHolds`**: a well-founded satisfaction relation on *all*
   natural numbers `n : ℕ` under valuations `v : ℕ → ZFSet.{u}`, with `[simp]` Tarski equations
   for every constructor and agreement with the structural `ZFFormula.Holds`.
3. **Hilbert System `ZFProvable`**: the 11 logical axiom schemes (`axB1..axB8c`), the 5
   set-theoretic schemes (`axExt`, `axRep`, `axPow`, `axUni`, `axInf`), and the rules `mp`/`gen`;
   `ZFInconsistent := ZFProvable (zfMem 0 0)`.
4. **Soundness**: `zfProvable_zfHolds`, `zfProvable_sound_zfSet`, and
   `not_zfInconsistent : ¬ ZFInconsistent`, derived from Mathlib's `ZFSet.{0}` model
   (`ZFSet.ext`, `ZFSet.powerset`, `ZFSet.sUnion`, `ZFSet.sep`/`ZFSet.image` for Replacement,
   and an explicit singleton-closed witness for Infinity).
-/

@[expose] public section

namespace ConjectureMachines.Semantics.Zf

/-! ## Section 1: Cantor Pairing and Gödel Numbering of ZF Formulas -/

/-- The Cantor pairing function $\operatorname{cantorPair}(x, y) = x + \frac{(x+y)(x+y+1)}{2}$
computed by `builtin_pair` in `zf2.nql`. -/
def cantorPair (x y : ℕ) : ℕ :=
  x + (x + y) * (x + y + 1) / 2

@[simp]
theorem cantorPair_zero_zero : cantorPair 0 0 = 0 := rfl

@[simp]
theorem cantorPair_zero_one : cantorPair 0 1 = 1 := rfl

/-- Gödel number of the atomic equality formula $v_x = v_y$ (`weq` in `zf2.nql`). -/
def zfEq (x y : ℕ) : ℕ :=
  cantorPair (cantorPair x y) 0

/-- Gödel number of the atomic membership formula $v_x \in v_y$ (`wel` in `zf2.nql`). -/
def zfMem (x y : ℕ) : ℕ :=
  cantorPair (cantorPair x y) 1

/-- Gödel number of the implication formula $\varphi \to \psi$ (`wim` in `zf2.nql`). -/
def zfImp (φ ψ : ℕ) : ℕ :=
  cantorPair (cantorPair φ ψ) 2

/-- Gödel number of the negation formula $\neg \varphi$ (`wn` in `zf2.nql`). -/
def zfNot (φ : ℕ) : ℕ :=
  cantorPair φ 3

/-- Gödel number of the universal formula $\forall v_x\, \varphi$ (`wal` in `zf2.nql`). -/
def zfAll (x φ : ℕ) : ℕ :=
  cantorPair (cantorPair x φ) 4

/-- Gödel number of the existential abbreviation
$\exists v_x\, \varphi \equiv \neg \forall v_x \neg \varphi$ (`wex` in `zf2.nql`). -/
def zfEx (x φ : ℕ) : ℕ :=
  zfNot (zfAll x (zfNot φ))

/-- Gödel number of the conjunction abbreviation
$\varphi \land \psi \equiv \neg (\varphi \to \neg \psi)$ (`wa` in `zf2.nql`). -/
def zfAnd (φ ψ : ℕ) : ℕ :=
  zfNot (zfImp φ (zfNot ψ))

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

/-! ## Section 2: Axiom Schemes and Hilbert System of `zf2.nql` -/

/-- Axiom scheme `B1` (`axiomcode = 3`):
$(\varphi \to \psi) \to ((\psi \to \chi) \to (\varphi \to \chi))$. -/
def axB1 (φ ψ χ : ℕ) : ℕ :=
  zfImp (zfImp φ ψ) (zfImp (zfImp ψ χ) (zfImp φ χ))

/-- Axiom scheme `B2` (`axiomcode = 4`): $(\neg \varphi \to \varphi) \to \varphi$. -/
def axB2 (φ : ℕ) : ℕ :=
  zfImp (zfImp (zfNot φ) φ) φ

/-- Axiom scheme `B3` (`axiomcode = 5`): $\varphi \to (\neg \varphi \to \psi)$. -/
def axB3 (φ ψ : ℕ) : ℕ :=
  zfImp φ (zfImp (zfNot φ) ψ)

/-- Axiom scheme `B4` (`axiomcode = 6`):
$\forall v_x (\varphi \to \psi) \to (\forall v_x \varphi \to \forall v_x \psi)$. -/
def axB4 (x φ ψ : ℕ) : ℕ :=
  zfImp (zfAll x (zfImp φ ψ)) (zfImp (zfAll x φ) (zfAll x ψ))

/-- Axiom scheme `B6a` (`axiomcode = 7`, subject to $x \ne z \land z \ne y$):
$(v_x = v_y \to \forall v_z\, v_x = v_y) \land (v_x \in v_y \to \forall v_z\, v_x \in v_y)$. -/
def axB6a (x y z : ℕ) : ℕ :=
  zfAnd (zfImp (zfEq x y) (zfAll z (zfEq x y))) (zfImp (zfMem x y) (zfAll z (zfMem x y)))

/-- Axiom scheme `B6b` (`axiomcode = 8`):
$\forall v_x \forall v_y \varphi \to \forall v_y \forall v_x \varphi$. -/
def axB6b (x y φ : ℕ) : ℕ :=
  zfImp (zfAll x (zfAll y φ)) (zfAll y (zfAll x φ))

/-- Axiom scheme `B6c` (`axiomcode = 9`): $\exists v_x \forall v_x \varphi \to \varphi$. -/
def axB6c (x φ : ℕ) : ℕ :=
  zfImp (zfEx x (zfAll x φ)) φ

/-- Axiom scheme `B7` (`axiomcode = 10`): $\exists v_x\, v_x = v_y$. -/
def axB7 (x y : ℕ) : ℕ :=
  zfEx x (zfEq x y)

/-- Axiom scheme `B8a` (`axiomcode = 11`): $v_x = v_y \to (v_x = v_z \to v_y = v_z)$. -/
def axB8a (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfEq x z) (zfEq y z))

/-- Axiom scheme `B8b` (`axiomcode = 12`): $v_x = v_y \to (v_x \in v_z \to v_y \in v_z)$. -/
def axB8b (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfMem x z) (zfMem y z))

/-- Axiom scheme `B8c` (`axiomcode = 13`): $v_x = v_y \to (v_z \in v_x \to v_z \in v_y)$. -/
def axB8c (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfMem z x) (zfMem z y))

/-- Axiom of Extensionality (`EXT`, `axiomcode = 14`):
$\forall v_2 ((v_2 \in v_0 \to v_2 \in v_1) \land (v_2 \in v_1 \to v_2 \in v_0)) \to v_0 = v_1$. -/
def axExt : ℕ :=
  zfImp
    (zfAll 2 (zfAnd (zfImp (zfMem 2 0) (zfMem 2 1)) (zfImp (zfMem 2 1) (zfMem 2 0))))
    (zfEq 0 1)

/-- Helper formula $\exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi)$ used in `axRep`. -/
def axRepRhs (φ : ℕ) : ℕ :=
  zfEx 3 (zfAnd (zfMem 3 0) (zfAll 1 φ))

/-- Axiom scheme of Replacement (`REP`, `axiomcode = 15`):
$\forall v_3 \exists v_1 \forall v_2 (\forall v_1 \varphi \to v_2 = v_1) \to
  \exists v_1 \forall v_2 ((v_2 \in v_1 \to \exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi))
    \land (\exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi) \to v_2 \in v_1))$. -/
def axRep (φ : ℕ) : ℕ :=
  zfImp
    (zfAll 3 (zfEx 1 (zfAll 2 (zfImp (zfAll 1 φ) (zfEq 2 1)))))
    (zfEx 1 (zfAll 2
      (zfAnd (zfImp (zfMem 2 1) (axRepRhs φ)) (zfImp (axRepRhs φ) (zfMem 2 1)))))

/-- Axiom of Power Set (`POW`, `axiomcode = 16`):
$\exists v_1 \forall v_2 (\forall v_3 (v_3 \in v_2 \to v_3 \in v_0) \to v_2 \in v_1)$. -/
def axPow : ℕ :=
  zfEx 1 (zfAll 2 (zfImp (zfAll 3 (zfImp (zfMem 3 2) (zfMem 3 0))) (zfMem 2 1)))

/-- Axiom of Union (`UNI`, `axiomcode = 17`):
$\exists v_1 \forall v_2 (\exists v_3 (v_2 \in v_3 \land v_3 \in v_0) \to v_2 \in v_1)$. -/
def axUni : ℕ :=
  zfEx 1 (zfAll 2 (zfImp (zfEx 3 (zfAnd (zfMem 2 3) (zfMem 3 0))) (zfMem 2 1)))

/-- Helper singleton-characterization formula
$\forall v_1 ((v_1 \in v_2 \to v_1 = v_0) \land (v_1 = v_0 \to v_1 \in v_2))$ used in `axInf`. -/
def axInfSingleton : ℕ :=
  zfAll 1 (zfAnd (zfImp (zfMem 1 2) (zfEq 1 0)) (zfImp (zfEq 1 0) (zfMem 1 2)))

/-- Axiom of Infinity (`INF`, `axiomcode > 17`):
$\exists v_1 (v_0 \in v_1 \land \forall v_0 (v_0 \in v_1 \to
  \exists v_2 (v_2 \in v_1 \land \forall v_1 (v_1 \in v_2 \leftrightarrow v_1 = v_0))))$. -/
def axInf : ℕ :=
  zfEx 1
    (zfAnd (zfMem 0 1)
      (zfAll 0 (zfImp (zfMem 0 1) (zfEx 2 (zfAnd (zfMem 2 1) axInfSingleton)))))

/-- The inductive provability predicate `ZFProvable φ` of O'Rear's `zf2.nql` Hilbert system
for Zermelo–Fraenkel set theory. -/
inductive ZFProvable : ℕ → Prop where
  | moot : ZFProvable (zfEq 0 0)
  | mp {φ ψ : ℕ} : ZFProvable φ → ZFProvable (zfImp φ ψ) → ZFProvable ψ
  | gen (x : ℕ) {φ : ℕ} : ZFProvable φ → ZFProvable (zfAll x φ)
  | b1 (φ ψ χ : ℕ) : ZFProvable (axB1 φ ψ χ)
  | b2 (φ : ℕ) : ZFProvable (axB2 φ)
  | b3 (φ ψ : ℕ) : ZFProvable (axB3 φ ψ)
  | b4 (x φ ψ : ℕ) : ZFProvable (axB4 x φ ψ)
  | b6a (x y z : ℕ) (hxz : x ≠ z) (hzy : z ≠ y) : ZFProvable (axB6a x y z)
  | b6b (x y φ : ℕ) : ZFProvable (axB6b x y φ)
  | b6c (x φ : ℕ) : ZFProvable (axB6c x φ)
  | b7 (x y : ℕ) : ZFProvable (axB7 x y)
  | b8a (x y z : ℕ) : ZFProvable (axB8a x y z)
  | b8b (x y z : ℕ) : ZFProvable (axB8b x y z)
  | b8c (x y z : ℕ) : ZFProvable (axB8c x y z)
  | ext : ZFProvable axExt
  | rep (φ : ℕ) : ZFProvable (axRep φ)
  | pow : ZFProvable axPow
  | uni : ZFProvable axUni
  | inf : ZFProvable axInf

/-- ZF set theory is inconsistent if the contradiction formula $v_0 \in v_0$ (`zfMem 0 0 = 1`)
is provable in `ZFProvable`. -/
def ZFInconsistent : Prop :=
  ZFProvable (zfMem 0 0)

/-! ## Section 3: First-Order Syntax and Interpretation in Mathlib's `ZFSet` -/

/-- Well-formed formulas of first-order set theory with variables indexed by `ℕ`. -/
inductive ZFFormula : Type where
  | eq (x y : ℕ) : ZFFormula
  | mem (x y : ℕ) : ZFFormula
  | imp (φ ψ : ZFFormula) : ZFFormula
  | not (φ : ZFFormula) : ZFFormula
  | all (x : ℕ) (φ : ZFFormula) : ZFFormula
  deriving DecidableEq, Repr

namespace ZFFormula

/-- Existential quantification abbreviation
$\exists v_x\, \varphi \equiv \neg \forall v_x \neg \varphi$. -/
def ex (x : ℕ) (φ : ZFFormula) : ZFFormula :=
  .not (.all x (.not φ))

/-- Conjunction abbreviation $\varphi \land \psi \equiv \neg (\varphi \to \neg \psi)$. -/
def and (φ ψ : ZFFormula) : ZFFormula :=
  .not (.imp φ (.not ψ))

/-- The Gödel number of a `ZFFormula`, matching `zf2.nql`. -/
def code : ZFFormula → ℕ
  | .eq x y => zfEq x y
  | .mem x y => zfMem x y
  | .imp φ ψ => zfImp φ.code ψ.code
  | .not φ => zfNot φ.code
  | .all x φ => zfAll x φ.code

@[simp]
theorem code_ex (x : ℕ) (φ : ZFFormula) : (ex x φ).code = zfEx x φ.code := rfl

@[simp]
theorem code_and (φ ψ : ZFFormula) : (and φ ψ).code = zfAnd φ.code ψ.code := rfl

/-- Tarski satisfaction of a `ZFFormula` in Mathlib's cumulative hierarchy `ZFSet.{u}`
under a variable assignment `v : ℕ → ZFSet.{u}`. -/
def Holds (v : ℕ → ZFSet.{u}) : ZFFormula → Prop
  | .eq x y => v x = v y
  | .mem x y => v x ∈ v y
  | .imp φ ψ => φ.Holds v → ψ.Holds v
  | .not φ => ¬ φ.Holds v
  | .all x φ => ∀ s : ZFSet.{u}, φ.Holds (Function.update v x s)

@[simp]
theorem holds_ex (v : ℕ → ZFSet.{u}) (x : ℕ) (φ : ZFFormula) :
    (ex x φ).Holds v ↔ ∃ s : ZFSet.{u}, φ.Holds (Function.update v x s) := by
  simp [ex, Holds]

@[simp]
theorem holds_and (v : ℕ → ZFSet.{u}) (φ ψ : ZFFormula) :
    (and φ ψ).Holds v ↔ φ.Holds v ∧ ψ.Holds v := by
  simp [and, Holds, Classical.not_imp]

/-- `zfHolds` on the Gödel code of any `ZFFormula` agrees with `ZFFormula.Holds`. -/
@[simp]
theorem zfHolds_code (φ : ZFFormula) (v : ℕ → ZFSet.{u}) :
    zfHolds φ.code v ↔ φ.Holds v := by
  induction φ generalizing v with
  | eq x y => simp [code, Holds]
  | mem x y => simp [code, Holds]
  | imp φ ψ ihφ ihψ => simp [code, Holds, ihφ, ihψ]
  | not φ ihφ => simp [code, Holds, ihφ]
  | all x φ ihφ => simp [code, Holds, ihφ]

/-- The contradiction formula $v_0 \in v_0$ is refutable in Mathlib's `ZFSet.{u}` under the
empty-set valuation `fun _ => ∅`. -/
theorem not_holds_mem_zero_zero : ¬ (ZFFormula.mem 0 0).Holds (fun _ => (∅ : ZFSet.{u})) :=
  ZFSet.notMem_empty ∅

end ZFFormula

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
      rwa [Function.update_idem] at this ⊢
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
  (ZFFormula.zfHolds_code φ v).mp (zfProvable_zfHolds h v)

/-- Relative consistency of `ZFProvable` from Mathlib's `ZFSet.{0}` model of ZFC:
`ZFInconsistent` is false assuming `zfProvable_sound_zfSet`. -/
theorem not_zfInconsistent : ¬ ZFInconsistent := by
  intro h
  have h0 : (ZFFormula.mem 0 0).Holds (fun _ => (∅ : ZFSet.{0})) :=
    zfProvable_sound_zfSet (.mem 0 0) h (fun _ => ∅)
  exact ZFFormula.not_holds_mem_zero_zero h0

end ConjectureMachines.Semantics.Zf
