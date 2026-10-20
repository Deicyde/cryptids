/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`.

Starting from the blank tape (`init []`), the trajectory reaches the guarded configuration family
$$C(a, b) := 0^\infty\,\mathrm{E}{>}\,(10)^a\,1^b\,0^\infty \quad (b \ge 1)$$
at $C(0, 3)$ in 7 steps, and every $C(a, b)$ with $b \ge 1$ advances in `ReachesPlus` either to
another $C(a', b')$ with $b' \ge 1$ or to a halting configuration (when $b = 2$).

## Collatz-like Acceleration Rules

```text
Consider:
C(a, b) = 0^inf E> 10^a 1^b 0^inf

C(a, b) -> C(2a+2, b-2a-2) if b > 2a+2
C(a, 1) -> C(2, 2a+2)
C(a, 2)  -> Halt
C(a, 2k) -> C((6a+2k+2)/4, (6a+2k+2)%4+1) if a >= 1 and 2 <= k <= a+1
C(a, 2k+1) -> C((6a+2k+6)/4, (6a+2k+6)%4+1) if a >= 1 and 1 <= k <= a

Start: C(0,3), reached after 7 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift Lemmas -/

/-- Rightward shift across `(10)^k` in state `E`, writing `(01)^k`. -/
private theorem shift_E_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r))
      (Cfg.headRight E (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E l
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight E (ListBlank.append [0, 1] l)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [0, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward shift across `(10)^k` in state `B`, writing `(11)^k`. -/
private theorem shift_B_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B (ListBlank.append [1, 1] l)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift across `(11)^k` in state `A`, writing `(10)^k`. -/
private theorem shift_A_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft A (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft A l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft A
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            r)
          (Cfg.headLeft A
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 0] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 0] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] r) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Leftward sweep of `(01)^k` across `1 F> 0`, producing `(11)^k` on the right. -/
private theorem shift_F_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
        (ListBlank.append [0] r))
      (Cfg.headRight F
        (ListBlank.append [1] l)
        (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append [1]
              (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)))
            (ListBlank.append [0] r))
          (Cfg.headRight F
            (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [0] (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern $A(a, b) := 0^\infty\,\mathrm{E}{>}\,(10)^a\,1^b\,0^\infty$. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .rep [1, 0] 0 (.rep [1] 1 .default) }

/-- Closed pattern set for `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .ge_const 1 1)]

/-- Configuration $A(a, b)$. -/
private def cfg_A (a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
      (ListBlank.append (([1] : List (Fin 2)) ^ b) default))

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) :=
  rfl

private theorem in_ps_A (a b : ℕ) (hb : b ≥ 1) : IsInPatternSet ps (cfg_A a b) :=
  ⟨(pat_A, .ge_const 1 1), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | _ => 0, rfl, hb⟩

/-! ## Rules for $b = 1$ and $b = 2$ -/

/-- Transition rule for $A(a, 1) \vdash^+ A(2, 2a + 2)$. -/
private theorem step_A_one (a : ℕ) :
    ReachesPlus target (cfg_A a 1) (cfg_A 2 (2 * a + 2)) := by
  unfold cfg_A
  have h1 := shift_E_right a default (ListBlank.append (([1] : List (Fin 2)) ^ 1) default)
  rw [list_pow_one] at h1 ⊢
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)
          (ListBlank.append [1] default))
        (Cfg.headRight F
          (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [0] (ListBlank.append [1] default))) := by
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := shift_F_01 a default (ListBlank.append [1] default)
  have h123 := h12.trans_star h3
  have h_ones :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append [1] (default : ListBlank (Fin 2))) =
        ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a)) default) := by
    rw [swap_1_11_pow, one_pow_two_mul]
  rw [h_ones] at h123
  have h4 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1] default)
          (ListBlank.append [0] (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a)) default))))
        (Cfg.headRight E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 2)) default))) := by
    have h_10 : (([1, 0] : List (Fin 2)) ^ 2) = [1, 0, 1, 0] := rfl
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * a + 2))
          (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * a)) default) := by
      rw [Nat.add_comm (2 * a) 2, ListBlank.append_pow_add]
      rfl
    rw [h_10, h_r]
    bb_steps
  exact h123.trans h4

/-- Halting transition rule for $A(a, 2)$. -/
private theorem step_A_two (a : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A a 2) cfg' ∧ (step target cfg').isNone := by
  have h1 := shift_E_right a default (ListBlank.append (([1] : List (Fin 2)) ^ 2) default)
  have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h_two] at h1
  refine ⟨Cfg.headRight D
    (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    default, ?_, ?_⟩
  · have h2 :
        ReachesPlus target
          (Cfg.headRight E
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)
            (ListBlank.append [1, 1] default))
          (Cfg.headRight D
            (ListBlank.append [0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
            default) := by
      bb_steps
    exact h1.trans_plus h2
  · bb_halt

/-! ## Intermediate Configuration $P(k, n, p)$ and Rules for $b \ge 3$ -/

/-- Intermediate configuration
$P(k, n, p) := 0^\infty\,(10)^k\,{<}\mathrm{A}\,(10)^n\,1^p\,0^\infty$. -/
private def cfg_P (k n p : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft A
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
      (ListBlank.append (([1] : List (Fin 2)) ^ p) default))

private theorem step_A_to_P (a d : ℕ) :
    ReachesPlus target (cfg_A a (d + 3)) (cfg_P a 0 (d + 3)) := by
  unfold cfg_A cfg_P
  have h1 := shift_E_right a default
    (ListBlank.append (([1] : List (Fin 2)) ^ (d + 3)) default)
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (d + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
    rw [Nat.add_comm d 3, ListBlank.append_pow_add]
    rfl
  rw [h_r] at h1
  rw [h_r, list_pow_zero, ListBlank.append_nil]
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))
        (Cfg.headLeft A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    bb_steps
  exact h1.trans_plus h2

private theorem cfg_P_succ_ge2 (k n p : ℕ) :
    ReachesPlus target (cfg_P (k + 1) n (p + 2)) (cfg_P k (n + 2) p) := by
  unfold cfg_P
  set l := ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default
  set r := ListBlank.append (([1] : List (Fin 2)) ^ p) default
  have h_p :
      ListBlank.append (([1] : List (Fin 2)) ^ (p + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] r := by
    rw [Nat.add_comm p 2, ListBlank.append_pow_add]
    rfl
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k, h_p]
  have h1 :
      ReachesPlus target
        (Cfg.headLeft A (ListBlank.append [0, 1] l)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1, 1] r)))
        (Cfg.headRight B (ListBlank.append [1, 1] l)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1, 1] r))) := by
    bb_steps
  have h2 := shift_B_right n (ListBlank.append [1, 1] l) (ListBlank.append [1, 1] r)
  have h12 := h1.trans_star h2
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ n) (ListBlank.append [1, 1] l) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (n + 1)) l := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_l] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (n + 1)) l)
          (ListBlank.append [1, 1] r))
        (Cfg.headLeft A
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (n + 1)) l)
          (ListBlank.append [1, 0] r)) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_A_left (n + 1) l (ListBlank.append [1, 0] r)
  have h1234 := h123.trans_star h4
  have h_r :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) (ListBlank.append [1, 0] r) =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 2)) r := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rwa [h_r] at h1234

private theorem cfg_P_zero_eq_one (k n : ℕ) :
    cfg_P k (n + 1) 0 = cfg_P k n 1 := by
  unfold cfg_P
  rw [list_pow_zero, list_pow_one, list_pow_succ', ListBlank.append_assoc]
  simp

private theorem cfg_P_succ_two (k n : ℕ) :
    ReachesPlus target (cfg_P (k + 1) n 2) (cfg_P k (n + 1) 1) := by
  have h := cfg_P_succ_ge2 k n 0
  rwa [cfg_P_zero_eq_one] at h

private theorem cfg_P_succ_one (k n : ℕ) :
    ReachesPlus target (cfg_P (k + 1) n 1) (cfg_P k (n + 1) 3) := by
  unfold cfg_P
  set l := ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k, list_pow_one]
  have h1 :
      ReachesPlus target
        (Cfg.headLeft A (ListBlank.append [0, 1] l)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1] default)))
        (Cfg.headRight B (ListBlank.append [1, 1] l)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1] default))) := by
    bb_steps
  have h2 := shift_B_right n (ListBlank.append [1, 1] l) (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ n) (ListBlank.append [1, 1] l) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (n + 1)) l := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_l] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (n + 1)) l)
          (ListBlank.append [1] default))
        (Cfg.headLeft A
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (n + 1)) l)
          (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)) := by
    have h_three : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h_three]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_A_left (n + 1) l (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)
  exact h123.trans_star h4

private theorem cfg_P_zero_ge2 (n p : ℕ) :
    ReachesPlus target (cfg_P 0 n (p + 2)) (cfg_A (n + 2) p) := by
  unfold cfg_P cfg_A
  set r := ListBlank.append (([1] : List (Fin 2)) ^ p) default
  have h_p :
      ListBlank.append (([1] : List (Fin 2)) ^ (p + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] r := by
    rw [Nat.add_comm p 2, ListBlank.append_pow_add]
    rfl
  rw [list_pow_zero, ListBlank.append_nil, h_p]
  have h1 :
      ReachesPlus target
        (Cfg.headLeft A default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1, 1] r)))
        (Cfg.headRight B (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1, 1] r))) := by
    bb_steps
  have h2 := shift_B_right n (ListBlank.append [1] default) (ListBlank.append [1, 1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ n) (ListBlank.append [1] default))
          (ListBlank.append [1, 1] r))
        (Cfg.headLeft A
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ n) (ListBlank.append [1] default))
          (ListBlank.append [1, 0] r)) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_A_left n (ListBlank.append [1] default) (ListBlank.append [1, 0] r)
  have h1234 := h123.trans_star h4
  have h_r1 :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1, 0] r) =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) r := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_r1] at h1234
  have h5 :
      ReachesPlus target
        (Cfg.headLeft A (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1)) r))
        (Cfg.headRight E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 2)) r)) := by
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) (n + 1)]
    bb_steps
  exact h1234.trans h5

private theorem cfg_A_zero_eq_one (n : ℕ) :
    cfg_A (n + 1) 0 = cfg_A n 1 := by
  unfold cfg_A
  rw [list_pow_zero, list_pow_one, list_pow_succ', ListBlank.append_assoc]
  simp

private theorem cfg_P_zero_two (n : ℕ) :
    ReachesPlus target (cfg_P 0 n 2) (cfg_A (n + 1) 1) := by
  have h := cfg_P_zero_ge2 n 0
  rwa [cfg_A_zero_eq_one] at h

private theorem cfg_P_zero_one (n : ℕ) :
    ReachesPlus target (cfg_P 0 n 1) (cfg_A (n + 1) 3) := by
  unfold cfg_P cfg_A
  rw [list_pow_zero, ListBlank.append_nil, list_pow_one]
  have h1 :
      ReachesPlus target
        (Cfg.headLeft A default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1] default)))
        (Cfg.headRight B (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1] default))) := by
    bb_steps
  have h2 := shift_B_right n (ListBlank.append [1] default) (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ n) (ListBlank.append [1] default))
          (ListBlank.append [1] default))
        (Cfg.headLeft A
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ n) (ListBlank.append [1] default))
          (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)) := by
    have h_three : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h_three]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_A_left n (ListBlank.append [1] default)
    (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headLeft A (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3) default)))
        (Cfg.headRight E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (n + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))) := by
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) n]
    bb_steps
  exact h1234.trans h5

private theorem step_P_closed (k n p : ℕ) (hp : p ≥ 1) :
    ∃ cfg', ReachesPlus target (cfg_P k n p) cfg' ∧ IsInPatternSet ps cfg' := by
  induction k generalizing n p with
  | zero =>
    rcases p with _ | _ | _ | d
    · omega
    · exact ⟨cfg_A (n + 1) 3, cfg_P_zero_one n, in_ps_A (n + 1) 3 (by decide)⟩
    · exact ⟨cfg_A (n + 1) 1, cfg_P_zero_two n, in_ps_A (n + 1) 1 (by decide)⟩
    · exact ⟨cfg_A (n + 2) (d + 1), cfg_P_zero_ge2 n (d + 1),
        in_ps_A (n + 2) (d + 1) (by omega)⟩
  | succ k ih =>
    rcases p with _ | _ | _ | d
    · omega
    · obtain ⟨cfg', h_reach, h_in⟩ := ih (n + 1) 3 (by decide)
      exact ⟨cfg', (cfg_P_succ_one k n).trans h_reach, h_in⟩
    · obtain ⟨cfg', h_reach, h_in⟩ := ih (n + 1) 1 (by decide)
      exact ⟨cfg', (cfg_P_succ_two k n).trans h_reach, h_in⟩
    · obtain ⟨cfg', h_reach, h_in⟩ := ih (n + 2) (d + 1) (by omega)
      exact ⟨cfg', (cfg_P_succ_ge2 k n (d + 1)).trans h_reach, h_in⟩

private theorem step_A_closed (a b : ℕ) (hb : b ≥ 1) :
    ∃ cfg', ReachesPlus target (cfg_A a b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | _ | d
  · omega
  · exact ⟨cfg_A 2 (2 * a + 2), step_A_one a,
      Or.inl (in_ps_A 2 (2 * a + 2) (by omega))⟩
  · obtain ⟨cfg', h_reach, h_halt⟩ := step_A_two a
    exact ⟨cfg', h_reach, Or.inr h_halt⟩
  · obtain ⟨cfg', h_reach, h_in⟩ := step_P_closed a 0 (d + 3) (by omega)
    exact ⟨cfg', (step_A_to_P a d).trans h_reach, Or.inl h_in⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_A 0 3) := by
  have h_init : ReachesPlus target (init []) (cfg_A 0 3) := by
    unfold cfg_A
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [list_pow_zero, ListBlank.append_nil, h3]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 0 3, init_reaches_start, in_ps_A 0 3 (by decide)⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_A]
  exact step_A_closed (vars 0) (vars 1) h_cond

/-- `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. -/
inductive State where
  /-- $C(a, b + 1) := 0^\infty\,\mathrm{E}{>}\,(10)^a\,1^{b+1}\,0^\infty$. -/
  | C (a b : ℕ)
  /-- $P(k, n, p + 1) := 0^\infty\,(10)^k\,{<}\mathrm{A}\,(10)^n\,1^{p+1}\,0^\infty$. -/
  | P (k n p : ℕ)

/-- Initial symbolic state $C(0, 3)$, reached after 7 raw TM steps. -/
def start : State := .C 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b =>
    Cfg.headRight SixState.E default
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))
  | .P k n p =>
    Cfg.headLeft SixState.A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append (([1] : List (Fin 2)) ^ (p + 1)) default))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C a 0 => some (.C 2 (2 * a + 1))
  | .C _ 1 => none
  | .C a (d + 2) => some (.P a 0 (d + 2))
  | .P 0 n 0 => some (.C (n + 1) 2)
  | .P 0 n 1 => some (.C (n + 1) 0)
  | .P 0 n (p + 2) => some (.C (n + 2) p)
  | .P (k + 1) n 0 => some (.P k (n + 1) 2)
  | .P (k + 1) n 1 => some (.P k (n + 1) 0)
  | .P (k + 1) n (p + 2) => some (.P k (n + 2) p)

private theorem encode_C (a b : ℕ) : encode (.C a b) = cfg_A a (b + 1) := rfl
private theorem encode_P (k n p : ℕ) : encode (.P k n p) = cfg_P k n (p + 1) := rfl

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro (⟨a, b⟩ | ⟨k, n, p⟩) s' hnext
    · rcases b with _ | _ | d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_A_one a
      · simp [next] at hnext
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_A_to_P a d
    · rcases k with _ | k
      · rcases p with _ | _ | p
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact cfg_P_zero_one n
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact cfg_P_zero_two n
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact cfg_P_zero_ge2 n (p + 1)
      · rcases p with _ | _ | p
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact cfg_P_succ_one k n
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact cfg_P_succ_two k n
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact cfg_P_succ_ge2 k n (p + 1)
  step_none := by
    rintro (⟨a, b⟩ | ⟨k, n, p⟩) hnext
    · rcases b with _ | _ | d
      · simp [next] at hnext
      · obtain ⟨cfg', hp, hh⟩ := step_A_two a
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
    · rcases k with _ | k <;> rcases p with _ | _ | p <;> simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
