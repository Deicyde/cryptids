/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`.

Starting from the blank tape (`init []`), the trajectory begins immediately in the canonical
configuration family
$$A(a, b, c, d) := 0^\infty\,1^a\,(10)^b\,\mathrm{A}{>}\,(01)^c\,1^d\,0^\infty$$
at $A(0, 0, 0, 0)$, and every member configuration advances in `ReachesPlus` either to another
member of the pattern set or to a halting configuration (when $a = 0, c = 0, d = b + 2$).

## Collatz-like Acceleration Rules

```text
Consider:
A(a, b, c, d) = 0^inf 1^a 10^b A> 01^c 1^d 0^inf

A(a, b, c, d) -> A(a, b+1, c-1, d) if c > 0
A(a, b, 0, 0) -> A(a+1, 0, 0, 2b+2)
A(a, b, 0, d) -> A(a-3, b+2, 0, d-1) if d > 0 and a >= 3
A(2, b, 0, d) -> A(0, 0, b+1, d-1) if d > 0
A(1, b, 0, d) -> A(1, 1, b+1, d-1) if d > 0 and b > 0
A(1, 0, 0, d) -> A(0, 0, 0, d+2) if d > 0
A(0, 0, 0, 1) -> A(0, 0, 2, 5)
A(0, b, 0, 1) -> A(0, 0, 2, 2b+1) if b > 0
A(0, b, 0, d) -> A(3d-4, 1, 2, 2b-2d+3) if d >= 2 and b >= d-1
A(0, b, 0, b+3) -> A(3b+2, 0, 0, 6)
A(0, b, 0, b+4) -> A(3b+4, 0, 0, 4)
A(0, b, 0, d) -> A(3b+3, 2, 0, d-b-5) if d >= b+5
A(0, b, 0, b+2) -> Halt

Start: A(0, 0, 0, 0), already present on the initial blank tape
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private theorem default_eq_append_00 :
    (default : ListBlank (Fin 2)) = ListBlank.append [0, 0] default := by
  simp

private theorem shift_A_01_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [0, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [0, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_B_10_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B (ListBlank.append [1, 0] l)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 0] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

private theorem shift_D_01_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft D (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft D l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft D
            (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l))
            r)
          (Cfg.headLeft D
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 0] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 0] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] r) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

private theorem shift_D_10_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft D (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft D l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft D
            (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l))
            r)
          (Cfg.headLeft D
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r := by
      have h11 : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
      rw [h11, ← ListBlank.append_pow_add]
      have h_eq : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [h_eq]
    rwa [h_pow_l, h_pow_r] at h3

private theorem shift_A_10_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.append [1] r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight A
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.append [1, 1] r)) =
          ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) (ListBlank.append [1] r) := by
      have h11 : ListBlank.append [1] (ListBlank.append [1, 1] r) =
          ListBlank.append (([1] : List (Fin 2)) ^ 2) (ListBlank.append [1] r) := rfl
      rw [h11, ← ListBlank.append_pow_add]
      have h_eq : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [h_eq]
    rwa [h_pow_l, h_pow_r] at h3

/-- Canonical tape pattern
$A(a, b, c, d) := 0^\infty\,1^a\,(10)^b\,\mathrm{A}{>}\,(01)^c\,1^d\,0^\infty$. -/
private def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 1 (.rep [1] 0 .default)
    head := some SixState.A
    right := .rep [0, 1] 2 (.rep [1] 3 .default) }

/-- Closed pattern set for `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .rep [0, 1] 1 (.rep [1] 0 .default)
      head := some SixState.A
      right := .rep [0, 1] 2 (.rep [1] 3 .default) }, .true)]

/-- Configuration $A(a, b, c, d)$. -/
private def cfg_A (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
      (ListBlank.append (([1] : List (Fin 2)) ^ d) default))

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) (vars 2) (vars 3) :=
  rfl

private theorem in_ps_A (a b c d : ℕ) : IsInPatternSet ps (cfg_A a b c d) :=
  ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0, rfl, trivial⟩

/-! ## Rules 1–8 -/

private theorem rule_1 (a b c d : ℕ) :
    ReachesPlus target (cfg_A a b (c + 1) d) (cfg_A a (b + 1) c d) := by
  unfold cfg_A
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) c,
    ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) b]
  bb_steps

private theorem rule_2 (a b : ℕ) :
    ReachesPlus target (cfg_A a b 0 0) (cfg_A (a + 1) 0 0 (2 * b + 2)) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          default)
        (Cfg.headRight A
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [1] (ListBlank.append [1] default))) := by
    bb_steps
  have h_l :
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)) =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default) := by
    rw [← append_10_pow_one, ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
  rw [h_l] at h1
  have h2 := shift_A_10_left b
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * b))
        (ListBlank.append [1] (ListBlank.append [1] default)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 2)) default := by
    change ListBlank.append (([1] : List (Fin 2)) ^ (2 * b))
      (ListBlank.append (([1] : List (Fin 2)) ^ 2) default) = _
    rw [← ListBlank.append_pow_add]
  rwa [h_r] at h12

private theorem rule_3 (a b d : ℕ) :
    ReachesPlus target (cfg_A (a + 3) b 0 (d + 1)) (cfg_A a (b + 2) 0 d) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))
        (Cfg.headLeft D
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    bb_steps
  have h2 := shift_D_01_left b
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h12 := h1.trans_star h2
  have h_a3 :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    rw [Nat.add_comm a 3, ListBlank.append_pow_add]
    rfl
  rw [h_a3, append_10_pow_one] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
        (Cfg.headRight A
          (ListBlank.append [0, 1, 0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_A_01_right b
    (ListBlank.append [0, 1, 0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ d) default)
  have h1234 := h123.trans_star h4
  have h_b2 :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [0, 1, 0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    change ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2) _) = _
    rw [← ListBlank.append_pow_add]
  rwa [h_b2] at h1234

private theorem rule_4 (b d : ℕ) :
    ReachesPlus target (cfg_A 2 b 0 (d + 1)) (cfg_A 0 0 (b + 1) d) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h2_ones : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h2_ones, ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [1, 1] default))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))
        (Cfg.headLeft D
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) (ListBlank.append [1, 1] default))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    bb_steps
  have h2 := shift_D_01_left b
    (ListBlank.append [1, 1] default)
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
        (Cfg.headRight A default
          (ListBlank.append [0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
              (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))) := by
    bb_steps
  have h123 := h12.trans h3
  rwa [append_zero_10_pow_one_succ] at h123

private theorem rule_5 (b d : ℕ) :
    ReachesPlus target (cfg_A 1 (b + 1) 0 (d + 1)) (cfg_A 1 1 (b + 2) d) := by
  unfold cfg_A
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1)) (ListBlank.append [1] default))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))
        (Cfg.headLeft D
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1)) (ListBlank.append [1] default))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    bb_steps
  have h2 := shift_D_01_left (b + 1)
    (ListBlank.append [1] default)
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h12 := h1.trans_star h2
  rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) b] at h12
  set R := ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h3 :
      ReachesPlus target
        (Cfg.headLeft D (ListBlank.append [1] default) (ListBlank.append [1, 0] R))
        (Cfg.headRight A
          (ListBlank.append [0, 1] (ListBlank.append [1] default))
          (ListBlank.append [0, 1] (ListBlank.append [0] R))) := by
    bb_steps
  have h123 := h12.trans h3
  have h_r :
      ListBlank.append [0, 1] (ListBlank.append [0] R) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
    dsimp only [R]
    rw [append_zero_10_pow_one_succ, ← ListBlank.append_pow_succ]
  rwa [h_r] at h123

private theorem rule_6 (d : ℕ) :
    ReachesPlus target (cfg_A 1 0 0 (d + 1)) (cfg_A 0 0 0 (d + 3)) := by
  unfold cfg_A
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
  have h_d3 :
      ListBlank.append (([1] : List (Fin 2)) ^ (d + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
    rw [Nat.add_comm d 3, ListBlank.append_pow_add]
    rfl
  rw [h_d3]
  bb_steps

private theorem rule_7 :
    ReachesPlus target (cfg_A 0 0 0 1) (cfg_A 0 0 2 5) := by
  unfold cfg_A
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  have h2 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
  have h5 : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
  rw [h2, h5]
  bb_steps

private theorem rule_8 (b : ℕ) :
    ReachesPlus target (cfg_A 0 (b + 1) 0 1) (cfg_A 0 0 2 (2 * b + 3)) := by
  unfold cfg_A
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1)) default)
          (ListBlank.append [1] default))
        (Cfg.headLeft D
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1)) default)
          (ListBlank.append [1] default)) := by
    bb_steps
  have h2 := shift_D_01_left (b + 1) default (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) b] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headLeft D default
          (ListBlank.append [1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) (ListBlank.append [1] default))))
        (Cfg.headRight B
          (ListBlank.append [0, 1, 1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) (ListBlank.append [1] default))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_B_10_right b
    (ListBlank.append [0, 1, 1, 1] default)
    (ListBlank.append [1] default)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ b) (ListBlank.append [0, 1, 1, 1] default))
          (ListBlank.append [1] default))
        (Cfg.headLeft D
          (ListBlank.append [1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
              (ListBlank.append [0, 1, 1, 1] default)))
          (ListBlank.append [1, 1] default)) := by
    bb_steps
  have h12345 := h1234.trans h5
  rw [← ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) b] at h12345
  have h6 := shift_D_10_left (b + 1)
    (ListBlank.append [0, 1, 1, 1] default)
    (ListBlank.append [1, 1] default)
  have h123456 := h12345.trans_star h6
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * (b + 1))) (ListBlank.append [1, 1] default) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 3)) default) := by
    have h11 : ListBlank.append [1, 1] (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ 2) default := rfl
    rw [h11, ← ListBlank.append_pow_add]
    have h_eq : 2 * (b + 1) + 2 = (2 * b + 3) + 1 := by omega
    rw [h_eq, ListBlank.append_pow_succ]
  rw [h_r] at h123456
  have h7 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append [0, 1, 1, 1] default)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 3)) default)))
        (Cfg.headRight A default
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * b + 3)) default))) := by
    have h01_2 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
    rw [h01_2]
    bb_steps
  exact h123456.trans h7

/-! ## Rules 9 and 13 (via `cfg_Bounce`) -/

private def cfg_Bounce (a b d : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
    (ListBlank.append [0, 0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))

private theorem to_bounce (b d : ℕ) :
    ReachesPlus target (cfg_A 0 b 0 (d + 1)) (cfg_Bounce 0 b (d + 1)) := by
  unfold cfg_A cfg_Bounce
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))
        (Cfg.headLeft D
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    bb_steps
  have h2 := shift_D_01_left b default
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))
        (Cfg.headRight A default
          (ListBlank.append [0, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b)
              (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default))))) := by
    bb_steps
  exact h12.trans h3

private theorem bounce_step (a b k : ℕ) :
    ReachesStar target
      (cfg_Bounce a (b + 2) (k + 2))
      (cfg_Bounce (a + 3) (b + 1) (k + 1)) := by
  unfold cfg_Bounce
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (k + 1),
    append_10_pow_one (b + 2),
    ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (b + 1)]
  set R₁ := ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1))
    (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) default)
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
          (ListBlank.append [0, 0] (ListBlank.append [1] (ListBlank.append [0, 1] R₁))))
        (Cfg.headRight A
          (ListBlank.append [0, 0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          R₁) := by
    bb_steps
  have h2 := shift_A_01_right (b + 1)
    (ListBlank.append [0, 0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) default)
  have h12 := h1.trans_star h2
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) k] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1))
            (ListBlank.append [0, 0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default)))
        (Cfg.headLeft D
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1))
            (ListBlank.append [0, 0, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_D_01_left (b + 1)
    (ListBlank.append [0, 0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) default))
  have h1234 := h123.trans_star h4
  have h_l :
      ListBlank.append [0, 0, 1, 1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2))) =
        ListBlank.append [0, 0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default) := by
    rw [Nat.add_comm a 3, ListBlank.append_pow_add]
    rfl
  rw [h_l, ← ListBlank.append_pow_succ ([1] : List (Fin 2)) k] at h1234
  have h5 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) default)))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
          (ListBlank.append [0, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (b + 1))
              (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) default)))) := by
    bb_steps
  exact (h1234.trans h5).to_star

private theorem bounce_loop (n a b d : ℕ) (hb : b ≥ 1) (hd : d ≥ 1) :
    ReachesStar target (cfg_Bounce a (b + n) (d + n)) (cfg_Bounce (a + 3 * n) b d) := by
  induction n generalizing a with
  | zero =>
    have ha : a + 3 * 0 = a := by omega
    rw [Nat.add_zero, Nat.add_zero, ha]
  | succ n ih =>
    have hb_eq : b + (n + 1) = (b + n - 1) + 2 := by omega
    have hd_eq : d + (n + 1) = (d + n - 1) + 2 := by omega
    have hb_eq' : (b + n - 1) + 1 = b + n := by omega
    have hd_eq' : (d + n - 1) + 1 = d + n := by omega
    have h1 := bounce_step a (b + n - 1) (d + n - 1)
    rw [← hb_eq, ← hd_eq, hb_eq', hd_eq'] at h1
    have h2 := ih (a + 3)
    have ha_eq : a + 3 + 3 * n = a + 3 * (n + 1) := by omega
    rw [ha_eq] at h2
    exact h1.trans h2

private theorem bounce_halt_0 (a : ℕ) :
    ∃ cfg', ReachesStar target (cfg_Bounce a 0 2) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_Bounce
  simp only [list_pow_zero, ListBlank.append_nil]
  have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h2]
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    default, ?_, ?_⟩
  · have h_step :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
            (ListBlank.append [0, 0] (ListBlank.append [1, 1] default)))
          (Cfg.headRight F
            (ListBlank.append [1, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
            default) := by
      bb_steps
    exact h_step.to_star
  · bb_halt

private theorem bounce_halt_1 (a : ℕ) :
    ∃ cfg', ReachesStar target (cfg_Bounce a 1 3) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_Bounce
  simp only [list_pow_one]
  have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
  rw [h3]
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 1, 1, 1, 1, 1, 1]
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
    default, ?_, ?_⟩
  · have h_step :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
            (ListBlank.append [0, 0]
              (ListBlank.append [1, 0] (ListBlank.append [1, 1, 1] default))))
          (Cfg.headRight F
            (ListBlank.append [1, 1, 1, 1, 1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
            default) := by
      bb_steps
    exact h_step.to_star
  · bb_halt

private theorem rule_13 (b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A 0 b 0 (b + 2)) cfg' ∧ (step target cfg').isNone := by
  have h_init := to_bounce b (b + 1)
  rcases b with _ | b'
  · obtain ⟨cfg', h_star, h_halt⟩ := bounce_halt_0 0
    exact ⟨cfg', h_init.trans_star h_star, h_halt⟩
  · have h_loop := bounce_loop b' 0 1 3 (by decide) (by decide)
    have hb1 : 1 + b' = b' + 1 := by omega
    have hb3 : 3 + b' = b' + 3 := by omega
    rw [hb1, hb3] at h_loop
    obtain ⟨cfg', h_star, h_halt⟩ := bounce_halt_1 (0 + 3 * b')
    exact ⟨cfg', (h_init.trans_star h_loop).trans_star h_star, h_halt⟩

private theorem bounce_phase1a (a m : ℕ) :
    ReachesStar target (cfg_Bounce a (m + 1) 2) (cfg_Bounce (a + 3) (m + 1) 0) := by
  unfold cfg_Bounce
  simp only [list_pow_zero, ListBlank.append_nil]
  have h2_ones : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h2_ones, ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) m]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
          (ListBlank.append [0, 0]
            (ListBlank.append [1, 0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ m) (ListBlank.append [1, 1] default)))))
        (Cfg.headRight B
          (ListBlank.append [0, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ m) (ListBlank.append [1, 1] default))) := by
    bb_steps
  have h_a3 :
      ListBlank.append [0, 1, 1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ a) (default : ListBlank (Fin 2))) =
        ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default) := by
    rw [Nat.add_comm a 3, ListBlank.append_pow_add]
    rfl
  rw [h_a3] at h1
  have h2 := shift_B_10_right m
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
    (ListBlank.append [1, 1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ m)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [1, 1] default))
        (Cfg.headLeft D
          (ListBlank.append [0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ m)
              (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))))
          (ListBlank.append [1] default)) := by
    bb_steps
  have h123 := h12.trans h3
  have h_l :
      ListBlank.append [0]
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ m)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2))))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)) := by
    rw [← append_01_pow_zero]
    rfl
  rw [h_l] at h123
  have h4 := shift_D_01_left m
    (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
    (ListBlank.append [1] default)
  have h1234 := h123.trans_star h4
  have h_r :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ m)
        (ListBlank.append [1] (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ m) default) := by
    have h_10 : ListBlank.append [1] (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 0] default := by simp
    rw [h_10, ListBlank.append_pow_comm ([1, 0] : List (Fin 2)) m default]
  rw [h_r] at h1234
  have h5 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
          (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ m) default)))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
          (ListBlank.append [0, 0]
            (ListBlank.append [1, 0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ m) default)))) := by
    bb_steps
  exact (h1234.trans h5).to_star

private theorem bounce_phase1b (a m : ℕ) :
    ReachesStar target (cfg_Bounce (a + 3) (m + 1) 0) (cfg_A (a + 5) 1 0 (2 * (m + 1))) := by
  unfold cfg_Bounce cfg_A
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) m]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
          (ListBlank.append [0, 0]
            (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ m) default))))
        (Cfg.headRight B
          (ListBlank.append [0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ m) default)) := by
    bb_steps
  have h_l :
      ListBlank.append [0, 1, 1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2))) =
        ListBlank.append [0, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) default) := by
    have h_eq : a + 5 = 2 + (a + 3) := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (a + 3)]
    rfl
  rw [h_l] at h1
  have h2 := shift_B_10_right m
    (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) default))
    default
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ m)
            (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) default)))
          default)
        (Cfg.headRight A
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ m)
            (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) default)))
          (ListBlank.append [1] (ListBlank.append [1] default))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_A_10_left m
    (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 5)) default))
    (ListBlank.append [1] default)
  have h1234 := h123.trans_star h4
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * m))
        (ListBlank.append [1] (ListBlank.append [1] (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (m + 1))) default := by
    change ListBlank.append (([1] : List (Fin 2)) ^ (2 * m))
      (ListBlank.append (([1] : List (Fin 2)) ^ 2) default) = _
    rw [← ListBlank.append_pow_add]
    have h_eq : 2 * m + 2 = 2 * (m + 1) := by omega
    rw [h_eq]
  rw [h_r] at h1234
  exact h1234.to_star

private theorem step_c0_10_to_12 (a d : ℕ) :
    ReachesStar target (cfg_A (a + 3) 1 0 (d + 1)) (cfg_A a 1 2 d) := by
  unfold cfg_A
  simp only [list_pow_zero, list_pow_one, ListBlank.append_nil]
  have h_a3 :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default) := by
    rw [Nat.add_comm a 3, ListBlank.append_pow_add]
    rfl
  have h01_2 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
  rw [h_a3, h01_2, ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
  have h_step :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0, 1]
            (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))
        (Cfg.headRight A
          (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ d) default))) := by
    bb_steps
  exact h_step.to_star

private theorem rule_9 (b d : ℕ) (h : b ≥ d + 1) :
    ReachesPlus target (cfg_A 0 b 0 (d + 2)) (cfg_A (3 * d + 2) 1 2 (2 * b - 2 * d - 1)) := by
  have h_init := to_bounce b (d + 1)
  set m := b - d - 1
  have hb_eq : (m + 1) + d = b := by omega
  have hd_eq : 2 + d = d + 2 := by omega
  have h_loop := bounce_loop d 0 (m + 1) 2 (by omega) (by decide)
  rw [hb_eq, hd_eq, Nat.zero_add] at h_loop
  have h1a := bounce_phase1a (3 * d) m
  have h1b := bounce_phase1b (3 * d) m
  have h_end := step_c0_10_to_12 (3 * d + 2) (2 * m + 1)
  have ha_eq : (3 * d + 2) + 3 = 3 * d + 5 := by omega
  have hm_eq : (2 * m + 1) + 1 = 2 * (m + 1) := by omega
  have hm_final : 2 * m + 1 = 2 * b - 2 * d - 1 := by omega
  rw [ha_eq, hm_eq, hm_final] at h_end
  exact (((h_init.trans_star h_loop).trans_star h1a).trans_star h1b).trans_star h_end

/-! ## Rules 10, 11, and 12 (Underflow Bounce) -/

private theorem underflow_step (b k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft D
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1))
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ k) l)))
        (ListBlank.append [1, 1] r))
      (Cfg.headLeft D
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) l)))
        (ListBlank.append [1] r)) := by
  rcases b with _ | b'
  · simp only [Nat.zero_add, list_pow_zero, list_pow_one, ListBlank.append_nil]
    have h_k3 :
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) l =
          ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) := by
      rw [Nat.add_comm k 3, ListBlank.append_pow_add]
      rfl
    rw [h_k3]
    have h_step :
        ReachesPlus target
          (Cfg.headLeft D
            (ListBlank.append [0, 1]
              (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ k) l)))
            (ListBlank.append [1, 1] r))
          (Cfg.headLeft D
            (ListBlank.append [0, 0]
              (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l)))
            (ListBlank.append [1] r)) := by
      bb_steps
    exact h_step.to_star
  · have h1 := shift_D_01_left (b' + 2)
      (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
      (ListBlank.append [1, 1] r)
    have h_10_2 :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ (b' + 2)) (ListBlank.append [1, 1] r) =
          ListBlank.append [1, 0, 1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b') (ListBlank.append [1, 1] r)) := by
      rw [Nat.add_comm b' 2, ListBlank.append_pow_add]
      rfl
    rw [h_10_2] at h1
    have h2 :
        ReachesPlus target
          (Cfg.headLeft D
            (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1, 0, 1, 0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ b') (ListBlank.append [1, 1] r))))
          (Cfg.headRight B
            (ListBlank.append [1]
              (ListBlank.append [0, 0]
                (ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))))
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b') (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h12 := h1.trans_plus h2
    have h_k3 :
        ListBlank.append [1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) l := by
      rw [Nat.add_comm k 3, ListBlank.append_pow_add]
      rfl
    rw [h_k3] at h12
    have h3 := shift_B_10_right b'
      (ListBlank.append [1]
        (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) l)))
      (ListBlank.append [1, 1] r)
    have h123 := h12.trans_star h3
    have h4 :
        ReachesPlus target
          (Cfg.headRight B
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ b')
              (ListBlank.append [1]
                (ListBlank.append [0, 0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) l))))
            (ListBlank.append [1, 1] r))
          (Cfg.headLeft D
            (ListBlank.append [0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ b')
                (ListBlank.append [1]
                  (ListBlank.append [0, 0]
                    (ListBlank.append (([1] : List (Fin 2)) ^ (k + 3)) l)))))
            (ListBlank.append [1] r)) := by
      bb_steps
    have h1234 := h123.trans h4
    rw [append_zero_10_pow_one_succ] at h1234
    exact h1234.to_star

private theorem underflow_loop (b k d : ℕ) (l : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft D
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ k) l)))
        (ListBlank.append (([1] : List (Fin 2)) ^ (d + b + 1)) default))
      (Cfg.headLeft D
        (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 3 * b)) l))
        (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)) := by
  induction b generalizing k with
  | zero =>
    have hk : k + 3 * 0 = k := by omega
    have hd : d + 0 + 1 = d + 1 := by omega
    simp only [list_pow_zero, ListBlank.append_nil, hk, hd]
    exact ReachesStar.refl _ _
  | succ b ih =>
    have hd_split :
        ListBlank.append (([1] : List (Fin 2)) ^ (d + (b + 1) + 1)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (d + b)) default) := by
      have h_eq : d + (b + 1) + 1 = 2 + (d + b) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [hd_split]
    have h1 := underflow_step b k l (ListBlank.append (([1] : List (Fin 2)) ^ (d + b)) default)
    have h_r :
        ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (d + b)) (default : ListBlank (Fin 2))) =
          ListBlank.append (([1] : List (Fin 2)) ^ (d + b + 1)) default := by
      rw [← ListBlank.append_pow_succ]
    rw [h_r] at h1
    have h2 := ih (k + 3)
    have hk_eq : k + 3 + 3 * b = k + 3 * (b + 1) := by omega
    rw [hk_eq] at h2
    exact h1.trans h2

private theorem to_underflow (b d : ℕ) :
    ReachesPlus target
      (cfg_A 0 b 0 (d + 1))
      (Cfg.headLeft D
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))
        (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil, ← default_eq_append_00]
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
  bb_steps

private theorem rule_10 (b : ℕ) :
    ReachesPlus target (cfg_A 0 b 0 (b + 3)) (cfg_A (3 * b + 2) 0 0 6) := by
  have h1 := to_underflow b (b + 2)
  have h2 := underflow_loop b 0 2 default
  have hb_eq : 2 + b + 1 = b + 3 := by omega
  rw [hb_eq, Nat.zero_add] at h2
  have h12 := h1.trans_star h2
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h3_ones : (([1] : List (Fin 2)) ^ (2 + 1)) = [1, 1, 1] := rfl
  have h6_ones : (([1] : List (Fin 2)) ^ 6) = [1, 1, 1, 1, 1, 1] := rfl
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (3 * b + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default) := by
    rw [Nat.add_comm (3 * b) 2, ListBlank.append_pow_add]
    rfl
  rw [h3_ones] at h12
  rw [h6_ones, h_l]
  have h3 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default))
          (ListBlank.append [1, 1, 1] default))
        (Cfg.headRight A
          (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default))
          (ListBlank.append [1, 1, 1, 1, 1, 1] default)) := by
    bb_steps
  exact h12.trans h3

private theorem rule_11 (b : ℕ) :
    ReachesPlus target (cfg_A 0 b 0 (b + 4)) (cfg_A (3 * b + 4) 0 0 4) := by
  have h1 := to_underflow b (b + 3)
  have h2 := underflow_loop b 0 3 default
  have hb_eq : 3 + b + 1 = b + 4 := by omega
  rw [hb_eq, Nat.zero_add] at h2
  have h12 := h1.trans_star h2
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h4_ones : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (3 * b + 4)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default) := by
    rw [Nat.add_comm (3 * b) 4, ListBlank.append_pow_add]
    rfl
  rw [show 3 + 1 = 4 from rfl, h4_ones] at h12
  rw [h4_ones, h_l]
  have h3 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default))
          (ListBlank.append [1, 1, 1, 1] default))
        (Cfg.headRight A
          (ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default))
          (ListBlank.append [1, 1, 1, 1] default)) := by
    bb_steps
  exact h12.trans h3

private theorem rule_12 (b d : ℕ) (h : d ≥ b + 5) :
    ReachesPlus target (cfg_A 0 b 0 d) (cfg_A (3 * b + 3) 2 0 (d - b - 5)) := by
  set m := d - b - 5
  have hd_eq : d = (m + b + 4) + 1 := by omega
  rw [hd_eq]
  have h1 := to_underflow b (m + b + 4)
  have h2 := underflow_loop b 0 (m + 4) default
  have hb_eq : (m + 4) + b + 1 = (m + b + 4) + 1 := by omega
  rw [hb_eq, Nat.zero_add] at h2
  have h12 := h1.trans_star h2
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ ((m + 4) + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ m) default) := by
    have h_eq : (m + 4) + 1 = 5 + m := by omega
    rw [h_eq, ListBlank.append_pow_add]
    rfl
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (3 * b + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default) := by
    rw [Nat.add_comm (3 * b) 3, ListBlank.append_pow_add]
    rfl
  have h01_2 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
  rw [h_r] at h12
  rw [h_l, h01_2]
  have h3 :
      ReachesPlus target
        (Cfg.headLeft D
          (ListBlank.append [0, 0] (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default))
          (ListBlank.append [1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
        (Cfg.headRight A
          (ListBlank.append [0, 1, 0, 1]
            (ListBlank.append [1, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (3 * b)) default)))
          (ListBlank.append (([1] : List (Fin 2)) ^ m) default)) := by
    bb_steps
  exact h12.trans h3

/-! ## Closedness and `HasCollatzReduction` -/

private theorem step_A_closed (a b c d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A a b c d) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases c with _ | c'
  · rcases d with _ | d'
    · exact ⟨cfg_A (a + 1) 0 0 (2 * b + 2), rule_2 a b,
        Or.inl (in_ps_A (a + 1) 0 0 (2 * b + 2))⟩
    · rcases a with _ | _ | _ | a'
      · rcases d' with _ | d''
        · rcases b with _ | b'
          · exact ⟨cfg_A 0 0 2 5, rule_7, Or.inl (in_ps_A 0 0 2 5)⟩
          · exact ⟨cfg_A 0 0 2 (2 * b' + 3), rule_8 b',
              Or.inl (in_ps_A 0 0 2 (2 * b' + 3))⟩
        · rcases lt_trichotomy b d'' with h_lt | rfl | h_gt
          · have h_split : d'' = b + 1 ∨ d'' = b + 2 ∨ d'' ≥ b + 3 := by omega
            rcases h_split with rfl | rfl | h_ge
            · exact ⟨cfg_A (3 * b + 2) 0 0 6, rule_10 b,
                Or.inl (in_ps_A (3 * b + 2) 0 0 6)⟩
            · exact ⟨cfg_A (3 * b + 4) 0 0 4, rule_11 b,
                Or.inl (in_ps_A (3 * b + 4) 0 0 4)⟩
            · exact ⟨cfg_A (3 * b + 3) 2 0 (d'' + 2 - b - 5),
                rule_12 b (d'' + 2) (by omega),
                Or.inl (in_ps_A (3 * b + 3) 2 0 (d'' + 2 - b - 5))⟩
          · obtain ⟨cfg', h_step, h_halt⟩ := rule_13 b
            exact ⟨cfg', h_step, Or.inr h_halt⟩
          · exact ⟨cfg_A (3 * d'' + 2) 1 2 (2 * b - 2 * d'' - 1),
              rule_9 b d'' h_gt,
              Or.inl (in_ps_A (3 * d'' + 2) 1 2 (2 * b - 2 * d'' - 1))⟩
      · rcases b with _ | b'
        · exact ⟨cfg_A 0 0 0 (d' + 3), rule_6 d', Or.inl (in_ps_A 0 0 0 (d' + 3))⟩
        · exact ⟨cfg_A 1 1 (b' + 2) d', rule_5 b' d', Or.inl (in_ps_A 1 1 (b' + 2) d')⟩
      · exact ⟨cfg_A 0 0 (b + 1) d', rule_4 b d', Or.inl (in_ps_A 0 0 (b + 1) d')⟩
      · exact ⟨cfg_A a' (b + 2) 0 d', rule_3 a' b d', Or.inl (in_ps_A a' (b + 2) 0 d')⟩
  · exact ⟨cfg_A a (b + 1) c' d, rule_1 a b c' d, Or.inl (in_ps_A a (b + 1) c' d)⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 0 0 0 0, ReachesStar.refl _ _, in_ps_A 0 0 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  exact step_A_closed (vars 0) (vars 1) (vars 2) (vars 3)

/-- `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B, Box 1) -/

/-- Symbolic configuration state space for `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`. -/
inductive State where
  /-- $A(a, b, c, d) := 0^\infty\,1^a\,(10)^b\,\mathrm{A}{>}\,(01)^c\,1^d\,0^\infty$. -/
  | A (a b c d : ℕ)

/-- Initial symbolic state $A(0, 0, 0, 0)$. -/
def start : State := .A 0 0 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b c d =>
    Cfg.headRight SixState.A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default))

/-- Accelerated Collatz-like transition function (Box 1). -/
def next : State → Option State
  | .A a b (c + 1) d => some (.A a (b + 1) c d)
  | .A a b 0 0 => some (.A (a + 1) 0 0 (2 * b + 2))
  | .A (a + 3) b 0 (d + 1) => some (.A a (b + 2) 0 d)
  | .A 2 b 0 (d + 1) => some (.A 0 0 (b + 1) d)
  | .A 1 (b + 1) 0 (d + 1) => some (.A 1 1 (b + 2) d)
  | .A 1 0 0 (d + 1) => some (.A 0 0 0 (d + 3))
  | .A 0 0 0 1 => some (.A 0 0 2 5)
  | .A 0 (b + 1) 0 1 => some (.A 0 0 2 (2 * b + 3))
  | .A 0 b 0 (d + 2) =>
    if b ≥ d + 1 then some (.A (3 * d + 2) 1 2 (2 * b - 2 * d - 1))
    else if d = b then none
    else if d = b + 1 then some (.A (3 * b + 2) 0 0 6)
    else if d = b + 2 then some (.A (3 * b + 4) 0 0 4)
    else some (.A (3 * b + 3) 2 0 (d - b - 3))

private theorem encode_A (a b c d : ℕ) : encode (.A a b c d) = cfg_A a b c d := rfl

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := ReachesStar.refl _ _
  step_some := by
    rintro ⟨a, b, c, d⟩ s' hnext
    rcases c with _ | c
    · rcases d with _ | d
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_2 a b
      · rcases a with _ | _ | _ | a
        · rcases d with _ | d
          · rcases b with _ | b
            · simp only [next, Option.some.injEq] at hnext
              subst hnext
              exact rule_7
            · simp only [next, Option.some.injEq] at hnext
              subst hnext
              exact rule_8 b
          · simp only [next] at hnext
            split_ifs at hnext with h1 h2 h3 h4
            · simp only [Option.some.injEq] at hnext
              subst hnext
              exact rule_9 b d h1
            · simp only [Option.some.injEq] at hnext
              subst hnext
              subst h3
              exact rule_10 b
            · simp only [Option.some.injEq] at hnext
              subst hnext
              subst h4
              exact rule_11 b
            · simp only [Option.some.injEq] at hnext
              subst hnext
              have h_ge : d + 2 ≥ b + 5 := by omega
              have h_sub : d + 2 - b - 5 = d - b - 3 := by omega
              simpa [encode_A, h_sub] using rule_12 b (d + 2) h_ge
        · rcases b with _ | b
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact rule_6 d
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            exact rule_5 b d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_4 b d
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_3 a b d
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact rule_1 a b c d
  step_none := by
    rintro ⟨a, b, c, d⟩ hnext
    rcases c with _ | c
    · rcases d with _ | d
      · simp [next] at hnext
      · rcases a with _ | _ | _ | a
        · rcases d with _ | d
          · rcases b with _ | b <;> simp [next] at hnext
          · simp only [next] at hnext
            split_ifs at hnext with h1 h2 h3 h4
            obtain ⟨cfg', h_plus, h_halt⟩ := rule_13 b
            rw [encode_A, h2]
            exact ⟨cfg', h_plus.to_star, h_halt⟩
        · rcases b with _ | b <;> simp [next] at hnext
        · simp [next] at hnext
        · simp [next] at hnext
    · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD
