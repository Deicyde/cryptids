/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`.

Starting from the blank tape (`init []`), the trajectory reaches the guarded configuration family
consisting of:
- $P_1(c) := 0^\infty\,\mathrm{C}{>}\,0\,1^c\,0^\infty$ ($c \ge 1$), and
- $P_2(a, c) := 0^\infty\,(10)^a\,1\,\mathrm{C}{>}\,0\,1^c\,0^\infty$ ($c \ge 1$),
at $P_1(1)$ in 3 steps, and every member configuration advances in `ReachesPlus` either to another
member of the pattern set or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
P_1(c) = 0^inf C> 0 1^c 0^inf
P_2(a, c) = 0^inf 10^a 1 C> 0 1^c 0^inf
D(a, b, w) = 0^inf 10^a 1^b D> 1^{w+1} 0^inf
where c >= 1

P_1(1) -> P_1(3)
P_1(w+2) -> D(0, 1, w)
P_2(a, 1) -> P_2(a, 3)
P_2(a, w+2) -> D(a+1, 1, w)

D(0, 2k+1, 0) -> P_1(2k+4)
D(0, 2k+1, 1) -> P_1(2k+6)
D(0, 2k+1, w+2) -> D(0, 2k+4, w)

D(0, 2k+2, 0) -> Halt
D(0, 2k+2, 1) -> P_2(k, 3)
D(0, 2k+2, 2) -> P_2(k, 5)
D(0, 2k+2, 3) -> P_2(k, 7)
D(0, 2k+2, w+4) -> D(k+1, 5, w)

D(1, 2k+1, 0) -> P_1(2k+5)
D(1, 2k+1, 1) -> P_1(2k+7)
D(a+2, 2k+1, 0) -> P_2(a, 2k+5)
D(a+2, 2k+1, 1) -> P_2(a, 2k+7)
D(a+1, 2k+1, w+2) -> D(a, 2k+5, w)

Start: P_1(1), reached after 3 raw TM steps
```

This initial acceleration can be simplified by composing transitions through $P_1$ and $P_2$,
yielding a system expressed in terms of the configuration $D$:

```text
Consider:
D(a, b, w) = 0^inf 10^a 1^b D> 1^{w+1} 0^inf where b >= 1, and b is odd if a >= 1

D(0, 2k+1, w) -> D(0, 1, 2k+2w+2) if w <= 1
D(0, 2k+1, w+2) -> D(0, 2k+4, w)
D(0, 2k+2, 0) -> Halt
D(0, 2k+2, w) -> D(k+1, 1, 2w-1) if 1 <= w <= 3
D(0, 2k+2, w+4) -> D(k+1, 5, w)
D(a+1, 2k+1, w) -> D(a, 1, 2k+2w+3) if w <= 1
D(a+1, 2k+1, w+2) -> D(a, 2k+5, w)

Start: D(0, 1, 1), reached after 13 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Leftward shift across `(11)^k` in state `E`, writing `(10)^k`. -/
private theorem shift_E_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft E (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft E l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft E
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            r)
          (Cfg.headLeft E
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

/-- Leftward shift across `1^k` in state `C`. -/
private theorem shift_C_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft C (ListBlank.append (([1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft C l (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft C
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            r)
          (Cfg.headLeft C
            (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Rightward shift across `(10)^k` in state `F`, preserving `(10)^k`. -/
private theorem shift_F_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight F l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r))
      (Cfg.headRight F (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight F l
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight F (ListBlank.append [1, 0] l)
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

/-- Rightward shift across `(01)^k` in state `A`, writing `(11)^k`. -/
private theorem shift_A_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight A (ListBlank.append [1, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Canonical tape pattern $P_1(c) := 0^\infty\,\mathrm{C}{>}\,0\,1^c\,0^\infty$. -/
private abbrev pat_1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.rep [1] 0 .default) }

/-- Canonical tape pattern $P_2(a, c) := 0^\infty\,(10)^a\,1\,\mathrm{C}{>}\,0\,1^c\,0^\infty$. -/
private abbrev pat_2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [0, 1] 0 .default)
    head := some C
    right := .sym 0 (.rep [1] 1 .default) }

/-- Closed pattern set for `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .default
      head := some SixState.C
      right := .sym 0 (.rep [1] 0 .default) }, .ge_const 0 1),
   ({ left := .sym 1 (.rep [0, 1] 0 .default)
      head := some SixState.C
      right := .sym 0 (.rep [1] 1 .default) }, .ge_const 1 1)]

/-- Configuration $P_1(c)$. -/
private def cfg_P1 (c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C default
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

/-- Configuration $P_2(a, c)$. -/
private def cfg_P2 (a c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

private theorem eval_pat_1 (vars : ℕ → ℕ) :
    evalTapePattern pat_1 vars = cfg_P1 (vars 0) :=
  rfl

private theorem eval_pat_2 (vars : ℕ → ℕ) :
    evalTapePattern pat_2 vars = cfg_P2 (vars 0) (vars 1) :=
  rfl

private theorem in_ps_P1 (c : ℕ) (hc : c ≥ 1) : IsInPatternSet ps (cfg_P1 c) :=
  ⟨(pat_1, .ge_const 0 1), List.Mem.head _,
    fun _ => c, rfl, hc⟩

private theorem in_ps_P2 (a c : ℕ) (hc : c ≥ 1) : IsInPatternSet ps (cfg_P2 a c) :=
  ⟨(pat_2, .ge_const 1 1), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 0 => a | 1 => c | _ => 0, rfl, hc⟩

/-- Intermediate configuration
$D_1(a, b, w) := 0^\infty\,(10)^a\,1^b\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
private def cfg_D1 (a b w : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append (([1] : List (Fin 2)) ^ b)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
    (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))

private theorem headLeft_C_default_eq_P1 (m : ℕ) :
    Cfg.headLeft C default (ListBlank.append (([1] : List (Fin 2)) ^ m) default) = cfg_P1 m := by
  simp [cfg_P1, Cfg.headLeft, Cfg.headRight]

private theorem headLeft_C_succ_eq_P2 (a m : ℕ) :
    Cfg.headLeft C
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append (([1] : List (Fin 2)) ^ m) default) = cfg_P2 a m := by
  unfold cfg_P2
  rw [ListBlank.append_pow_succ]
  simp [Cfg.headLeft, Cfg.headRight]

/-! ## Transitions from $P_1$ and $P_2$ -/

private theorem step_P1_c1 : ReachesPlus target (cfg_P1 1) (cfg_P1 3) := by
  unfold cfg_P1
  have h1 : (([1] : List (Fin 2)) ^ 1) = [1] := rfl
  have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
  rw [h1, h3]
  bb_steps

private theorem step_P1_ge2 (w : ℕ) :
    ReachesPlus target (cfg_P1 (w + 2)) (cfg_D1 0 1 w) := by
  unfold cfg_P1 cfg_D1
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
    rw [Nat.add_comm w 2, ListBlank.append_pow_add]
    rfl
  rw [h_r, list_pow_one, list_pow_zero, ListBlank.append_nil]
  bb_steps

private theorem step_P2_c1 (a : ℕ) :
    ReachesPlus target (cfg_P2 a 1) (cfg_P2 a 3) := by
  unfold cfg_P2
  have h1 : (([1] : List (Fin 2)) ^ 1) = [1] := rfl
  have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
  rw [h1, h3]
  bb_steps

private theorem step_P2_ge2 (a w : ℕ) :
    ReachesPlus target (cfg_P2 a (w + 2)) (cfg_D1 (a + 1) 1 w) := by
  unfold cfg_P2 cfg_D1
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
    rw [Nat.add_comm w 2, ListBlank.append_pow_add]
    rfl
  rw [h_r, list_pow_one, ListBlank.append_pow_succ]
  bb_steps

/-! ## Case 1: $D_1(0, 2k+1, w)$ -/

private theorem sweep_case1 (k w : ℕ) :
    ReachesPlus target
      (cfg_D1 0 (2 * k + 1) w)
      (Cfg.headRight B
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))) := by
  unfold cfg_D1
  rw [list_pow_zero, ListBlank.append_nil]
  have h_l1 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] default) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1, ← one_pow_two_mul, list_pow_one]
  rw [h_l1]
  set r := ListBlank.append (([1] : List (Fin 2)) ^ w) default
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] default))
          (ListBlank.append [1] r))
        (Cfg.headLeft E
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] default))
          (ListBlank.append [1] r)) := by
    bb_steps
  have h2 := shift_E_left k (ListBlank.append [1] default) (ListBlank.append [1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))
        (Cfg.headRight B
          (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] r))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_B_right k (ListBlank.append [1, 1] default) (ListBlank.append [1] r)
  have h1234 := h123.trans_star h4
  have h_l2 :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default := by
    rw [one_pow_two_mul, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 2]
    rfl
  rwa [h_l2] at h1234

private theorem step_D1_case1_ge2 (k w : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 1) (w + 2)) (cfg_D1 0 (2 * (k + 1) + 2) w) := by
  have h1 := sweep_case1 k (w + 2)
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) default)))
        (cfg_D1 0 (2 * (k + 1) + 2) w) := by
    unfold cfg_D1
    rw [list_pow_zero, ListBlank.append_nil]
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
      rw [Nat.add_comm w 2, ListBlank.append_pow_add]
      rfl
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1) + 2))
          (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default) := by
      have h_eq : 2 * (k + 1) + 2 = 2 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r, h_l]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case1_w0 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 1) 0) (cfg_P1 (2 * k + 4)) := by
  have h1 := sweep_case1 k 0
  rw [list_pow_zero, ListBlank.append_nil] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)
          (ListBlank.append [1] default))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 4)) default)
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default) := by
      have h_eq : 2 * k + 4 = 2 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_left (2 * k + 4) default default
  have h123 := h12.trans_star h3
  rwa [headLeft_C_default_eq_P1] at h123

private theorem step_D1_case1_w1 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 1) 1) (cfg_P1 (2 * k + 6)) := by
  have h1 := sweep_case1 k 1
  rw [list_pow_one] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default)
          (ListBlank.append [1] (ListBlank.append [1] default)))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 6)) default)
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 6)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) default) := by
      have h_eq : 2 * k + 6 = 4 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_left (2 * k + 6) default default
  have h123 := h12.trans_star h3
  rwa [headLeft_C_default_eq_P1] at h123

/-! ## Case 2: $D_1(0, 2k+2, w)$ -/

private theorem sweep_case2 (k w : ℕ) :
    ReachesPlus target
      (cfg_D1 0 (2 * k + 2) w)
      (Cfg.headRight F
        (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))) := by
  unfold cfg_D1
  rw [list_pow_zero, ListBlank.append_nil]
  have h_l1 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default := by
    have h_eq : 2 * k + 2 = 2 * (k + 1) := by omega
    rw [h_eq, ← one_pow_two_mul]
  rw [h_l1]
  set r := ListBlank.append (([1] : List (Fin 2)) ^ w) default
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default)
          (ListBlank.append [1] r))
        (Cfg.headLeft E
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default)
          (ListBlank.append [1] r)) := by
    bb_steps
  have h2 := shift_E_left (k + 1) default (ListBlank.append [1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] r)))
        (Cfg.headRight F
          (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] r))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_F_right (k + 1) (ListBlank.append [1] default) (ListBlank.append [1] r)
  have h1234 := h123.trans_star h4
  have h_l2 :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [1] (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default) := by
    rw [ListBlank.append_pow_succ, append_10_pow_one]
    rfl
  rwa [h_l2] at h1234

private theorem step_D1_case2_w0 (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_D1 0 (2 * k + 2) 0) cfg' ∧ (step target cfg').isNone := by
  have h1 := sweep_case2 k 0
  rw [list_pow_zero, ListBlank.append_nil] at h1
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 0, 1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
    default, ?_, ?_⟩
  · have h2 :
        ReachesPlus target
          (Cfg.headRight F
            (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
            (ListBlank.append [1] default))
          (Cfg.headRight F
            (ListBlank.append [1, 0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
            default) := by
      bb_steps
    exact h1.trans h2
  · bb_halt

private theorem step_D1_case2_w1 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 2) 1) (cfg_P2 k 3) := by
  have h1 := sweep_case2 k 1
  rw [list_pow_one] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append [1] default)))
        (cfg_P2 k 3) := by
    unfold cfg_P2
    have h3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
    rw [h3]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case2_w2 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 2) 2) (cfg_P2 k 5) := by
  have h1 := sweep_case2 k 2
  have h_w2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [h_w2] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append [1, 1] default)))
        (cfg_P2 k 5) := by
    unfold cfg_P2
    have h5 : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
    rw [h5]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case2_w3 (k : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 2) 3) (cfg_P2 k 7) := by
  have h1 := sweep_case2 k 3
  have h_w3 : (([1] : List (Fin 2)) ^ 3) = [1, 1, 1] := rfl
  rw [h_w3] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append [1, 1, 1] default)))
        (cfg_P2 k 7) := by
    unfold cfg_P2
    have h7 : (([1] : List (Fin 2)) ^ 7) = [1, 1, 1, 1, 1, 1, 1] := rfl
    rw [h7]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case2_ge4 (k w : ℕ) :
    ReachesPlus target (cfg_D1 0 (2 * k + 2) (w + 4)) (cfg_D1 (k + 1) (2 * 2 + 1) w) := by
  have h1 := sweep_case2 k (w + 4)
  have h2 :
      ReachesPlus target
        (Cfg.headRight F
          (ListBlank.append [1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ (w + 4)) default)))
        (cfg_D1 (k + 1) (2 * 2 + 1) w) := by
    unfold cfg_D1
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (w + 4)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
      rw [Nat.add_comm w 4, ListBlank.append_pow_add]
      rfl
    have h5 : (([1] : List (Fin 2)) ^ (2 * 2 + 1)) = [1, 1, 1, 1, 1] := rfl
    rw [h_r, h5, ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans h2

/-! ## Case 3: $D_1(a+1, 2k+1, w)$ -/

private theorem sweep_case3 (a k w : ℕ) :
    ReachesPlus target
      (cfg_D1 (a + 1) (2 * k + 1) w)
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))) := by
  unfold cfg_D1
  set l := ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default
  set r := ListBlank.append (([1] : List (Fin 2)) ^ w) default
  have h_l1 :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 0, 1] l) := by
    rw [ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 1, ← one_pow_two_mul,
      list_pow_one, ListBlank.append_pow_succ]
    rfl
  rw [h_l1]
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 0, 1] l))
          (ListBlank.append [1] r))
        (Cfg.headLeft E
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 0, 1] l))
          (ListBlank.append [1] r)) := by
    bb_steps
  have h2 := shift_E_left k (ListBlank.append [1, 0, 1] l) (ListBlank.append [1] r)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append [1, 0, 1] l)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))
        (Cfg.headRight A
          (ListBlank.append [1, 1] l)
          (ListBlank.append [0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))) := by
    bb_steps
  have h123 := h12.trans h3
  rw [append_zero_10_pow_one] at h123
  have h4 := shift_A_right k (ListBlank.append [1, 1] l) (ListBlank.append [0, 1] r)
  have h1234 := h123.trans_star h4
  have h_l2 :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l := by
    rw [one_pow_two_mul, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * k) 2]
    rfl
  rwa [h_l2] at h1234

private theorem step_D1_case3_ge2 (a k w : ℕ) :
    ReachesPlus target (cfg_D1 (a + 1) (2 * k + 1) (w + 2)) (cfg_D1 a (2 * (k + 2) + 1) w) := by
  have h1 := sweep_case3 a k (w + 2)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) default)))
        (cfg_D1 a (2 * (k + 2) + 1) w) := by
    unfold cfg_D1
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (w + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default) := by
      rw [Nat.add_comm w 2, ListBlank.append_pow_add]
      rfl
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 2) + 1))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)) := by
      have h_eq : 2 * (k + 2) + 1 = 3 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_r, h_l]
    bb_steps
  exact h1.trans h2

private theorem step_D1_case3_w0 (a k : ℕ) :
    ReachesPlus target
      (cfg_D1 (a + 1) (2 * k + 1) 0)
      (Cfg.headLeft C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) default)) := by
  have h1 := sweep_case3 a k 0
  rw [list_pow_zero, ListBlank.append_nil] at h1
  set l := ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l)
          (ListBlank.append [0, 1] default))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) l)
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 5)) l =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l) := by
      have h_eq : 2 * k + 5 = 3 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_left (2 * k + 5) l default
  exact h12.trans_star h3

private theorem step_D1_case3_w1 (a k : ℕ) :
    ReachesPlus target
      (cfg_D1 (a + 1) (2 * k + 1) 1)
      (Cfg.headLeft C
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 7)) default)) := by
  have h1 := sweep_case3 a k 1
  rw [list_pow_one] at h1
  set l := ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l)
          (ListBlank.append [0, 1] (ListBlank.append [1] default)))
        (Cfg.headLeft C
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 7)) l)
          default) := by
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 7)) l =
          ListBlank.append [1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2)) l) := by
      have h_eq : 2 * k + 7 = 5 + (2 * k + 2) := by omega
      rw [h_eq, ListBlank.append_pow_add]
      rfl
    rw [h_l]
    bb_steps
  have h12 := h1.trans h2
  have h3 := shift_C_left (2 * k + 7) l default
  exact h12.trans_star h3

/-! ## Strong Induction on $w$ and `HasCollatzReduction` -/

private def IH_Prop (w : ℕ) : Prop :=
  (∀ k, StepsToClosed target ps (cfg_D1 0 (2 * k + 1) w)) ∧
  (∀ k, StepsToClosed target ps (cfg_D1 0 (2 * k + 2) w)) ∧
  (∀ a k, StepsToClosed target ps (cfg_D1 (a + 1) (2 * k + 1) w))

private theorem d1_closed_case1 (w k : ℕ) (ih : ∀ m < w, IH_Prop m) :
    StepsToClosed target ps (cfg_D1 0 (2 * k + 1) w) := by
  rcases w with _ | _ | w'
  · exact ⟨cfg_P1 (2 * k + 4), step_D1_case1_w0 k, Or.inl (in_ps_P1 (2 * k + 4) (by omega))⟩
  · exact ⟨cfg_P1 (2 * k + 6), step_D1_case1_w1 k, Or.inl (in_ps_P1 (2 * k + 6) (by omega))⟩
  · exact StepsToClosed.of_reachesPlus (step_D1_case1_ge2 k w')
      ((ih w' (by omega)).2.1 (k + 1))

private theorem d1_closed_case2 (w k : ℕ) (ih : ∀ m < w, IH_Prop m) :
    StepsToClosed target ps (cfg_D1 0 (2 * k + 2) w) := by
  rcases w with _ | _ | _ | _ | w'
  · obtain ⟨cfg', h_step, h_halt⟩ := step_D1_case2_w0 k
    exact ⟨cfg', h_step, Or.inr h_halt⟩
  · exact ⟨cfg_P2 k 3, step_D1_case2_w1 k, Or.inl (in_ps_P2 k 3 (by decide))⟩
  · exact ⟨cfg_P2 k 5, step_D1_case2_w2 k, Or.inl (in_ps_P2 k 5 (by decide))⟩
  · exact ⟨cfg_P2 k 7, step_D1_case2_w3 k, Or.inl (in_ps_P2 k 7 (by decide))⟩
  · exact StepsToClosed.of_reachesPlus (step_D1_case2_ge4 k w')
      ((ih w' (by omega)).2.2 k 2)

private theorem d1_closed_case3 (w a k : ℕ) (ih : ∀ m < w, IH_Prop m) :
    StepsToClosed target ps (cfg_D1 (a + 1) (2 * k + 1) w) := by
  rcases w with _ | _ | w'
  · have h_step := step_D1_case3_w0 a k
    rcases a with _ | a'
    · rw [list_pow_zero, ListBlank.append_nil, headLeft_C_default_eq_P1] at h_step
      exact ⟨cfg_P1 (2 * k + 5), h_step, Or.inl (in_ps_P1 (2 * k + 5) (by omega))⟩
    · rw [headLeft_C_succ_eq_P2] at h_step
      exact ⟨cfg_P2 a' (2 * k + 5), h_step, Or.inl (in_ps_P2 a' (2 * k + 5) (by omega))⟩
  · have h_step := step_D1_case3_w1 a k
    rcases a with _ | a'
    · rw [list_pow_zero, ListBlank.append_nil, headLeft_C_default_eq_P1] at h_step
      exact ⟨cfg_P1 (2 * k + 7), h_step, Or.inl (in_ps_P1 (2 * k + 7) (by omega))⟩
    · rw [headLeft_C_succ_eq_P2] at h_step
      exact ⟨cfg_P2 a' (2 * k + 7), h_step, Or.inl (in_ps_P2 a' (2 * k + 7) (by omega))⟩
  · have h_step := step_D1_case3_ge2 a k w'
    rcases a with _ | a'
    · exact StepsToClosed.of_reachesPlus h_step ((ih w' (by omega)).1 (k + 2))
    · exact StepsToClosed.of_reachesPlus h_step ((ih w' (by omega)).2.2 a' (k + 2))

private theorem d1_closed (w : ℕ) : IH_Prop w := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    exact ⟨fun k => d1_closed_case1 w k ih,
      fun k => d1_closed_case2 w k ih,
      fun a k => d1_closed_case3 w a k ih⟩

private theorem step_P1_closed (c : ℕ) (hc : c ≥ 1) : StepsToClosed target ps (cfg_P1 c) := by
  rcases c with _ | _ | w
  · omega
  · exact ⟨cfg_P1 3, step_P1_c1, Or.inl (in_ps_P1 3 (by decide))⟩
  · exact StepsToClosed.of_reachesPlus (step_P1_ge2 w) ((d1_closed w).1 0)

private theorem step_P2_closed (a c : ℕ) (hc : c ≥ 1) : StepsToClosed target ps (cfg_P2 a c) := by
  rcases c with _ | _ | w
  · omega
  · exact ⟨cfg_P2 a 3, step_P2_c1 a, Or.inl (in_ps_P2 a 3 (by decide))⟩
  · exact StepsToClosed.of_reachesPlus (step_P2_ge2 a w) ((d1_closed w).2.2 a 0)

private theorem init_reaches_start : ReachesStar target (init []) (cfg_P1 1) := by
  have h_init : ReachesPlus target (init []) (cfg_P1 1) := by
    unfold cfg_P1
    have h1 : (([1] : List (Fin 2)) ^ 1) = [1] := rfl
    rw [h1]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_P1 1, init_reaches_start, in_ps_P1 1 (by decide)⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl
  · exact step_P1_closed (vars 0) h_cond
  · exact step_P2_closed (vars 0) (vars 1) h_cond

/-- `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B, Box 1) -/

/-- Symbolic configuration state space for `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`. -/
inductive State where
  /-- $P_1(c + 1) := 0^\infty\,\mathrm{C}{>}\,0\,1^{c+1}\,0^\infty$. -/
  | P_1 (c : ℕ)
  /-- $P_2(a, c + 1) := 0^\infty\,(10)^a\,1\,\mathrm{C}{>}\,0\,1^{c+1}\,0^\infty$. -/
  | P_2 (a c : ℕ)
  /-- $D(0, 2k + 1, w) := 0^\infty\,1^{2k+1}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_0_odd (k w : ℕ)
  /-- $D(0, 2k + 2, w) := 0^\infty\,1^{2k+2}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_0_even (k w : ℕ)
  /-- $D(a + 1, 2k + 1, w) :=
    0^\infty\,(10)^{a+1}\,1^{2k+1}\,\mathrm{D}{>}\,1\,1^w\,0^\infty$. -/
  | D_succ_odd (a k w : ℕ)

/-- Initial symbolic state $P_1(1)$, reached after 3 raw TM steps. -/
def start : State := .P_1 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 c =>
    Cfg.headRight SixState.C default
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .P_2 a c =>
    Cfg.headRight SixState.C
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .D_0_odd k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_0_even k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_succ_odd a k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))

/-- Accelerated Collatz-like transition function (Box 1). -/
def next : State → Option State
  | .P_1 0 => some (.P_1 2)
  | .P_1 (w + 1) => some (.D_0_odd 0 w)
  | .P_2 a 0 => some (.P_2 a 2)
  | .P_2 a (w + 1) => some (.D_succ_odd a 0 w)
  | .D_0_odd k 0 => some (.P_1 (2 * k + 3))
  | .D_0_odd k 1 => some (.P_1 (2 * k + 5))
  | .D_0_odd k (w + 2) => some (.D_0_even (k + 1) w)
  | .D_0_even _ 0 => none
  | .D_0_even k 1 => some (.P_2 k 2)
  | .D_0_even k 2 => some (.P_2 k 4)
  | .D_0_even k 3 => some (.P_2 k 6)
  | .D_0_even k (w + 4) => some (.D_succ_odd k 2 w)
  | .D_succ_odd 0 k 0 => some (.P_1 (2 * k + 4))
  | .D_succ_odd 0 k 1 => some (.P_1 (2 * k + 6))
  | .D_succ_odd (a + 1) k 0 => some (.P_2 a (2 * k + 4))
  | .D_succ_odd (a + 1) k 1 => some (.P_2 a (2 * k + 6))
  | .D_succ_odd 0 k (w + 2) => some (.D_0_odd (k + 2) w)
  | .D_succ_odd (a + 1) k (w + 2) => some (.D_succ_odd a (k + 2) w)

private theorem step_state : ∀ s : State,
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesPlus target (encode s) cfg' ∧ (step target cfg').isNone
  | .P_1 0 => step_P1_c1
  | .P_1 (w + 1) => step_P1_ge2 w
  | .P_2 a 0 => step_P2_c1 a
  | .P_2 a (w + 1) => step_P2_ge2 a w
  | .D_0_odd k 0 => step_D1_case1_w0 k
  | .D_0_odd k 1 => step_D1_case1_w1 k
  | .D_0_odd k (w + 2) => step_D1_case1_ge2 k w
  | .D_0_even k 0 => step_D1_case2_w0 k
  | .D_0_even k 1 => step_D1_case2_w1 k
  | .D_0_even k 2 => step_D1_case2_w2 k
  | .D_0_even k 3 => step_D1_case2_w3 k
  | .D_0_even k (w + 4) => step_D1_case2_ge4 k w
  | .D_succ_odd 0 k 0 => by
    have h := step_D1_case3_w0 0 k
    rwa [list_pow_zero, ListBlank.append_nil, headLeft_C_default_eq_P1] at h
  | .D_succ_odd 0 k 1 => by
    have h := step_D1_case3_w1 0 k
    rwa [list_pow_zero, ListBlank.append_nil, headLeft_C_default_eq_P1] at h
  | .D_succ_odd (a + 1) k 0 => by
    have h := step_D1_case3_w0 (a + 1) k
    rwa [headLeft_C_succ_eq_P2] at h
  | .D_succ_odd (a + 1) k 1 => by
    have h := step_D1_case3_w1 (a + 1) k
    rwa [headLeft_C_succ_eq_P2] at h
  | .D_succ_odd 0 k (w + 2) => step_D1_case3_ge2 0 k w
  | .D_succ_odd (a + 1) k (w + 2) => step_D1_case3_ge2 (a + 1) k w

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := fun s s' hnext => by
    have h := step_state s
    rwa [hnext] at h
  step_none := fun s hnext => by
    have h := step_state s
    rw [hnext] at h
    obtain ⟨cfg', hp, hh⟩ := h
    exact ⟨cfg', hp.to_star, hh⟩

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE
