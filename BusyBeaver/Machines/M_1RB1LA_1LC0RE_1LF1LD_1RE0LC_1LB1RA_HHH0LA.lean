/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Cryptid `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`

Formal `IsCryptid` proof for the 6-state, 2-symbol Busy Beaver cryptid
`1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`.

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$C(a, f, g, h) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^h\,011\,0^\infty$$
with $h \in \{3, 6\}$ at $C(4, 0, 0, 3)$, and every $C(a, f, g, h)$ with $h \in \{3, 6\}$ steps in
`ReachesPlus` either to another such configuration or to a halting configuration.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Leftward shift across `1^k` in state `A`. -/
private theorem shift_A_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight A
            (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ k)
          (ListBlank.append [1] (ListBlank.append [1] r)) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) (ListBlank.append [1] r) := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Leftward sweep across `0 1^k` in state `A`. -/
private theorem sweep_A_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [0] l))
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
  have h1 := shift_A_left k (ListBlank.append [0] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [0] l)
          (ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r)))
        (Cfg.headRight A l
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))) := by
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r) =
          ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) :=
      ListBlank.append_pow_comm [1] k r
    rw [h_pow, ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans_plus h2

/-- Rightward shift loop across `1^k` behind `011` in state `A`. -/
private theorem shift_A_right_loop (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l
        (ListBlank.append [0, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r)))
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [0, 1, 1] r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r)))
          (Cfg.headRight A
            (ListBlank.append [1] l)
            (ListBlank.append [0, 1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward sweep across `0 1^(k + 2)` in state `A`. -/
private theorem sweep_A_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A l
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r)))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l)))
        r) := by
  have h_split :
      ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r) =
        ListBlank.append [0, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r) := by
    rw [Nat.add_comm k 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 k r]
    rfl
  rw [h_split]
  have h1 := shift_A_right_loop k l r
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
          (ListBlank.append [0, 1, 1] r))
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l)))
          r) := by
    rw [ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans_plus h2

/-- Rightward sweep across `0 1^(k + 2)` starting with `01` on the left. -/
private theorem sweep_A_right_from_01 (k : ℕ) (l₀ r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append [0] l₀))
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) r)))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) (ListBlank.append [0] l₀))))
        r) := by
  have h1 := sweep_A_right k (ListBlank.append [1] (ListBlank.append [0] l₀)) r
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (k + 1))
        (ListBlank.append [1] (ListBlank.append [0] l₀)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (k + 2)) (ListBlank.append [0] l₀) := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rwa [h_l] at h1

/-- Leftward shift across `1^(2 * k)` in state `C`, producing `(01)^k` on the right. -/
private theorem shift_C_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
        (ListBlank.append [1] r))
      (Cfg.headRight C l
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_l :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l =
          ListBlank.append [1] (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)) := by
      have h_eq : 2 * (k + 1) = 2 + 2 * k := by omega
      rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * k) l]
      rfl
    rw [h_l]
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1] (ListBlank.append [1]
              (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)))
            (ListBlank.append [1] r))
          (Cfg.headRight C
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
            (ListBlank.append [1] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_r] at h3

/-- Full left-right sweep from state `C` reading `00` across `1^m 0 1^(c + 3)`. -/
private theorem sweep_C_00 (m c : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (c + 3))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
        (ListBlank.append [0, 0] r))
      (Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1] r)) := by
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 3))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2)))) =
        ListBlank.append [1] (ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))) := by
    have h_eq : c + 3 = 2 + (c + 1) := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (c + 1)]
    rfl
  rw [h_l]
  have h1 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1] (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))))
          (ListBlank.append [0, 0] r))
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ m) default)))
          (ListBlank.append [1] (ListBlank.append [0, 1, 0] r))) := by
    bb_steps
  have h2 := sweep_A_left (c + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
    (ListBlank.append [0, 1, 0] r)
  have h12 := h1.trans h2
  have h3 := sweep_A_right c
    (ListBlank.append (([1] : List (Fin 2)) ^ m) default)
    (ListBlank.append [0, 1, 0] r)
  have h123 := h12.trans h3
  have h_comb :
      ListBlank.append (([1] : List (Fin 2)) ^ (c + 1))
        (ListBlank.append (([1] : List (Fin 2)) ^ m) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default := by
    have h_eq : c + 1 + m = m + c + 1 := by omega
    rw [← ListBlank.append_pow_add, h_eq]
  rw [h_comb] at h123
  have h4 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)))
          (ListBlank.append [0, 1, 0] r))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (m + c + 1)) default)
          (ListBlank.append [0, 0, 1, 1, 1] r)) := by
    bb_steps
  exact h123.trans h4

/-- First canonical tape pattern ($h = 3$):
$C(a, f, g, 3) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^3\,011\,0^\infty$. -/
private def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .sym 1 (.rep [1] 0 .default)
    head  := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
              (.rep [1] 1 (.rep [0, 1] 2
                (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default))))))))))))) }

/-- Second canonical tape pattern ($h = 6$):
$C(a, f, g, 6) := 0^\infty\,1^{a+1}\,\mathrm{C}{>}\,00\,1^{f+4}\,(01)^g\,1^6\,011\,0^\infty$. -/
private def pat_B : TapePattern (Fin 2) (Fin 6) :=
  { left  := .sym 1 (.rep [1] 0 .default)
    head  := some C
    right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
              (.rep [1] 1 (.rep [0, 1] 2
                (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                  (.sym 0 (.sym 1 (.sym 1 .default)))))))))))))))) }

/-- Closed pattern set for `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`. -/
private def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true), (pat_B, .true)]

/-- Configuration $C(a, f, g, h)$. -/
private def cfg_C (a f g h : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
    (ListBlank.append [0, 0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
          (ListBlank.append (([1] : List (Fin 2)) ^ h)
            (ListBlank.append [0, 1, 1] default)))))

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_C (vars 0) (vars 1) (vars 2) 3 := by
  unfold pat_A cfg_C
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (vars 0) default,
    Nat.add_comm (vars 1) 4, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (vars 1)]
  rfl

private theorem eval_pat_B (vars : ℕ → ℕ) :
    evalTapePattern pat_B vars = cfg_C (vars 0) (vars 1) (vars 2) 6 := by
  unfold pat_B cfg_C
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) (vars 0) default,
    Nat.add_comm (vars 1) 4, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (vars 1)]
  rfl

private theorem in_ps_A (a f g : ℕ) : IsInPatternSet ps (cfg_C a f g 3) := by
  refine ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => f | 2 => g | _ => 0, ?_, trivial⟩
  rw [eval_pat_A]
  rfl

private theorem in_ps_B (a f g : ℕ) : IsInPatternSet ps (cfg_C a f g 6) := by
  refine ⟨(pat_B, .true), List.Mem.tail _ (List.Mem.head _),
    fun i => match i with | 0 => a | 1 => f | 2 => g | _ => 0, ?_, trivial⟩
  rw [eval_pat_B]
  rfl

private theorem cfg_C_g0_h6 (a f : ℕ) : cfg_C a f 0 6 = cfg_C a (f + 3) 0 3 := by
  unfold cfg_C
  simp only [list_pow_zero, ListBlank.append_nil]
  have h_eq : f + 3 + 4 = (f + 4) + 3 := by omega
  have h_6 :
      ListBlank.append (([1] : List (Fin 2)) ^ 6)
        (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append (([1] : List (Fin 2)) ^ 3)
            (ListBlank.append [0, 1, 1] default)) := by
    rw [← ListBlank.append_pow_add ([1] : List (Fin 2)) 3 3]
  rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) (f + 4) 3, h_6]

private theorem rule_dec_a (a f g h : ℕ) :
    ReachesPlus target (cfg_C (a + 2) f g h) (cfg_C a (f + 3) g h) := by
  unfold cfg_C
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (a + 2 + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (a + 3))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)) := by
    simp
  have h_r2 :
      ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (f + 3 + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
            (ListBlank.append (([1] : List (Fin 2)) ^ h)
              (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))))) =
        ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default)))) := by
    have h_f : f + 3 + 4 = 3 + (f + 4) := by omega
    rw [h_f, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (f + 4)]
    rfl
  rw [h_l, h_r2]
  have h_step := sweep_C_00 0 a
    (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] default))))
  have h_add : 0 + a + 1 = a + 1 := by omega
  rwa [h_add] at h_step

private def cfg_M (a f g h : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [1] (ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
    (ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
          (ListBlank.append (([1] : List (Fin 2)) ^ h)
            (ListBlank.append [0, 1, 1] default)))))

private theorem step_C_a0_to_M (f g h : ℕ) :
    ReachesPlus target (cfg_C 0 f g h) (cfg_M 0 f g h) := by
  unfold cfg_C cfg_M
  bb_steps

private theorem step_C_a1_to_M (f g h : ℕ) :
    ReachesPlus target (cfg_C 1 f g h) (cfg_M 1 f g h) := by
  unfold cfg_C cfg_M
  bb_steps

private theorem step_M_g2 (a f g h : ℕ) :
    ReachesPlus target (cfg_M a f (g + 2) h) (cfg_C (f + 4 + a) 3 g h) := by
  unfold cfg_M
  have h1 := sweep_A_right_from_01 (f + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
      (ListBlank.append (([1] : List (Fin 2)) ^ h)
        (ListBlank.append [0, 1, 1] default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
            (ListBlank.append (([1] : List (Fin 2)) ^ h)
              (ListBlank.append [0, 1, 1] default))))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1 + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 4)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
                (ListBlank.append (([1] : List (Fin 2)) ^ h)
                  (ListBlank.append [0, 1, 1] default)))))) := by
    have h_g :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (g + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ h)
            (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))) =
          ListBlank.append [0, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default))) := by
      rw [Nat.add_comm g 2, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 g]
      rfl
    have h_f :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      have h_eq : f + 4 = 3 + (f + 1) := by omega
      rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (f + 1)]
      rfl
    rw [h_g, h_f]
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_C_00 (a + 3) (f + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 4)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] default))))
  have h123 := h12.trans h3
  have h_end :
      Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3 + (f + 1) + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 4)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ g)
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default))))) =
        cfg_C (f + 4 + a) 3 g h := by
    unfold cfg_C
    have h_a : a + 3 + (f + 1) + 1 = f + 4 + a + 1 := by omega
    rw [h_a]
    rfl
  rwa [h_end] at h123

private theorem step_M_g1_h6 (a f : ℕ) :
    ReachesPlus target (cfg_M a f 1 6) (cfg_C (f + 4 + a) 0 3 3) := by
  unfold cfg_M
  have h1 := sweep_A_right_from_01 (f + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([1] : List (Fin 2)) ^ 6)
        (ListBlank.append [0, 1, 1] default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0, 1, 1] default))))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1 + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
                (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                  (ListBlank.append [0, 1, 1] default)))))) := by
    have h_f :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      have h_eq : f + 4 = 3 + (f + 1) := by omega
      rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (f + 1)]
      rfl
    rw [h_f]
    bb_steps
  have h12 := h1.trans h2
  have h3 := sweep_C_00 (a + 3) (f + 1)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append [0, 1, 1] default))))
  have h123 := h12.trans h3
  have h_end :
      Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3 + (f + 1) + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
              (ListBlank.append (([1] : List (Fin 2)) ^ 3)
                (ListBlank.append [0, 1, 1] default))))) =
        cfg_C (f + 4 + a) 0 3 3 := by
    unfold cfg_C
    have h_a : a + 3 + (f + 1) + 1 = f + 4 + a + 1 := by omega
    rw [h_a]
    rfl
  rwa [h_end] at h123

private def cfg_L (a m h : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append (([1] : List (Fin 2)) ^ (m + 6))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
    (ListBlank.append [1]
      (ListBlank.append (([1] : List (Fin 2)) ^ h)
        (ListBlank.append [0, 1, 1] default)))

private theorem step_M_g0_h3 (a f : ℕ) :
    ReachesPlus target (cfg_M a f 0 3) (cfg_L a (f + 1) 3) := by
  have h_eq :
      cfg_M a f 0 3 =
        Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 5 + 2))
              (ListBlank.append [0, 1, 1] default))) := by
    unfold cfg_M
    simp only [list_pow_zero, ListBlank.append_nil]
    have h_f : f + 5 + 2 = (f + 4) + 3 := by omega
    rw [h_f, ListBlank.append_pow_add ([1] : List (Fin 2)) (f + 4) 3]
  rw [h_eq]
  have h1 := sweep_A_right_from_01 (f + 5)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append [0, 1, 1] default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 5 + 2))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))))
          (ListBlank.append [0, 1, 1] default))
        (cfg_L a (f + 1) 3) := by
    unfold cfg_L
    have h_f :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 5 + 2))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      have h_add : f + 5 + 2 = 6 + (f + 1) := by omega
      rw [h_add, ListBlank.append_pow_add ([1] : List (Fin 2)) 6 (f + 1)]
      rfl
    rw [h_f]
    bb_steps
  exact h1.trans h2

private theorem step_M_g1_h3 (a f : ℕ) :
    ReachesPlus target (cfg_M a f 1 3) (cfg_L a f 6) := by
  unfold cfg_M
  have h1 := sweep_A_right_from_01 (f + 2)
    (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([1] : List (Fin 2)) ^ 3)
        (ListBlank.append [0, 1, 1] default)))
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default))))
        (cfg_L a f 6) := by
    unfold cfg_L
    have h_l1 :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 4))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ f)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      rw [Nat.add_comm f 4, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 f]
      rfl
    have h_l2 :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 6))
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
          ListBlank.append [1, 1, 1, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ f)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
      rw [Nat.add_comm f 6, ListBlank.append_pow_add ([1] : List (Fin 2)) 6 f]
      rfl
    rw [h_l1, h_l2]
    bb_steps
  exact h1.trans h2

private theorem step_L_odd (a k h : ℕ) :
    ReachesPlus target (cfg_L a (2 * k + 1) h) (cfg_C a 0 (k + 3) h) := by
  unfold cfg_L
  have h_l :
      ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1 + 6))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 3)))
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default))) := by
    have h_eq : 2 * k + 1 + 6 = 2 * (k + 3) + 1 := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 3)) 1]
  rw [h_l]
  have h1 := shift_C_left (k + 3)
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
    (ListBlank.append (([1] : List (Fin 2)) ^ h) (ListBlank.append [0, 1, 1] default))
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3)) default)))
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default)))))
        (Cfg.headRight C
          (ListBlank.append (([1] : List (Fin 2)) ^ (a + 3))
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ 0) default)))
          (ListBlank.append [0, 0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
                (ListBlank.append (([1] : List (Fin 2)) ^ h)
                  (ListBlank.append [0, 1, 1] default)))))) := by
    simp only [list_pow_zero, list_pow_one, ListBlank.append_nil, ListBlank.append_cons,
      ListBlank.cons_zero_default]
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := sweep_C_00 0 a
    (ListBlank.append (([1] : List (Fin 2)) ^ 1)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] default))))
  have h123 := h12.trans h3
  have h_end :
      Cfg.headRight C
        (ListBlank.append (([1] : List (Fin 2)) ^ (0 + a + 1)) default)
        (ListBlank.append [0, 0, 1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ 1)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default))))) =
        cfg_C a 0 (k + 3) h := by
    unfold cfg_C
    have h_a : 0 + a + 1 = a + 1 := by omega
    rw [h_a]
    rfl
  rwa [h_end] at h123

private theorem step_L_even_a0_halt (k h : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_L 0 (2 * k) h) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_L
  have h_eq : 2 * k + 6 = 2 * (k + 3) := by omega
  rw [h_eq]
  have h1 := shift_C_left (k + 3)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ h) (ListBlank.append [0, 1, 1] default))
  have h_k :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 3))
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append [0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ h)
              (ListBlank.append [0, 1, 1] default))) := by
    have h_add : k + 3 = 2 + (k + 1) := by omega
    rw [h_add, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 (k + 1)]
    rfl
  rw [h_k] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 3) default))
          (ListBlank.append [1]
            (ListBlank.append [0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
                (ListBlank.append (([1] : List (Fin 2)) ^ h)
                  (ListBlank.append [0, 1, 1] default))))))
        (Cfg.headRight F default
          (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1))
              (ListBlank.append (([1] : List (Fin 2)) ^ h)
                (ListBlank.append [0, 1, 1] default))))) := by
    bb_steps
  refine ⟨_, h1.trans_plus h2, ?_⟩
  bb_halt

private theorem step_L_even_a1_zero :
    ReachesPlus target (cfg_L 1 0 6) (cfg_C 6 0 3 3) := by
  unfold cfg_L cfg_C
  bb_steps

private theorem step_L_even_a1_succ (j h : ℕ) :
    ReachesPlus target (cfg_L 1 (2 * (j + 1)) h) (cfg_C 6 3 j h) := by
  unfold cfg_L
  have h_eq : 2 * (j + 1) + 6 = 2 * (j + 4) := by omega
  rw [h_eq]
  have h1 := shift_C_left (j + 4)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 4) default))
    (ListBlank.append (([1] : List (Fin 2)) ^ h) (ListBlank.append [0, 1, 1] default))
  have h_j :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (j + 4))
        (ListBlank.append (([1] : List (Fin 2)) ^ h)
          (ListBlank.append [0, 1, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ j)
            (ListBlank.append (([1] : List (Fin 2)) ^ h)
              (ListBlank.append [0, 1, 1] default))) := by
    rw [Nat.add_comm j 4, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 4 j]
    rfl
  rw [h_j] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 4) default))
          (ListBlank.append [1]
            (ListBlank.append [0, 1, 0, 1, 0, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ j)
                (ListBlank.append (([1] : List (Fin 2)) ^ h)
                  (ListBlank.append [0, 1, 1] default))))))
        (cfg_C 6 3 j h) := by
    unfold cfg_C
    have h4 : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
    have h7 : (([1] : List (Fin 2)) ^ 7) = [1, 1, 1, 1, 1, 1, 1] := rfl
    rw [h4, h7]
    bb_steps
  exact h1.trans_plus h2

private theorem step_C_h3 (a f g : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C a f g 3) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases a with _ | _ | a'
  · have h0 := step_C_a0_to_M f g 3
    rcases g with _ | _ | g'
    · have h1 := h0.trans (step_M_g0_h3 0 f)
      rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨cfg_C 0 0 (k + 3) 3, h1.trans (step_L_odd 0 k 3),
          Or.inl (in_ps_A 0 0 (k + 3))⟩
      · have h_eq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [h_eq] at h1
        obtain ⟨cfg', h2, h_halt⟩ := step_L_even_a0_halt (k + 1) 3
        exact ⟨cfg', h1.trans h2, Or.inr h_halt⟩
    · have h1 := h0.trans (step_M_g1_h3 0 f)
      rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · obtain ⟨cfg', h2, h_halt⟩ := step_L_even_a0_halt k 6
        exact ⟨cfg', h1.trans h2, Or.inr h_halt⟩
      · exact ⟨cfg_C 0 0 (k + 3) 6, h1.trans (step_L_odd 0 k 6),
          Or.inl (in_ps_B 0 0 (k + 3))⟩
    · exact ⟨cfg_C (f + 4 + 0) 3 g' 3, h0.trans (step_M_g2 0 f g' 3),
        Or.inl (in_ps_A (f + 4 + 0) 3 g')⟩
  · have h0 := step_C_a1_to_M f g 3
    rcases g with _ | _ | g'
    · have h1 := h0.trans (step_M_g0_h3 1 f)
      rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨cfg_C 1 0 (k + 3) 3, h1.trans (step_L_odd 1 k 3),
          Or.inl (in_ps_A 1 0 (k + 3))⟩
      · have h_eq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [h_eq] at h1
        exact ⟨cfg_C 6 3 k 3, h1.trans (step_L_even_a1_succ k 3),
          Or.inl (in_ps_A 6 3 k)⟩
    · have h1 := h0.trans (step_M_g1_h3 1 f)
      rcases nat_even_or_odd_two_mul f with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · rcases k with _ | j
        · exact ⟨cfg_C 6 0 3 3, h1.trans step_L_even_a1_zero,
            Or.inl (in_ps_A 6 0 3)⟩
        · exact ⟨cfg_C 6 3 j 6, h1.trans (step_L_even_a1_succ j 6),
            Or.inl (in_ps_B 6 3 j)⟩
      · exact ⟨cfg_C 1 0 (k + 3) 6, h1.trans (step_L_odd 1 k 6),
          Or.inl (in_ps_B 1 0 (k + 3))⟩
    · exact ⟨cfg_C (f + 4 + 1) 3 g' 3, h0.trans (step_M_g2 1 f g' 3),
        Or.inl (in_ps_A (f + 4 + 1) 3 g')⟩
  · exact ⟨cfg_C a' (f + 3) g 3, rule_dec_a a' f g 3,
      Or.inl (in_ps_A a' (f + 3) g)⟩

private theorem step_C_h6 (a f g : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C a f g 6) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases g with _ | _ | g'
  · rw [cfg_C_g0_h6 a f]
    exact step_C_h3 a (f + 3) 0
  · rcases a with _ | _ | a'
    · exact ⟨cfg_C (f + 4 + 0) 0 3 3,
        (step_C_a0_to_M f 1 6).trans (step_M_g1_h6 0 f),
        Or.inl (in_ps_A (f + 4 + 0) 0 3)⟩
    · exact ⟨cfg_C (f + 4 + 1) 0 3 3,
        (step_C_a1_to_M f 1 6).trans (step_M_g1_h6 1 f),
        Or.inl (in_ps_A (f + 4 + 1) 0 3)⟩
    · exact ⟨cfg_C a' (f + 3) 1 6, rule_dec_a a' f 1 6,
        Or.inl (in_ps_B a' (f + 3) 1)⟩
  · rcases a with _ | _ | a'
    · exact ⟨cfg_C (f + 4 + 0) 3 g' 6,
        (step_C_a0_to_M f (g' + 2) 6).trans (step_M_g2 0 f g' 6),
        Or.inl (in_ps_B (f + 4 + 0) 3 g')⟩
    · exact ⟨cfg_C (f + 4 + 1) 3 g' 6,
        (step_C_a1_to_M f (g' + 2) 6).trans (step_M_g2 1 f g' 6),
        Or.inl (in_ps_B (f + 4 + 1) 3 g')⟩
    · exact ⟨cfg_C a' (f + 3) (g' + 2) 6, rule_dec_a a' f (g' + 2) 6,
        Or.inl (in_ps_B a' (f + 3) (g' + 2))⟩

/-- `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` is a cryptid. -/
theorem is_cryptid : IsCryptid target := by
  refine ⟨ps, ⟨cfg_C 4 0 0 3, ?_, in_ps_A 4 0 0⟩, ?_⟩
  · have h_init : ReachesPlus target (init []) (cfg_C 4 0 0 3) := by
      unfold cfg_C
      bb_steps
    exact h_init.to_star
  · intro cfg h_in
    rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
    simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
    rcases h_mem with rfl | rfl
    · rw [eval_pat_A]
      exact step_C_h3 (vars 0) (vars 1) (vars 2)
    · rw [eval_pat_B]
      exact step_C_h6 (vars 0) (vars 1) (vars 2)

end BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA
