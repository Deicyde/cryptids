/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Cryptid `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`

Formal `IsCryptid` proof for the 6-state, 2-symbol Busy Beaver cryptid
`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`.

Starting from the blank tape (`init []`), the trajectory reaches the four-pattern configuration
system (`pat_Junc`, `pat_ScanE`, `pat_ScanE0`, `pat_ScanE1`) at `cfg_Junc 0 0 0` in 35 steps, and
every member configuration steps in `ReachesPlus` either to another member configuration or to a
halting configuration.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private theorem ones_comm_111_to_11 (k : ℕ) (l : ListBlank (Fin 2)) :
    ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1, 1] l) =
      ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l) := by
  have h1 :
      ListBlank.append [1, 1, 1] l =
        ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1) l) := rfl
  rw [h1, swap_1_11_pow, ← ListBlank.append_pow_add]

private theorem shift_A_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight A (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
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

private theorem shift_B_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B (ListBlank.append [0, 1] l)
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

private theorem shift_A_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
        (ListBlank.append [1, 1] r))
      (Cfg.headRight A
        (ListBlank.append [1] l)
        (ListBlank.append [1, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [1] (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)))
            (ListBlank.append [1, 1] r))
          (Cfg.headRight A
            (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1, 1] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

private theorem shift_E_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1] r))
      (Cfg.headRight E l
        (ListBlank.append [1, 1, 1, 1, 1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1, 1, 1, 1, 1, 1, 1] r))
          (Cfg.headRight E
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1, 1, 1, 1, 1, 1] (ListBlank.append [1, 1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

private theorem shift_C_1101 (m p : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C
        (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ p) l))
        (ListBlank.append [1]
          (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
            (ListBlank.append [1, 1] r))))
      (Cfg.headRight C
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (p + 2 * m)) l))
        (ListBlank.append [1, 1, 1] r)) := by
  induction m generalizing p l r with
  | zero => exact ReachesStar.refl _ _
  | succ m ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C
            (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ p) l))
            (ListBlank.append [1]
              (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ (m + 1))
                (ListBlank.append [1, 1] r))))
          (Cfg.headRight C
            (ListBlank.append [1]
              (ListBlank.append [1, 1, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ p) l)))
            (ListBlank.append [1]
              (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
                (ListBlank.append [1, 1] r)))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h_l :
        ListBlank.append [1, 1, 1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ p) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (p + 2)) l := by
      change ListBlank.append (([1, 1] : List (Fin 2)) ^ 2)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ p) l) = _
      rw [← ListBlank.append_pow_add, Nat.add_comm]
    rw [h_l] at h1
    have h2 := ih (p + 2) l r
    have h3 := (h1.trans_star h2).to_star
    have h_arith : p + 2 + 2 * m = p + 2 * (m + 1) := by omega
    rwa [h_arith] at h3

/-- Junction configuration `Junc(u, v, w)`. -/
private def cfg_Junc (u v w : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append [1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
        (ListBlank.append [1, 1, 1, 1, 1] default)))
    (ListBlank.append [1, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ v)
        (ListBlank.append (([1] : List (Fin 2)) ^ w)
          (ListBlank.append [0, 1] default))))

/-- Scan configuration `ScanE(b, m, k)`. -/
private def cfg_ScanE (b m k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
      (ListBlank.append [1, 1, 1, 1, 1] default))
    (ListBlank.append [1]
      (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
        (ListBlank.append [1, 1, 1, 1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] default)))))

/-- Scan configuration `ScanE0(b, m)`. -/
private def cfg_ScanE0 (b m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
      (ListBlank.append [1, 1, 1, 1, 1] default))
    (ListBlank.append [1]
      (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
        (ListBlank.append [1, 1, 0, 1] default)))

/-- Scan configuration `ScanE1(b, m, n)`. -/
private def cfg_ScanE1 (b m n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
      (ListBlank.append [1, 1, 1, 1, 1] default))
    (ListBlank.append [1]
      (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
        (ListBlank.append [1, 1, 1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
            (ListBlank.append [0, 1, 0, 0, 1] default)))))

/-- Tape pattern for `cfg_Junc`. -/
private def pat_Junc : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))))
    head := some A
    right := .sym 1 (.sym 1 (.rep [0, 1] 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }

/-- Tape pattern for `cfg_ScanE`. -/
private def pat_ScanE : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
    head := some E
    right := .sym 1 (.rep [1, 1, 0, 1] 1
      (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
        (.rep [1, 1] 2 (.sym 0 (.sym 1 .default)))))))))) }

/-- Tape pattern for `cfg_ScanE0`. -/
private def pat_ScanE0 : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
    head := some E
    right := .sym 1 (.rep [1, 1, 0, 1] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))) }

/-- Tape pattern for `cfg_ScanE1`. -/
private def pat_ScanE1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
    head := some E
    right := .sym 1 (.rep [1, 1, 0, 1] 1
      (.sym 1 (.sym 1 (.sym 1 (.rep [0, 1] 2
        (.sym 0 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default)))))))))) }

/-- Closed pattern set for `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`. -/
private def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_Junc, .true), (pat_ScanE, .true), (pat_ScanE0, .true), (pat_ScanE1, .true)]

private theorem eval_pat_Junc (vars : ℕ → ℕ) :
    evalTapePattern pat_Junc vars = cfg_Junc (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem eval_pat_ScanE (vars : ℕ → ℕ) :
    evalTapePattern pat_ScanE vars = cfg_ScanE (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem eval_pat_ScanE0 (vars : ℕ → ℕ) :
    evalTapePattern pat_ScanE0 vars = cfg_ScanE0 (vars 0) (vars 1) :=
  rfl

private theorem eval_pat_ScanE1 (vars : ℕ → ℕ) :
    evalTapePattern pat_ScanE1 vars = cfg_ScanE1 (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_Junc (u v w : ℕ) : IsInPatternSet ps (cfg_Junc u v w) :=
  ⟨(pat_Junc, .true), by simp [ps], fun | 0 => u | 1 => v | _ => w, rfl, trivial⟩

private theorem in_ps_ScanE (b m k : ℕ) : IsInPatternSet ps (cfg_ScanE b m k) :=
  ⟨(pat_ScanE, .true), by simp [ps], fun | 0 => b | 1 => m | _ => k, rfl, trivial⟩

private theorem in_ps_ScanE0 (b m : ℕ) : IsInPatternSet ps (cfg_ScanE0 b m) :=
  ⟨(pat_ScanE0, .true), by simp [ps], fun | 0 => b | _ => m, rfl, trivial⟩

private theorem in_ps_ScanE1 (b m n : ℕ) : IsInPatternSet ps (cfg_ScanE1 b m n) :=
  ⟨(pat_ScanE1, .true), by simp [ps], fun | 0 => b | 1 => m | _ => n, rfl, trivial⟩

private theorem step_u0_to_B (n : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1, 1] default))
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r)))
      (Cfg.headRight B
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 3))
          (ListBlank.append [1, 1, 1, 1, 1] default))
        r) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [1, 1, 1, 1, 1] default))
          (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r)))
        (Cfg.headRight B
          (ListBlank.append [1, 1, 1, 1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r))) := by
    have h3 : (([0, 1] : List (Fin 2)) ^ 3) = [0, 1, 0, 1, 0, 1] := rfl
    rw [h3]
    bb_steps
  have h_r :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 3)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n) r) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 3)) r := by
    rw [← ListBlank.append_pow_add, Nat.add_comm]
  rw [h_r] at h1
  exact h1.trans_star (shift_B_01 (n + 3) _ r)

private theorem step_u_pos_to_MidA (v : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append [0, 1] l))
        (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ v) r)))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 2)) l))
        r) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1] (ListBlank.append [0, 1] l))
          (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ v) r)))
        (Cfg.headRight A
          (ListBlank.append [1, 1, 1] l)
          (ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ v) r))) := by
    bb_steps
  have h_r :
      ListBlank.append [0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ v) r) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1)) r := by
    rw [← ListBlank.append_pow_succ]
  rw [h_r] at h1
  have h2 := shift_A_01 (v + 1) (ListBlank.append [1, 1, 1] l) r
  have h3 := h1.trans_star h2
  rwa [ones_comm_111_to_11] at h3

private theorem enter_C_b0 (m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append [1, 1, 1, 1, 1] default)
        (ListBlank.append [1]
          (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
            (ListBlank.append [1, 1] r))))
      (Cfg.headRight C
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (2 * m))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
              (ListBlank.append [1, 1, 1, 1, 1] default))))
        (ListBlank.append [1, 1, 1] r)) := by
  have h_bounce : ∀ r' : ListBlank (Fin 2),
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1, 1, 1] default)
          (ListBlank.append [1, 1, 1] r'))
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append [1, 1, 1] r')) := by
    intro r'
    have h2 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
    rw [h2, list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [1, 1, 1, 1, 1] default)
          (ListBlank.append [1]
            (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
              (ListBlank.append [1, 1] r))))
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append [1]
            (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
              (ListBlank.append [1, 1] r)))) := by
    cases m with
    | zero => exact h_bounce r
    | succ m' =>
      exact h_bounce
        (ListBlank.append [0, 1]
          (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m')
            (ListBlank.append [1, 1] r)))
  have h2 := shift_C_1101 m 0
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
      (ListBlank.append [1, 1, 1, 1, 1] default)) r
  have h3 := h1.trans_star h2
  simpa using h3

private theorem enter_C_b1 (m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 1, 1] default))
        (ListBlank.append [1]
          (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
            (ListBlank.append [1, 1] r))))
      (Cfg.headRight C
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (1 + 2 * m))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
              (ListBlank.append [1, 1, 1, 1, 1] default))))
        (ListBlank.append [1, 1, 1] r)) := by
  have h_bounce : ∀ r' : ListBlank (Fin 2),
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 1, 1] default))
          (ListBlank.append [1, 1, 1] r'))
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append [1, 1, 1] r')) := by
    intro r'
    rw [list_pow_one, list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [0, 1] (ListBlank.append [1, 1, 1, 1, 1] default))
          (ListBlank.append [1]
            (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
              (ListBlank.append [1, 1] r))))
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append [1]
            (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
              (ListBlank.append [1, 1] r)))) := by
    cases m with
    | zero => exact h_bounce r
    | succ m' =>
      exact h_bounce
        (ListBlank.append [0, 1]
          (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m')
            (ListBlank.append [1, 1] r)))
  have h2 := shift_C_1101 m 1
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
      (ListBlank.append [1, 1, 1, 1, 1] default)) r
  exact h1.trans_star h2

private theorem finish_A_001 (u p d : ℕ) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
              (ListBlank.append [1, 1, 1, 1, 1] default))))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (d + 1))
          (ListBlank.append [0, 0, 1] default)))
      (cfg_ScanE u 0 (p + d)) := by
  have h1 := shift_A_01 (d + 1)
    (ListBlank.append [1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
          (ListBlank.append [1, 1, 1, 1, 1] default))))
    (ListBlank.append [0, 0, 1] default)
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (d + 1))
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
              (ListBlank.append [1, 1, 1, 1, 1] default)))) =
        ListBlank.append [1]
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (p + d))
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
                (ListBlank.append [1, 1, 1, 1, 1] default)))) := by
    rw [swap_1_11_pow, ← ListBlank.append_pow_add]
    have h_add : d + 1 + p = 1 + (p + d) := by omega
    rw [h_add, ListBlank.append_pow_add, list_pow_one]
  rw [h_l] at h1
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1]
            (ListBlank.append [1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ (p + d))
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
                  (ListBlank.append [1, 1, 1, 1, 1] default)))))
          (ListBlank.append [0, 0, 1] default))
        (Cfg.headRight E
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (p + d))
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
              (ListBlank.append [1, 1, 1, 1, 1] default)))
          (ListBlank.append [1, 1, 1, 1, 1, 1, 1]
            (ListBlank.append [0, 1] default))) := by
    bb_steps
  have h3 := shift_E_11 (p + d)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
      (ListBlank.append [1, 1, 1, 1, 1] default))
    (ListBlank.append [0, 1] default)
  exact h1.trans_plus (h2.trans_star h3)

private theorem finish_C_ScanE (u p k : ℕ) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
              (ListBlank.append [1, 1, 1, 1, 1] default))))
        (ListBlank.append [1, 1, 1]
          (ListBlank.append [1, 1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0, 1] default)))))
      (cfg_Junc u (p + 2) (2 * k + 1)) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append [1, 1, 1]
            (ListBlank.append [1, 1, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
                (ListBlank.append [0, 1] default)))))
        (Cfg.headRight A
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
              (ListBlank.append [1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
                  (ListBlank.append [0, 1] default)))))) := by
    have h2 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
    rw [h2]
    bb_steps
  have h2 := shift_A_11 p
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
      (ListBlank.append [1, 1, 1, 1, 1] default))
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
      (ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0, 1] default))))
  have h3 := h1.trans_star h2
  have h_r1 :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ p)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0, 1] default)))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (p + 2))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
            (ListBlank.append [0, 1] default)) := by
    rw [← ListBlank.append_pow_add, one_pow_two_mul, ← ListBlank.append_pow_succ]
  rwa [h_r1] at h3

private theorem finish_C_ScanE0 (u p : ℕ) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
              (ListBlank.append [1, 1, 1, 1, 1] default))))
        (ListBlank.append [1, 1, 1]
          (ListBlank.append [0, 1] default)))
      (cfg_ScanE u 0 p) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append [1, 1, 1]
            (ListBlank.append [0, 1] default)))
        (Cfg.headRight A
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0, 0, 1] default))) := by
    rw [list_pow_one]
    bb_steps
  have h2 := finish_A_001 u p 0
  have h3 := h1.trans h2
  simpa using h3

private theorem finish_C_ScanE1 (u p n : ℕ) :
    ReachesPlus target
      (Cfg.headRight C
        (ListBlank.append [1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
              (ListBlank.append [1, 1, 1, 1, 1] default))))
        (ListBlank.append [1, 1, 1]
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
              (ListBlank.append [0, 1, 0, 0, 1] default)))))
      (cfg_ScanE u 0 (p + n + 2)) := by
  have h1 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append [1, 1, 1]
            (ListBlank.append [1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
                (ListBlank.append [0, 1, 0, 0, 1] default)))))
        (Cfg.headRight A
          (ListBlank.append [1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ p)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
                (ListBlank.append [1, 1, 1, 1, 1] default))))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
                (ListBlank.append [0, 0, 1] default))))) := by
    have h2 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
    rw [h2, list_pow_one]
    bb_steps
  have h_r :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
            (ListBlank.append [0, 0, 1] default))) =
        ListBlank.append (([0, 1] : List (Fin 2)) ^ (n + 2 + 1))
          (ListBlank.append [0, 0, 1] default) := by
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add]
    have h_add : 2 + n + 1 = n + 2 + 1 := by omega
    rw [h_add]
  rw [h_r] at h1
  have h2 := finish_A_001 u p (n + 2)
  have h3 := h1.trans h2
  have h_arith : p + (n + 2) = p + n + 2 := by omega
  rwa [h_arith] at h3

private theorem step_Junc (u v w : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Junc u v w) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases u with _ | u'
  · have h_pre := step_u0_to_B v
      (ListBlank.append (([1] : List (Fin 2)) ^ w)
        (ListBlank.append [0, 1] default))
    rcases w with _ | _ | _ | w'
    · have h_post :
          ReachesPlus target
            (Cfg.headRight B
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 3))
                (ListBlank.append [1, 1, 1, 1, 1] default))
              (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                (ListBlank.append [0, 1] default)))
            (cfg_ScanE0 (v + 3) 0) := by
        unfold cfg_ScanE0
        simp only [list_pow_zero, ListBlank.append_nil]
        bb_steps
      exact ⟨cfg_ScanE0 (v + 3) 0, h_pre.trans h_post,
        Or.inl (in_ps_ScanE0 (v + 3) 0)⟩
    · have h_post :
          ReachesPlus target
            (Cfg.headRight B
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 3))
                (ListBlank.append [1, 1, 1, 1, 1] default))
              (ListBlank.append (([1] : List (Fin 2)) ^ 1)
                (ListBlank.append [0, 1] default)))
            (cfg_ScanE1 (v + 2) 0 0) := by
        unfold cfg_ScanE1
        rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (v + 2)]
        simp only [list_pow_one, list_pow_zero, ListBlank.append_nil]
        bb_steps
      exact ⟨cfg_ScanE1 (v + 2) 0 0, h_pre.trans h_post,
        Or.inl (in_ps_ScanE1 (v + 2) 0 0)⟩
    · have h_post :
          ReachesPlus target
            (Cfg.headRight B
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 3))
                (ListBlank.append [1, 1, 1, 1, 1] default))
              (ListBlank.append (([1] : List (Fin 2)) ^ 2)
                (ListBlank.append [0, 1] default)))
            (cfg_ScanE (v + 2) 0 0) := by
        unfold cfg_ScanE
        have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
        rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (v + 2), h2]
        simp only [list_pow_zero, ListBlank.append_nil]
        bb_steps
      exact ⟨cfg_ScanE (v + 2) 0 0, h_pre.trans h_post,
        Or.inl (in_ps_ScanE (v + 2) 0 0)⟩
    · have h_post :
          ReachesPlus target
            (Cfg.headRight B
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 3))
                (ListBlank.append [1, 1, 1, 1, 1] default))
              (ListBlank.append (([1] : List (Fin 2)) ^ (w' + 3))
                (ListBlank.append [0, 1] default)))
            (cfg_Junc (v + 3) 0 w') := by
        unfold cfg_Junc
        have h_w3 :
            ListBlank.append (([1] : List (Fin 2)) ^ (w' + 3))
              (ListBlank.append [0, 1] default) =
              ListBlank.append [1, 1, 1]
                (ListBlank.append (([1] : List (Fin 2)) ^ w')
                  (ListBlank.append [0, 1] default)) := by
          rw [Nat.add_comm w' 3, ListBlank.append_pow_add]
          rfl
        rw [h_w3, list_pow_zero, ListBlank.append_nil]
        bb_steps
      exact ⟨cfg_Junc (v + 3) 0 w', h_pre.trans h_post,
        Or.inl (in_ps_Junc (v + 3) 0 w')⟩
  · have h_l_split :
        ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (u' + 1))
            (ListBlank.append [1, 1, 1, 1, 1] default)) =
          ListBlank.append [1]
            (ListBlank.append [0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                (ListBlank.append [1, 1, 1, 1, 1] default))) := by
      rw [ListBlank.append_pow_succ]
    have h_pre := step_u_pos_to_MidA v
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
        (ListBlank.append [1, 1, 1, 1, 1] default))
      (ListBlank.append (([1] : List (Fin 2)) ^ w)
        (ListBlank.append [0, 1] default))
    rw [← h_l_split] at h_pre
    rcases w with _ | _ | w'
    · have h_mid :
          ReachesPlus target
            (Cfg.headRight A
              (ListBlank.append [1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 2))
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                    (ListBlank.append [1, 1, 1, 1, 1] default))))
              (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                (ListBlank.append [0, 1] default)))
            (Cfg.headRight A
              (ListBlank.append [1, 1]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                  (ListBlank.append [1, 1, 1, 1, 1] default)))
              (ListBlank.append [1, 1]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
                  (ListBlank.append [0, 0, 1] default)))) := by
        have h_step9 :
            ReachesPlus target
              (Cfg.headRight A
                (ListBlank.append [1]
                  (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 2))
                    (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                      (ListBlank.append [1, 1, 1, 1, 1] default))))
                (ListBlank.append (([1] : List (Fin 2)) ^ 0)
                  (ListBlank.append [0, 1] default)))
              (Cfg.headRight A
                (ListBlank.append [1]
                  (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 2))
                    (ListBlank.append [1]
                      (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                        (ListBlank.append [1, 1, 1, 1, 1] default)))))
                (ListBlank.append [1, 1]
                  (ListBlank.append [0, 0, 1] default))) := by
          rw [swap_1_11_pow (v + 2), list_pow_zero, ListBlank.append_nil]
          bb_steps
        have h_sh := shift_A_11 (v + 2)
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
              (ListBlank.append [1, 1, 1, 1, 1] default)))
          (ListBlank.append [0, 0, 1] default)
        exact h_step9.trans_star h_sh
      have h_pre2 := h_pre.trans h_mid
      rcases u' with _ | b
      · have h_14 :
            ReachesPlus target
              (Cfg.headRight A
                (ListBlank.append [1, 1]
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
                    (ListBlank.append [1, 1, 1, 1, 1] default)))
                (ListBlank.append [1, 1]
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
                    (ListBlank.append [0, 0, 1] default))))
              (Cfg.headRight A
                (ListBlank.append [1]
                  (ListBlank.append (([1, 1] : List (Fin 2)) ^ 0)
                    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0)
                      (ListBlank.append [1, 1, 1, 1, 1] default))))
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
                    (ListBlank.append [0, 0, 1] default)))) := by
          have h2 : (([0, 1] : List (Fin 2)) ^ 2) = [0, 1, 0, 1] := rfl
          rw [h2]
          simp only [list_pow_zero, ListBlank.append_nil]
          bb_steps
        have h_r :
            ListBlank.append (([0, 1] : List (Fin 2)) ^ 2)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
                (ListBlank.append [0, 0, 1] default)) =
              ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 3 + 1))
                (ListBlank.append [0, 0, 1] default) := by
          rw [← ListBlank.append_pow_add]
          have h_add : 2 + (v + 2) = v + 3 + 1 := by omega
          rw [h_add]
        rw [h_r] at h_14
        have h_fin := finish_A_001 0 0 (v + 3)
        have h_tot := h_pre2.trans (h_14.trans h_fin)
        have h_z : 0 + (v + 3) = v + 3 := by omega
        rw [h_z] at h_tot
        exact ⟨cfg_ScanE 0 0 (v + 3), h_tot, Or.inl (in_ps_ScanE 0 0 (v + 3))⟩
      · have h_6 :
            ReachesPlus target
              (Cfg.headRight A
                (ListBlank.append [1, 1]
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 1))
                    (ListBlank.append [1, 1, 1, 1, 1] default)))
                (ListBlank.append [1, 1]
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
                    (ListBlank.append [0, 0, 1] default))))
              (cfg_ScanE1 b 0 (v + 2)) := by
          unfold cfg_ScanE1
          have h_r_comm :
              ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
                (ListBlank.append [0, 1, 0, 0, 1] default) =
                ListBlank.append [0, 1]
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
                    (ListBlank.append [0, 0, 1] default)) := by
            change ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
                (ListBlank.append [0, 0, 1] default)) =
              ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 2))
                  (ListBlank.append [0, 0, 1] default))
            rw [← ListBlank.append_pow_add, Nat.add_comm (v + 2) 1,
              ListBlank.append_pow_add]
          rw [h_r_comm, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) b,
            list_pow_zero, ListBlank.append_nil]
          bb_steps
        exact ⟨cfg_ScanE1 b 0 (v + 2), h_pre2.trans h_6,
          Or.inl (in_ps_ScanE1 b 0 (v + 2))⟩
    · have h_mid :
          ReachesPlus target
            (Cfg.headRight A
              (ListBlank.append [1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 2))
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                    (ListBlank.append [1, 1, 1, 1, 1] default))))
              (ListBlank.append (([1] : List (Fin 2)) ^ 1)
                (ListBlank.append [0, 1] default)))
            (Cfg.headRight A
              (ListBlank.append [1]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                  (ListBlank.append [1, 1, 1, 1, 1] default)))
              (ListBlank.append [1, 1]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1))
                  (ListBlank.append [0, 0, 1] default)))) := by
        rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) (v + 1)]
        have h_step2 :
            ReachesPlus target
              (Cfg.headRight A
                (ListBlank.append [1]
                  (ListBlank.append [1, 1]
                    (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 1))
                      (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                        (ListBlank.append [1, 1, 1, 1, 1] default)))))
                (ListBlank.append (([1] : List (Fin 2)) ^ 1)
                  (ListBlank.append [0, 1] default)))
              (Cfg.headRight A
                (ListBlank.append [1]
                  (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 1))
                    (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
                      (ListBlank.append [1, 1, 1, 1, 1] default))))
                (ListBlank.append [1, 1]
                  (ListBlank.append [0, 0, 1] default))) := by
          rw [list_pow_one]
          bb_steps
        have h_sh := shift_A_11 (v + 1)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
            (ListBlank.append [1, 1, 1, 1, 1] default))
          (ListBlank.append [0, 0, 1] default)
        exact h_step2.trans_star h_sh
      have h_pre2 := h_pre.trans h_mid
      rcases u' with _ | b
      · have h_b := step_u0_to_B (v + 1) (ListBlank.append [0, 0, 1] default)
        have h_pre3 := h_pre2.trans h_b
        let cfg_halt := Cfg.headRight D
          (ListBlank.append [0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1 + 3))
              (ListBlank.append [1, 1, 1, 1, 1] default)))
          (ListBlank.append [1] default)
        have h_halt_step :
            ReachesPlus target
              (Cfg.headRight B
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1 + 3))
                  (ListBlank.append [1, 1, 1, 1, 1] default))
                (ListBlank.append [0, 0, 1] default))
              cfg_halt := by
          dsimp [cfg_halt]
          bb_steps
        have h_isNone : (step target cfg_halt).isNone := by
          dsimp [cfg_halt]
          bb_halt
        exact ⟨cfg_halt, h_pre3.trans h_halt_step, Or.inr h_isNone⟩
      · rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) b] at h_pre2
        have h_4 :
            ReachesPlus target
              (Cfg.headRight A
                (ListBlank.append [1]
                  (ListBlank.append [0, 1]
                    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
                      (ListBlank.append [1, 1, 1, 1, 1] default))))
                (ListBlank.append [1, 1]
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1))
                    (ListBlank.append [0, 0, 1] default))))
              (Cfg.headRight A
                (ListBlank.append [1]
                  (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
                    (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
                      (ListBlank.append [1, 1, 1, 1, 1] default))))
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1))
                    (ListBlank.append [0, 0, 1] default)))) := by
          rw [list_pow_one, list_pow_one]
          bb_steps
        have h_r :
            ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1))
                (ListBlank.append [0, 0, 1] default)) =
              ListBlank.append (([0, 1] : List (Fin 2)) ^ (v + 1 + 1))
                (ListBlank.append [0, 0, 1] default) := by
          rw [← ListBlank.append_pow_add, Nat.add_comm]
        rw [h_r] at h_4
        have h_fin := finish_A_001 b 1 (v + 1)
        have h_tot := h_pre2.trans (h_4.trans h_fin)
        have h_arith : 1 + (v + 1) = v + 2 := by omega
        rw [h_arith] at h_tot
        exact ⟨cfg_ScanE b 0 (v + 2), h_tot, Or.inl (in_ps_ScanE b 0 (v + 2))⟩
    · have h_w2 :
          ListBlank.append (([1] : List (Fin 2)) ^ (w' + 2))
            (ListBlank.append [0, 1] default) =
            ListBlank.append [1, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ w')
                (ListBlank.append [0, 1] default)) := by
        rw [Nat.add_comm w' 2, ListBlank.append_pow_add]
        rfl
      rw [h_w2] at h_pre
      have h_sh := shift_A_11 (v + 2)
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ u')
          (ListBlank.append [1, 1, 1, 1, 1] default))
        (ListBlank.append (([1] : List (Fin 2)) ^ w')
          (ListBlank.append [0, 1] default))
      have h_tot := h_pre.trans_star h_sh
      exact ⟨cfg_Junc u' (v + 2) w', h_tot, Or.inl (in_ps_Junc u' (v + 2) w')⟩

private theorem step_ScanE (b m k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_ScanE b m k) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | b'
  · rcases m with _ | m'
    · have h1 : ReachesPlus target (cfg_ScanE 0 0 k) (cfg_Junc 0 0 (2 * k + 6)) := by
        unfold cfg_ScanE cfg_Junc
        have h_r :
            ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 6))
              (ListBlank.append [0, 1] default) =
              ListBlank.append [1, 1, 1, 1, 1, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
                  (ListBlank.append [0, 1] default)) := by
          have h_add : 2 * k + 6 = 6 + 2 * k := by omega
          rw [h_add, ListBlank.append_pow_add, one_pow_two_mul]
          rfl
        rw [h_r]
        simp only [list_pow_zero, ListBlank.append_nil]
        bb_steps
      exact ⟨cfg_Junc 0 0 (2 * k + 6), h1, Or.inl (in_ps_Junc 0 0 (2 * k + 6))⟩
    · have h_pre := enter_C_b0 (m' + 1)
        (ListBlank.append [1, 1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
            (ListBlank.append [0, 1] default)))
      have h_post := finish_C_ScanE 2 (2 * (m' + 1)) k
      have h_tot := h_pre.trans h_post
      have h_arith : 2 * (m' + 1) + 2 = 2 * m' + 4 := by omega
      rw [h_arith] at h_tot
      exact ⟨cfg_Junc 2 (2 * m' + 4) (2 * k + 1), h_tot,
        Or.inl (in_ps_Junc 2 (2 * m' + 4) (2 * k + 1))⟩
  · have h_pre := enter_C_b1 m
      (ListBlank.append [1, 1, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0, 1] default)))
    have h_post := finish_C_ScanE 0 (1 + 2 * m) k
    have h_tot := h_pre.trans h_post
    have h_arith : 1 + 2 * m + 2 = 2 * m + 3 := by omega
    rw [h_arith] at h_tot
    exact ⟨cfg_Junc 0 (2 * m + 3) (2 * k + 1), h_tot,
      Or.inl (in_ps_Junc 0 (2 * m + 3) (2 * k + 1))⟩
  · have h1 : ReachesPlus target (cfg_ScanE (b' + 2) m k) (cfg_ScanE b' (m + 1) k) := by
      unfold cfg_ScanE
      rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (b' + 1),
        ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) b',
        ListBlank.append_pow_succ ([1, 1, 0, 1] : List (Fin 2)) m]
      bb_steps
    exact ⟨cfg_ScanE b' (m + 1) k, h1, Or.inl (in_ps_ScanE b' (m + 1) k)⟩

private theorem step_ScanE0 (b m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_ScanE0 b m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | b'
  · have h_pre := enter_C_b0 m (ListBlank.append [0, 1] default)
    have h_post := finish_C_ScanE0 2 (2 * m)
    exact ⟨cfg_ScanE 2 0 (2 * m), h_pre.trans h_post, Or.inl (in_ps_ScanE 2 0 (2 * m))⟩
  · have h_pre := enter_C_b1 m (ListBlank.append [0, 1] default)
    have h_post := finish_C_ScanE0 0 (1 + 2 * m)
    have h_tot := h_pre.trans h_post
    have h_arith : 1 + 2 * m = 2 * m + 1 := by omega
    rw [h_arith] at h_tot
    exact ⟨cfg_ScanE 0 0 (2 * m + 1), h_tot, Or.inl (in_ps_ScanE 0 0 (2 * m + 1))⟩
  · have h1 : ReachesPlus target (cfg_ScanE0 (b' + 2) m) (cfg_ScanE0 b' (m + 1)) := by
      unfold cfg_ScanE0
      rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (b' + 1),
        ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) b',
        ListBlank.append_pow_succ ([1, 1, 0, 1] : List (Fin 2)) m]
      bb_steps
    exact ⟨cfg_ScanE0 b' (m + 1), h1, Or.inl (in_ps_ScanE0 b' (m + 1))⟩

private theorem step_ScanE1 (b m n : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_ScanE1 b m n) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | b'
  · have h_pre := enter_C_b0 m
      (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
          (ListBlank.append [0, 1, 0, 0, 1] default)))
    have h_post := finish_C_ScanE1 2 (2 * m) n
    exact ⟨cfg_ScanE 2 0 (2 * m + n + 2), h_pre.trans h_post,
      Or.inl (in_ps_ScanE 2 0 (2 * m + n + 2))⟩
  · have h_pre := enter_C_b1 m
      (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
          (ListBlank.append [0, 1, 0, 0, 1] default)))
    have h_post := finish_C_ScanE1 0 (1 + 2 * m) n
    have h_tot := h_pre.trans h_post
    have h_arith : 1 + 2 * m + n + 2 = 2 * m + n + 3 := by omega
    rw [h_arith] at h_tot
    exact ⟨cfg_ScanE 0 0 (2 * m + n + 3), h_tot,
      Or.inl (in_ps_ScanE 0 0 (2 * m + n + 3))⟩
  · have h1 : ReachesPlus target (cfg_ScanE1 (b' + 2) m n) (cfg_ScanE1 b' (m + 1) n) := by
      unfold cfg_ScanE1
      rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (b' + 1),
        ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) b',
        ListBlank.append_pow_succ ([1, 1, 0, 1] : List (Fin 2)) m]
      bb_steps
    exact ⟨cfg_ScanE1 b' (m + 1) n, h1, Or.inl (in_ps_ScanE1 b' (m + 1) n)⟩

/-- `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` is a cryptid. -/
theorem is_cryptid : IsCryptid target := by
  refine ⟨ps, ⟨cfg_Junc 0 0 0, ?_, in_ps_Junc 0 0 0⟩, ?_⟩
  · have h_init : ReachesPlus target (init []) (cfg_Junc 0 0 0) := by
      unfold cfg_Junc
      simp only [list_pow_zero, ListBlank.append_nil]
      bb_steps
    exact h_init.to_star
  · intro cfg h_in
    rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
    simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
    rcases h_mem with rfl | rfl | rfl | rfl
    · rw [eval_pat_Junc]; exact step_Junc (vars 0) (vars 1) (vars 2)
    · rw [eval_pat_ScanE]; exact step_ScanE (vars 0) (vars 1) (vars 2)
    · rw [eval_pat_ScanE0]; exact step_ScanE0 (vars 0) (vars 1)
    · rw [eval_pat_ScanE1]; exact step_ScanE1 (vars 0) (vars 1) (vars 2)

end BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
