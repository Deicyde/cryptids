/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Zf429
public import Cryptids.Semantics.Riemann.Gadgets

/-!
# Boot Verification (`0a.boot1` & `0b.boot2`) for `zf_432_wade.tm` (`Zf429.reference`)

This file proves `boot_to_root`, showing that starting from the blank initial configuration
`init = ⟨0, default⟩`, `ConjectureMachines.Zf429.reference` (`zf_432_wade.tm`) reaches
`zfRootCfg 3821 [] (List.replicate 1909 0)` at `main().0` (State `126`).
-/

@[expose] public section

namespace ConjectureMachines.Zf429.Boot

open Turing StateTransition ConjectureMachines.Zf429

abbrev reference : Machine 432 2 := Machines.zf432
open ConjectureMachines.Riemann543.Layer1
  (nSteps nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_reaches nSteps_eval_dom mk_append_replicate_zero default_eq_mk_nil
   default_cons_zero append_replicate_zero_default fin2_cases
   Tape.mkL Tape.mkL_cons Tape.mk'_cons Tape.mkL_default
   append_replicate_cons append_cons_snoc append_reverse_cons
   encodeReg encodeReg_length encodeReg_reverse append_encodeReg_reverse append_encodeReg
   encodeRegs encodeRegs_nil encodeRegs_cons encodeRegs_append
   regsTape regsTape_nil regsTape_cons regsTape_append
   list_take_cons_drop list_take_set_drop)

/-!
## 1. Basic Step & Scan Primitives
-/

abbrev refTrans (q : Fin 432) (a : Fin 2) : Option (Fin 2 × Dir × Fin 432) :=
  reference.transition q a

theorem step_mkL_left {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem nSteps_mkL_left_scan {q : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {q : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

/-!
## 2. Phase 1 (`0a.boot1.A..E`, States `0..4`)
-/

/-- `k` repetitions of `[0, 1]`. -/
def pair01 : ℕ → List (Fin 2)
  | 0 => []
  | k + 1 => 0 :: 1 :: pair01 k

/-- `k` repetitions of `[1, 0]`. -/
def pair10 : ℕ → List (Fin 2)
  | 0 => []
  | k + 1 => 1 :: 0 :: pair10 k

theorem pair01_snoc (k : ℕ) : pair01 k ++ [0, 1] = pair01 (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pair01, ih]

theorem pair10_snoc (k : ℕ) : pair10 k ++ [1, 0] = pair10 (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pair10, ih]

theorem pair01_add (a b : ℕ) : pair01 (a + b) = pair01 a ++ pair01 b := by
  induction a with
  | zero => simp [pair01]
  | succ a ih => simp [pair01, Nat.succ_add, ih]

theorem pair10_add (a b : ℕ) : pair10 (a + b) = pair10 a ++ pair10 b := by
  induction a with
  | zero => simp [pair10]
  | succ a ih => simp [pair10, Nat.succ_add, ih]

theorem cons_one_pair01 (k : ℕ) : (1 : Fin 2) :: pair01 k = pair10 k ++ [1] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pair01, pair10, ih]

/-- States `3`/`4` (`0a.boot1.D/E`) scan right across `pair10 k` in `2 * k` steps. -/
theorem boot1_scan_DE (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (2 * k)
      ⟨3, Tape.mk' L (ListBlank.append (pair10 k) R)⟩ =
      some ⟨3, Tape.mk' (ListBlank.append (pair10 k).reverse L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    simp only [pair10, ListBlank.append]
    have h1 : step reference ⟨3, Tape.mk' L (((ListBlank.append (pair10 k) R).cons 0).cons 1)⟩ =
        some ⟨4, Tape.mk' (L.cons 1) ((ListBlank.append (pair10 k) R).cons 0)⟩ :=
      step_mk'_right (by rfl) _ _
    have h2 : step reference ⟨4, Tape.mk' (L.cons 1) ((ListBlank.append (pair10 k) R).cons 0)⟩ =
        some ⟨3, Tape.mk' ((L.cons 1).cons 0) (ListBlank.append (pair10 k) R)⟩ :=
      step_mk'_right (by rfl) _ _
    have hrest := ih ((L.cons 1).cons 0)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [hlen] at hcomb
    simpa [pair10, List.reverse_cons, ListBlank.append_assoc] using hcomb

/-- States `3`/`1` (`0a.boot1.D/B`) scan left across `(pair10 k).reverse` in `2 * k` steps,
inverting it to `pair01 k`. -/
theorem boot1_scan_DB (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (2 * k)
      ⟨3, Tape.mkL (ListBlank.append (pair10 k).reverse L) R⟩ =
      some ⟨3, Tape.mkL L (ListBlank.append (pair01 k) R)⟩ := by
  induction k generalizing L R with
  | zero => rfl
  | succ k ih =>
    rw [← pair10_snoc, List.reverse_append, ListBlank.append_assoc]
    have h1 : step reference
        ⟨3, Tape.mkL (((ListBlank.append (pair10 k).reverse L).cons 1).cons 0) R⟩ =
        some ⟨1, Tape.mkL ((ListBlank.append (pair10 k).reverse L).cons 1) (R.cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have h2 : step reference
        ⟨1, Tape.mkL ((ListBlank.append (pair10 k).reverse L).cons 1) (R.cons 1)⟩ =
        some ⟨3, Tape.mkL (ListBlank.append (pair10 k).reverse L) ((R.cons 1).cons 0)⟩ :=
      step_mkL_left (by rfl) _ _
    have hrest := ih L ((R.cons 1).cons 0)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    have hR : ListBlank.append (pair01 k) ((R.cons 1).cons 0) =
        ListBlank.append (pair01 (k + 1)) R := by
      rw [← pair01_snoc, ListBlank.append_assoc]
      rfl
    rw [hlen, hR] at hcomb
    exact hcomb

/-- States `0`/`2` (`0a.boot1.A/C`) scan left across `(pair01 k).reverse` in `2 * k` steps,
converting it to `List.replicate (2 * k) 1`. -/
theorem boot1_scan_AC (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (2 * k)
      ⟨0, Tape.mkL (ListBlank.append (pair01 k).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (List.replicate (2 * k) 1) R)⟩ := by
  induction k generalizing L R with
  | zero => rfl
  | succ k ih =>
    rw [← pair01_snoc, List.reverse_append, ListBlank.append_assoc]
    have h1 : step reference
        ⟨0, Tape.mkL (((ListBlank.append (pair01 k).reverse L).cons 0).cons 1) R⟩ =
        some ⟨2, Tape.mkL ((ListBlank.append (pair01 k).reverse L).cons 0) (R.cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have h2 : step reference
        ⟨2, Tape.mkL ((ListBlank.append (pair01 k).reverse L).cons 0) (R.cons 1)⟩ =
        some ⟨0, Tape.mkL (ListBlank.append (pair01 k).reverse L) ((R.cons 1).cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have hrest := ih L ((R.cons 1).cons 1)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    have hR : ListBlank.append (List.replicate (2 * k) 1) ((R.cons 1).cons 1) =
        ListBlank.append (List.replicate (2 * (k + 1)) 1) R := by
      rw [append_replicate_cons, append_replicate_cons, hlen]
    rw [hlen, hR] at hcomb
    exact hcomb

/-- Canonical left-edge configuration during Phase 1 (`0a.boot1`):
State `0` (`0a.boot1.A`), blank left tape `default`, and `[0, 1, 1] ++ pair01 k ++ 1^m ++ R`
on the right tape. -/
def midCfg (k m : ℕ) (R : ListBlank (Fin 2)) : Cfg 432 2 :=
  ⟨0, Tape.mk' default
    (ListBlank.append ([0, 1, 1] ++ pair01 k ++ List.replicate m 1) R)⟩

/-- Initial 2 steps from `midCfg k m R` (`0 -> 1 -> 3`), converting `[0, 1, 1] ++ pair01 k`
into `pair10 (k + 1) ++ [1]`. -/
theorem midCfg_to_state3 (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps reference 2
      ⟨0, Tape.mk' default (ListBlank.append ([0, 1, 1] ++ pair01 k) R)⟩ =
      some ⟨3, Tape.mk' default (ListBlank.append (pair10 (k + 1) ++ [1]) R)⟩ := by
  simp only [List.cons_append, List.nil_append, ListBlank.append]
  have h1 : step reference
      ⟨0, Tape.mk' default (((ListBlank.append (pair01 k) R).cons 1).cons 1 |>.cons 0)⟩ =
      some ⟨1, Tape.mk' (ListBlank.cons 1 default)
        (((ListBlank.append (pair01 k) R).cons 1).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference
      ⟨1, Tape.mk' (ListBlank.cons 1 default)
        (((ListBlank.append (pair01 k) R).cons 1).cons 1)⟩ =
      some ⟨3, Tape.mk' default
        (((ListBlank.append (pair01 k) R).cons 1).cons 0 |>.cons 1)⟩ := by
    rw [step_mk'_left (by rfl), Tape.mkL_cons, ← Tape.mk'_cons]
  have hcomb := step_nSteps h1 (step_one h2)
  have hR : (((ListBlank.append (pair01 k) R).cons 1).cons 0 |>.cons 1) =
      ListBlank.append (pair10 (k + 1) ++ [1]) R := by
    change ListBlank.append (1 :: 0 :: 1 :: pair01 k) R = _
    rw [cons_one_pair01]
    rfl
  rw [hR] at hcomb
  exact hcomb

/-- From `midCfg k 2 R`, `reference` runs for `4 * k + 17` steps to reach
`midCfg (k + 3) 0 (R.cons 0)`. -/
theorem midCfg_step_two (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps reference (4 * k + 17) (midCfg k 2 R) =
      some (midCfg (k + 3) 0 (R.cons 0)) := by
  unfold midCfg
  simp only [List.replicate, List.append_nil, List.append_assoc, ListBlank.append_assoc]
  have hinit := midCfg_to_state3 k (ListBlank.append [1, 1] R)
  have hscanR := boot1_scan_DE (k + 1) default (ListBlank.append [1, 1, 1] R)
  simp only [ListBlank.append_assoc, ListBlank.append] at hinit hscanR
  set L_k := ListBlank.append (pair10 (k + 1)).reverse default
  -- 5 steps on `[1, 1, 1]`: `3 -> 4 -> 1 -> 3 -> 1 -> 3`
  have hs1 : step reference ⟨3, Tape.mk' L_k (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨4, Tape.mk' (L_k.cons 1) ((R.cons 1).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs2 : step reference ⟨4, Tape.mk' (L_k.cons 1) ((R.cons 1).cons 1)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs3 : step reference ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 1)⟩ =
      some ⟨3, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ _
  have hs4 : step reference ⟨3, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hs5 : step reference ⟨1, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨3, Tape.mkL L_k (((R.cons 0).cons 1).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hturn := step_nSteps hs1 (step_nSteps hs2 (step_nSteps hs3 (step_nSteps hs4 (step_one hs5))))
  have hscanL := boot1_scan_DB (k + 1) default (((R.cons 0).cons 1).cons 0)
  set R_k := ListBlank.append (pair01 (k + 1)) (((R.cons 0).cons 1).cons 0)
  -- 6 steps at the left edge `default`: `3 -> 1 -> 0 -> 1 -> 0 -> 2 -> 0`
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have he1 : step reference ⟨3, Tape.mkL default R_k⟩ =
      some ⟨1, Tape.mkL default (R_k.cons 1)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_left (by rfl) default R_k
  have he2 : step reference ⟨1, Tape.mkL default (R_k.cons 1)⟩ =
      some ⟨0, Tape.mkL default ((R_k.cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_left (by rfl) default (R_k.cons 1)
  have he3 : step reference ⟨0, Tape.mkL default ((R_k.cons 1).cons 0)⟩ =
      some ⟨1, Tape.mk' (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_right (by rfl) default ((R_k.cons 1).cons 0)
  have he4 : step reference ⟨1, Tape.mk' (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ =
      some ⟨0, Tape.mkL (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ :=
    step_mk'_left (by rfl) _ (R_k.cons 1)
  have he5 : step reference ⟨0, Tape.mkL (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ =
      some ⟨2, Tape.mkL default (((R_k.cons 1).cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have he6 : step reference ⟨2, Tape.mkL default (((R_k.cons 1).cons 0).cons 1)⟩ =
      some ⟨0, Tape.mk' default ((((R_k.cons 1).cons 0).cons 1).cons 1 |>.cons 0)⟩ := by
    conv_lhs => rw [hdef]
    rw [step_mkL_left (by rfl), Tape.mkL_default]
  have hedge := step_nSteps he1 (step_nSteps he2 (step_nSteps he3
    (step_nSteps he4 (step_nSteps he5 (step_one he6)))))
  have htotal := nSteps_bind_eq hinit (nSteps_bind_eq hscanR
    (nSteps_bind_eq hturn (nSteps_bind_eq hscanL hedge)))
  have hlen : 2 + (2 * (k + 1) + (5 + (2 * (k + 1) + 6))) = 4 * k + 17 := by omega
  rw [hlen] at htotal
  have hR_eq : ((((R_k.cons 1).cons 0).cons 1).cons 1 |>.cons 0) =
      ListBlank.append [0, 1, 1] (ListBlank.append (pair01 (k + 3)) (R.cons 0)) := by
    simp only [R_k]
    change ListBlank.append [0, 1, 1]
      (ListBlank.append (pair01 (k + 2)) (ListBlank.append [0, 1] (R.cons 0))) = _
    rw [← ListBlank.append_assoc (pair01 (k + 2)), pair01_snoc]
  rw [hR_eq] at htotal
  exact htotal

/-- Corollary: `midCfg k (m + 3) R` transitions to `midCfg (k + 4) m R` in `4 * k + 17` steps. -/
theorem midCfg_step_three (k m : ℕ) (R : ListBlank (Fin 2)) :
    nSteps reference (4 * k + 17) (midCfg k (m + 3) R) =
      some (midCfg (k + 4) m R) := by
  have heq : midCfg k (m + 3) R = midCfg k 2 (ListBlank.append (List.replicate (m + 1) 1) R) := by
    unfold midCfg
    have hrep : List.replicate (m + 3) (1 : Fin 2) =
        List.replicate 2 1 ++ List.replicate (m + 1) 1 := by
      rw [show m + 3 = 2 + (m + 1) by omega, List.replicate_add]
    simp only [hrep, List.append_assoc, ListBlank.append_assoc]
  rw [heq, midCfg_step_two]
  congr 1
  unfold midCfg
  simp only [List.replicate, List.append_assoc, ListBlank.append_assoc, ListBlank.append]
  have hpair : ListBlank.append (pair01 (k + 3))
      (((ListBlank.append (List.replicate m 1) R).cons 1).cons 0) =
      ListBlank.append (pair01 (k + 4)) (ListBlank.append (List.replicate m 1) R) := by
    rw [← pair01_snoc (k + 3), ListBlank.append_assoc]
    rfl
  rw [hpair]

/-- Multi-step loop: `midCfg k (3 * j + r) R` reaches `midCfg (k + 4 * j) r R`. -/
theorem midCfg_loop (j k r : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, nSteps reference s (midCfg k (3 * j + r) R) =
      some (midCfg (k + 4 * j) r R) := by
  induction j generalizing k with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ j ih =>
    have h1 : 3 * (j + 1) + r = (3 * j + r) + 3 := by omega
    rw [h1]
    have hstep := midCfg_step_three k (3 * j + r) R
    obtain ⟨s, hs⟩ := ih (k + 4)
    have h2 : k + 4 + 4 * j = k + 4 * (j + 1) := by omega
    rw [h2] at hs
    exact ⟨_, nSteps_bind_eq hstep hs⟩

theorem pair10_succ_eq (m : ℕ) : pair10 (m + 1) = (1 :: pair01 m) ++ [0] := by
  rw [cons_one_pair01, List.append_assoc, ← pair10_snoc]; rfl

/-- From `midCfg k 0 ((R.cons 0).cons 0)`, `reference` runs for `4 * k + 12` steps to reach
`midCfg 0 (2 * k + 2) ((R.cons 1).cons 0)`. -/
theorem midCfg_step_zero (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps reference (4 * k + 12) (midCfg k 0 ((R.cons 0).cons 0)) =
      some (midCfg 0 (2 * k + 2) ((R.cons 1).cons 0)) := by
  unfold midCfg
  simp only [List.replicate, List.append_nil]
  have hinit := midCfg_to_state3 k ((R.cons 0).cons 0)
  have hpair : ListBlank.append (pair10 (k + 1) ++ [1]) ((R.cons 0).cons 0) =
      ListBlank.append (pair10 (k + 2)) (R.cons 0) := by
    rw [ListBlank.append_assoc, ← pair10_snoc (k + 1), ListBlank.append_assoc]
    rfl
  rw [hpair] at hinit
  have hscanR := boot1_scan_DE (k + 2) default (R.cons 0)
  have hL_split : ListBlank.append (pair10 (k + 2)).reverse default =
      (ListBlank.append (pair01 (k + 1)).reverse (ListBlank.cons 1 default)).cons 0 := by
    simp only [pair10_succ_eq (k + 1), List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, ListBlank.append_assoc, ListBlank.append]
  rw [hL_split] at hscanR
  set L_p := ListBlank.append (pair01 (k + 1)).reverse (ListBlank.cons 1 default)
  have hs1 : step reference ⟨3, Tape.mk' (L_p.cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mkL (L_p.cons 0) (R.cons 1)⟩ :=
    step_mk'_left (by rfl) _ _
  have hs2 : step reference ⟨1, Tape.mkL (L_p.cons 0) (R.cons 1)⟩ =
      some ⟨0, Tape.mkL L_p ((R.cons 1).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscanL := boot1_scan_AC (k + 1) (ListBlank.cons 1 default) ((R.cons 1).cons 0)
  set R_ones := ListBlank.append (List.replicate (2 * (k + 1)) 1) ((R.cons 1).cons 0)
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have he1 : step reference ⟨0, Tape.mkL (ListBlank.cons 1 default) R_ones⟩ =
      some ⟨2, Tape.mkL default (R_ones.cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have he2 : step reference ⟨2, Tape.mkL default (R_ones.cons 1)⟩ =
      some ⟨0, Tape.mk' default (((R_ones.cons 1).cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    rw [step_mkL_left (by rfl), Tape.mkL_default]
  have htotal := nSteps_bind_eq hinit (nSteps_bind_eq hscanR
    (step_nSteps hs1 (step_nSteps hs2 (nSteps_bind_eq hscanL
      (step_nSteps he1 (step_one he2))))))
  have hlen : 2 + (2 * (k + 2) + (2 * (k + 1) + (1 + 1) + 1 + 1)) = 4 * k + 12 := by omega
  rw [hlen] at htotal
  have hR_eq : (((R_ones.cons 1).cons 1).cons 0) =
      ListBlank.append ([0, 1,
        1] ++ pair01 0 ++ List.replicate (2 * k + 2) 1) ((R.cons 1).cons 0) := by
    simp only [R_ones, pair01, List.append_nil]
    rfl
  rw [hR_eq] at htotal
  exact htotal

/-- Exit from Phase 1 (`0a.boot1`): from `midCfg k 1 (R.cons 0)`, `reference` runs for
`2 * k + 11` steps to reach State `60` (`3.prooflist.inc`). -/
theorem midCfg_exit_one (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps reference (2 * k + 11) (midCfg k 1 (R.cons 0)) =
      some ⟨60, Tape.mk' (ListBlank.append (pair10 (k + 1) ++ [1]).reverse default)
        ((R.cons 0).cons 1)⟩ := by
  unfold midCfg
  simp only [List.replicate, List.append_assoc, ListBlank.append_assoc]
  have hinit := midCfg_to_state3 k ((R.cons 0).cons 1)
  have hscanR := boot1_scan_DE (k + 1) default (((R.cons 0).cons 1).cons 1)
  simp only [ListBlank.append_assoc, ListBlank.append] at hinit hscanR
  set L_k := ListBlank.append (pair10 (k + 1)).reverse default
  have hs1 : step reference ⟨3, Tape.mk' L_k (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨4, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs2 : step reference ⟨4, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs3 : step reference ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨0, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ _
  have hs4 : step reference ⟨0, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mkL_right (by rfl) _ _
  have hs5 : step reference ⟨1, Tape.mk' ((L_k.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨0, Tape.mkL ((L_k.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ _
  have hs6 : step reference ⟨0, Tape.mkL ((L_k.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨2, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hs7 : step reference ⟨2, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨60, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_right (by rfl) _ _
  have htotal := nSteps_bind_eq hinit (nSteps_bind_eq hscanR
    (step_nSteps hs1 (step_nSteps hs2 (step_nSteps hs3
      (step_nSteps hs4 (step_nSteps hs5 (step_nSteps hs6 (step_one hs7))))))))
  have hlen : 2 + (2 * (k + 1) + 7) = 2 * k + 11 := by omega
  rw [hlen] at htotal
  simpa [L_k, List.reverse_append, ListBlank.append_assoc] using htotal

/-- Complete Phase 1 (`0a.boot1`) evaluation: from `init = ⟨0, default⟩`, `reference` reaches
State `60` (`3.prooflist.inc`) with `pair10 1909 ++ [1]` reversed on the left tape and
`[1, 0, 1, 1, 1, 1]` on the right tape. -/
theorem boot1_eval :
    ∃ s, nSteps reference s init =
      some ⟨60, Tape.mk' (ListBlank.append (pair10 1909 ++ [1]).reverse default)
        (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ := by
  -- Step 0..4: `init -> midCfg 0 0 default`
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have h0_1 : step reference init = some ⟨1, Tape.mk' (ListBlank.cons 1 default) default⟩ := by
    have h := step_mk'_right (q := 0) (q' := 1) (a := 0) (b := 1) (by rfl) default default
    rwa [← hdef] at h
  have h0_2 : step reference ⟨1, Tape.mk' (ListBlank.cons 1 default) default⟩ =
      some ⟨0, Tape.mkL (ListBlank.cons 1 default) default⟩ := by
    have h := step_mk'_left (q := 1) (q' := 0) (a := 0) (b := 0) (by rfl)
      (ListBlank.cons 1 default) default
    rwa [← hdef] at h
  have h0_3 : step reference ⟨0, Tape.mkL (ListBlank.cons 1 default) default⟩ =
      some ⟨2, Tape.mkL default (ListBlank.cons 1 default)⟩ :=
    step_mkL_left (by rfl) _ _
  have h0_4 : step reference ⟨2, Tape.mkL default (ListBlank.cons 1 default)⟩ =
      some (midCfg 0 0 default) := by
    have h := step_mkL_left (q := 2) (q' := 0) (a := 0) (b := 1) (by rfl)
      default (ListBlank.cons 1 default)
    rw [← hdef, Tape.mkL_default] at h
    exact h
  have hr0 : nSteps reference 4 init = some (midCfg 0 0 default) :=
    step_nSteps h0_1 (step_nSteps h0_2 (step_nSteps h0_3 (step_one h0_4)))
  -- Round 0 -> Round 1 (`midCfg 0 0 default -> midCfg 0 2 [0, 1]`)
  have hr0_1 : nSteps reference 12 (midCfg 0 0 default) =
      some (midCfg 0 2 (ListBlank.append [0, 1] default)) := by
    have h := midCfg_step_zero 0 default
    rwa [default_cons_zero, default_cons_zero] at h
  -- Round 1 -> Round 2 (`midCfg 0 2 [0, 1] -> midCfg 3 0 [0, 0, 1] -> midCfg 0 8 [0, 1, 1]`)
  have hr1_a := midCfg_step_two 0 (ListBlank.append [0, 1] default)
  have hr1_b : nSteps reference 24 (midCfg 3 0 ((ListBlank.append [0, 1] default).cons 0)) =
      some (midCfg 0 8 (ListBlank.append [0, 1, 1] default)) :=
    midCfg_step_zero 3 (ListBlank.cons 1 default)
  -- Round 2 -> Round 3 (`midCfg 0 8 [0, 1, 1] -> midCfg 8 2 [0, 1, 1] -> midCfg 11 0 [0, 0, 1, 1]
  -- -> midCfg 0 24 [0, 1, 1, 1]`)
  obtain ⟨s2, hr2_loop⟩ := midCfg_loop 2 0 2 (ListBlank.append [0, 1, 1] default)
  have hr2_a := midCfg_step_two 8 (ListBlank.append [0, 1, 1] default)
  have hr2_b : nSteps reference 56 (midCfg 11 0 ((ListBlank.append [0, 1, 1] default).cons 0)) =
      some (midCfg 0 24 (ListBlank.append [0, 1, 1, 1] default)) :=
    midCfg_step_zero 11 (ListBlank.append [1, 1] default)
  -- Round 3 -> Round 4 (`midCfg 0 24 [0, 1, 1, 1] -> midCfg 32 0 [0, 1, 1, 1] = midCfg 33 2 default
  -- -> midCfg 36 0 [0] -> midCfg 0 74 [0, 1]`)
  obtain ⟨s3, hr3_loop⟩ := midCfg_loop 8 0 0 (ListBlank.append [0, 1, 1, 1] default)
  have hr3_eq : midCfg 32 0 (ListBlank.append [0, 1, 1, 1] default) = midCfg 33 2 default := by
    unfold midCfg
    simp only [List.replicate, List.append_nil, List.append_assoc, ListBlank.append_assoc]
    have hp : ListBlank.append (pair01 32) (ListBlank.append [0, 1, 1, 1] default) =
        ListBlank.append (pair01 33) (ListBlank.append [1, 1] default) := by
      rw [← pair01_snoc 32, ListBlank.append_assoc]
      rfl
    rw [hp]
  rw [hr3_eq] at hr3_loop
  have hr3_a := midCfg_step_two 33 default
  have hr3_b : nSteps reference 156 (midCfg 36 0 (ListBlank.cons 0 default)) =
      some (midCfg 0 74 (ListBlank.append [0, 1] default)) := by
    have h := midCfg_step_zero 36 default
    rwa [default_cons_zero] at h
  -- Round 4 -> Round 5 (`midCfg 0 74 [0, 1] -> midCfg 96 2 [0, 1] -> midCfg 99 0 [0, 0, 1] ->
  -- midCfg 0 200 [0, 1, 1]`)
  obtain ⟨s4, hr4_loop⟩ := midCfg_loop 24 0 2 (ListBlank.append [0, 1] default)
  have hr4_a := midCfg_step_two 96 (ListBlank.append [0, 1] default)
  have hr4_b : nSteps reference 408 (midCfg 99 0 ((ListBlank.append [0, 1] default).cons 0)) =
      some (midCfg 0 200 (ListBlank.append [0, 1, 1] default)) :=
    midCfg_step_zero 99 (ListBlank.cons 1 default)
  -- Round 5 -> Round 6 (`midCfg 0 200 [0, 1, 1] -> midCfg 264 2 [0, 1, 1] -> midCfg 267 0 [0, 0, 1,
  -- 1] -> midCfg 0 536 [0, 1, 1, 1]`)
  obtain ⟨s5, hr5_loop⟩ := midCfg_loop 66 0 2 (ListBlank.append [0, 1, 1] default)
  have hr5_a := midCfg_step_two 264 (ListBlank.append [0, 1, 1] default)
  have hr5_b : nSteps reference 1080 (midCfg 267 0 ((ListBlank.append [0, 1, 1] default).cons 0)) =
      some (midCfg 0 536 (ListBlank.append [0, 1, 1, 1] default)) :=
    midCfg_step_zero 267 (ListBlank.append [1, 1] default)
  -- Round 6 -> Round 7 (`midCfg 0 536 [0, 1, 1, 1] -> midCfg 712 2 [0, 1, 1, 1] -> midCfg 715 0 [0,
  -- 0, 1, 1, 1] -> midCfg 0 1432 [0, 1, 1, 1, 1]`)
  obtain ⟨s6, hr6_loop⟩ := midCfg_loop 178 0 2 (ListBlank.append [0, 1, 1, 1] default)
  have hr6_a := midCfg_step_two 712 (ListBlank.append [0, 1, 1, 1] default)
  have hr6_b : nSteps reference 2872 (midCfg 715 0 ((ListBlank.append [0, 1, 1,
      1] default).cons 0)) =
      some (midCfg 0 1432 (ListBlank.append [0, 1, 1, 1, 1] default)) :=
    midCfg_step_zero 715 (ListBlank.append [1, 1, 1] default)
  -- Round 7 -> Exit (`midCfg 0 1432 [0, 1, 1, 1, 1] -> midCfg 1908 1 [0, 1, 1, 1, 1] -> State 60`)
  obtain ⟨s7, hr7_loop⟩ := midCfg_loop 477 0 1 (ListBlank.append [0, 1, 1, 1, 1] default)
  have hexit := midCfg_exit_one 1908 (ListBlank.append [1, 1, 1, 1] default)
  exact ⟨_, nSteps_bind_eq hr0 (nSteps_bind_eq hr0_1 (nSteps_bind_eq hr1_a (nSteps_bind_eq hr1_b
    (nSteps_bind_eq hr2_loop (nSteps_bind_eq hr2_a (nSteps_bind_eq hr2_b
      (nSteps_bind_eq hr3_loop (nSteps_bind_eq hr3_a (nSteps_bind_eq hr3_b
        (nSteps_bind_eq hr4_loop (nSteps_bind_eq hr4_a (nSteps_bind_eq hr4_b
          (nSteps_bind_eq hr5_loop (nSteps_bind_eq hr5_a (nSteps_bind_eq hr5_b
            (nSteps_bind_eq hr6_loop (nSteps_bind_eq hr6_a (nSteps_bind_eq hr6_b
              (nSteps_bind_eq hr7_loop hexit)))))))))))))))))))⟩

/-!
## 3. Layer 1 Register & Dispatch Gadgets Needed for Phase 2 (`0b.boot2`)
-/

/-- The `[1, 1, 0]` root prefix on the left half-tape at `main().0` (State `126`). -/
abbrev rootLeft : ListBlank (Fin 2) :=
  (default : ListBlank (Fin 2)).cons 1 |>.cons 1 |>.cons 0

/-- Canonical configuration at `main().0` (State `126`). -/
def zfRootCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 432 2 :=
  ⟨126, Tape.mk' rootLeft
    (ListBlank.append
      (stack ++ List.replicate (padTotal - stack.length) 0 ++ [1, 0] ++ encodeRegs regs)
      extra)⟩

theorem zfRootCfg_default_eq (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    zfRootCfg padTotal stack regs default =
      ⟨126, Tape.mk' rootLeft
        (ListBlank.append stack
          (ListBlank.append (List.replicate (padTotal - stack.length) 0)
            (regsTape (0 :: regs))))⟩ := by
  unfold zfRootCfg
  simp only [List.append_assoc, ListBlank.append_assoc]
  rfl

/-- `4.dispatch` chain (`0 ↦ 4.dispatch.scan = 86`, `d + 1 ↦ 4.dispatch.<d>` for `0 ≤ d ≤ 14`). -/
def zfDispatchState : ℕ → Fin 432
  | 0 => 86
  | 1 => 71
  | 2 => 72
  | 3 => 78
  | 4 => 79
  | 5 => 80
  | 6 => 81
  | 7 => 82
  | 8 => 83
  | 9 => 84
  | 10 => 85
  | 11 => 73
  | 12 => 74
  | 13 => 75
  | 14 => 76
  | 15 => 77
  | _ => 86

theorem zfDispatch_trans_zero (d : ℕ) (hd1 : 1 ≤ d) (hd15 : d ≤ 15) :
    refTrans (zfDispatchState d) 0 = some (0, .left, zfDispatchState (d - 1)) := by
  revert d hd1 hd15; decide

theorem zfDispatch_trans_one (d : ℕ) (hd1 : 1 ≤ d) (hd15 : d ≤ 15) :
    refTrans (zfDispatchState d) 1 = some (1, .left, zfDispatchState d) := by
  revert d hd1 hd15; decide

/-- `zfDispatchState d` scans left across `(pair10 k).reverse` (`k < d ≤ 15`) in `2 * k` steps,
ending in `zfDispatchState (d - k)`. -/
theorem zfDispatch_scan_pair10 (k d : ℕ) (hk : k < d) (hd15 : d ≤ 15)
    (L R : ListBlank (Fin 2)) :
    nSteps reference (2 * k)
      ⟨zfDispatchState d, Tape.mkL (ListBlank.append (pair10 k).reverse L) R⟩ =
      some ⟨zfDispatchState (d - k), Tape.mkL L (ListBlank.append (pair10 k) R)⟩ := by
  induction k generalizing d L R with
  | zero => rfl
  | succ k ih =>
    have hL : ListBlank.append (pair10 (k + 1)).reverse L =
        ((ListBlank.append (pair10 k).reverse L).cons 1).cons 0 := by
      rw [← pair10_snoc, List.reverse_append, ListBlank.append_assoc]
      rfl
    rw [hL]
    have hd1 : 1 ≤ d := by omega
    have hd1' : 1 ≤ d - 1 := by omega
    have hd15' : d - 1 ≤ 15 := by omega
    have hk' : k < d - 1 := by omega
    have h1 : step reference
        ⟨zfDispatchState d, Tape.mkL (((ListBlank.append (pair10 k).reverse L).cons 1).cons 0) R⟩ =
        some ⟨zfDispatchState (d - 1),
          Tape.mkL ((ListBlank.append (pair10 k).reverse L).cons 1) (R.cons 0)⟩ :=
      step_mkL_left (zfDispatch_trans_zero d hd1 hd15) _ _
    have h2 : step reference
        ⟨zfDispatchState (d - 1),
          Tape.mkL ((ListBlank.append (pair10 k).reverse L).cons 1) (R.cons 0)⟩ =
        some ⟨zfDispatchState (d - 1),
          Tape.mkL (ListBlank.append (pair10 k).reverse L) ((R.cons 0).cons 1)⟩ :=
      step_mkL_left (zfDispatch_trans_one (d - 1) hd1' hd15') _ _
    have hrest := ih (d - 1) hk' hd15' L ((R.cons 0).cons 1)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    have hsub : d - 1 - k = d - (k + 1) := by omega
    have hR : ListBlank.append (pair10 k) ((R.cons 0).cons 1) =
        ListBlank.append (pair10 (k + 1)) R := by
      rw [← pair10_snoc, ListBlank.append_assoc]
      rfl
    rw [hlen, hsub, hR] at hcomb
    exact hcomb

/-- On the blank left tape `default`, `zfDispatchState k` (`1 ≤ k ≤ 15`) steps left `k` times
into `default` to reach `4.dispatch.scan` (`86`), then scans right `k + 1` times back to `R`. -/
theorem zfDispatch_bounce_default (k : ℕ) (_hk1 : 1 ≤ k) (hk15 : k ≤ 15)
    (R : ListBlank (Fin 2)) :
    nSteps reference (2 * k + 1)
      ⟨zfDispatchState k, Tape.mkL default R⟩ =
      some ⟨86, Tape.mk' default R⟩ := by
  have hleft : ∀ m, m ≤ 15 → ∀ R',
      nSteps reference m ⟨zfDispatchState m, Tape.mkL default R'⟩ =
        some ⟨86, Tape.mkL default (ListBlank.append (List.replicate m 0) R')⟩ := by
    intro m hm R'
    induction m generalizing R' with
    | zero => rfl
    | succ m ihm =>
      have hm1 : 1 ≤ m + 1 := by omega
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      have h1 : step reference ⟨zfDispatchState (m + 1), Tape.mkL default R'⟩ =
          some ⟨zfDispatchState m, Tape.mkL default (R'.cons 0)⟩ := by
        conv_lhs => rw [hdef]
        exact step_mkL_left (zfDispatch_trans_zero (m + 1) hm1 hm) default R'
      have hrest := ihm (by omega) (R'.cons 0)
      rw [append_replicate_cons] at hrest
      exact step_nSteps h1 hrest
  have hl := hleft k hk15 R
  conv at hl => rhs; rw [Tape.mkL_default]
  have hcons : (ListBlank.append (List.replicate k 0) R).cons 0 =
      ListBlank.append (List.replicate (k + 1) 0) R := by
    rw [List.replicate_succ, ListBlank.append]
  rw [hcons] at hl
  have hr := nSteps_mk'_right_scan (q := 86) (a := 0) (b := 0) (by rfl) (k + 1) default R
  rw [append_replicate_zero_default] at hr
  have hcomb := nSteps_bind_eq hl hr
  have hlen : k + (k + 1) = 2 * k + 1 := by omega
  rw [hlen] at hcomb
  exact hcomb

/-- From `4.dispatch.scan` (`86`) at `[1, 1, a]`, `reference` takes 3 steps (`86 -> 87 -> 88 ->
126`)
to reach `main().0` (`126`) with `rootLeft` on the left tape. -/
theorem root_scan_to_main (a : Fin 2) (R : ListBlank (Fin 2)) :
    nSteps reference 3
      ⟨86, Tape.mk' default (ListBlank.append [1, 1, a] R)⟩ =
      some ⟨126, Tape.mk' rootLeft R⟩ := by
  simp only [ListBlank.append]
  have h1 : step reference ⟨86, Tape.mk' default (((R.cons a).cons 1).cons 1)⟩ =
      some ⟨87, Tape.mk' (ListBlank.cons 1 default) ((R.cons a).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference ⟨87, Tape.mk' (ListBlank.cons 1 default) ((R.cons a).cons 1)⟩ =
      some ⟨88, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons a)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step reference ⟨88, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons a)⟩ =
      some ⟨126, Tape.mk' rootLeft R⟩ := by
    rcases fin2_cases a with rfl | rfl
    · exact step_mk'_right (by rfl) _ _
    · exact step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- `0b.boot2.0/1` (`5`/`6`) scans right across a `[1, 0]` pair in 2 steps. -/
theorem boot2_scan_pair (L R : ListBlank (Fin 2)) :
    nSteps reference 2
      ⟨5, Tape.mk' L (ListBlank.append [1, 0] R)⟩ =
      some ⟨5, Tape.mk' ((L.cons 1).cons 0) R⟩ := by
  have h1 : step reference ⟨5, Tape.mk' L ((R.cons 0).cons 1)⟩ =
      some ⟨6, Tape.mk' (L.cons 1) (R.cons 0)⟩ :=
    step_mk'_right (by rfl) L (R.cons 0)
  have h2 : step reference ⟨6, Tape.mk' (L.cons 1) (R.cons 0)⟩ =
      some ⟨5, Tape.mk' ((L.cons 1).cons 0) R⟩ :=
    step_mk'_right (by rfl) (L.cons 1) R
  exact step_nSteps h1 (step_one h2)

/-- `0b.boot2.0/1` (`5`/`6`) scans right across `pair10 m` in `2 * m` steps. -/
theorem boot2_scan_pairs (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (2 * m)
      ⟨5, Tape.mk' L (ListBlank.append (pair10 m) R)⟩ =
      some ⟨5, Tape.mk' (ListBlank.append (pair10 m).reverse L) R⟩ := by
  induction m generalizing L with
  | zero => rfl
  | succ m ih =>
    have hp : ListBlank.append (pair10 (m + 1)) R =
        ListBlank.append [1, 0] (ListBlank.append (pair10 m) R) := rfl
    rw [hp]
    have h1 := boot2_scan_pair L (ListBlank.append (pair10 m) R)
    have h2 := ih ((L.cons 1).cons 0)
    have hcomb := nSteps_bind_eq h1 h2
    have hlen : 2 + 2 * m = 2 * (m + 1) := by omega
    rw [hlen] at hcomb
    simpa [pair10, List.reverse_cons, ListBlank.append_assoc] using hcomb

/-- `0b.boot2.0..2` (`5 -> 6 -> 7`) on `[1, 1, 0]` transitions to `3.prooflist.inc` (`60`). -/
theorem boot2_to_inc0 (L R : ListBlank (Fin 2)) :
    nSteps reference 3
      ⟨5, Tape.mk' L (ListBlank.append [1, 1, 0] R)⟩ =
      some ⟨60, Tape.mk' (((L.cons 1).cons 1).cons 0) R⟩ := by
  have h1 : step reference ⟨5, Tape.mk' L (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (L.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference ⟨6, Tape.mk' (L.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨7, Tape.mk' ((L.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step reference ⟨7, Tape.mk' ((L.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨60, Tape.mk' (((L.cons 1).cons 1).cons 0) R⟩ :=
    step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- `0b.boot2.0..2` (`5 -> 6 -> 7`) on `[1, 1, 1]` transitions to `3.prooflist.decnz` (`59`). -/
theorem boot2_to_decnz0 (L R : ListBlank (Fin 2)) :
    nSteps reference 3
      ⟨5, Tape.mk' L (ListBlank.append [1, 1, 1] R)⟩ =
      some ⟨59, Tape.mk' (((L.cons 1).cons 1).cons 1) R⟩ := by
  have h1 : step reference ⟨5, Tape.mk' L (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (L.cons 1) ((R.cons 1).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference ⟨6, Tape.mk' (L.cons 1) ((R.cons 1).cons 1)⟩ =
      some ⟨7, Tape.mk' ((L.cons 1).cons 1) (R.cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step reference ⟨7, Tape.mk' ((L.cons 1).cons 1) (R.cons 1)⟩ =
      some ⟨59, Tape.mk' (((L.cons 1).cons 1).cons 1) R⟩ :=
    step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- Key Phase 2 bounce theorem: from `zfDispatchState d` (`1 ≤ d ≤ 15`) with `pair10 m` (`m ≥ 1`)
reversed on the left tape, `reference` bounces and scans right in `0b.boot2.0/1` (`5`/`6`) back
to State `5` at the right end of `pair10 m`. -/
theorem zfDispatch_to_boot2 (m d : ℕ) (hm : 1 ≤ m) (hd1 : 1 ≤ d) (hd15 : d ≤ 15)
    (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨zfDispatchState d, Tape.mkL (ListBlank.append (pair10 m).reverse default) R⟩ =
      some ⟨5, Tape.mk' (ListBlank.append (pair10 m).reverse default) R⟩ := by
  by_cases hmd : m < d
  · have hscan := zfDispatch_scan_pair10 m d hmd hd15 default R
    have hbounce := zfDispatch_bounce_default (d - m) (by omega) (by omega)
      (ListBlank.append (pair10 m) R)
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hp : ListBlank.append (pair10 (m' + 1)) R =
        ((ListBlank.append (pair10 m') R).cons 0).cons 1 := rfl
    rw [hp] at hbounce
    have hs1 : step reference
        ⟨86, Tape.mk' default (((ListBlank.append (pair10 m') R).cons 0).cons 1)⟩ =
        some ⟨87, Tape.mk' (ListBlank.cons 1 default)
          ((ListBlank.append (pair10 m') R).cons 0)⟩ :=
      step_mk'_right (by rfl) _ _
    have hs2 : step reference
        ⟨87, Tape.mk' (ListBlank.cons 1 default)
          ((ListBlank.append (pair10 m') R).cons 0)⟩ =
        some ⟨5, Tape.mk' ((ListBlank.cons 1 default).cons 0)
          (ListBlank.append (pair10 m') R)⟩ :=
      step_mk'_right (by rfl) _ _
    have hboot := boot2_scan_pairs m' ((ListBlank.cons 1 default).cons 0) R
    have hL_eq : ListBlank.append (pair10 m').reverse ((ListBlank.cons 1 default).cons 0) =
        ListBlank.append (pair10 (m' + 1)).reverse default := by
      simp [pair10, List.reverse_cons, ListBlank.append_assoc]
    rw [hL_eq] at hboot
    have htotal := nSteps_bind_eq hscan (nSteps_bind_eq hbounce
      (step_nSteps hs1 (step_nSteps hs2 hboot)))
    exact ⟨_, by omega, htotal⟩
  · have hsplit : m = (m - d) + 1 + (d - 1) := by omega
    have hp : ListBlank.append (pair10 m).reverse default =
        ListBlank.append (pair10 (d - 1)).reverse
          (((ListBlank.append (pair10 (m - d)).reverse default).cons 1).cons 0) := by
      conv_lhs => rw [hsplit, pair10_add, pair10_add]
      simp [pair10, List.reverse_append, ListBlank.append_assoc]
    rw [hp]
    set L_rem := ListBlank.append (pair10 (m - d)).reverse default
    have hscan := zfDispatch_scan_pair10 (d - 1) d (by omega) hd15
      ((L_rem.cons 1).cons 0) R
    have hsub : d - (d - 1) = 1 := by omega
    rw [hsub] at hscan
    set R_d := ListBlank.append (pair10 (d - 1)) R
    have hs1 : step reference ⟨zfDispatchState 1, Tape.mkL ((L_rem.cons 1).cons 0) R_d⟩ =
        some ⟨86, Tape.mkL (L_rem.cons 1) (R_d.cons 0)⟩ :=
      step_mkL_left (by rfl) _ _
    have hs2 : step reference ⟨86, Tape.mkL (L_rem.cons 1) (R_d.cons 0)⟩ =
        some ⟨87, Tape.mk' (L_rem.cons 1) (R_d.cons 0)⟩ :=
      step_mkL_right (by rfl) _ _
    have hs3 : step reference ⟨87, Tape.mk' (L_rem.cons 1) (R_d.cons 0)⟩ =
        some ⟨5, Tape.mk' ((L_rem.cons 1).cons 0) R_d⟩ :=
      step_mk'_right (by rfl) _ _
    have hboot := boot2_scan_pairs (d - 1) ((L_rem.cons 1).cons 0) R
    have htotal := nSteps_bind_eq hscan (step_nSteps hs1 (step_nSteps hs2 (step_nSteps hs3 hboot)))
    exact ⟨_, by omega, htotal⟩

/-!
### Pass 2 Register Increment & Decrement Lemmas (for Register `0` = `prooflist`)
-/

theorem return0_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (r + 2)
      ⟨43, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨43, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨43, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨44, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨44, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨43, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 43) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

theorem return0_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (encodeRegs regs).length
      ⟨43, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨43, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return0_scan_reg, ListBlank.append_assoc]

theorem return0_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs regs).length + 2)
      ⟨43, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨89, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return0_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step reference
      ⟨43, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨44, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨44, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨89, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

theorem inc_shift_eval_zf (suff : List ℕ) (m : ℕ) (L_prev : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨41, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev) (regsTape suff)⟩ =
      some ⟨43, Tape.mkL L_prev (regsTape (m :: suff))⟩ := by
  induction suff generalizing m L_prev with
  | nil =>
    rw [regsTape_nil, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨41, Tape.mk' ((ListBlank.append (List.replicate m 1) L_prev).cons 1) default⟩ =
        some ⟨43, Tape.mkL ((ListBlank.append (List.replicate m 1) L_prev).cons 1)
          (ListBlank.cons 0 default)⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      exact step_mk'_left (by rfl) _ default
    have hscan := nSteps_mkL_left_scan (q := 43) (a := 1) (b := 1) (by rfl)
      (m + 1) L_prev (ListBlank.cons 0 default)
    conv at hscan => lhs; rw [List.replicate_succ, ListBlank.append]
    have hcomb := step_nSteps h1 hscan
    rw [← append_encodeReg, ← regsTape_nil, ← regsTape_cons] at hcomb
    exact ⟨m + 2, by omega, hcomb⟩
  | cons r rs ih =>
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨41, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨42, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) L_prev).cons 0)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    rw [← append_encodeReg_reverse] at h1
    have hscan := nSteps_mk'_right_scan (q := 42) (a := 1) (b := 1) (by rfl)
      r (ListBlank.append (encodeReg m).reverse L_prev) ((regsTape rs).cons 0)
    have h2 : step reference
        ⟨42, Tape.mk' (ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)) ((regsTape rs).cons 0)⟩ =
        some ⟨41, Tape.mk' ((ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)).cons 1) (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcons1 : (ListBlank.append (List.replicate r 1)
        (ListBlank.append (encodeReg m).reverse L_prev)).cons 1 =
        ListBlank.append (List.replicate (r + 1) 1)
          (ListBlank.append (encodeReg m).reverse L_prev) := by
      rw [List.replicate_succ, ListBlank.append]
    rw [hcons1] at h2
    obtain ⟨s, hs1, hs⟩ := ih r (ListBlank.append (encodeReg m).reverse L_prev)
    have hret := return0_scan_reg m L_prev (regsTape (r :: rs))
    rw [← regsTape_cons] at hret
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan
      (step_nSteps h2 (nSteps_bind_eq hs hret)))
    exact ⟨_, by omega, hcomb⟩

/-- Pass 2 `3.prooflist.inc` (`60`) evaluation on `p :: 0 :: rs`: increments `0` to `1` and
returns to State `89` (`6.break.0`). -/
theorem stage3_inc0_pass2 (p : ℕ) (rs : List ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨60, Tape.mk' L ((regsTape (p :: 0 :: rs)).cons 0 |>.cons 1)⟩ =
      some ⟨89, Tape.mkL L ((regsTape (p :: 1 :: rs)).cons 0 |>.cons 0)⟩ := by
  rw [regsTape_cons, append_encodeReg]
  have h1 : step reference
      ⟨60, Tape.mk' L
        (((ListBlank.append (List.replicate (p +
          1) 1) ((regsTape (0 :: rs)).cons 0)).cons 0).cons 1)⟩ =
      some ⟨15, Tape.mk' (L.cons 0)
        ((ListBlank.append (List.replicate (p + 1) 1) ((regsTape (0 :: rs)).cons 0)).cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference
      ⟨15, Tape.mk' (L.cons 0)
        ((ListBlank.append (List.replicate (p + 1) 1) ((regsTape (0 :: rs)).cons 0)).cons 0)⟩ =
      some ⟨11, Tape.mk' ((L.cons 0).cons 0)
        (ListBlank.append (List.replicate (p + 1) 1) ((regsTape (0 :: rs)).cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 11) (a := 1) (b := 1) (by rfl)
    (p + 1) ((L.cons 0).cons 0) ((regsTape (0 :: rs)).cons 0)
  have h3 : step reference
      ⟨11, Tape.mk' (ListBlank.append (List.replicate (p + 1) 1) ((L.cons 0).cons 0))
        ((regsTape (0 :: rs)).cons 0)⟩ =
      some ⟨13, Tape.mk' (ListBlank.append (encodeReg p).reverse ((L.cons 0).cons 0))
        (regsTape (0 :: rs))⟩ := by
    rw [append_encodeReg_reverse]
    exact step_mk'_right (by rfl) _ _
  set L_p := ListBlank.append (encodeReg p).reverse ((L.cons 0).cons 0)
  rw [regsTape_cons, append_encodeReg] at h3 ⊢
  have h4 : step reference ⟨13, Tape.mk' L_p (((regsTape rs).cons 0).cons 1)⟩ =
      some ⟨13, Tape.mk' (L_p.cons 1) ((regsTape rs).cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h5 : step reference ⟨13, Tape.mk' (L_p.cons 1) ((regsTape rs).cons 0)⟩ =
      some ⟨41, Tape.mk' (ListBlank.append (List.replicate 2 1) L_p) (regsTape rs)⟩ :=
    step_mk'_right (by rfl) _ _
  obtain ⟨s_sh, _, hshift⟩ := inc_shift_eval_zf rs 1 L_p
  have hret := return0_scan_fence [p] L (regsTape (1 :: rs))
  simp only [encodeRegs_cons, encodeRegs_nil, List.append_nil] at hret
  rw [← regsTape_cons] at hret
  have htotal := step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan
    (step_nSteps h3 (step_nSteps h4 (step_nSteps h5 (nSteps_bind_eq hshift hret))))))
  exact ⟨_, by omega, htotal⟩

theorem dec_shift_reg_zf (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (m + 2)
      ⟨40, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ =
      some ⟨40, Tape.mkL L (ListBlank.append (encodeReg m) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨40, Tape.mkL ((ListBlank.append (List.replicate m 1) (L.cons 0)).cons 1) R⟩ =
      some ⟨39, Tape.mkL (ListBlank.append (List.replicate m 1) (L.cons 0)) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 39) (a := 1) (b := 1) (by rfl)
    m (L.cons 0) (R.cons 0)
  have h2 : step reference
      ⟨39, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ =
      some ⟨40, Tape.mkL L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcons : (ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1 =
      ListBlank.append (encodeReg m) R := by
    rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  rw [hcons] at h2
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  simpa [Nat.add_assoc] using hcomb

theorem dec_scan_and_shift_zf (suff : List ℕ) (m : ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨38, Tape.mk' (ListBlank.append (encodeReg m).reverse (L.cons 0)) (regsTape suff)⟩ =
      some ⟨40, Tape.mkL L (regsTape (m :: (suff ++ [0])))⟩ := by
  induction suff generalizing m L with
  | nil =>
    rw [regsTape_nil, append_encodeReg_reverse]
    have h1 : step reference
        ⟨38, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨39, Tape.mkL ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0)
          default⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      rw [step_mk'_left (by rfl), default_cons_zero]
    have h2 : step reference
        ⟨39, Tape.mkL ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨40, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0))
          (regsTape [0])⟩ := by
      have h := step_mkL_left (q := 39) (q' := 40) (a := 0) (b := 1) (by rfl)
        (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default
      have h0 : (default : ListBlank (Fin 2)).cons 1 = regsTape [0] := by
        rw [regsTape_cons, regsTape_nil, append_encodeReg, default_cons_zero]
        rfl
      rw [h0] at h
      exact h
    have hshift := dec_shift_reg_zf m L (regsTape [0])
    rw [← regsTape_cons] at hshift
    exact ⟨m + 4, by omega, step_nSteps h1 (step_nSteps h2 hshift)⟩
  | cons r rs ih =>
    let L' := ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)
    have hL' : ListBlank.append (encodeReg m).reverse (L.cons 0) = L'.cons 0 :=
      append_encodeReg_reverse m (L.cons 0)
    rw [hL', regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨38, Tape.mk' (L'.cons 0)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨37, Tape.mk' ((L'.cons 0).cons 1)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 37) (a := 1) (b := 1) (by rfl)
      r ((L'.cons 0).cons 1) ((regsTape rs).cons 0)
    have h2 : step reference
        ⟨37, Tape.mk' (ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1))
          ((regsTape rs).cons 0)⟩ =
        some ⟨38, Tape.mk' ((ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1)).cons 0)
          (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan_reg := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r (L'.cons 0)] at hscan_reg
    obtain ⟨s, hs1, hs⟩ := ih r L'
    have hshift := dec_shift_reg_zf m L (regsTape (r :: (rs ++ [0])))
    rw [← regsTape_cons] at hshift
    have hcomb := nSteps_bind_eq hscan_reg (nSteps_bind_eq hs hshift)
    exact ⟨_, by omega, hcomb⟩

theorem dec_shift2_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (r + 2)
      ⟨40, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨43, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨40, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨43, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨43, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨43, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 43) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

/-- Pass 2 `3.prooflist.decnz` (`59`) evaluation on `p :: 1 :: rs`: decrements `1` to `0`,
appends `[0]` to `rs`, and returns to State `89` (`6.break.0`). -/
theorem stage3_decnz0_pass2_one (p : ℕ) (rs : List ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨59, Tape.mk' L ((regsTape (p :: 1 :: rs)).cons 0 |>.cons 1)⟩ =
      some ⟨89, Tape.mkL L ((regsTape (p :: 0 :: (rs ++ [0]))).cons 0 |>.cons 0)⟩ := by
  rw [regsTape_cons, append_encodeReg]
  have h1 : step reference
      ⟨59, Tape.mk' L
        (((ListBlank.append (List.replicate (p +
          1) 1) ((regsTape (1 :: rs)).cons 0)).cons 0).cons 1)⟩ =
      some ⟨14, Tape.mk' (L.cons 0)
        ((ListBlank.append (List.replicate (p + 1) 1) ((regsTape (1 :: rs)).cons 0)).cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference
      ⟨14, Tape.mk' (L.cons 0)
        ((ListBlank.append (List.replicate (p + 1) 1) ((regsTape (1 :: rs)).cons 0)).cons 0)⟩ =
      some ⟨10, Tape.mk' ((L.cons 0).cons 0)
        (ListBlank.append (List.replicate (p + 1) 1) ((regsTape (1 :: rs)).cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 10) (a := 1) (b := 1) (by rfl)
    (p + 1) ((L.cons 0).cons 0) ((regsTape (1 :: rs)).cons 0)
  have h3 : step reference
      ⟨10, Tape.mk' (ListBlank.append (List.replicate (p + 1) 1) ((L.cons 0).cons 0))
        ((regsTape (1 :: rs)).cons 0)⟩ =
      some ⟨12, Tape.mk' (ListBlank.append (encodeReg p).reverse ((L.cons 0).cons 0))
        (regsTape (1 :: rs))⟩ := by
    rw [append_encodeReg_reverse]
    exact step_mk'_right (by rfl) _ _
  set L_p := ListBlank.append (encodeReg p).reverse ((L.cons 0).cons 0)
  rw [regsTape_cons, append_encodeReg] at h3 ⊢
  have h4 : step reference ⟨12, Tape.mk' L_p ((((regsTape rs).cons 0).cons 1).cons 1)⟩ =
      some ⟨36, Tape.mk' (L_p.cons 0) (((regsTape rs).cons 0).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h5 : step reference ⟨36, Tape.mk' (L_p.cons 0) (((regsTape rs).cons 0).cons 1)⟩ =
      some ⟨37, Tape.mk' ((L_p.cons 0).cons 1) ((regsTape rs).cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h6 : step reference ⟨37, Tape.mk' ((L_p.cons 0).cons 1) ((regsTape rs).cons 0)⟩ =
      some ⟨38, Tape.mk' (ListBlank.append (encodeReg 0).reverse (L_p.cons 0)) (regsTape rs)⟩ :=
    step_mk'_right (by rfl) _ _
  obtain ⟨s_sh, _, hshift⟩ := dec_scan_and_shift_zf rs 0 L_p
  have hret1 := dec_shift2_scan_reg p ((L.cons 0).cons 0) (regsTape (0 :: (rs ++ [0])))
  rw [← regsTape_cons] at hret1
  have hret2 : step reference
      ⟨43, Tape.mkL ((L.cons 0).cons 0) (regsTape (p :: 0 :: (rs ++ [0])))⟩ =
      some ⟨44, Tape.mkL (L.cons 0) ((regsTape (p :: 0 :: (rs ++ [0]))).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hret3 : step reference
      ⟨44, Tape.mkL (L.cons 0) ((regsTape (p :: 0 :: (rs ++ [0]))).cons 0)⟩ =
      some ⟨89, Tape.mkL L (((regsTape (p :: 0 :: (rs ++ [0]))).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have htotal := step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan
    (step_nSteps h3 (step_nSteps h4 (step_nSteps h5 (step_nSteps h6
      (nSteps_bind_eq hshift (nSteps_bind_eq hret1 (step_nSteps hret2 (step_one hret3))))))))))
  exact ⟨_, by omega, htotal⟩

theorem break0_step (c₀ : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (c₀ + 1)
      ⟨89, Tape.mkL (ListBlank.append (List.replicate c₀ 1) (L.cons 0)) R⟩ =
      some ⟨47, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate c₀ 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 89) (a := 1) (b := 0) (by rfl) c₀ (L.cons 0) R
  have h1 : step reference ⟨89, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate c₀ 0) R)⟩ =
      some ⟨47, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate c₀ 0) R)⟩ :=
    step_mkL_right (by rfl) _ _
  exact nSteps_bind_eq hscan (step_one h1)

/-- Cleanup gadget (`47 -> 48 -> 5 -> 92`) from State `47` to State `92` (`6.continue.0`),
for any left tape `L`. -/
theorem cleanup_to_92 (L : ListBlank (Fin 2)) (z p : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨47, Tape.mk' L (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg p) R))⟩ =
      some ⟨92, Tape.mkL L (ListBlank.append (List.replicate (z + p) 0) (ListBlank.append [1,
        0] R))⟩ := by
  have hscan_z := nSteps_mk'_right_scan (q := 47) (a := 0) (b := 0) (by rfl) z
    L (ListBlank.append (encodeReg p) R)
  conv at hscan_z => rhs; rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨47, Tape.mk' (ListBlank.append (List.replicate z 0) L)
        ((ListBlank.append (List.replicate p 1) (R.cons 0)).cons 1)⟩ =
      some ⟨48, Tape.mk' ((ListBlank.append (List.replicate z 0) L).cons 0)
        (ListBlank.append (List.replicate p 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan_p := nSteps_mk'_right_scan (q := 48) (a := 1) (b := 0) (by rfl) p
    ((ListBlank.append (List.replicate z 0) L).cons 0) (R.cons 0)
  have hzeros : ListBlank.append (List.replicate p 0)
      ((ListBlank.append (List.replicate z 0) L).cons 0) =
      (ListBlank.append (List.replicate (z + p) 0) L).cons 0 := by
    rw [append_replicate_cons, ← ListBlank.append_assoc, ← List.replicate_add]
    have hadd : p + 1 + z = (z + p) + 1 := by omega
    rw [hadd, List.replicate_succ, ListBlank.append]
  rw [hzeros] at hscan_p
  have h2 : step reference
      ⟨48, Tape.mk' ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ =
      some ⟨5, Tape.mkL ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ R
  have h3 : step reference
      ⟨5, Tape.mkL ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ =
      some ⟨92, Tape.mkL (ListBlank.append (List.replicate (z + p) 0) L)
        (ListBlank.append [1, 0] R)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan_back := nSteps_mkL_left_scan (q := 92) (a := 0) (b := 0) (by rfl) (z + p)
    L (ListBlank.append [1, 0] R)
  have htotal := nSteps_bind_eq hscan_z (step_nSteps h1 (nSteps_bind_eq hscan_p
    (step_nSteps h2 (step_nSteps h3 hscan_back))))
  exact ⟨_, by omega, htotal⟩

/-!
## 4. Phase 2 (`0b.boot2`) Loop and `boot_to_root`
-/

/-- Left tape during Phase 2: `pair10 m ++ [1, 1, a]` reversed on `default`. -/
def bootLeft (m : ℕ) (a : Fin 2) : ListBlank (Fin 2) :=
  (((ListBlank.append (pair10 m).reverse default).cons 1).cons 1).cons a

theorem bootLeft_zero : bootLeft 0 0 = rootLeft := rfl

/-- From State `92` (`6.continue.0`) with `bootLeft m a` (`1 ≤ m`) on the left tape,
`reference` scans `[1, 1, a]`, bounces in `4.dispatch` / `0b.boot2` via `zfDispatch_to_boot2`,
and enters State `60` (when `a = 0`) or State `59` (when `a = 1`). -/
theorem continue0_boot_pos (m : ℕ) (hm : 1 ≤ m) (a : Fin 2) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨92, Tape.mkL (bootLeft m a) R⟩ =
      some ⟨if a = 0 then 60 else 59, Tape.mk' (bootLeft m a) R⟩ := by
  unfold bootLeft
  set L_m := ListBlank.append (pair10 m).reverse default
  rcases fin2_cases a with rfl | rfl
  · have h1 : step reference ⟨92, Tape.mkL (((L_m.cons 1).cons 1).cons 0) R⟩ =
        some ⟨92, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 0)⟩ := step_mkL_left (by rfl) _ _
    have h2 : step reference ⟨92, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 0)⟩ =
        some ⟨77, Tape.mkL (L_m.cons 1) ((R.cons 0).cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h3 : step reference ⟨77, Tape.mkL (L_m.cons 1) ((R.cons 0).cons 1)⟩ =
        some ⟨zfDispatchState 15, Tape.mkL L_m (ListBlank.append [1, 1, 0] R)⟩ :=
      step_mkL_left (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := zfDispatch_to_boot2 m 15 hm (by decide) (by decide)
      (ListBlank.append [1, 1, 0] R)
    have hinc := boot2_to_inc0 L_m R
    exact ⟨_, by omega, step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hb hinc)))⟩
  · have h1 : step reference ⟨92, Tape.mkL (((L_m.cons 1).cons 1).cons 1) R⟩ =
        some ⟨77, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h2 : step reference ⟨77, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 1)⟩ =
        some ⟨77, Tape.mkL (L_m.cons 1) ((R.cons 1).cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h3 : step reference ⟨77, Tape.mkL (L_m.cons 1) ((R.cons 1).cons 1)⟩ =
        some ⟨zfDispatchState 15, Tape.mkL L_m (ListBlank.append [1, 1, 1] R)⟩ :=
      step_mkL_left (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := zfDispatch_to_boot2 m 15 hm (by decide) (by decide)
      (ListBlank.append [1, 1, 1] R)
    have hdec := boot2_to_decnz0 L_m R
    exact ⟨_, by omega, step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hb hdec)))⟩

/-- Pass 1 register preparation during Phase 2 (`1b.reg.prep_1/2` = `8/9`):
from `⟨if a = 0 then 60 else 59, Tape.mk' (bootLeft m a) ...⟩` with `r + 3` zeros before `[1, 0]`,
`reference` prepares `encodeReg (r + 1)` and returns to `⟨if a = 0 then 60 else 59, ...⟩`. -/
theorem boot_pass1_eval (m : ℕ) (hm : 1 ≤ m) (a : Fin 2) (r : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨if a = 0 then 60 else 59, Tape.mk' (bootLeft m a)
        (ListBlank.append (List.replicate (r + 3) 0) (ListBlank.append [1, 0] R))⟩ =
      some ⟨if a = 0 then 60 else 59, Tape.mk' (bootLeft m a)
        ((ListBlank.append (encodeReg (r + 1)) R).cons 0 |>.cons 1)⟩ := by
  set q : Fin 432 := if a = 0 then 60 else 59
  have hq : refTrans q 0 = some (1, .right, 8) := by
    rcases fin2_cases a with rfl | rfl <;> rfl
  set L := bootLeft m a
  have hrep : List.replicate (r + 3) (0 : Fin 2) = 0 :: 0 :: List.replicate (r + 1) 0 := rfl
  rw [hrep, ListBlank.append, ListBlank.append]
  have h1 : step reference
      ⟨q, Tape.mk' L (((ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1,
        0] R)).cons 0).cons 0)⟩ =
      some ⟨8, Tape.mk' (L.cons 1)
        ((ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R)).cons 0)⟩ :=
    step_mk'_right hq _ _
  have h2 : step reference
      ⟨8, Tape.mk' (L.cons 1)
        ((ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R)).cons 0)⟩ =
      some ⟨9, Tape.mk' ((L.cons 1).cons 0)
        (ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan_r := nSteps_mk'_right_scan (q := 9) (a := 0) (b := 1) (by rfl) (r + 1)
    ((L.cons 1).cons 0) (ListBlank.append [1, 0] R)
  have h3 : step reference
      ⟨9, Tape.mk' (ListBlank.append (List.replicate (r + 1) 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨92, Tape.mkL (ListBlank.append (List.replicate (r + 1) 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ :=
    step_mk'_left (by rfl) _ (R.cons 0)
  rw [List.replicate_succ, ListBlank.append] at h3
  have h4 : step reference
      ⟨92, Tape.mkL ((ListBlank.append (List.replicate r 1) ((L.cons 1).cons 0)).cons 1)
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨77, Tape.mkL (ListBlank.append (List.replicate r 1) ((L.cons 1).cons 0))
        ((ListBlank.append [1, 0] R).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan_back := nSteps_mkL_left_scan (q := 77) (a := 1) (b := 1) (by rfl) r
    ((L.cons 1).cons 0) ((ListBlank.append [1, 0] R).cons 1)
  have henc : ListBlank.append (List.replicate r 1) ((ListBlank.append [1, 0] R).cons 1) =
      ListBlank.append (encodeReg (r + 1)) R := by
    have h10 : ListBlank.append [1, 0] R = (R.cons 0).cons 1 := rfl
    rw [h10, append_replicate_cons, append_replicate_cons, ← append_encodeReg]
  rw [henc] at hscan_back
  set R_enc := ListBlank.append (encodeReg (r + 1)) R
  have h5 : step reference ⟨77, Tape.mkL ((L.cons 1).cons 0) R_enc⟩ =
      some ⟨76, Tape.mkL (L.cons 1) (R_enc.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h6 : step reference ⟨76, Tape.mkL (L.cons 1) (R_enc.cons 0)⟩ =
      some ⟨76, Tape.mkL L ((R_enc.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  set R_prep := (R_enc.cons 0).cons 1
  set L_m := ListBlank.append (pair10 m).reverse default
  rcases fin2_cases a with rfl | rfl
  · have h7 : step reference ⟨76, Tape.mkL (((L_m.cons 1).cons 1).cons 0) R_prep⟩ =
        some ⟨75, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 0)⟩ := step_mkL_left (by rfl) _ _
    have h8 : step reference ⟨75, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 0)⟩ =
        some ⟨75, Tape.mkL (L_m.cons 1) ((R_prep.cons 0).cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h9 : step reference ⟨75, Tape.mkL (L_m.cons 1) ((R_prep.cons 0).cons 1)⟩ =
        some ⟨zfDispatchState 13, Tape.mkL L_m (ListBlank.append [1, 1, 0] R_prep)⟩ :=
      step_mkL_left (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := zfDispatch_to_boot2 m 13 hm (by decide) (by decide)
      (ListBlank.append [1, 1, 0] R_prep)
    have hinc := boot2_to_inc0 L_m R_prep
    have htotal := step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan_r
      (step_nSteps h3 (step_nSteps h4 (nSteps_bind_eq hscan_back
        (step_nSteps h5 (step_nSteps h6 (step_nSteps h7 (step_nSteps h8
          (step_nSteps h9 (nSteps_bind_eq hb hinc)))))))))))
    exact ⟨_, by omega, htotal⟩
  · have h7 : step reference ⟨76, Tape.mkL (((L_m.cons 1).cons 1).cons 1) R_prep⟩ =
        some ⟨76, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h8 : step reference ⟨76, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 1)⟩ =
        some ⟨76, Tape.mkL (L_m.cons 1) ((R_prep.cons 1).cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h9 : step reference ⟨76, Tape.mkL (L_m.cons 1) ((R_prep.cons 1).cons 1)⟩ =
        some ⟨zfDispatchState 14, Tape.mkL L_m (ListBlank.append [1, 1, 1] R_prep)⟩ :=
      step_mkL_left (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := zfDispatch_to_boot2 m 14 hm (by decide) (by decide)
      (ListBlank.append [1, 1, 1] R_prep)
    have hdec := boot2_to_decnz0 L_m R_prep
    have htotal := step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan_r
      (step_nSteps h3 (step_nSteps h4 (nSteps_bind_eq hscan_back
        (step_nSteps h5 (step_nSteps h6 (step_nSteps h7 (step_nSteps h8
          (step_nSteps h9 (nSteps_bind_eq hb hdec)))))))))))
    exact ⟨_, by omega, htotal⟩

/-- Invariant configuration at the start of each Phase 2 outer cycle (`m` pairs of `[1, 0]` on
the left of `[1, 1, 0]`, `2 * i + 3` zeros before `[1, 0]`, and `i` zero-initialized registers). -/
def boot2CycleCfg (m i : ℕ) : Cfg 432 2 :=
  ⟨60, Tape.mk' (bootLeft m 0)
    (ListBlank.append (List.replicate (2 * i + 3) 0)
      (ListBlank.append [1, 0] (regsTape (List.replicate i 0))))⟩

/-- Initial Phase 2 transition from the exit of Phase 1 (`k = m + 1`) to `boot2CycleCfg m 1`. -/
theorem boot2_init_step (m : ℕ) (hm : 1 ≤ m) :
    ∃ s, nSteps reference s
      ⟨60, Tape.mk' (ListBlank.append (pair10 (m + 1) ++ [1]).reverse default)
        (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ =
      some (boot2CycleCfg m 1) := by
  set L_m := ListBlank.append (pair10 m).reverse default
  have hL : ListBlank.append (pair10 (m + 1) ++ [1]).reverse default =
      (((L_m.cons 1).cons 0).cons 1) := by
    rw [← pair10_snoc m, List.append_assoc, List.reverse_append, ListBlank.append_assoc]
    rfl
  rw [hL]
  set L₀ := ((L_m.cons 1).cons 0).cons 1
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have hs1 : step reference ⟨60, Tape.mk' L₀ (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ =
      some ⟨15, Tape.mk' (L₀.cons 0) (ListBlank.append [0, 1, 1, 1, 1] default)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs2 : step reference ⟨15, Tape.mk' (L₀.cons 0) (ListBlank.append [0, 1, 1, 1, 1] default)⟩ =
      some ⟨11, Tape.mk' ((L₀.cons 0).cons 0) (ListBlank.append (List.replicate 4 1) default)⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 11) (a := 1) (b := 1) (by rfl) 4
    ((L₀.cons 0).cons 0) default
  set L_ones := ListBlank.append (List.replicate 4 1) ((L₀.cons 0).cons 0)
  have hs3 : step reference ⟨11, Tape.mk' L_ones default⟩ =
      some ⟨13, Tape.mk' (ListBlank.append (encodeReg 3).reverse ((L₀.cons 0).cons 0)) default⟩ :=
        by
    rw [append_encodeReg_reverse]
    have h := step_mk'_right (q := 11) (q' := 13) (a := 0) (b := 0) (by rfl) L_ones default
    rwa [← hdef] at h
  set L_p := ListBlank.append (encodeReg 3).reverse ((L₀.cons 0).cons 0)
  have hs4 : step reference ⟨13, Tape.mk' L_p default⟩ =
      some ⟨41, Tape.mk' (L_p.cons 1) default⟩ := by
    have h := step_mk'_right (q := 13) (q' := 41) (a := 0) (b := 1) (by rfl) L_p default
    rwa [← hdef] at h
  have hs5 : step reference ⟨41, Tape.mk' (L_p.cons 1) default⟩ =
      some ⟨43, Tape.mkL (L_p.cons 1) default⟩ := by
    have h := step_mk'_left (q := 41) (q' := 43) (a := 0) (b := 0) (by rfl) (L_p.cons 1) default
    rwa [← hdef] at h
  have hs6 : step reference ⟨43, Tape.mkL (L_p.cons 1) default⟩ =
      some ⟨43, Tape.mkL L_p (regsTape [0])⟩ := by
    have h := step_mkL_left (q := 43) (q' := 43) (a := 1) (b := 1) (by rfl) L_p default
    have h0 : (default : ListBlank (Fin 2)).cons 1 = regsTape [0] := by
      rw [regsTape_cons, regsTape_nil, append_encodeReg, default_cons_zero]
      rfl
    rwa [h0] at h
  have hret := return0_scan_fence [3] L₀ (regsTape [0])
  simp only [encodeRegs_cons, encodeRegs_nil, List.append_nil] at hret
  have hb0 := break0_step 1 (L_m.cons 1)
    ((ListBlank.append (encodeReg 3) (regsTape [0])).cons 0 |>.cons 0)
  simp only [List.replicate, ListBlank.append] at hb0
  have hs7 : step reference
      ⟨47, Tape.mk' ((L_m.cons 1).cons 1)
        ((((ListBlank.append (encodeReg 3) (regsTape [0])).cons 0).cons 0).cons 0)⟩ =
      some ⟨47, Tape.mk' (bootLeft m 0)
        (ListBlank.append (List.replicate 2 0) (ListBlank.append (encodeReg 3) (regsTape [0])))⟩ :=
    step_mk'_right (by rfl) _ _
  obtain ⟨s_cl, _, hcl⟩ := cleanup_to_92 (bootLeft m 0) 2 3 (regsTape [0])
  obtain ⟨s_cont, _, hcont⟩ := continue0_boot_pos m hm 0
    (ListBlank.append (List.replicate 5 0) (ListBlank.append [1, 0] (regsTape [0])))
  have htotal := step_nSteps hs1 (step_nSteps hs2 (nSteps_bind_eq hscan
    (step_nSteps hs3 (step_nSteps hs4 (step_nSteps hs5 (step_nSteps hs6
      (nSteps_bind_eq hret (nSteps_bind_eq hb0 (step_nSteps hs7 (nSteps_bind_eq hcl hcont))))))))))
  exact ⟨_, htotal⟩

/-- One complete 4-substep cycle of Phase 2 from `boot2CycleCfg (m' + 1) i` (`1 ≤ i`) to
State `92` (`6.continue.0`) at `bootLeft m' 0`. -/
theorem boot2_cycle_to_92 (m' i : ℕ) (hi : 1 ≤ i) :
    ∃ s, nSteps reference s (boot2CycleCfg (m' + 1) i) =
      some ⟨92, Tape.mkL (bootLeft m' 0)
        (ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
          (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0))))⟩ := by
  have hm : 1 ≤ m' + 1 := by omega
  have hi_split : List.replicate i 0 = 0 :: List.replicate (i - 1) 0 := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega, List.replicate_succ]
  -- Substep A: Pass 1 of `3.prooflist.inc` (`60 -> 60`)
  obtain ⟨sA, _, hA⟩ := boot_pass1_eval (m' + 1) hm 0 (2 * i) (regsTape (List.replicate i 0))
  simp only [↓reduceIte, ← regsTape_cons] at hA
  -- Substep B: Pass 2 of `3.prooflist.inc` (`60 -> 89 -> 47 -> 92 -> 59`)
  rw [hi_split] at hA
  obtain ⟨sB1, _, hB1⟩ := stage3_inc0_pass2 (2 * i + 1) (List.replicate (i - 1) 0)
    (bootLeft (m' + 1) 0)
  have hB2 : step reference
      ⟨89, Tape.mkL (bootLeft (m' + 1) 0)
        ((regsTape ((2 * i + 1) :: 1 :: List.replicate (i - 1) 0)).cons 0 |>.cons 0)⟩ =
      some ⟨47, Tape.mk' (bootLeft (m' + 1) 1)
        (ListBlank.append (List.replicate 2 0)
          (ListBlank.append (encodeReg (2 * i +
            1)) (regsTape (1 :: List.replicate (i - 1) 0))))⟩ := by
    rw [regsTape_cons]
    exact step_mkL_right (by rfl) _ _
  obtain ⟨sB3, _, hB3⟩ := cleanup_to_92 (bootLeft (m' + 1) 1) 2 (2 * i + 1)
    (regsTape (1 :: List.replicate (i - 1) 0))
  obtain ⟨sB4, _, hB4⟩ := continue0_boot_pos (m' + 1) hm 1
    (ListBlank.append (List.replicate (2 + (2 * i + 1)) 0)
      (ListBlank.append [1, 0] (regsTape (1 :: List.replicate (i - 1) 0))))
  have haddB : 2 + (2 * i + 1) = 2 * i + 3 := by omega
  rw [haddB] at hB3 hB4
  -- Substep C: Pass 1 of `3.prooflist.decnz` (`59 -> 59`)
  obtain ⟨sC, _, hC⟩ := boot_pass1_eval (m' + 1) hm 1 (2 * i)
    (regsTape (1 :: List.replicate (i - 1) 0))
  have h10 : (1 : Fin 2) = 0 ↔ False := by decide
  simp only [h10, ↓reduceIte, ← regsTape_cons] at hB4 hC
  -- Substep D: Pass 2 of `3.prooflist.decnz` (`59 -> 89 -> 47 -> 92`)
  obtain ⟨sD1, _, hD1⟩ := stage3_decnz0_pass2_one (2 * i + 1) (List.replicate (i - 1) 0)
    (bootLeft (m' + 1) 1)
  have hrep_snoc : 0 :: (List.replicate (i - 1) 0 ++ [0]) = List.replicate (i + 1) 0 := by
    rw [← List.replicate_succ', show i - 1 + 1 = i by omega, ← List.replicate_succ]
  rw [hrep_snoc] at hD1
  set L_m' := ListBlank.append (pair10 m').reverse default
  have hboot_split : bootLeft (m' + 1) 1 =
      ListBlank.append (List.replicate 3 1) ((L_m'.cons 1).cons 0) := by
    unfold bootLeft
    rw [← pair10_snoc m', List.reverse_append, ListBlank.append_assoc]
    rfl
  have hD2 := break0_step 3 (L_m'.cons 1)
    ((regsTape ((2 * i + 1) :: List.replicate (i + 1) 0)).cons 0 |>.cons 0)
  rw [← hboot_split] at hD2
  have hD3 : step reference
      ⟨47, Tape.mk' ((L_m'.cons 1).cons 1)
        (ListBlank.append (List.replicate 3 0)
          ((regsTape ((2 * i + 1) :: List.replicate (i + 1) 0)).cons 0 |>.cons 0))⟩ =
      some ⟨47, Tape.mk' (bootLeft m' 0)
        (ListBlank.append (List.replicate 4 0)
          (ListBlank.append (encodeReg (2 * i + 1)) (regsTape (List.replicate (i + 1) 0))))⟩ := by
    rw [regsTape_cons]
    exact step_mk'_right (by rfl) _ _
  obtain ⟨sD4, _, hD4⟩ := cleanup_to_92 (bootLeft m' 0) 4 (2 * i + 1)
    (regsTape (List.replicate (i + 1) 0))
  have haddD : 4 + (2 * i + 1) = 2 * (i + 1) + 3 := by omega
  rw [haddD] at hD4
  unfold boot2CycleCfg
  rw [hi_split]
  exact ⟨_, nSteps_bind_eq hA (nSteps_bind_eq hB1 (step_nSteps hB2
    (nSteps_bind_eq hB3 (nSteps_bind_eq hB4 (nSteps_bind_eq hC
      (nSteps_bind_eq hD1 (nSteps_bind_eq hD2 (step_nSteps hD3 hD4))))))))⟩

/-- Inductive Phase 2 loop: from `boot2CycleCfg m i` (`1 ≤ m`, `1 ≤ i`), `reference` reaches
`zfRootCfg (2 * (i + m) + 3) [] (List.replicate (i + m) 0)`. -/
theorem boot2_loop (m i : ℕ) (hm : 1 ≤ m) (hi : 1 ≤ i) :
    ∃ s, nSteps reference s (boot2CycleCfg m i) =
      some (zfRootCfg (2 * (i + m) + 3) [] (List.replicate (i + m) 0)) := by
  induction m generalizing i with
  | zero => omega
  | succ m' ih =>
    obtain ⟨s₁, h92⟩ := boot2_cycle_to_92 m' i hi
    by_cases hm' : m' = 0
    · subst hm'
      rw [bootLeft_zero] at h92
      set R_end := ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
        (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0)))
      have hs1 : step reference ⟨92, Tape.mkL rootLeft R_end⟩ =
          some ⟨92, Tape.mkL ((ListBlank.cons 1 default).cons 1) (R_end.cons 0)⟩ :=
        step_mkL_left (by rfl) _ _
      have hs2 : step reference ⟨92, Tape.mkL ((ListBlank.cons 1 default).cons 1) (R_end.cons 0)⟩ =
          some ⟨77, Tape.mkL (ListBlank.cons 1 default) ((R_end.cons 0).cons 1)⟩ :=
        step_mkL_left (by rfl) _ _
      have hs3 : step reference ⟨77, Tape.mkL (ListBlank.cons 1 default) ((R_end.cons 0).cons 1)⟩ =
          some ⟨zfDispatchState 15, Tape.mkL default (ListBlank.append [1, 1, 0] R_end)⟩ :=
        step_mkL_left (by rfl) _ _
      have hbounce := zfDispatch_bounce_default 15 (by decide) (by decide)
        (ListBlank.append [1, 1, 0] R_end)
      have hroot := root_scan_to_main 0 R_end
      have hroot_eq : ⟨126, Tape.mk' rootLeft R_end⟩ =
          zfRootCfg (2 * (i + 1) + 3) [] (List.replicate (i + 1) 0) := by
        rw [zfRootCfg_default_eq, regsTape_cons]
        rfl
      rw [hroot_eq] at hroot
      exact ⟨_, nSteps_bind_eq h92 (step_nSteps hs1 (step_nSteps hs2
        (step_nSteps hs3 (nSteps_bind_eq hbounce hroot))))⟩
    · have hm'1 : 1 ≤ m' := by omega
      obtain ⟨s₂, _, hcont⟩ := continue0_boot_pos m' hm'1 0
        (ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
          (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0))))
      obtain ⟨s₃, hrest⟩ := ih (i + 1) hm'1 (by omega)
      have hadd : i + 1 + m' = i + (m' + 1) := by omega
      rw [hadd] at hrest
      exact ⟨_, nSteps_bind_eq h92 (nSteps_bind_eq hcont hrest)⟩

/-- Main boot theorem: starting from `init = ⟨0, default⟩`, `Zf429.reference` reaches
`zfRootCfg padTotal [] initRegs` at `main().0` (State `126`) with `padTotal = 3821 ≥ 160` and
`initRegs = List.replicate 1909 0` (`initRegs.length = 1909 ≥ 11`,
`initRegs.take 11 = List.replicate 11 0`). -/
theorem boot_to_root :
    ∃ s padTotal initRegs, 160 ≤ padTotal ∧ 11 ≤ initRegs.length ∧
      initRegs.take 11 = List.replicate 11 0 ∧
      nSteps reference s init = some (zfRootCfg padTotal [] initRegs) := by
  obtain ⟨s₁, hb1⟩ := boot1_eval
  obtain ⟨s₂, hb2_init⟩ := boot2_init_step 1908 (by decide)
  obtain ⟨s₃, hb2_loop⟩ := boot2_loop 1908 1 (by decide) (by decide)
  have htotal := nSteps_bind_eq hb1 (nSteps_bind_eq hb2_init hb2_loop)
  refine ⟨s₁ + (s₂ + s₃), 3821, List.replicate 1909 0, by decide, ?_, ?_, htotal⟩
  · rw [List.length_replicate]; decide
  · rw [List.take_replicate]; rfl

end ConjectureMachines.Zf429.Boot

