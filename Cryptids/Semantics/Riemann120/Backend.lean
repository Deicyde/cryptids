/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann120

/-!
# Backend Gadgets & Bootstrap for Shunia's 120-State Riemann Machine (`riemann120`)
-/

@[expose] public section

namespace ConjectureMachines.Riemann120.Backend

open Turing StateTransition ConjectureMachines ConjectureMachines.Riemann120
open ConjectureMachines.Riemann543.Layer1
  (nSteps nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_reaches nSteps_eval_dom nSteps_of_halt mem_eval_iff_nSteps
   mk_append_replicate_zero default_eq_mk_nil
   default_cons_zero append_replicate_zero_default fin2_cases
   Tape.mkL Tape.mkL_cons Tape.mk'_cons Tape.mkL_default
   append_replicate_cons append_cons_snoc append_reverse_cons
   encodeReg encodeReg_length encodeReg_reverse append_encodeReg_reverse append_encodeReg
   encodeRegs encodeRegs_nil encodeRegs_cons encodeRegs_append
   regsTape regsTape_nil regsTape_cons regsTape_append
   list_take_cons_drop list_take_set_drop)
open ConjectureMachines.Zf429.Layer1
  (rootLeft rootLeft_eq_append stackLeft stackLeft_nil stackLeft_eq_append
   stackLeft_append stackLeft_append_singleton)
open ConjectureMachines.Zf429.Boot
  (pair01 pair10 pair01_snoc pair10_snoc cons_one_pair01 pair10_succ_eq
   bootLeft bootLeft_zero)

set_option maxRecDepth 200000

/-!
## 3. Symbolic Step Helpers & `NoFourZeros` Scanner (`4.run.0..3`, `6.continue.0..2`)
-/

theorem step_mkL_left {q q' : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, rh121Trans_eq, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, rh121Trans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {q q' : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, rh121Trans_eq, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {q q' : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, rh121Trans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem nSteps_mkL_left_scan {q : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {q : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

/-- `NoFourZeros bits`: `true` iff no 4 consecutive `0`s (`[0, 0, 0, 0]`) occur in `bits`. -/
def NoFourZeros : List (Fin 2) → Bool
  | 0 :: 0 :: 0 :: 0 :: _ => false
  | _ :: xs => NoFourZeros xs
  | [] => true

theorem NoFourZeros_head4 (a b c d : Fin 2) (xs : List (Fin 2)) :
    NoFourZeros (a :: b :: c :: d :: xs) =
      (NoFourZeros [a, b, c, d] && NoFourZeros (b :: c :: d :: xs)) := by
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
    rcases fin2_cases c with rfl | rfl <;> rcases fin2_cases d with rfl | rfl <;> rfl

theorem NoFourZeros_snoc_one : ∀ l : List (Fin 2), NoFourZeros (l ++ [1]) = NoFourZeros l
  | [] => rfl
  | [a] => by revert a; decide
  | [a, b] => by revert a b; decide
  | [a, b, c] => by revert a b c; decide
  | a :: b :: c :: d :: xs => by
    have ih := NoFourZeros_snoc_one (b :: c :: d :: xs)
    simp only [List.cons_append] at ih ⊢
    rw [NoFourZeros_head4 a b c d (xs ++ [1]), NoFourZeros_head4 a b c d xs, ih]

theorem NoFourZeros_snoc_one_bit (b₀ : Fin 2) :
    ∀ l : List (Fin 2), NoFourZeros (l ++ [1, b₀]) = NoFourZeros l
  | [] => by revert b₀; decide
  | [a] => by revert a b₀; decide
  | [a, b] => by revert a b b₀; decide
  | [a, b, c] => by revert a b c b₀; decide
  | a :: b :: c :: d :: xs => by
    have ih := NoFourZeros_snoc_one_bit b₀ (b :: c :: d :: xs)
    simp only [List.cons_append] at ih ⊢
    rw [NoFourZeros_head4 a b c d (xs ++ [1, b₀]), NoFourZeros_head4 a b c d xs, ih]

theorem NoFourZeros_append_replicate_one (l : List (Fin 2)) (p : ℕ) :
    NoFourZeros (l ++ List.replicate p 1) = NoFourZeros l := by
  induction p generalizing l with
  | zero => simp
  | succ p ih =>
    rw [List.replicate_succ', ← List.append_assoc, NoFourZeros_snoc_one, ih]

theorem NoFourZeros_snoc_of_head4 (a b c d : Fin 2) :
    ∀ xs : List (Fin 2),
      NoFourZeros (xs ++ [d, c, b, a]) =
        (NoFourZeros [a, b, c, d] && NoFourZeros (xs ++ [d, c, b]))
  | [] => by revert a b c d; decide
  | [x₁] => by revert a b c d x₁; decide
  | [x₁, x₂] => by revert a b c d x₁ x₂; decide
  | [x₁, x₂, x₃] => by revert a b c d x₁ x₂ x₃; decide
  | x₁ :: x₂ :: x₃ :: x₄ :: xs => by
    have ih := NoFourZeros_snoc_of_head4 a b c d (x₂ :: x₃ :: x₄ :: xs)
    simp only [List.cons_append] at ih ⊢
    rw [NoFourZeros_head4 x₁ x₂ x₃ x₄ (xs ++ [d, c, b, a]),
      NoFourZeros_head4 x₁ x₂ x₃ x₄ (xs ++ [d, c, b]), ih]
    rcases fin2_cases x₁ with rfl | rfl <;> rcases fin2_cases x₂ with rfl | rfl <;>
      rcases fin2_cases x₃ with rfl | rfl <;> rcases fin2_cases x₄ with rfl | rfl <;>
      rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
      rcases fin2_cases c with rfl | rfl <;> rcases fin2_cases d with rfl | rfl <;> rfl

theorem NoFourZeros_reverse : ∀ bits : List (Fin 2), NoFourZeros bits.reverse = NoFourZeros bits
  | [] => rfl
  | [a] => by revert a; decide
  | [a, b] => by revert a b; decide
  | [a, b, c] => by revert a b c; decide
  | a :: b :: c :: d :: xs => by
    have hrev : (a :: b :: c :: d :: xs).reverse = xs.reverse ++ [d, c, b, a] := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hrev, NoFourZeros_snoc_of_head4]
    have ih := NoFourZeros_reverse (b :: c :: d :: xs)
    have hrev3 : (b :: c :: d :: xs).reverse = xs.reverse ++ [d, c, b] := by
      simp [List.reverse_cons, List.append_assoc]
    rw [← hrev3, ih, NoFourZeros_head4]
    rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
      rcases fin2_cases c with rfl | rfl <;> rcases fin2_cases d with rfl | rfl <;> rfl

/-- `4.run.0..3` scanner states (`0 ↦ 12`, `1 ↦ 14`, `2 ↦ 16`, `3 ↦ 18`). -/
def rhRunState : ℕ → Fin 121
  | 0 => 12
  | 1 => 14
  | 2 => 16
  | 3 => 18
  | _ => 12

/-- Scanning left across `rev` from `rhRunState z` (`z ≤ 3`) when `NoFourZeros` holds. -/
theorem rhRun_scan_rev (rev : List (Fin 2)) (z : ℕ) (hz : z ≤ 3)
    (hok : NoFourZeros (List.replicate z 0 ++ rev) = true) (R : ListBlank (Fin 2)) :
    ∃ z', z' ≤ 3 ∧
      nSteps riemann121 rev.length
        ⟨rhRunState z, Tape.mkL (ListBlank.append rev default) R⟩ =
      some ⟨rhRunState z', Tape.mkL default (ListBlank.append rev.reverse R)⟩ := by
  induction rev generalizing z R with
  | nil =>
    exact ⟨z, hz, rfl⟩
  | cons a xs ih =>
    rcases fin2_cases a with rfl | rfl
    · match z, hz with
      | 0, _ =>
        have hstep : step riemann121 ⟨12, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨14, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left (by rfl) _ _
        obtain ⟨z', hz', hrest⟩ := ih 1 (by decide) hok (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at hrest
        exact ⟨z', hz', step_nSteps hstep hrest⟩
      | 1, _ =>
        have hstep : step riemann121 ⟨14, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨16, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left (by rfl) _ _
        obtain ⟨z', hz', hrest⟩ := ih 2 (by decide) hok (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at hrest
        exact ⟨z', hz', step_nSteps hstep hrest⟩
      | 2, _ =>
        have hstep : step riemann121 ⟨16, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨18, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left (by rfl) _ _
        obtain ⟨z', hz', hrest⟩ := ih 3 (by decide) hok (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at hrest
        exact ⟨z', hz', step_nSteps hstep hrest⟩
      | 3, _ =>
        cases hok
    · have htr1_all : ∀ z₀, z₀ ≤ 3 → rh121Trans (rhRunState z₀) 1 = some (1, .left, 12) := by
        decide
      have hstep : step riemann121
          ⟨rhRunState z, Tape.mkL ((ListBlank.append xs default).cons 1) R⟩ =
          some ⟨12, Tape.mkL (ListBlank.append xs default) (R.cons 1)⟩ :=
        step_mkL_left (htr1_all z hz) _ _
      have hok' : NoFourZeros (List.replicate 0 0 ++ xs) = true := by
        match z, hz with
        | 0, _ => exact hok
        | 1, _ => exact hok
        | 2, _ => exact hok
        | 3, _ => exact hok
      obtain ⟨z', hz', hrest⟩ := ih 0 (by decide) hok' (R.cons 1)
      rw [append_cons_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', step_nSteps hstep hrest⟩

/-- Bouncing off `default` from `rhRunState z` (`z ≤ 3`) into `4.dispatch.scan` (`State 20`). -/
theorem rhRun_bounce_default (z : ℕ) (hz : z ≤ 3) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * (3 - z) + 1) ⟨rhRunState z, Tape.mkL default R⟩ =
      some ⟨20, Tape.mk' default R⟩ := by
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have hb3 : ∀ R' : ListBlank (Fin 2),
      nSteps riemann121 1 ⟨18, Tape.mkL default R'⟩ = some ⟨20, Tape.mk' default R'⟩ := by
    intro R'
    apply step_one
    conv_lhs => rw [hdef]
    rw [step_mkL_right (by rfl), default_cons_zero]
  match z, hz with
  | 3, _ => exact hb3 R
  | 2, _ =>
    have h1 : step riemann121 ⟨16, Tape.mkL default R⟩ =
        some ⟨18, Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default R
    have h2 := hb3 (R.cons 0)
    have h3 := nSteps_mk'_right_scan (q := 20) (a := 0) (b := 0) (by rfl) 1 default R
    rw [append_replicate_zero_default] at h3
    exact step_nSteps h1 (nSteps_bind_eq (m := 1) (n := 1) h2 h3)
  | 1, _ =>
    have h1 : step riemann121 ⟨14, Tape.mkL default R⟩ =
        some ⟨16, Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default R
    have h2 : step riemann121 ⟨16, Tape.mkL default (R.cons 0)⟩ =
        some ⟨18, Tape.mkL default ((R.cons 0).cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default _
    have h3 := hb3 ((R.cons 0).cons 0)
    have h4 := nSteps_mk'_right_scan (q := 20) (a := 0) (b := 0) (by rfl) 2 default R
    rw [append_replicate_zero_default] at h4
    exact step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq h3 h4))
  | 0, _ =>
    have h1 : step riemann121 ⟨12, Tape.mkL default R⟩ =
        some ⟨14, Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default R
    have h2 : step riemann121 ⟨14, Tape.mkL default (R.cons 0)⟩ =
        some ⟨16, Tape.mkL default ((R.cons 0).cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default _
    have h3 : step riemann121 ⟨16, Tape.mkL default ((R.cons 0).cons 0)⟩ =
        some ⟨18, Tape.mkL default (((R.cons 0).cons 0).cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default _
    have h4 := hb3 (((R.cons 0).cons 0).cons 0)
    have h5 := nSteps_mk'_right_scan (q := 20) (a := 0) (b := 0) (by rfl) 3 default R
    rw [append_replicate_zero_default] at h5
    exact step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq h4 h5)))

/-- From `4.dispatch.scan` (`State 20`) at `[1, 1, b]`, `riemann121` takes 3 steps
(`20 -> 22 -> 25 -> 27`) writing `0` over `b` to enter `main.0` (`State 27`). -/
theorem root_scan_to_main (b : Fin 2) (R : ListBlank (Fin 2)) :
    nSteps riemann121 3 ⟨20, Tape.mk' default (ListBlank.append [1, 1, b] R)⟩ =
      some ⟨27, Tape.mk' rootLeft R⟩ := by
  simp only [ListBlank.append]
  have h1 : step riemann121 ⟨20, Tape.mk' default (((R.cons b).cons 1).cons 1)⟩ =
      some ⟨22, Tape.mk' (ListBlank.cons 1 default) ((R.cons b).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step riemann121 ⟨22, Tape.mk' (ListBlank.cons 1 default) ((R.cons b).cons 1)⟩ =
      some ⟨25, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons b)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step riemann121 ⟨25, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons b)⟩ =
      some ⟨27, Tape.mk' rootLeft R⟩ := by
    rcases fin2_cases b with rfl | rfl
    · exact step_mk'_right (by rfl) _ _
    · exact step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- From `12` (`4.run.0`), if `prefix = [1, 1, b] ++ rest` satisfies `NoFourZeros prefix = true`,
`riemann121` scans left to `default` and reaches `27` (`main.0`) with `rootLeft` on `Tape.left`
and `rest` on `Tape.right`. -/
theorem run0_reaches_main0 (b : Fin 2) (rest : List (Fin 2))
    (hok : NoFourZeros ([1, 1, b] ++ rest) = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨12, Tape.mkL (ListBlank.append ([1, 1, b] ++ rest).reverse default) R⟩ =
      some ⟨27, Tape.mk' rootLeft (ListBlank.append rest R)⟩ := by
  have hrev_ok : NoFourZeros ([1, 1, b] ++ rest).reverse = true := by
    rwa [NoFourZeros_reverse]
  obtain ⟨z', hz', hscan⟩ := rhRun_scan_rev ([1, 1, b] ++ rest).reverse 0 (by decide) hrev_ok R
  rw [List.reverse_reverse] at hscan
  have hbounce := rhRun_bounce_default z' hz' (ListBlank.append ([1, 1, b] ++ rest) R)
  rw [ListBlank.append_assoc] at hbounce
  have hroot := root_scan_to_main b (ListBlank.append rest R)
  exact ⟨_, by omega, nSteps_bind_eq hscan (nSteps_bind_eq hbounce hroot)⟩

/-- From `10` (`6.continue.0`), if `rev` contains `1` and satisfies `NoFourZeros rev = true`,
`riemann121` scans left into `12` (`4.run.0`) and reaches `default` in `rhRunState z'`. -/
theorem continue0_scan_rev (rev : List (Fin 2)) (hone : (1 : Fin 2) ∈ rev)
    (hok : NoFourZeros rev = true) (R : ListBlank (Fin 2)) :
    ∃ z', z' ≤ 3 ∧ ∃ s, 1 ≤ s ∧
      nSteps riemann121 s ⟨10, Tape.mkL (ListBlank.append rev default) R⟩ =
      some ⟨rhRunState z', Tape.mkL default (ListBlank.append rev.reverse R)⟩ := by
  induction rev generalizing R with
  | nil => cases hone
  | cons a xs ih =>
    rcases fin2_cases a with rfl | rfl
    · have hone' : (1 : Fin 2) ∈ xs := by
        rcases List.mem_cons.mp hone with h | h
        · cases h
        · exact h
      have hok' : NoFourZeros xs = true := by
        rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, xs'⟩⟩⟩
        · rfl
        · rcases fin2_cases x₁ with rfl | rfl <;> rfl
        · rcases fin2_cases x₁ with rfl | rfl <;> rcases fin2_cases x₂ with rfl | rfl <;> rfl
        · rcases fin2_cases x₁ with rfl | rfl <;> rcases fin2_cases x₂ with rfl | rfl <;>
            rcases fin2_cases x₃ with rfl | rfl <;> first | exact hok | cases hok
      have hstep : step riemann121 ⟨10, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
          some ⟨10, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
        step_mkL_left (by rfl) _ _
      obtain ⟨z', hz', s, hs1, hrest⟩ := ih hone' hok' (R.cons 0)
      rw [append_cons_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', s + 1, by omega, step_nSteps hstep hrest⟩
    · have hstep : step riemann121 ⟨10, Tape.mkL ((ListBlank.append xs default).cons 1) R⟩ =
          some ⟨12, Tape.mkL (ListBlank.append xs default) (R.cons 1)⟩ :=
        step_mkL_left (by rfl) _ _
      obtain ⟨z', hz', hrest⟩ := rhRun_scan_rev xs 0 (by decide) hok (R.cons 1)
      rw [append_cons_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', xs.length + 1, by omega, step_nSteps hstep hrest⟩

/-- From `10` (`6.continue.0`), if `prefix = [1, 1, b] ++ rest` satisfies `NoFourZeros prefix`,
`riemann121` scans left and enters `27` (`main.0`) with `rootLeft` on `Tape.left` and `rest` on
`Tape.right`. -/
theorem continue0_reaches_main0 (b : Fin 2) (rest : List (Fin 2))
    (hok : NoFourZeros ([1, 1, b] ++ rest) = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨10, Tape.mkL (ListBlank.append ([1, 1, b] ++ rest).reverse default) R⟩ =
      some ⟨27, Tape.mk' rootLeft (ListBlank.append rest R)⟩ := by
  have hone : (1 : Fin 2) ∈ ([1, 1, b] ++ rest).reverse := by
    rw [List.mem_reverse]
    simp
  have hrev_ok : NoFourZeros ([1, 1, b] ++ rest).reverse = true := by
    rwa [NoFourZeros_reverse]
  obtain ⟨z', hz', s₁, _, hscan⟩ :=
    continue0_scan_rev ([1, 1, b] ++ rest).reverse hone hrev_ok R
  rw [List.reverse_reverse] at hscan
  have hbounce := rhRun_bounce_default z' hz' (ListBlank.append ([1, 1, b] ++ rest) R)
  rw [ListBlank.append_assoc] at hbounce
  have hroot := root_scan_to_main b (ListBlank.append rest R)
  exact ⟨_, by omega, nSteps_bind_eq hscan (nSteps_bind_eq hbounce hroot)⟩

/-!
## 4. Canonical Tape Layouts (`rhRootCfg`, `rhPrepCfg`) & 5-Register Gadgets (`m, j, x, f, v`)
-/

/-- Canonical root configuration at `main.0` (`State 27`):
- Left of head: `rootLeft = (default.cons 1 |>.cons 1 |>.cons 0)`.
- Right of head: `stack`, then `padTotal - stack.length` zeros, `[1, 0]`, `encodeRegs regs`,
  and `extra` (which defaults to `default`). -/
def rhRootCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 121 2 :=
  ⟨27, Tape.mk' rootLeft
    (ListBlank.append
      (stack ++ List.replicate (padTotal - stack.length) 0 ++ [1, 0] ++ encodeRegs regs)
      extra)⟩

theorem rhRootCfg_default_eq (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    rhRootCfg padTotal stack regs default =
      ⟨27, Tape.mk' rootLeft
        (ListBlank.append stack
          (ListBlank.append (List.replicate (padTotal - stack.length) 0)
            (regsTape (0 :: regs))))⟩ := by
  unfold rhRootCfg
  simp only [List.append_assoc, ListBlank.append_assoc]
  rfl

/-- Prepared configuration at `main.0` (`State 27`) after Pass 1 (`1b.reg.prep_1/2`):
`padTotal - stack.length` zeros + `[1, 0]` have been turned into `[1, 0]` followed by
`encodeReg (padTotal - stack.length - 2)` and `encodeRegs regs`. -/
def rhPrepCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 121 2 :=
  ⟨27, Tape.mk' rootLeft
    (ListBlank.append
      (stack ++ [1, 0] ++ encodeRegs ((padTotal - stack.length - 2) :: regs))
      extra)⟩

theorem rhPrepCfg_default_eq (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    rhPrepCfg padTotal stack regs default =
      ⟨27, Tape.mk' rootLeft
        (ListBlank.append stack
          ((regsTape ((padTotal - stack.length - 2) :: regs)).cons 0 |>.cons 1))⟩ := by
  unfold rhPrepCfg
  simp only [List.append_assoc, ListBlank.append_assoc]
  rfl

/-- `3.<reg_k>.inc` states for the 5 registers (`0=m, 1=j, 2=x, 3=f, 4=v`). -/
def regIncStage3 : ℕ → Fin 121
  | 0 => 4
  | 1 => 44
  | 2 => 99
  | 3 => 36
  | 4 => 70
  | _ => 4

/-- `3.<reg_k>.decnz` states for the 5 registers (`0=m, 1=j, 2=x, 3=f, 4=v`). -/
def regDecnzStage3 : ℕ → Fin 121
  | 0 => 31
  | 1 => 47
  | 2 => 71
  | 3 => 46
  | 4 => 73
  | _ => 31

/-- `2b.reg.<m-2>.inc` chain (`0 ↦ -2.inc = 11`, `1 ↦ -1.inc = 9`, `2..6 ↦ 0..4.inc`). -/
def rhRegIncrChain : ℕ → Fin 121
  | 0 => 11
  | 1 => 9
  | 2 => 7
  | 3 => 53
  | 4 => 52
  | 5 => 43
  | 6 => 85
  | _ => 11

/-- `2b.reg.<m-2>.dec` chain (`0 ↦ -2.dec = 51`, `1 ↦ -1.dec = 42`, `2..6 ↦ 0..4.dec`). -/
def rhRegDecrChain : ℕ → Fin 121
  | 0 => 51
  | 1 => 42
  | 2 => 35
  | 3 => 57
  | 4 => 69
  | 5 => 56
  | 6 => 87
  | _ => 51

/-- Return scan from `10` (`6.continue.0`) on `stackLeft w` when `NoFourZeros ([1, 1, 0] ++ w)`. -/
theorem continue0_return (w : List (Fin 2)) (hw : NoFourZeros ([1, 1, 0] ++ w) = true)
    (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s ⟨10, Tape.mkL (stackLeft w) R⟩ =
      some ⟨27, Tape.mk' rootLeft (ListBlank.append w R)⟩ := by
  rw [stackLeft_eq_append]
  exact continue0_reaches_main0 0 w hw R

/-- `6.continue.0` (`10`) scans left across `z` zeros in `z` steps. -/
theorem continue0_scan_zeros (z : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 z ⟨10, Tape.mkL (ListBlank.append (List.replicate z 0) L) R⟩ =
      some ⟨10, Tape.mkL L (ListBlank.append (List.replicate z 0) R)⟩ :=
  nSteps_mkL_left_scan (by rfl) z L R

/-- `6.continue.1` (`37`) scans left across `z` zeros, erases the preceding `1`, and enters `10`. -/
theorem continue1_step (z : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (z + 1)
      ⟨37, Tape.mkL (ListBlank.append (List.replicate z 0) (L.cons 1)) R⟩ =
      some ⟨10, Tape.mkL L (ListBlank.append (List.replicate (z + 1) 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 37) (a := 0) (b := 0) (by rfl) z (L.cons 1) R
  have h1 : step riemann121
      ⟨37, Tape.mkL (L.cons 1) (ListBlank.append (List.replicate z 0) R)⟩ =
      some ⟨10, Tape.mkL L ((ListBlank.append (List.replicate z 0) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq hscan (step_one h1)
  rwa [List.replicate_succ, ListBlank.append]

/-- `6.continue.2` (`97`) scans left across `z` zeros, erases the preceding `1`, and enters `37`. -/
theorem continue2_step (z : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (z + 1)
      ⟨97, Tape.mkL (ListBlank.append (List.replicate z 0) (L.cons 1)) R⟩ =
      some ⟨37, Tape.mkL L (ListBlank.append (List.replicate (z + 1) 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 97) (a := 0) (b := 0) (by rfl) z (L.cons 1) R
  have h1 : step riemann121
      ⟨97, Tape.mkL (L.cons 1) (ListBlank.append (List.replicate z 0) R)⟩ =
      some ⟨37, Tape.mkL L ((ListBlank.append (List.replicate z 0) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq hscan (step_one h1)
  rwa [List.replicate_succ, ListBlank.append]

/-- Full return from `6.continue.1` (`37`) when the left tape is `stackLeft (w ++ [1])`. -/
theorem continue1_return (w : List (Fin 2)) (hw : NoFourZeros ([1, 1, 0] ++ w) = true)
    (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s ⟨37, Tape.mkL (stackLeft (w ++ [1])) R⟩ =
      some ⟨27, Tape.mk' rootLeft (ListBlank.append w (R.cons 0))⟩ := by
  rw [stackLeft_append_singleton]
  have h1 := continue1_step 0 (stackLeft w) R
  simp only [List.replicate, ListBlank.append, Nat.zero_add] at h1
  obtain ⟨s, hs1, hret⟩ := continue0_return w hw (R.cons 0)
  exact ⟨1 + s, by omega, nSteps_bind_eq h1 hret⟩

/-- Full return from `6.continue.2` (`97`) when the left tape is `stackLeft (w ++ [1, 1])`. -/
theorem continue2_return (w : List (Fin 2)) (hw : NoFourZeros ([1, 1, 0] ++ w) = true)
    (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s ⟨97, Tape.mkL (stackLeft (w ++ [1, 1])) R⟩ =
      some ⟨27, Tape.mk' rootLeft (ListBlank.append w ((R.cons 0).cons 0))⟩ := by
  have heq : w ++ [1, 1] = (w ++ [1]) ++ [1] := by simp
  rw [heq, stackLeft_append_singleton]
  have h1 := continue2_step 0 (stackLeft (w ++ [1])) R
  simp only [List.replicate, ListBlank.append, Nat.zero_add] at h1
  obtain ⟨s, hs1, hret⟩ := continue1_return w hw (R.cons 0)
  exact ⟨1 + s, by omega, nSteps_bind_eq h1 hret⟩

/-- Pass 1 register prep evaluation (`1b.reg.prep_1/2` = `6/8`) from `State 6`. -/
theorem prep_pass1_eval (stack : List (Fin 2)) (hstack : NoFourZeros ([1, 1, 0] ++ stack) = true)
    (p : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨6, Tape.mk' ((stackLeft stack).cons 1)
        (ListBlank.append (List.replicate (p + 1) 0) (ListBlank.append [1, 0] R))⟩ =
      some ⟨27, Tape.mk' rootLeft
        (ListBlank.append (stack ++ [1, 0] ++ encodeReg p) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step riemann121
      ⟨6, Tape.mk' ((stackLeft stack).cons 1)
        ((ListBlank.append (List.replicate p 0) (ListBlank.append [1, 0] R)).cons 0)⟩ =
      some ⟨8, Tape.mk' (((stackLeft stack).cons 1).cons 0)
        (ListBlank.append (List.replicate p 0) (ListBlank.append [1, 0] R))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 8) (a := 0) (b := 1) (by rfl) p
    (((stackLeft stack).cons 1).cons 0) (ListBlank.append [1, 0] R)
  have h2 : step riemann121
      ⟨8, Tape.mk' (ListBlank.append (List.replicate p 1) (((stackLeft stack).cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨10, Tape.mkL
        (ListBlank.append (List.replicate p 1) (((stackLeft stack).cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ :=
    step_mk'_left (by rfl) _ (R.cons 0)
  have hL_eq : ListBlank.append (List.replicate p 1) (((stackLeft stack).cons 1).cons 0) =
      stackLeft (stack ++ [1, 0] ++ List.replicate p 1) := by
    rw [stackLeft_append, stackLeft_append, List.reverse_replicate]
    rfl
  conv at h2 => rhs; rw [hL_eq]
  have hw_ok : NoFourZeros ([1, 1, 0] ++ (stack ++ [1, 0] ++ List.replicate p 1)) = true := by
    have ha : [1, 1, 0] ++ (stack ++ [1, 0] ++ List.replicate p 1) =
        (([1, 1, 0] ++ stack) ++ [1, 0]) ++ List.replicate p 1 := by
      simp [List.append_assoc]
    rw [ha, NoFourZeros_append_replicate_one, NoFourZeros_snoc_one_bit]
    exact hstack
  obtain ⟨s_ret, hs1, hret⟩ := continue0_return (stack ++ [1, 0] ++ List.replicate p 1) hw_ok
    (ListBlank.append [1, 0] R)
  have hR_eq : ListBlank.append (stack ++ [1, 0] ++ List.replicate p 1)
      (ListBlank.append [1, 0] R) =
      ListBlank.append (stack ++ [1, 0] ++ encodeReg p) R := by
    simp only [encodeReg, List.replicate_succ', List.append_assoc, ListBlank.append_assoc]
    rfl
  rw [hR_eq] at hret
  exact ⟨_, by omega, step_nSteps h1 (nSteps_bind_eq hscan (step_nSteps h2 hret))⟩

theorem regIncStage3_trans_zero (k : ℕ) (hk : k < 5) :
    rh121Trans (regIncStage3 k) 0 = some (1, .right, 6) := by
  revert k hk; decide

theorem regDecnzStage3_trans_zero (k : ℕ) (hk : k < 5) :
    rh121Trans (regDecnzStage3 k) 0 = some (1, .right, 6) := by
  revert k hk; decide

/-- Pass 1 from any `3.<reg_k>.inc` / `3.<reg_k>.decnz` state (`rh121Trans q 0 = some (1, R, 6)`):
prepares the `-1` register `encodeReg (padTotal - stack.length - 2)` and returns to `rhPrepCfg`. -/
theorem stage3_pass1_from_stack {q : Fin 121} (hq : rh121Trans q 0 = some (1, .right, 6))
    (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) (extra : ListBlank (Fin 2))
    (hpad : stack.length + 2 ≤ padTotal) (hstack : NoFourZeros ([1, 1, 0] ++ stack) = true) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨q, Tape.mk' (stackLeft stack)
        (ListBlank.append (List.replicate (padTotal - stack.length) 0 ++ [1, 0] ++ encodeRegs regs)
          extra)⟩ =
      some (rhPrepCfg padTotal stack regs extra) := by
  set p := padTotal - stack.length - 2
  have hp_eq : padTotal - stack.length = (p + 1) + 1 := by omega
  rw [hp_eq, List.replicate_succ, List.cons_append, List.cons_append, ListBlank.append]
  have h1 : step riemann121
      ⟨q, Tape.mk' (stackLeft stack)
        ((ListBlank.append (List.replicate (p + 1) 0 ++ [1, 0] ++ encodeRegs regs)
          extra).cons 0)⟩ =
      some ⟨6, Tape.mk' ((stackLeft stack).cons 1)
        (ListBlank.append (List.replicate (p + 1) 0)
          (ListBlank.append [1, 0] (ListBlank.append (encodeRegs regs) extra)))⟩ := by
    simp only [List.append_assoc, ListBlank.append_assoc]
    exact step_mk'_right hq (stackLeft stack) _
  obtain ⟨s, hs1, hprep⟩ :=
    prep_pass1_eval stack hstack p (ListBlank.append (encodeRegs regs) extra)
  have hcomb := step_nSteps h1 hprep
  unfold rhPrepCfg
  simp only [List.append_assoc, ListBlank.append_assoc, encodeRegs_cons] at hcomb ⊢
  exact ⟨s + 1, by omega, hcomb⟩

/-!
## 5. Pass 2 Register Return Scans (`15/17` = `return_0`, `63/78` = `return_1`)
-/

theorem return0_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (r + 2)
      ⟨15, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨15, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step riemann121
      ⟨15, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨17, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step riemann121
      ⟨17, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨15, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 15) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

theorem return0_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (encodeRegs regs).length
      ⟨15, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨15, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return0_scan_reg, ListBlank.append_assoc]

theorem return0_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 ((encodeRegs regs).length + 2)
      ⟨15, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨19, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return0_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step riemann121
      ⟨15, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨17, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step riemann121
      ⟨17, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨19, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

theorem return1_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (r + 2)
      ⟨63, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨63, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step riemann121
      ⟨63, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨78, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step riemann121
      ⟨78, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨63, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 63) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

theorem return1_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (encodeRegs regs).length
      ⟨63, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨63, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return1_scan_reg, ListBlank.append_assoc]

theorem return1_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 ((encodeRegs regs).length + 2)
      ⟨63, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨91, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return1_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step riemann121
      ⟨63, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨78, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step riemann121
      ⟨78, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨91, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-!
## 6. Pass 2 Register Increment & Decrement (`inc`, `decnz_zero`, `decnz_succ`)
-/

theorem regIncStage3_trans_one (k : ℕ) (hk : k < 5) :
    rh121Trans (regIncStage3 k) 1 = some (0, .right, rhRegIncrChain (k + 2)) := by
  revert k hk; decide

theorem rhRegIncrChain_trans_one (m : ℕ) (hm : m ≤ 6) :
    rh121Trans (rhRegIncrChain m) 1 = some (1, .right, rhRegIncrChain m) := by
  revert m hm; decide

theorem rhRegIncrChain_trans_zero (m : ℕ) (hm : m < 6) :
    rh121Trans (rhRegIncrChain (m + 1)) 0 = some (0, .right, rhRegIncrChain m) := by
  revert m hm; decide

theorem rhRegIncrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 5)
    (L R : ListBlank (Fin 2)) :
    nSteps riemann121 ((encodeRegs pref).length + 1)
      ⟨rhRegIncrChain (pref.length + 1),
        Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨11, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length + 1 < 6 := by omega
    have hrs_le : rs.length ≤ 5 := by omega
    have h0 : step riemann121
        ⟨rhRegIncrChain (rs.length + 1 + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨rhRegIncrChain (rs.length + 1),
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (rhRegIncrChain_trans_zero (rs.length + 1) hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan (rhRegIncrChain_trans_one (rs.length + 1) (by omega))
      (r + 1) (L.cons 0) ((ListBlank.append (encodeRegs rs) R).cons 0)
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
      ← encodeRegs_cons] at hrest
    have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
    have hlen : (r + 1) + ((encodeRegs rs).length + 1) + 1 =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

/-- Rightward shift in States `13`/`11` (`2b.reg.inc.shift_1/2`) and return scan in `15`. -/
theorem inc_shift_eval (suff : List ℕ) (m : ℕ) (L_prev : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev) (regsTape suff)⟩ =
      some ⟨15, Tape.mkL L_prev (regsTape (m :: suff))⟩ := by
  induction suff generalizing m L_prev with
  | nil =>
    rw [regsTape_nil, List.replicate_succ, ListBlank.append]
    have h1 : step riemann121
        ⟨13, Tape.mk' ((ListBlank.append (List.replicate m 1) L_prev).cons 1) default⟩ =
        some ⟨15, Tape.mkL ((ListBlank.append (List.replicate m 1) L_prev).cons 1)
          (ListBlank.cons 0 default)⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      exact step_mk'_left (by rfl) _ default
    have hscan := nSteps_mkL_left_scan (q := 15) (a := 1) (b := 1) (by rfl)
      (m + 1) L_prev (ListBlank.cons 0 default)
    conv at hscan => lhs; rw [List.replicate_succ, ListBlank.append]
    have hcomb := step_nSteps h1 hscan
    rw [← append_encodeReg, ← regsTape_nil, ← regsTape_cons] at hcomb
    exact ⟨m + 2, by omega, hcomb⟩
  | cons r rs ih =>
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step riemann121
        ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨11, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) L_prev).cons 0)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    rw [← append_encodeReg_reverse] at h1
    have hscan := nSteps_mk'_right_scan (q := 11) (a := 1) (b := 1) (by rfl)
      r (ListBlank.append (encodeReg m).reverse L_prev) ((regsTape rs).cons 0)
    have h2 : step riemann121
        ⟨11, Tape.mk' (ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)) ((regsTape rs).cons 0)⟩ =
        some ⟨13, Tape.mk' ((ListBlank.append (List.replicate r 1)
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

/-- Pass 2 `3.<reg_k>.inc` (`k < 5`): increments `regs[k]` and lands in `19` (`6.break.0`). -/
theorem stage3_inc_pass2 (k : ℕ) (hk5 : k < 5) (p : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨19, Tape.mkL L_stack
        ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩ := by
  set pref := p :: regs.take k
  set r := regs[k]
  set suff := regs.drop (k + 1)
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape (r :: suff)) := by
    have hlist : p :: regs = pref ++ r :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step riemann121
      ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨rhRegIncrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape (r :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regIncStage3_trans_one k hk5) L_stack _
  have hpref_scan := rhRegIncrChain_scan_pref pref (by omega)
    (L_stack.cons 0) (regsTape (r :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have hr_scan : nSteps riemann121 ((r + 1) + 1)
      ⟨11, Tape.mk' L_pref (regsTape (r :: suff))⟩ =
      some ⟨13, Tape.mk' (ListBlank.append (List.replicate (r + 2) 1) L_pref) (regsTape suff)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    have hones := nSteps_mk'_right_scan (q := 11) (a := 1) (b := 1) (by rfl)
      (r + 1) L_pref ((regsTape suff).cons 0)
    have hzero : step riemann121
        ⟨11, Tape.mk' (ListBlank.append (List.replicate (r + 1) 1) L_pref)
          ((regsTape suff).cons 0)⟩ =
        some ⟨13, Tape.mk' ((ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := nSteps_bind_eq hones (step_one hzero)
    have hcons : (ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1 =
        ListBlank.append (List.replicate (r + 2) 1) L_pref := by
      rw [← ListBlank.append, ← List.replicate_succ]
    rw [hcons] at hcomb
    exact hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := inc_shift_eval suff (r + 1) L_pref
  have hret := return0_scan_fence pref L_stack (regsTape ((r + 1) :: suff))
  have hset : ListBlank.append (encodeRegs pref) (regsTape ((r + 1) :: suff)) =
      regsTape (p :: regs.set k (r + 1)) := by
    rw [← regsTape_append]
    congr 1
    simp only [pref, List.cons_append]
    congr 1
    exact list_take_set_drop regs k (r + 1) hk
  rw [hset] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (nSteps_bind_eq hr_scan (nSteps_bind_eq hshift hret)))
  exact ⟨_, by omega, htotal⟩

theorem regDecnzStage3_trans_one (k : ℕ) (hk : k < 5) :
    rh121Trans (regDecnzStage3 k) 1 = some (0, .right, rhRegDecrChain (k + 2)) := by
  revert k hk; decide

theorem rhRegDecrChain_trans_one (m : ℕ) (hm1 : 1 ≤ m) (hm6 : m ≤ 6) :
    rh121Trans (rhRegDecrChain m) 1 = some (1, .right, rhRegDecrChain m) := by
  revert m hm1 hm6; decide

theorem rhRegDecrChain_trans_zero (m : ℕ) (hm : m < 6) :
    rh121Trans (rhRegDecrChain (m + 1)) 0 = some (0, .right, rhRegDecrChain m) := by
  revert m hm; decide

theorem rhRegDecrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 5)
    (L R : ListBlank (Fin 2)) :
    nSteps riemann121 ((encodeRegs pref).length + 1)
      ⟨rhRegDecrChain (pref.length + 1),
        Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨51, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length + 1 < 6 := by omega
    have hrs_le : rs.length ≤ 5 := by omega
    have h0 : step riemann121
        ⟨rhRegDecrChain (rs.length + 1 + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨rhRegDecrChain (rs.length + 1),
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (rhRegDecrChain_trans_zero (rs.length + 1) hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan
      (rhRegDecrChain_trans_one (rs.length + 1) (by omega) (by omega))
      (r + 1) (L.cons 0) ((ListBlank.append (encodeRegs rs) R).cons 0)
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
      ← encodeRegs_cons] at hrest
    have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
    have hlen : (r + 1) + ((encodeRegs rs).length + 1) + 1 =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

/-- Leftward shift of a single register `m` in States `106`/`100` (`2b.reg.dec.shift_2/1`). -/
theorem dec_shift_reg (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (m + 2)
      ⟨106, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ =
      some ⟨106, Tape.mkL L (ListBlank.append (encodeReg m) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step riemann121
      ⟨106, Tape.mkL ((ListBlank.append (List.replicate m 1) (L.cons 0)).cons 1) R⟩ =
      some ⟨100, Tape.mkL (ListBlank.append (List.replicate m 1) (L.cons 0)) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 100) (a := 1) (b := 1) (by rfl)
    m (L.cons 0) (R.cons 0)
  have h2 : step riemann121
      ⟨100, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ =
      some ⟨106, Tape.mkL L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcons : (ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1 =
      ListBlank.append (encodeReg m) R := by
    rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  rw [hcons] at h2
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  simpa [Nat.add_assoc] using hcomb

/-- Forward scan in States `92`/`79` (`scan_2/1`) and leftward shift in `100`/`106`. -/
theorem dec_scan_and_shift (suff : List ℕ) (m : ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨92, Tape.mk' (ListBlank.append (encodeReg m).reverse (L.cons 0)) (regsTape suff)⟩ =
      some ⟨106, Tape.mkL L (regsTape (m :: (suff ++ [0])))⟩ := by
  induction suff generalizing m L with
  | nil =>
    rw [regsTape_nil, append_encodeReg_reverse]
    have h1 : step riemann121
        ⟨92, Tape.mk'
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨100, Tape.mkL
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      rw [step_mk'_left (by rfl), default_cons_zero]
    have h2 : step riemann121
        ⟨100, Tape.mkL
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨106, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0))
          (regsTape [0])⟩ := by
      have h := step_mkL_left (q := 100) (q' := 106) (a := 0) (b := 1) (by rfl)
        (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default
      have h0 : (default : ListBlank (Fin 2)).cons 1 = regsTape [0] := by
        rw [regsTape_cons, regsTape_nil, append_encodeReg, default_cons_zero]
        rfl
      rw [h0] at h
      exact h
    have hshift := dec_shift_reg m L (regsTape [0])
    rw [← regsTape_cons] at hshift
    exact ⟨m + 4, by omega, step_nSteps h1 (step_nSteps h2 hshift)⟩
  | cons r rs ih =>
    let L' := ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)
    have hL' : ListBlank.append (encodeReg m).reverse (L.cons 0) = L'.cons 0 :=
      append_encodeReg_reverse m (L.cons 0)
    rw [hL', regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step riemann121
        ⟨92, Tape.mk' (L'.cons 0)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨79, Tape.mk' ((L'.cons 0).cons 1)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 79) (a := 1) (b := 1) (by rfl)
      r ((L'.cons 0).cons 1) ((regsTape rs).cons 0)
    have h2 : step riemann121
        ⟨79, Tape.mk' (ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1))
          ((regsTape rs).cons 0)⟩ =
        some ⟨92, Tape.mk' ((ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1)).cons 0)
          (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan_reg := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r (L'.cons 0)] at hscan_reg
    obtain ⟨s, hs1, hs⟩ := ih r L'
    have hshift := dec_shift_reg m L (regsTape (r :: (rs ++ [0])))
    rw [← regsTape_cons] at hshift
    have hcomb := nSteps_bind_eq hscan_reg (nSteps_bind_eq hs hshift)
    exact ⟨_, by omega, hcomb⟩

theorem dec_shift2_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (r + 2)
      ⟨106, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨15, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step riemann121
      ⟨106, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨15, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step riemann121
      ⟨15, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨15, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 15) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

theorem dec_return0_scan_fence (p : ℕ) (rs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 ((encodeRegs (p :: rs)).length + 2)
      ⟨106, Tape.mkL (ListBlank.append (encodeRegs (p :: rs)).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨19, Tape.mkL L ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0 |>.cons 0)⟩ := by
  have hscan_nonempty : ∀ (pref : List ℕ), pref ≠ [] → ∀ L' R',
      nSteps riemann121 (encodeRegs pref).length
        ⟨106, Tape.mkL (ListBlank.append (encodeRegs pref).reverse L') R'⟩ =
        some ⟨15, Tape.mkL L' (ListBlank.append (encodeRegs pref) R')⟩ := by
    intro pref hne L' R'
    induction pref using List.reverseRecOn generalizing L' R' with
    | nil => contradiction
    | append_singleton xs x _ =>
      rw [encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil,
        List.reverse_append, ListBlank.append_assoc, List.length_append,
        Nat.add_comm, nSteps_add, encodeReg_length,
        dec_shift2_scan_reg, Option.bind_some, return0_scan_regs, ListBlank.append_assoc]
  have hregs := hscan_nonempty (p :: rs) (List.cons_ne_nil p rs) ((L.cons 0).cons 0) R
  have h1 : step riemann121
      ⟨15, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs (p :: rs)) R)⟩ =
      some ⟨17, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step riemann121
      ⟨17, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0)⟩ =
      some ⟨19, Tape.mkL L (((ListBlank.append (encodeRegs (p :: rs)) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-- Pass 2 `3.<reg_k>.decnz` when `regs[k] = 0`: leaves `regs` unchanged and enters `91`. -/
theorem stage3_decnz_pass2_zero (k : ℕ) (hk5 : k < 5) (p : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hz : regs[k] = 0) (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨91, Tape.mkL L_stack ((regsTape (p :: regs)).cons 0 |>.cons 0)⟩ := by
  set pref := p :: regs.take k
  set suff := regs.drop (k + 1)
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape (0 :: suff)) := by
    have hlist : p :: regs = pref ++ 0 :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      rw [← hz]
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step riemann121
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨rhRegDecrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape (0 :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecnzStage3_trans_one k hk5) L_stack _
  have hpref_scan := rhRegDecrChain_scan_pref pref (by omega)
    (L_stack.cons 0) (regsTape (0 :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have h1 : step riemann121 ⟨51, Tape.mk' L_pref (regsTape (0 :: suff))⟩ =
      some ⟨64, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mk'_right (by rfl) L_pref ((regsTape suff).cons 0)
  have h2 : step riemann121 ⟨64, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨51, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ :=
    step_mk'_left (by rfl) (L_pref.cons 0) (regsTape suff)
  have h3 : step riemann121 ⟨51, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨63, Tape.mkL L_pref (regsTape (0 :: suff))⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mkL_left (by rfl) L_pref ((regsTape suff).cons 0)
  have hret := return1_scan_fence pref L_stack (regsTape (0 :: suff))
  rw [← hregs_split] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps h1 (step_nSteps h2 (step_nSteps h3 hret))))
  exact ⟨_, by omega, htotal⟩

/-- Pass 2 `3.<reg_k>.decnz` when `regs[k] > 0`:
decrements `regs[k]`, appends `[0]`, enters `19`. -/
theorem stage3_decnz_pass2_pos (k : ℕ) (hk5 : k < 5) (p : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hpos : 0 < regs[k]) (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨19, Tape.mkL L_stack
        ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0)⟩ := by
  set pref := p :: regs.take k
  set r' := regs[k] - 1
  set suff := regs.drop (k + 1)
  have hr_eq : regs[k] = r' + 1 := by omega
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape ((r' + 1) :: suff)) := by
    have hlist : p :: regs = pref ++ (r' + 1) :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      rw [← hr_eq]
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step riemann121
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨rhRegDecrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape ((r' + 1) :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecnzStage3_trans_one k hk5) L_stack _
  have hpref_scan := rhRegDecrChain_scan_pref pref (by omega) (L_stack.cons 0)
    (regsTape ((r' + 1) :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have hinit : step riemann121 ⟨51, Tape.mk' L_pref (regsTape ((r' + 1) :: suff))⟩ =
      some ⟨64, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ := by
    have hcons : regsTape ((r' + 1) :: suff) = (regsTape (r' :: suff)).cons 1 := by
      rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append,
        ← append_encodeReg, ← regsTape_cons]
    rw [hcons]
    exact step_mk'_right (by rfl) L_pref (regsTape (r' :: suff))
  have hr'_scan : nSteps riemann121 (r' + 2)
      ⟨64, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ =
      some ⟨92, Tape.mk' (ListBlank.append (encodeReg r').reverse (L_pref.cons 0))
        (regsTape suff)⟩ := by
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step riemann121
        ⟨64, Tape.mk' (L_pref.cons 0)
          ((ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0)).cons 1)⟩ =
        some ⟨79, Tape.mk' ((L_pref.cons 0).cons 1)
          (ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 79) (a := 1) (b := 1) (by rfl)
      r' ((L_pref.cons 0).cons 1) ((regsTape suff).cons 0)
    have h2 : step riemann121
        ⟨79, Tape.mk' (ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1))
          ((regsTape suff).cons 0)⟩ =
        some ⟨92, Tape.mk'
          ((ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1)).cons 0)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r' (L_pref.cons 0)] at hcomb
    simpa [Nat.add_assoc] using hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := dec_scan_and_shift suff r' L_pref
  have hret := dec_return0_scan_fence p (regs.take k) L_stack (regsTape (r' :: (suff ++ [0])))
  have hset : ListBlank.append (encodeRegs pref) (regsTape (r' :: (suff ++ [0]))) =
      regsTape (p :: (regs.set k r' ++ [0])) := by
    rw [← regsTape_append]
    congr 1
    have h1 : pref ++ r' :: (suff ++ [0]) = p :: ((regs.take k ++ r' :: suff) ++ [0]) := by
      simp [pref]
    rw [h1, list_take_set_drop regs k r' hk]
  rw [hset] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps hinit (nSteps_bind_eq hr'_scan (nSteps_bind_eq hshift hret))))
  exact ⟨_, by omega, htotal⟩

/-!
## 7. Break, Cleanup, Halt & End-to-End Root Gadgets
-/

theorem halt_at_6 (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨6, Tape.mk' L (R.cons 1)⟩ = none := by
  simp [step, rh121Trans_eq, Tape.mk']; rfl

theorem halt_at_77 (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨77, Tape.mk' L (R.cons 1)⟩ = none := by
  simp [step, rh121Trans_eq, Tape.mk']; rfl

theorem cleanup_to_10 (L : ListBlank (Fin 2)) (z p : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨21, Tape.mk' L (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg p) R))⟩ =
      some ⟨10, Tape.mkL L (ListBlank.append (List.replicate (z + p) 0)
        (ListBlank.append [1, 0] R))⟩ := by
  have hscan_z := nSteps_mk'_right_scan (q := 21) (a := 0) (b := 0) (by rfl) z
    L (ListBlank.append (encodeReg p) R)
  conv at hscan_z => rhs; rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step riemann121
      ⟨21, Tape.mk' (ListBlank.append (List.replicate z 0) L)
        ((ListBlank.append (List.replicate p 1) (R.cons 0)).cons 1)⟩ =
      some ⟨23, Tape.mk' ((ListBlank.append (List.replicate z 0) L).cons 0)
        (ListBlank.append (List.replicate p 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan_p := nSteps_mk'_right_scan (q := 23) (a := 1) (b := 0) (by rfl) p
    ((ListBlank.append (List.replicate z 0) L).cons 0) (R.cons 0)
  have hzeros : ListBlank.append (List.replicate p 0)
      ((ListBlank.append (List.replicate z 0) L).cons 0) =
      (ListBlank.append (List.replicate (z + p) 0) L).cons 0 := by
    rw [append_replicate_cons, ← ListBlank.append_assoc, ← List.replicate_add]
    have hadd : p + 1 + z = (z + p) + 1 := by omega
    rw [hadd, List.replicate_succ, ListBlank.append]
  rw [hzeros] at hscan_p
  have h2 : step riemann121
      ⟨23, Tape.mk' ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ =
      some ⟨24, Tape.mkL ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ R
  have h3 : step riemann121
      ⟨24, Tape.mkL ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ =
      some ⟨10, Tape.mkL (ListBlank.append (List.replicate (z + p) 0) L)
        (ListBlank.append [1, 0] R)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan_back := continue0_scan_zeros (z + p) L (ListBlank.append [1, 0] R)
  have htotal := nSteps_bind_eq hscan_z (step_nSteps h1 (nSteps_bind_eq hscan_p
    (step_nSteps h2 (step_nSteps h3 hscan_back))))
  exact ⟨_, by omega, htotal⟩

theorem cleanup_to_main (stack' : List (Fin 2))
    (hstack' : NoFourZeros ([1, 1, 0] ++ stack') = true) (z m : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨21, Tape.mk' (stackLeft stack')
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨27, Tape.mk' rootLeft
        (ListBlank.append stack'
          (ListBlank.append (List.replicate (z + m) 0) (ListBlank.append [1, 0] R)))⟩ := by
  obtain ⟨s₁, hs1, h10⟩ := cleanup_to_10 (stackLeft stack') z m R
  obtain ⟨s₂, hs2, hret⟩ := continue0_return stack' hstack'
    (ListBlank.append (List.replicate (z + m) 0) (ListBlank.append [1, 0] R))
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq h10 hret⟩

theorem break0_step (c₀ : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (c₀ + 1)
      ⟨19, Tape.mkL (ListBlank.append (List.replicate c₀ 1) (L.cons 0)) R⟩ =
      some ⟨21, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate c₀ 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 19) (a := 1) (b := 0) (by rfl) c₀ (L.cons 0) R
  have h1 : step riemann121
      ⟨19, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate c₀ 0) R)⟩ =
      some ⟨21, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate c₀ 0) R)⟩ :=
    step_mkL_right (by rfl) _ _
  exact nSteps_bind_eq hscan (step_one h1)

theorem break1_step (c₁ : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (c₁ + 1)
      ⟨91, Tape.mkL (ListBlank.append (List.replicate c₁ 1) (L.cons 0)) R⟩ =
      some ⟨19, Tape.mkL L (ListBlank.append (List.replicate (c₁ + 1) 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 91) (a := 1) (b := 0) (by rfl) c₁ (L.cons 0) R
  have h1 : step riemann121
      ⟨91, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate c₁ 0) R)⟩ =
      some ⟨19, Tape.mkL L ((ListBlank.append (List.replicate c₁ 0) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq hscan (step_one h1)
  rwa [List.replicate_succ, ListBlank.append]

theorem break0_cleanup_to_main (stack' : List (Fin 2))
    (hstack' : NoFourZeros ([1, 1, 0] ++ stack') = true) (c₀ z m : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨19, Tape.mkL (stackLeft (stack' ++ [0] ++ List.replicate c₀ 1))
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨27, Tape.mk' rootLeft
        (ListBlank.append (stack' ++ [1])
          (ListBlank.append (List.replicate (c₀ + z + m) 0) (ListBlank.append [1, 0] R)))⟩ := by
  have hL : stackLeft (stack' ++ [0] ++ List.replicate c₀ 1) =
      ListBlank.append (List.replicate c₀ 1) ((stackLeft stack').cons 0) := by
    rw [stackLeft_append, List.reverse_replicate, stackLeft_append_singleton]
  rw [hL]
  have hb0 := break0_step c₀ (stackLeft stack')
    (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))
  have hL1 : (stackLeft stack').cons 1 = stackLeft (stack' ++ [1]) := by
    rw [stackLeft_append_singleton]
  have hR1 : ListBlank.append (List.replicate c₀ 0)
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R)) =
      ListBlank.append (List.replicate (c₀ + z) 0) (ListBlank.append (encodeReg m) R) := by
    rw [← ListBlank.append_assoc, ← List.replicate_add]
  rw [hL1, hR1] at hb0
  have hcnt1 : NoFourZeros ([1, 1, 0] ++ (stack' ++ [1])) = true := by
    have ha : [1, 1, 0] ++ (stack' ++ [1]) = ([1, 1, 0] ++ stack') ++ [1] := by
      simp only [List.append_assoc]
    rw [ha, NoFourZeros_snoc_one]
    exact hstack'
  obtain ⟨s_cl, hs1, hcl⟩ := cleanup_to_main (stack' ++ [1]) hcnt1 (c₀ + z) m R
  exact ⟨_, by omega, nSteps_bind_eq hb0 hcl⟩

theorem break1_cleanup_to_main (stack' : List (Fin 2))
    (hstack' : NoFourZeros ([1, 1, 0] ++ stack') = true) (c₀ c₁ z m : ℕ)
    (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨91, Tape.mkL
        (stackLeft (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1))
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨27, Tape.mk' rootLeft
        (ListBlank.append (stack' ++ [1])
          (ListBlank.append (List.replicate (c₀ + (c₁ + 1 + z) + m) 0)
            (ListBlank.append [1, 0] R)))⟩ := by
  have hL : stackLeft (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1) =
      ListBlank.append (List.replicate c₁ 1)
        ((stackLeft (stack' ++ [0] ++ List.replicate c₀ 1)).cons 0) := by
    rw [stackLeft_append, List.reverse_replicate, stackLeft_append_singleton]
  rw [hL]
  have hb1 := break1_step c₁ (stackLeft (stack' ++ [0] ++ List.replicate c₀ 1))
    (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))
  have hR1 : ListBlank.append (List.replicate (c₁ + 1) 0)
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R)) =
      ListBlank.append (List.replicate (c₁ + 1 + z) 0) (ListBlank.append (encodeReg m) R) := by
    rw [← ListBlank.append_assoc, ← List.replicate_add]
  rw [hR1] at hb1
  obtain ⟨s_b0, hs1, hb0⟩ := break0_cleanup_to_main stack' hstack' c₀ (c₁ + 1 + z) m R
  exact ⟨_, by omega, nSteps_bind_eq hb1 hb0⟩

theorem stage3_inc_pass2_to_root (k : ℕ) (hk5 : k < 5) (padTotal : ℕ)
    (stack' : List (Fin 2)) (c₀ : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (hpad : (stack' ++ [0] ++ List.replicate c₀ 1).length + 2 ≤ padTotal)
    (hstack' : NoFourZeros ([1, 1, 0] ++ stack') = true) :
    let stack := stack' ++ [0] ++ List.replicate c₀ 1
    let p := padTotal - stack.length - 2
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨regIncStage3 k, Tape.mk' (stackLeft stack) ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some (rhRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] + 1))) := by
  intro stack p
  obtain ⟨s₁, hs1, hp2⟩ := stage3_inc_pass2 k hk5 p regs hk (stackLeft stack)
  have hR_eq : ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0) =
      ListBlank.append (List.replicate 2 0)
        (ListBlank.append (encodeReg p) (regsTape (regs.set k (regs[k] + 1)))) := by
    rw [regsTape_cons]
    rfl
  rw [hR_eq] at hp2
  obtain ⟨s₂, hs2, hcl⟩ := break0_cleanup_to_main stack' hstack' c₀ 2 p
    (regsTape (regs.set k (regs[k] + 1)))
  have hpad_eq : c₀ + 2 + p = padTotal - (stack' ++ [1]).length := by
    simp only [stack, p, List.length_append, List.length_singleton, List.length_replicate] at hpad ⊢
    omega
  rw [hpad_eq] at hcl
  have hroot_eq : ⟨27, Tape.mk' rootLeft
      (ListBlank.append (stack' ++ [1])
        (ListBlank.append (List.replicate (padTotal - (stack' ++ [1]).length) 0)
          (ListBlank.append [1, 0] (regsTape (regs.set k (regs[k] + 1))))))⟩ =
      rhRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] + 1)) := by
    rw [rhRootCfg_default_eq, regsTape_cons]
    rfl
  rw [hroot_eq] at hcl
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hp2 hcl⟩

theorem stage3_decnz_pass2_zero_to_root (k : ℕ) (hk5 : k < 5) (padTotal : ℕ)
    (stack' : List (Fin 2)) (c₀ c₁ : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (hz : regs[k] = 0)
    (hpad : (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1).length +
      2 ≤ padTotal)
    (hstack' : NoFourZeros ([1, 1, 0] ++ stack') = true) :
    let stack := stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1
    let p := padTotal - stack.length - 2
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨regDecnzStage3 k, Tape.mk' (stackLeft stack) ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some (rhRootCfg padTotal (stack' ++ [1]) regs) := by
  intro stack p
  obtain ⟨s₁, hs1, hp2⟩ := stage3_decnz_pass2_zero k hk5 p regs hk hz (stackLeft stack)
  have hR_eq : ((regsTape (p :: regs)).cons 0 |>.cons 0) =
      ListBlank.append (List.replicate 2 0)
        (ListBlank.append (encodeReg p) (regsTape regs)) := by
    rw [regsTape_cons]
    rfl
  rw [hR_eq] at hp2
  obtain ⟨s₂, hs2, hcl⟩ := break1_cleanup_to_main stack' hstack' c₀ c₁ 2 p (regsTape regs)
  have hpad_eq : c₀ + (c₁ + 1 + 2) + p = padTotal - (stack' ++ [1]).length := by
    simp only [stack, p, List.length_append, List.length_singleton, List.length_replicate] at hpad ⊢
    omega
  rw [hpad_eq] at hcl
  have hroot_eq : ⟨27, Tape.mk' rootLeft
      (ListBlank.append (stack' ++ [1])
        (ListBlank.append (List.replicate (padTotal - (stack' ++ [1]).length) 0)
          (ListBlank.append [1, 0] (regsTape regs))))⟩ =
      rhRootCfg padTotal (stack' ++ [1]) regs := by
    rw [rhRootCfg_default_eq, regsTape_cons]
    rfl
  rw [hroot_eq] at hcl
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hp2 hcl⟩

theorem stage3_decnz_pass2_pos_to_root (k : ℕ) (hk5 : k < 5) (padTotal : ℕ)
    (stack' : List (Fin 2)) (c₀ : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (hpos : 0 < regs[k])
    (hpad : (stack' ++ [0] ++ List.replicate c₀ 1).length + 2 ≤ padTotal)
    (hstack' : NoFourZeros ([1, 1, 0] ++ stack') = true) :
    let stack := stack' ++ [0] ++ List.replicate c₀ 1
    let p := padTotal - stack.length - 2
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨regDecnzStage3 k, Tape.mk' (stackLeft stack) ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some (rhRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] - 1) ++ [0])) := by
  intro stack p
  obtain ⟨s₁, hs1, hp2⟩ := stage3_decnz_pass2_pos k hk5 p regs hk hpos (stackLeft stack)
  have hR_eq : ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0) =
      ListBlank.append (List.replicate 2 0)
        (ListBlank.append (encodeReg p) (regsTape (regs.set k (regs[k] - 1) ++ [0]))) := by
    rw [regsTape_cons]
    rfl
  rw [hR_eq] at hp2
  obtain ⟨s₂, hs2, hcl⟩ := break0_cleanup_to_main stack' hstack' c₀ 2 p
    (regsTape (regs.set k (regs[k] - 1) ++ [0]))
  have hpad_eq : c₀ + 2 + p = padTotal - (stack' ++ [1]).length := by
    simp only [stack, p, List.length_append, List.length_singleton, List.length_replicate] at hpad ⊢
    omega
  rw [hpad_eq] at hcl
  have hroot_eq : ⟨27, Tape.mk' rootLeft
      (ListBlank.append (stack' ++ [1])
        (ListBlank.append (List.replicate (padTotal - (stack' ++ [1]).length) 0)
          (ListBlank.append [1, 0] (regsTape (regs.set k (regs[k] - 1) ++ [0])))))⟩ =
      rhRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] - 1) ++ [0]) := by
    rw [rhRootCfg_default_eq, regsTape_cons]
    rfl
  rw [hroot_eq] at hcl
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hp2 hcl⟩

/-!
## 8. Bootstrap Proof (`0a.boot1` & `0b.boot2`) from `init` to `main.0` (`State 27`)
-/

theorem boot1_scan_DE (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * k) ⟨3, Tape.mk' L (ListBlank.append (pair10 k) R)⟩ =
      some ⟨3, Tape.mk' (ListBlank.append (pair10 k).reverse L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    simp only [pair10, ListBlank.append]
    have h1 : step riemann121
        ⟨3, Tape.mk' L (((ListBlank.append (pair10 k) R).cons 0).cons 1)⟩ =
        some ⟨5, Tape.mk' (L.cons 1) ((ListBlank.append (pair10 k) R).cons 0)⟩ :=
      step_mk'_right (by rfl) _ _
    have h2 : step riemann121
        ⟨5, Tape.mk' (L.cons 1) ((ListBlank.append (pair10 k) R).cons 0)⟩ =
        some ⟨3, Tape.mk' ((L.cons 1).cons 0) (ListBlank.append (pair10 k) R)⟩ :=
      step_mk'_right (by rfl) _ _
    have hrest := ih ((L.cons 1).cons 0)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [hlen] at hcomb
    simpa [pair10, List.reverse_cons, ListBlank.append_assoc] using hcomb

theorem boot1_scan_DB (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * k) ⟨3, Tape.mkL (ListBlank.append (pair10 k).reverse L) R⟩ =
      some ⟨3, Tape.mkL L (ListBlank.append (pair01 k) R)⟩ := by
  induction k generalizing L R with
  | zero => rfl
  | succ k ih =>
    rw [← pair10_snoc, List.reverse_append, ListBlank.append_assoc]
    have h1 : step riemann121
        ⟨3, Tape.mkL (((ListBlank.append (pair10 k).reverse L).cons 1).cons 0) R⟩ =
        some ⟨1, Tape.mkL ((ListBlank.append (pair10 k).reverse L).cons 1) (R.cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have h2 : step riemann121
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

theorem boot1_scan_AC (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * k) ⟨0, Tape.mkL (ListBlank.append (pair01 k).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (List.replicate (2 * k) 1) R)⟩ := by
  induction k generalizing L R with
  | zero => rfl
  | succ k ih =>
    rw [← pair01_snoc, List.reverse_append, ListBlank.append_assoc]
    have h1 : step riemann121
        ⟨0, Tape.mkL (((ListBlank.append (pair01 k).reverse L).cons 0).cons 1) R⟩ =
        some ⟨2, Tape.mkL ((ListBlank.append (pair01 k).reverse L).cons 0) (R.cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have h2 : step riemann121
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

def rhMidCfg (k m : ℕ) (R : ListBlank (Fin 2)) : Cfg 121 2 :=
  ⟨0, Tape.mk' default
    (ListBlank.append ([0, 1, 1] ++ pair01 k ++ List.replicate m 1) R)⟩

theorem rhMidCfg_to_state3 (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 2 ⟨0, Tape.mk' default (ListBlank.append ([0, 1, 1] ++ pair01 k) R)⟩ =
      some ⟨3, Tape.mk' default (ListBlank.append (pair10 (k + 1) ++ [1]) R)⟩ := by
  simp only [List.cons_append, List.nil_append, ListBlank.append]
  have h1 : step riemann121
      ⟨0, Tape.mk' default (((ListBlank.append (pair01 k) R).cons 1).cons 1 |>.cons 0)⟩ =
      some ⟨1, Tape.mk' (ListBlank.cons 1 default)
        (((ListBlank.append (pair01 k) R).cons 1).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step riemann121
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

theorem rhMidCfg_step_two (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (4 * k + 17) (rhMidCfg k 2 R) =
      some (rhMidCfg (k + 3) 0 (R.cons 0)) := by
  unfold rhMidCfg
  simp only [List.replicate, List.append_nil, List.append_assoc, ListBlank.append_assoc]
  have hinit := rhMidCfg_to_state3 k (ListBlank.append [1, 1] R)
  have hscanR := boot1_scan_DE (k + 1) default (ListBlank.append [1, 1, 1] R)
  simp only [ListBlank.append_assoc, ListBlank.append] at hinit hscanR
  set L_k := ListBlank.append (pair10 (k + 1)).reverse default
  have hs1 : step riemann121 ⟨3, Tape.mk' L_k (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨5, Tape.mk' (L_k.cons 1) ((R.cons 1).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs2 : step riemann121 ⟨5, Tape.mk' (L_k.cons 1) ((R.cons 1).cons 1)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs3 : step riemann121 ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 1)⟩ =
      some ⟨3, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ _
  have hs4 : step riemann121 ⟨3, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hs5 : step riemann121 ⟨1, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨3, Tape.mkL L_k (((R.cons 0).cons 1).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hturn := step_nSteps hs1 (step_nSteps hs2 (step_nSteps hs3 (step_nSteps hs4 (step_one hs5))))
  have hscanL := boot1_scan_DB (k + 1) default (((R.cons 0).cons 1).cons 0)
  set R_k := ListBlank.append (pair01 (k + 1)) (((R.cons 0).cons 1).cons 0)
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have he1 : step riemann121 ⟨3, Tape.mkL default R_k⟩ =
      some ⟨1, Tape.mkL default (R_k.cons 1)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_left (by rfl) default R_k
  have he2 : step riemann121 ⟨1, Tape.mkL default (R_k.cons 1)⟩ =
      some ⟨0, Tape.mkL default ((R_k.cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_left (by rfl) default (R_k.cons 1)
  have he3 : step riemann121 ⟨0, Tape.mkL default ((R_k.cons 1).cons 0)⟩ =
      some ⟨1, Tape.mk' (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_right (by rfl) default ((R_k.cons 1).cons 0)
  have he4 : step riemann121 ⟨1, Tape.mk' (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ =
      some ⟨0, Tape.mkL (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ :=
    step_mk'_left (by rfl) _ (R_k.cons 1)
  have he5 : step riemann121 ⟨0, Tape.mkL (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ =
      some ⟨2, Tape.mkL default (((R_k.cons 1).cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have he6 : step riemann121 ⟨2, Tape.mkL default (((R_k.cons 1).cons 0).cons 1)⟩ =
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

theorem rhMidCfg_step_three (k m : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (4 * k + 17) (rhMidCfg k (m + 3) R) =
      some (rhMidCfg (k + 4) m R) := by
  have heq :
      rhMidCfg k (m + 3) R = rhMidCfg k 2 (ListBlank.append (List.replicate (m + 1) 1) R) := by
    unfold rhMidCfg
    have hrep : List.replicate (m + 3) (1 : Fin 2) =
        List.replicate 2 1 ++ List.replicate (m + 1) 1 := by
      rw [show m + 3 = 2 + (m + 1) by omega, List.replicate_add]
    simp only [hrep, List.append_assoc, ListBlank.append_assoc]
  rw [heq, rhMidCfg_step_two]
  congr 1
  unfold rhMidCfg
  simp only [List.replicate, List.append_assoc, ListBlank.append_assoc, ListBlank.append]
  have hpair : ListBlank.append (pair01 (k + 3))
      (((ListBlank.append (List.replicate m 1) R).cons 1).cons 0) =
      ListBlank.append (pair01 (k + 4)) (ListBlank.append (List.replicate m 1) R) := by
    rw [← pair01_snoc (k + 3), ListBlank.append_assoc]
    rfl
  rw [hpair]

theorem rhMidCfg_loop (j k r : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, nSteps riemann121 s (rhMidCfg k (3 * j + r) R) =
      some (rhMidCfg (k + 4 * j) r R) := by
  induction j generalizing k with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ j ih =>
    have h1 : 3 * (j + 1) + r = (3 * j + r) + 3 := by omega
    rw [h1]
    have hstep := rhMidCfg_step_three k (3 * j + r) R
    obtain ⟨s, hs⟩ := ih (k + 4)
    have h2 : k + 4 + 4 * j = k + 4 * (j + 1) := by omega
    rw [h2] at hs
    exact ⟨_, nSteps_bind_eq hstep hs⟩

theorem rhMidCfg_step_zero (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (4 * k + 12) (rhMidCfg k 0 ((R.cons 0).cons 0)) =
      some (rhMidCfg 0 (2 * k + 2) ((R.cons 1).cons 0)) := by
  unfold rhMidCfg
  simp only [List.replicate, List.append_nil]
  have hinit := rhMidCfg_to_state3 k ((R.cons 0).cons 0)
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
  have hs1 : step riemann121 ⟨3, Tape.mk' (L_p.cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mkL (L_p.cons 0) (R.cons 1)⟩ :=
    step_mk'_left (by rfl) _ _
  have hs2 : step riemann121 ⟨1, Tape.mkL (L_p.cons 0) (R.cons 1)⟩ =
      some ⟨0, Tape.mkL L_p ((R.cons 1).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscanL := boot1_scan_AC (k + 1) (ListBlank.cons 1 default) ((R.cons 1).cons 0)
  set R_ones := ListBlank.append (List.replicate (2 * (k + 1)) 1) ((R.cons 1).cons 0)
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have he1 : step riemann121 ⟨0, Tape.mkL (ListBlank.cons 1 default) R_ones⟩ =
      some ⟨2, Tape.mkL default (R_ones.cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have he2 : step riemann121 ⟨2, Tape.mkL default (R_ones.cons 1)⟩ =
      some ⟨0, Tape.mk' default (((R_ones.cons 1).cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    rw [step_mkL_left (by rfl), Tape.mkL_default]
  have htotal := nSteps_bind_eq hinit (nSteps_bind_eq hscanR
    (step_nSteps hs1 (step_nSteps hs2 (nSteps_bind_eq hscanL
      (step_nSteps he1 (step_one he2))))))
  have hlen : 2 + (2 * (k + 2) + (2 * (k + 1) + (1 + 1) + 1 + 1)) = 4 * k + 12 := by omega
  rw [hlen] at htotal
  have hR_eq : (((R_ones.cons 1).cons 1).cons 0) =
      ListBlank.append ([0, 1, 1] ++ pair01 0 ++ List.replicate (2 * k + 2) 1)
        ((R.cons 1).cons 0) := by
    simp only [R_ones, pair01, List.append_nil]
    rfl
  rw [hR_eq] at htotal
  exact htotal

theorem rhMidCfg_exit_one (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * k + 11) (rhMidCfg k 1 (R.cons 0)) =
      some ⟨4, Tape.mk' (ListBlank.append (pair10 (k + 1) ++ [1]).reverse default)
        ((R.cons 0).cons 1)⟩ := by
  unfold rhMidCfg
  simp only [List.replicate, List.append_assoc, ListBlank.append_assoc]
  have hinit := rhMidCfg_to_state3 k ((R.cons 0).cons 1)
  have hscanR := boot1_scan_DE (k + 1) default (((R.cons 0).cons 1).cons 1)
  simp only [ListBlank.append_assoc, ListBlank.append] at hinit hscanR
  set L_k := ListBlank.append (pair10 (k + 1)).reverse default
  have hs1 : step riemann121 ⟨3, Tape.mk' L_k (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨5, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs2 : step riemann121 ⟨5, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs3 : step riemann121 ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨0, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ _
  have hs4 : step riemann121 ⟨0, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mkL_right (by rfl) _ _
  have hs5 : step riemann121 ⟨1, Tape.mk' ((L_k.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨0, Tape.mkL ((L_k.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ _
  have hs6 : step riemann121 ⟨0, Tape.mkL ((L_k.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨2, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hs7 : step riemann121 ⟨2, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨4, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_right (by rfl) _ _
  have htotal := nSteps_bind_eq hinit (nSteps_bind_eq hscanR
    (step_nSteps hs1 (step_nSteps hs2 (step_nSteps hs3
      (step_nSteps hs4 (step_nSteps hs5 (step_nSteps hs6 (step_one hs7))))))))
  have hlen : 2 + (2 * (k + 1) + 7) = 2 * k + 11 := by omega
  rw [hlen] at htotal
  simpa [L_k, List.reverse_append, ListBlank.append_assoc] using htotal

theorem boot1_eval :
    ∃ s, nSteps riemann121 s init =
      some ⟨4, Tape.mk' (ListBlank.append (pair10 1909 ++ [1]).reverse default)
        (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ := by
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have h0_1 : step riemann121 init = some ⟨1, Tape.mk' (ListBlank.cons 1 default) default⟩ := by
    have h := step_mk'_right (q := 0) (q' := 1) (a := 0) (b := 1) (by rfl) default default
    rwa [← hdef] at h
  have h0_2 : step riemann121 ⟨1, Tape.mk' (ListBlank.cons 1 default) default⟩ =
      some ⟨0, Tape.mkL (ListBlank.cons 1 default) default⟩ := by
    have h := step_mk'_left (q := 1) (q' := 0) (a := 0) (b := 0) (by rfl)
      (ListBlank.cons 1 default) default
    rwa [← hdef] at h
  have h0_3 : step riemann121 ⟨0, Tape.mkL (ListBlank.cons 1 default) default⟩ =
      some ⟨2, Tape.mkL default (ListBlank.cons 1 default)⟩ :=
    step_mkL_left (by rfl) _ _
  have h0_4 : step riemann121 ⟨2, Tape.mkL default (ListBlank.cons 1 default)⟩ =
      some (rhMidCfg 0 0 default) := by
    have h := step_mkL_left (q := 2) (q' := 0) (a := 0) (b := 1) (by rfl)
      default (ListBlank.cons 1 default)
    rw [← hdef, Tape.mkL_default] at h
    exact h
  have hr0 : nSteps riemann121 4 init = some (rhMidCfg 0 0 default) :=
    step_nSteps h0_1 (step_nSteps h0_2 (step_nSteps h0_3 (step_one h0_4)))
  have hr0_1 : nSteps riemann121 12 (rhMidCfg 0 0 default) =
      some (rhMidCfg 0 2 (ListBlank.append [0, 1] default)) := by
    have h := rhMidCfg_step_zero 0 default
    rwa [default_cons_zero, default_cons_zero] at h
  have hr1_a := rhMidCfg_step_two 0 (ListBlank.append [0, 1] default)
  have hr1_b : nSteps riemann121 24 (rhMidCfg 3 0 ((ListBlank.append [0, 1] default).cons 0)) =
      some (rhMidCfg 0 8 (ListBlank.append [0, 1, 1] default)) :=
    rhMidCfg_step_zero 3 (ListBlank.cons 1 default)
  obtain ⟨s2, hr2_loop⟩ := rhMidCfg_loop 2 0 2 (ListBlank.append [0, 1, 1] default)
  have hr2_a := rhMidCfg_step_two 8 (ListBlank.append [0, 1, 1] default)
  have hr2_b : nSteps riemann121 56
      (rhMidCfg 11 0 ((ListBlank.append [0, 1, 1] default).cons 0)) =
      some (rhMidCfg 0 24 (ListBlank.append [0, 1, 1, 1] default)) :=
    rhMidCfg_step_zero 11 (ListBlank.append [1, 1] default)
  obtain ⟨s3, hr3_loop⟩ := rhMidCfg_loop 8 0 0 (ListBlank.append [0, 1, 1, 1] default)
  have hr3_eq : rhMidCfg 32 0 (ListBlank.append [0, 1, 1, 1] default) = rhMidCfg 33 2 default := by
    unfold rhMidCfg
    simp only [List.replicate, List.append_nil, List.append_assoc, ListBlank.append_assoc]
    have hp : ListBlank.append (pair01 32) (ListBlank.append [0, 1, 1, 1] default) =
        ListBlank.append (pair01 33) (ListBlank.append [1, 1] default) := by
      rw [← pair01_snoc 32, ListBlank.append_assoc]
      rfl
    rw [hp]
  rw [hr3_eq] at hr3_loop
  have hr3_a := rhMidCfg_step_two 33 default
  have hr3_b : nSteps riemann121 156 (rhMidCfg 36 0 (ListBlank.cons 0 default)) =
      some (rhMidCfg 0 74 (ListBlank.append [0, 1] default)) := by
    have h := rhMidCfg_step_zero 36 default
    rwa [default_cons_zero] at h
  obtain ⟨s4, hr4_loop⟩ := rhMidCfg_loop 24 0 2 (ListBlank.append [0, 1] default)
  have hr4_a := rhMidCfg_step_two 96 (ListBlank.append [0, 1] default)
  have hr4_b : nSteps riemann121 408 (rhMidCfg 99 0 ((ListBlank.append [0, 1] default).cons 0)) =
      some (rhMidCfg 0 200 (ListBlank.append [0, 1, 1] default)) :=
    rhMidCfg_step_zero 99 (ListBlank.cons 1 default)
  obtain ⟨s5, hr5_loop⟩ := rhMidCfg_loop 66 0 2 (ListBlank.append [0, 1, 1] default)
  have hr5_a := rhMidCfg_step_two 264 (ListBlank.append [0, 1, 1] default)
  have hr5_b : nSteps riemann121 1080
      (rhMidCfg 267 0 ((ListBlank.append [0, 1, 1] default).cons 0)) =
      some (rhMidCfg 0 536 (ListBlank.append [0, 1, 1, 1] default)) :=
    rhMidCfg_step_zero 267 (ListBlank.append [1, 1] default)
  obtain ⟨s6, hr6_loop⟩ := rhMidCfg_loop 178 0 2 (ListBlank.append [0, 1, 1, 1] default)
  have hr6_a := rhMidCfg_step_two 712 (ListBlank.append [0, 1, 1, 1] default)
  have hr6_b : nSteps riemann121 2872
      (rhMidCfg 715 0 ((ListBlank.append [0, 1, 1, 1] default).cons 0)) =
      some (rhMidCfg 0 1432 (ListBlank.append [0, 1, 1, 1, 1] default)) :=
    rhMidCfg_step_zero 715 (ListBlank.append [1, 1, 1] default)
  obtain ⟨s7, hr7_loop⟩ := rhMidCfg_loop 477 0 1 (ListBlank.append [0, 1, 1, 1, 1] default)
  have hexit := rhMidCfg_exit_one 1908 (ListBlank.append [1, 1, 1, 1] default)
  exact ⟨_, nSteps_bind_eq hr0 (nSteps_bind_eq hr0_1 (nSteps_bind_eq hr1_a (nSteps_bind_eq hr1_b
    (nSteps_bind_eq hr2_loop (nSteps_bind_eq hr2_a (nSteps_bind_eq hr2_b
      (nSteps_bind_eq hr3_loop (nSteps_bind_eq hr3_a (nSteps_bind_eq hr3_b
        (nSteps_bind_eq hr4_loop (nSteps_bind_eq hr4_a (nSteps_bind_eq hr4_b
          (nSteps_bind_eq hr5_loop (nSteps_bind_eq hr5_a (nSteps_bind_eq hr5_b
            (nSteps_bind_eq hr6_loop (nSteps_bind_eq hr6_a (nSteps_bind_eq hr6_b
              (nSteps_bind_eq hr7_loop hexit)))))))))))))))))))⟩

theorem boot2_scan_pair (L R : ListBlank (Fin 2)) :
    nSteps riemann121 2 ⟨24, Tape.mk' L (ListBlank.append [1, 0] R)⟩ =
      some ⟨24, Tape.mk' ((L.cons 1).cons 0) R⟩ := by
  have h1 : step riemann121 ⟨24, Tape.mk' L ((R.cons 0).cons 1)⟩ =
      some ⟨26, Tape.mk' (L.cons 1) (R.cons 0)⟩ :=
    step_mk'_right (by rfl) L (R.cons 0)
  have h2 : step riemann121 ⟨26, Tape.mk' (L.cons 1) (R.cons 0)⟩ =
      some ⟨24, Tape.mk' ((L.cons 1).cons 0) R⟩ :=
    step_mk'_right (by rfl) (L.cons 1) R
  exact step_nSteps h1 (step_one h2)

theorem boot2_scan_pairs (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * m) ⟨24, Tape.mk' L (ListBlank.append (pair10 m) R)⟩ =
      some ⟨24, Tape.mk' (ListBlank.append (pair10 m).reverse L) R⟩ := by
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

theorem boot2_to_inc0 (L R : ListBlank (Fin 2)) :
    nSteps riemann121 3 ⟨24, Tape.mk' L (ListBlank.append [1, 1, 0] R)⟩ =
      some ⟨4, Tape.mk' (((L.cons 1).cons 1).cons 0) R⟩ := by
  have h1 : step riemann121 ⟨24, Tape.mk' L (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨26, Tape.mk' (L.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step riemann121 ⟨26, Tape.mk' (L.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨28, Tape.mk' ((L.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step riemann121 ⟨28, Tape.mk' ((L.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨4, Tape.mk' (((L.cons 1).cons 1).cons 0) R⟩ :=
    step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

theorem boot2_to_decnz0 (L R : ListBlank (Fin 2)) :
    nSteps riemann121 3 ⟨24, Tape.mk' L (ListBlank.append [1, 1, 1] R)⟩ =
      some ⟨31, Tape.mk' (((L.cons 1).cons 1).cons 1) R⟩ := by
  have h1 : step riemann121 ⟨24, Tape.mk' L (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨26, Tape.mk' (L.cons 1) ((R.cons 1).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step riemann121 ⟨26, Tape.mk' (L.cons 1) ((R.cons 1).cons 1)⟩ =
      some ⟨28, Tape.mk' ((L.cons 1).cons 1) (R.cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step riemann121 ⟨28, Tape.mk' ((L.cons 1).cons 1) (R.cons 1)⟩ =
      some ⟨31, Tape.mk' (((L.cons 1).cons 1).cons 1) R⟩ :=
    step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- `rhRunState 0` (`12`) scans left across `(pair10 m).reverse` in `2 * m` steps, landing back in
`12` (`4.run.0`) because every `0` in `pair10 m` is immediately preceded by `1`! -/
theorem rhRun_scan_pair10 (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * m) ⟨12, Tape.mkL (ListBlank.append (pair10 m).reverse L) R⟩ =
      some ⟨12, Tape.mkL L (ListBlank.append (pair10 m) R)⟩ := by
  induction m generalizing L R with
  | zero => rfl
  | succ m ih =>
    have hL : ListBlank.append (pair10 (m + 1)).reverse L =
        ((ListBlank.append (pair10 m).reverse L).cons 1).cons 0 := by
      rw [← pair10_snoc, List.reverse_append, ListBlank.append_assoc]
      rfl
    rw [hL]
    have h1 : step riemann121
        ⟨12, Tape.mkL (((ListBlank.append (pair10 m).reverse L).cons 1).cons 0) R⟩ =
        some ⟨14, Tape.mkL ((ListBlank.append (pair10 m).reverse L).cons 1) (R.cons 0)⟩ :=
      step_mkL_left (by rfl) _ _
    have h2 : step riemann121
        ⟨14, Tape.mkL ((ListBlank.append (pair10 m).reverse L).cons 1) (R.cons 0)⟩ =
        some ⟨12, Tape.mkL (ListBlank.append (pair10 m).reverse L) ((R.cons 0).cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have hrest := ih L ((R.cons 0).cons 1)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    have hR : ListBlank.append (pair10 m) ((R.cons 0).cons 1) =
        ListBlank.append (pair10 (m + 1)) R := by
      rw [← pair10_snoc, ListBlank.append_assoc]
      rfl
    rw [hlen, hR] at hcomb
    exact hcomb

/-- From `12` (`4.run.0`) with `pair10 m` (`1 ≤ m`) reversed on `default`, `riemann121` bounces off
`default` into `20 -> 22 -> 24` and scans right back to `State 24` (`0b.boot2.0`). -/
theorem rhRun_to_boot2 (m : ℕ) (hm : 1 ≤ m) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨12, Tape.mkL (ListBlank.append (pair10 m).reverse default) R⟩ =
      some ⟨24, Tape.mk' (ListBlank.append (pair10 m).reverse default) R⟩ := by
  have hscan := rhRun_scan_pair10 m default R
  have hbounce := rhRun_bounce_default 0 (by decide) (ListBlank.append (pair10 m) R)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hp : ListBlank.append (pair10 (m' + 1)) R =
      ((ListBlank.append (pair10 m') R).cons 0).cons 1 := rfl
  rw [hp] at hbounce
  have hs1 : step riemann121
      ⟨20, Tape.mk' default (((ListBlank.append (pair10 m') R).cons 0).cons 1)⟩ =
      some ⟨22, Tape.mk' (ListBlank.cons 1 default)
        ((ListBlank.append (pair10 m') R).cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs2 : step riemann121
      ⟨22, Tape.mk' (ListBlank.cons 1 default)
        ((ListBlank.append (pair10 m') R).cons 0)⟩ =
      some ⟨24, Tape.mk' ((ListBlank.cons 1 default).cons 0)
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

theorem continue0_boot_pos (m : ℕ) (hm : 1 ≤ m) (a : Fin 2) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s ⟨10, Tape.mkL (bootLeft m a) R⟩ =
      some ⟨if a = 0 then 4 else 31, Tape.mk' (bootLeft m a) R⟩ := by
  unfold bootLeft
  set L_m := ListBlank.append (pair10 m).reverse default
  rcases fin2_cases a with rfl | rfl
  · have h1 : step riemann121 ⟨10, Tape.mkL (((L_m.cons 1).cons 1).cons 0) R⟩ =
        some ⟨10, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 0)⟩ := step_mkL_left (by rfl) _ _
    have h2 : step riemann121 ⟨10, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 0)⟩ =
        some ⟨12, Tape.mkL (L_m.cons 1) ((R.cons 0).cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h3 : step riemann121 ⟨12, Tape.mkL (L_m.cons 1) ((R.cons 0).cons 1)⟩ =
        some ⟨12, Tape.mkL L_m (ListBlank.append [1, 1, 0] R)⟩ :=
      step_mkL_left (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := rhRun_to_boot2 m hm (ListBlank.append [1, 1, 0] R)
    have hinc := boot2_to_inc0 L_m R
    exact ⟨_, by omega, step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hb hinc)))⟩
  · have h1 : step riemann121 ⟨10, Tape.mkL (((L_m.cons 1).cons 1).cons 1) R⟩ =
        some ⟨12, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h2 : step riemann121 ⟨12, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 1)⟩ =
        some ⟨12, Tape.mkL (L_m.cons 1) ((R.cons 1).cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h3 : step riemann121 ⟨12, Tape.mkL (L_m.cons 1) ((R.cons 1).cons 1)⟩ =
        some ⟨12, Tape.mkL L_m (ListBlank.append [1, 1, 1] R)⟩ :=
      step_mkL_left (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := rhRun_to_boot2 m hm (ListBlank.append [1, 1, 1] R)
    have hdec := boot2_to_decnz0 L_m R
    exact ⟨_, by omega, step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hb hdec)))⟩

theorem boot_pass1_eval (m : ℕ) (hm : 1 ≤ m) (a : Fin 2) (r : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨if a = 0 then 4 else 31, Tape.mk' (bootLeft m a)
        (ListBlank.append (List.replicate (r + 3) 0) (ListBlank.append [1, 0] R))⟩ =
      some ⟨if a = 0 then 4 else 31, Tape.mk' (bootLeft m a)
        ((ListBlank.append (encodeReg (r + 1)) R).cons 0 |>.cons 1)⟩ := by
  set q : Fin 121 := if a = 0 then 4 else 31
  have hq : rh121Trans q 0 = some (1, .right, 6) := by
    rcases fin2_cases a with rfl | rfl <;> rfl
  set L := bootLeft m a
  have hrep : List.replicate (r + 3) (0 : Fin 2) = 0 :: 0 :: List.replicate (r + 1) 0 := rfl
  rw [hrep, ListBlank.append, ListBlank.append]
  have h1 : step riemann121
      ⟨q, Tape.mk' L (((ListBlank.append (List.replicate (r + 1) 0)
        (ListBlank.append [1, 0] R)).cons 0).cons 0)⟩ =
      some ⟨6, Tape.mk' (L.cons 1)
        ((ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R)).cons 0)⟩ :=
    step_mk'_right hq _ _
  have h2 : step riemann121
      ⟨6, Tape.mk' (L.cons 1)
        ((ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R)).cons 0)⟩ =
      some ⟨8, Tape.mk' ((L.cons 1).cons 0)
        (ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan_r := nSteps_mk'_right_scan (q := 8) (a := 0) (b := 1) (by rfl) (r + 1)
    ((L.cons 1).cons 0) (ListBlank.append [1, 0] R)
  have h3 : step riemann121
      ⟨8, Tape.mk' (ListBlank.append (List.replicate (r + 1) 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨10, Tape.mkL (ListBlank.append (List.replicate (r + 1) 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ :=
    step_mk'_left (by rfl) _ (R.cons 0)
  rw [List.replicate_succ, ListBlank.append] at h3
  have h4 : step riemann121
      ⟨10, Tape.mkL ((ListBlank.append (List.replicate r 1) ((L.cons 1).cons 0)).cons 1)
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨12, Tape.mkL (ListBlank.append (List.replicate r 1) ((L.cons 1).cons 0))
        ((ListBlank.append [1, 0] R).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan_back := nSteps_mkL_left_scan (q := 12) (a := 1) (b := 1) (by rfl) r
    ((L.cons 1).cons 0) ((ListBlank.append [1, 0] R).cons 1)
  have henc : ListBlank.append (List.replicate r 1) ((ListBlank.append [1, 0] R).cons 1) =
      ListBlank.append (encodeReg (r + 1)) R := by
    have h10 : ListBlank.append [1, 0] R = (R.cons 0).cons 1 := rfl
    rw [h10, append_replicate_cons, append_replicate_cons, ← append_encodeReg]
  rw [henc] at hscan_back
  set R_enc := ListBlank.append (encodeReg (r + 1)) R
  have h5 : step riemann121 ⟨12, Tape.mkL ((L.cons 1).cons 0) R_enc⟩ =
      some ⟨14, Tape.mkL (L.cons 1) (R_enc.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h6 : step riemann121 ⟨14, Tape.mkL (L.cons 1) (R_enc.cons 0)⟩ =
      some ⟨12, Tape.mkL L ((R_enc.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  set R_prep := (R_enc.cons 0).cons 1
  set L_m := ListBlank.append (pair10 m).reverse default
  rcases fin2_cases a with rfl | rfl
  · have h7 : step riemann121 ⟨12, Tape.mkL (((L_m.cons 1).cons 1).cons 0) R_prep⟩ =
        some ⟨14, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 0)⟩ := step_mkL_left (by rfl) _ _
    have h8 : step riemann121 ⟨14, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 0)⟩ =
        some ⟨12, Tape.mkL (L_m.cons 1) ((R_prep.cons 0).cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h9 : step riemann121 ⟨12, Tape.mkL (L_m.cons 1) ((R_prep.cons 0).cons 1)⟩ =
        some ⟨12, Tape.mkL L_m (ListBlank.append [1, 1, 0] R_prep)⟩ :=
      step_mkL_left (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := rhRun_to_boot2 m hm (ListBlank.append [1, 1, 0] R_prep)
    have hinc := boot2_to_inc0 L_m R_prep
    have htotal := step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan_r
      (step_nSteps h3 (step_nSteps h4 (nSteps_bind_eq hscan_back
        (step_nSteps h5 (step_nSteps h6 (step_nSteps h7 (step_nSteps h8
          (step_nSteps h9 (nSteps_bind_eq hb hinc)))))))))))
    exact ⟨_, by omega, htotal⟩
  · have h7 : step riemann121 ⟨12, Tape.mkL (((L_m.cons 1).cons 1).cons 1) R_prep⟩ =
        some ⟨12, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h8 : step riemann121 ⟨12, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 1)⟩ =
        some ⟨12, Tape.mkL (L_m.cons 1) ((R_prep.cons 1).cons 1)⟩ := step_mkL_left (by rfl) _ _
    have h9 : step riemann121 ⟨12, Tape.mkL (L_m.cons 1) ((R_prep.cons 1).cons 1)⟩ =
        some ⟨12, Tape.mkL L_m (ListBlank.append [1, 1, 1] R_prep)⟩ :=
      step_mkL_left (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := rhRun_to_boot2 m hm (ListBlank.append [1, 1, 1] R_prep)
    have hdec := boot2_to_decnz0 L_m R_prep
    have htotal := step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan_r
      (step_nSteps h3 (step_nSteps h4 (nSteps_bind_eq hscan_back
        (step_nSteps h5 (step_nSteps h6 (step_nSteps h7 (step_nSteps h8
          (step_nSteps h9 (nSteps_bind_eq hb hdec)))))))))))
    exact ⟨_, by omega, htotal⟩

def rhBoot2CycleCfg (m i : ℕ) : Cfg 121 2 :=
  ⟨4, Tape.mk' (bootLeft m 0)
    (ListBlank.append (List.replicate (2 * i + 3) 0)
      (ListBlank.append [1, 0] (regsTape (List.replicate i 0))))⟩

theorem boot2_init_step (m : ℕ) (hm : 1 ≤ m) :
    ∃ s, nSteps riemann121 s
      ⟨4, Tape.mk' (ListBlank.append (pair10 (m + 1) ++ [1]).reverse default)
        (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ =
      some (rhBoot2CycleCfg m 1) := by
  set L_m := ListBlank.append (pair10 m).reverse default
  have hL : ListBlank.append (pair10 (m + 1) ++ [1]).reverse default =
      (((L_m.cons 1).cons 0).cons 1) := by
    rw [← pair10_snoc m, List.append_assoc, List.reverse_append, ListBlank.append_assoc]
    rfl
  rw [hL]
  set L₀ := ((L_m.cons 1).cons 0).cons 1
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have hs1 : step riemann121 ⟨4, Tape.mk' L₀ (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ =
      some ⟨7, Tape.mk' (L₀.cons 0) (ListBlank.append [0, 1, 1, 1, 1] default)⟩ :=
    step_mk'_right (by rfl) _ _
  have hs2 : step riemann121
      ⟨7, Tape.mk' (L₀.cons 0) (ListBlank.append [0, 1, 1, 1, 1] default)⟩ =
      some ⟨9, Tape.mk' ((L₀.cons 0).cons 0) (ListBlank.append (List.replicate 4 1) default)⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 9) (a := 1) (b := 1) (by rfl) 4
    ((L₀.cons 0).cons 0) default
  set L_ones := ListBlank.append (List.replicate 4 1) ((L₀.cons 0).cons 0)
  have hs3 : step riemann121 ⟨9, Tape.mk' L_ones default⟩ =
      some ⟨11, Tape.mk' (ListBlank.append (encodeReg 3).reverse ((L₀.cons 0).cons 0))
        default⟩ := by
    rw [append_encodeReg_reverse]
    have h := step_mk'_right (q := 9) (q' := 11) (a := 0) (b := 0) (by rfl) L_ones default
    rwa [← hdef] at h
  set L_p := ListBlank.append (encodeReg 3).reverse ((L₀.cons 0).cons 0)
  have hs4 : step riemann121 ⟨11, Tape.mk' L_p default⟩ =
      some ⟨13, Tape.mk' (L_p.cons 1) default⟩ := by
    have h := step_mk'_right (q := 11) (q' := 13) (a := 0) (b := 1) (by rfl) L_p default
    rwa [← hdef] at h
  have hs5 : step riemann121 ⟨13, Tape.mk' (L_p.cons 1) default⟩ =
      some ⟨15, Tape.mkL (L_p.cons 1) default⟩ := by
    have h := step_mk'_left (q := 13) (q' := 15) (a := 0) (b := 0) (by rfl) (L_p.cons 1) default
    rwa [← hdef] at h
  have hs6 : step riemann121 ⟨15, Tape.mkL (L_p.cons 1) default⟩ =
      some ⟨15, Tape.mkL L_p (regsTape [0])⟩ := by
    have h := step_mkL_left (q := 15) (q' := 15) (a := 1) (b := 1) (by rfl) L_p default
    have h0 : (default : ListBlank (Fin 2)).cons 1 = regsTape [0] := by
      rw [regsTape_cons, regsTape_nil, append_encodeReg, default_cons_zero]
      rfl
    rwa [h0] at h
  have hret := return0_scan_fence [3] L₀ (regsTape [0])
  simp only [encodeRegs_cons, encodeRegs_nil, List.append_nil] at hret
  have hb0 := break0_step 1 (L_m.cons 1)
    ((ListBlank.append (encodeReg 3) (regsTape [0])).cons 0 |>.cons 0)
  simp only [List.replicate, ListBlank.append] at hb0
  have hs7 : step riemann121
      ⟨21, Tape.mk' ((L_m.cons 1).cons 1)
        ((((ListBlank.append (encodeReg 3) (regsTape [0])).cons 0).cons 0).cons 0)⟩ =
      some ⟨21, Tape.mk' (bootLeft m 0)
        (ListBlank.append (List.replicate 2 0)
          (ListBlank.append (encodeReg 3) (regsTape [0])))⟩ :=
    step_mk'_right (by rfl) _ _
  obtain ⟨s_cl, _, hcl⟩ := cleanup_to_10 (bootLeft m 0) 2 3 (regsTape [0])
  obtain ⟨s_cont, _, hcont⟩ := continue0_boot_pos m hm 0
    (ListBlank.append (List.replicate 5 0) (ListBlank.append [1, 0] (regsTape [0])))
  have htotal := step_nSteps hs1 (step_nSteps hs2 (nSteps_bind_eq hscan
    (step_nSteps hs3 (step_nSteps hs4 (step_nSteps hs5 (step_nSteps hs6
      (nSteps_bind_eq hret (nSteps_bind_eq hb0 (step_nSteps hs7 (nSteps_bind_eq hcl hcont))))))))))
  exact ⟨_, htotal⟩

theorem boot2_cycle_to_10 (m' i : ℕ) (hi : 1 ≤ i) :
    ∃ s, nSteps riemann121 s (rhBoot2CycleCfg (m' + 1) i) =
      some ⟨10, Tape.mkL (bootLeft m' 0)
        (ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
          (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0))))⟩ := by
  have hm : 1 ≤ m' + 1 := by omega
  have hi_split : List.replicate i 0 = 0 :: List.replicate (i - 1) 0 := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega, List.replicate_succ]
  obtain ⟨sA, _, hA⟩ := boot_pass1_eval (m' + 1) hm 0 (2 * i) (regsTape (List.replicate i 0))
  simp only [↓reduceIte, ← regsTape_cons] at hA
  rw [hi_split] at hA
  obtain ⟨sB1, _, hB1⟩ := stage3_inc_pass2 0 (by decide) (2 * i + 1)
    (0 :: List.replicate (i - 1) 0) (by simp) (bootLeft (m' + 1) 0)
  simp only [List.set_cons_zero, List.getElem_cons_zero, Nat.zero_add] at hB1
  have hB2 : step riemann121
      ⟨19, Tape.mkL (bootLeft (m' + 1) 0)
        ((regsTape ((2 * i + 1) :: 1 :: List.replicate (i - 1) 0)).cons 0 |>.cons 0)⟩ =
      some ⟨21, Tape.mk' (bootLeft (m' + 1) 1)
        (ListBlank.append (List.replicate 2 0)
          (ListBlank.append (encodeReg (2 * i + 1))
            (regsTape (1 :: List.replicate (i - 1) 0))))⟩ := by
    rw [regsTape_cons]
    exact step_mkL_right (by rfl) _ _
  obtain ⟨sB3, _, hB3⟩ := cleanup_to_10 (bootLeft (m' + 1) 1) 2 (2 * i + 1)
    (regsTape (1 :: List.replicate (i - 1) 0))
  obtain ⟨sB4, _, hB4⟩ := continue0_boot_pos (m' + 1) hm 1
    (ListBlank.append (List.replicate (2 + (2 * i + 1)) 0)
      (ListBlank.append [1, 0] (regsTape (1 :: List.replicate (i - 1) 0))))
  have haddB : 2 + (2 * i + 1) = 2 * i + 3 := by omega
  rw [haddB] at hB3 hB4
  obtain ⟨sC, _, hC⟩ := boot_pass1_eval (m' + 1) hm 1 (2 * i)
    (regsTape (1 :: List.replicate (i - 1) 0))
  have h10 : (1 : Fin 2) = 0 ↔ False := by decide
  simp only [h10, ↓reduceIte, ← regsTape_cons] at hB4 hC
  obtain ⟨sD1, _, hD1⟩ := stage3_decnz_pass2_pos 0 (by decide) (2 * i + 1)
    (1 :: List.replicate (i - 1) 0) (by simp) (by simp) (bootLeft (m' + 1) 1)
  simp only [List.getElem_cons_zero, Nat.sub_self, List.set_cons_zero] at hD1
  have hrep_snoc : 0 :: List.replicate (i - 1) 0 ++ [0] =
      List.replicate (i + 1) 0 := by
    rw [← hi_split, ← List.replicate_succ']
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
  have hD3 : step riemann121
      ⟨21, Tape.mk' ((L_m'.cons 1).cons 1)
        (ListBlank.append (List.replicate 3 0)
          ((regsTape ((2 * i + 1) :: List.replicate (i + 1) 0)).cons 0 |>.cons 0))⟩ =
      some ⟨21, Tape.mk' (bootLeft m' 0)
        (ListBlank.append (List.replicate 4 0)
          (ListBlank.append (encodeReg (2 * i + 1)) (regsTape (List.replicate (i + 1) 0))))⟩ := by
    rw [regsTape_cons]
    exact step_mk'_right (by rfl) _ _
  obtain ⟨sD4, _, hD4⟩ := cleanup_to_10 (bootLeft m' 0) 4 (2 * i + 1)
    (regsTape (List.replicate (i + 1) 0))
  have haddD : 4 + (2 * i + 1) = 2 * (i + 1) + 3 := by omega
  rw [haddD] at hD4
  unfold rhBoot2CycleCfg
  rw [hi_split]
  exact ⟨_, nSteps_bind_eq hA (nSteps_bind_eq hB1 (step_nSteps hB2
    (nSteps_bind_eq hB3 (nSteps_bind_eq hB4 (nSteps_bind_eq hC
      (nSteps_bind_eq hD1 (nSteps_bind_eq hD2 (step_nSteps hD3 hD4))))))))⟩

theorem boot2_loop (m i : ℕ) (hm : 1 ≤ m) (hi : 1 ≤ i) :
    ∃ s, nSteps riemann121 s (rhBoot2CycleCfg m i) =
      some (rhRootCfg (2 * (i + m) + 3) [] (List.replicate (i + m) 0)) := by
  induction m generalizing i with
  | zero => omega
  | succ m' ih =>
    obtain ⟨s₁, h10⟩ := boot2_cycle_to_10 m' i hi
    by_cases hm' : m' = 0
    · subst hm'
      rw [bootLeft_zero] at h10
      set R_end := ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
        (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0)))
      obtain ⟨s₂, _, hret⟩ := continue0_return [] (by decide) R_end
      simp only [ListBlank.append] at hret
      have hroot_eq : ⟨27, Tape.mk' rootLeft R_end⟩ =
          rhRootCfg (2 * (i + 1) + 3) [] (List.replicate (i + 1) 0) := by
        rw [rhRootCfg_default_eq, regsTape_cons]
        rfl
      rw [hroot_eq] at hret
      exact ⟨_, nSteps_bind_eq h10 hret⟩
    · have hm'1 : 1 ≤ m' := by omega
      obtain ⟨s₂, _, hcont⟩ := continue0_boot_pos m' hm'1 0
        (ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
          (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0))))
      obtain ⟨s₃, hrest⟩ := ih (i + 1) hm'1 (by omega)
      have hadd : i + 1 + m' = i + (m' + 1) := by omega
      rw [hadd] at hrest
      exact ⟨_, nSteps_bind_eq h10 (nSteps_bind_eq hcont hrest)⟩

/-- Complete bootstrap theorem: starting from `init = ⟨0, default⟩`, `riemann121` reaches
`main.0` (`State 27`) at `rhRootCfg 3821 [] (List.replicate 1909 0)` (i.e. `3821` pad zeros
followed by `[1, 0]`, `[0, 0, 0, 0, 0]`, and `regsTape (List.replicate 1904 0)`). -/
theorem boot_to_root :
    ∃ s, nSteps riemann121 s init =
      some (rhRootCfg 3821 [] (List.replicate 1909 0) default) := by
  obtain ⟨s₁, hb1⟩ := boot1_eval
  obtain ⟨s₂, hb2_init⟩ := boot2_init_step 1908 (by decide)
  obtain ⟨s₃, hb2_loop⟩ := boot2_loop 1908 1 (by decide) (by decide)
  exact ⟨s₁ + (s₂ + s₃), nSteps_bind_eq hb1 (nSteps_bind_eq hb2_init hb2_loop)⟩

/-- Equivalent 5-register form of `boot_to_root`: reaches `main.0` (`State 27`)
with `[0, 0, 0, 0, 0]` and trailing register tape `regsTape (List.replicate 1904 0)`. -/
theorem boot_reaches_main0 :
    ∃ s, nSteps riemann121 s init =
      some (rhRootCfg 3821 [] [0, 0, 0, 0, 0] (regsTape (List.replicate 1904 0))) := by
  obtain ⟨s, hs⟩ := boot_to_root
  have heq : rhRootCfg 3821 [] (List.replicate 1909 0) default =
      rhRootCfg 3821 [] [0, 0, 0, 0, 0] (regsTape (List.replicate 1904 0)) := by
    have hr : List.replicate 1909 0 = [0, 0, 0, 0, 0] ++ List.replicate 1904 0 := rfl
    unfold rhRootCfg
    rw [hr, encodeRegs_append]
    simp only [List.append_assoc, ListBlank.append_assoc]
    rfl
  rw [heq] at hs
  exact ⟨s, hs⟩

end ConjectureMachines.Riemann120.Backend
