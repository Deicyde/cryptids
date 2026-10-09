/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann543

/-!
# Layer 1: Tape Layout and Primitive Register Gadgets for `riemann_744`

This file formalizes the canonical tape layout, unary register encodings, return-scan gadgets,
11-bit PC carry chain, and primitive register operations (`reg_init`, `reg_incr`, `reg_decr`)
for the 744-state Riemann Hypothesis Turing machine `reference` (`riemann_744`).
-/

@[expose] public section

namespace ConjectureMachines.Riemann543.Layer1

open Turing StateTransition ConjectureMachines.Riemann543

abbrev reference : Machine 744 2 := Machines.riemann744

/-!
## 1. `nSteps` and Symbolic Tape Primitives (`Tape.mkL`, `Tape.mk'`)
-/

/-- Bounded `n`-step execution of a Turing machine from configuration `c`. -/
def nSteps {K : ℕ} [NeZero K] (M : Machine K 2) : ℕ → Cfg K 2 → Option (Cfg K 2)
  | 0, c => some c
  | n + 1, c => (step M c).bind (nSteps M n)

@[simp]
theorem nSteps_zero {K : ℕ} [NeZero K] (M : Machine K 2) (c : Cfg K 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ {K : ℕ} [NeZero K] (M : Machine K 2) (n : ℕ) (c : Cfg K 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

theorem nSteps_add {K : ℕ} [NeZero K] {M : Machine K 2} (m n : ℕ) (c : Cfg K 2) :
    nSteps M (m + n) c = (nSteps M m c).bind (nSteps M n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, nSteps_succ, nSteps_succ]
    cases step M c with
    | none => rfl
    | some c' => exact ih c'

theorem nSteps_bind_eq {K : ℕ} [NeZero K] {M : Machine K 2} {m n : ℕ} {c c₁ c₂ : Cfg K 2}
    (h₁ : nSteps M m c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (m + n) c = some c₂ := by
  rw [nSteps_add, h₁, Option.bind_some, h₂]

theorem step_nSteps {K : ℕ} [NeZero K] {M : Machine K 2} {n : ℕ} {c c₁ c₂ : Cfg K 2}
    (h₁ : step M c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (n + 1) c = some c₂ := by
  rw [nSteps_succ, h₁, Option.bind_some, h₂]

theorem step_one {K : ℕ} [NeZero K] {M : Machine K 2} {c c₁ : Cfg K 2}
    (h : step M c = some c₁) :
    nSteps M 1 c = some c₁ := by
  rw [nSteps_succ, h]; rfl

theorem nSteps_reaches {K : ℕ} [NeZero K] {M : Machine K 2} {n : ℕ} {c c' : Cfg K 2}
    (h : nSteps M n c = some c') : Reaches (step M) c c' := by
  induction n generalizing c with
  | zero =>
    injection h with h'
    subst h'
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [nSteps_succ, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, hstep, hrest⟩ := h
    exact Relation.ReflTransGen.head hstep (ih hrest)

theorem nSteps_eval_dom {K : ℕ} [NeZero K] {M : Machine K 2} {n : ℕ} {c c' : Cfg K 2}
    (h : nSteps M n c = some c') :
    (eval (step M) c).Dom ↔ (eval (step M) c').Dom := by
  rw [StateTransition.reaches_eval (nSteps_reaches h)]

theorem mk_append_replicate_zero (l : List (Fin 2)) (n : ℕ) :
    ListBlank.mk (l ++ List.replicate n 0) = ListBlank.mk l :=
  Quotient.sound' (Or.inr ⟨n, rfl⟩)

theorem default_eq_mk_nil : (default : ListBlank (Fin 2)) = ListBlank.mk [] := rfl

@[simp]
theorem default_cons_zero : ListBlank.cons 0 (default : ListBlank (Fin 2)) = default := by
  change ListBlank.mk [0] = ListBlank.mk []
  exact mk_append_replicate_zero [] 1

theorem append_replicate_zero_default (n : ℕ) :
    ListBlank.append (List.replicate n 0) (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, ListBlank.append, ih, default_cons_zero]

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- Tape constructor with the head taken from the left half-tape `L`. -/
def Tape.mkL (L R : ListBlank (Fin 2)) : Tape (Fin 2) :=
  ⟨L.head, L.tail, R⟩

@[simp]
theorem Tape.mkL_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mkL (L.cons a) R = ⟨a, L, R⟩ := by
  simp [Tape.mkL]

@[simp]
theorem Tape.mk'_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mk' L (R.cons a) = ⟨a, L, R⟩ := by
  simp [Tape.mk']

theorem Tape.mkL_default (R : ListBlank (Fin 2)) :
    Tape.mkL default R = Tape.mk' default (R.cons 0) := by
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  conv_lhs => rw [hdef]
  rw [Tape.mkL_cons, Tape.mk'_cons]

theorem step_mkL_left {q q' : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {q q' : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, refTrans_eq, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {q q' : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mkL_left_any {q q' : Fin 744}
    (h0 : refTrans q 0 = some (0, .left, q'))
    (h1 : refTrans q 1 = some (1, .left, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons a)⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mkL_left h0 L R
  · exact step_mkL_left h1 L R

theorem step_mk'_right_any {q q' : Fin 744}
    (h0 : refTrans q 0 = some (0, .right, q'))
    (h1 : refTrans q 1 = some (1, .right, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons a) R⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mk'_right h0 L R
  · exact step_mk'_right h1 L R

theorem step_mkL_left_const {q q' : Fin 744} {b : Fin 2}
    (h0 : refTrans q 0 = some (b, .left, q'))
    (h1 : refTrans q 1 = some (b, .left, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mkL_left h0 L R
  · exact step_mkL_left h1 L R

theorem append_replicate_cons (k : ℕ) (b : Fin 2) (L : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate k b) (L.cons b) =
      ListBlank.append (List.replicate (k + 1) b) L := by
  rw [List.replicate_succ', ListBlank.append_assoc, ListBlank.append, ListBlank.append]

theorem append_cons_snoc (l : List (Fin 2)) (a : Fin 2) (L : ListBlank (Fin 2)) :
    ListBlank.append l (L.cons a) = ListBlank.append (l ++ [a]) L := by
  rw [ListBlank.append_assoc, ListBlank.append, ListBlank.append]

theorem append_reverse_cons (a : Fin 2) (l : List (Fin 2)) (L : ListBlank (Fin 2)) :
    ListBlank.append l.reverse (L.cons a) = ListBlank.append (a :: l).reverse L := by
  rw [List.reverse_cons, append_cons_snoc]

theorem move_right_append (l : List (Fin 2)) (L R : ListBlank (Fin 2))
    {q : Fin 744}
    (h0 : refTrans q 0 = some (0, .right, q))
    (h1 : refTrans q 1 = some (1, .right, q)) :
    nSteps reference l.length ⟨q, Tape.mk' L (ListBlank.append l R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append l.reverse L) R⟩ := by
  induction l generalizing L with
  | nil => rfl
  | cons a l ih =>
    have hstep : step reference ⟨q, Tape.mk' L ((ListBlank.append l R).cons a)⟩ =
        some ⟨q, Tape.mk' (L.cons a) (ListBlank.append l R)⟩ :=
      step_mk'_right_any h0 h1 a L (ListBlank.append l R)
    rw [List.length_cons, ListBlank.append, step_nSteps hstep (ih (L.cons a)), append_reverse_cons]

theorem move_left_append (l : List (Fin 2)) (L R : ListBlank (Fin 2))
    {q : Fin 744}
    (h0 : refTrans q 0 = some (0, .left, q))
    (h1 : refTrans q 1 = some (1, .left, q)) :
    nSteps reference l.length ⟨q, Tape.mkL (ListBlank.append l.reverse L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append l R)⟩ := by
  induction l using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
      ListBlank.append, List.length_append, List.length_singleton]
    have hstep : step reference ⟨q, Tape.mkL ((ListBlank.append l.reverse L).cons a) R⟩ =
        some ⟨q, Tape.mkL (ListBlank.append l.reverse L) (R.cons a)⟩ :=
      step_mkL_left_any h0 h1 a (ListBlank.append l.reverse L) R
    rw [step_nSteps hstep (ih (R.cons a)), append_cons_snoc]

theorem nSteps_mkL_left_scan {q : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {q : Fin 744} {a b : Fin 2}
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
## 2. Unary Register Encodings & `entryCfg`
-/

/-- Unary encoding of a single register value `r : ℕ`: `1^{r+1} ++ [0]`. -/
def encodeReg (r : ℕ) : List (Fin 2) :=
  List.replicate (r + 1) 1 ++ [0]

@[simp]
theorem encodeReg_length (r : ℕ) : (encodeReg r).length = r + 2 := by
  simp [encodeReg]

theorem encodeReg_reverse (r : ℕ) :
    (encodeReg r).reverse = 0 :: List.replicate (r + 1) 1 := by
  simp [encodeReg]

theorem append_encodeReg_reverse (r : ℕ) (L : ListBlank (Fin 2)) :
    ListBlank.append (encodeReg r).reverse L =
      (ListBlank.append (List.replicate (r + 1) 1) L).cons 0 := by
  rw [encodeReg_reverse, ListBlank.append]

theorem append_encodeReg (r : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (encodeReg r) R =
      ListBlank.append (List.replicate (r + 1) 1) (R.cons 0) := by
  rw [encodeReg, ← append_cons_snoc]

/-- Unary encoding of a bank of registers `regs : List ℕ`. -/
def encodeRegs : List ℕ → List (Fin 2)
  | [] => []
  | r :: rs => encodeReg r ++ encodeRegs rs

@[simp]
theorem encodeRegs_nil : encodeRegs [] = [] := rfl

@[simp]
theorem encodeRegs_cons (r : ℕ) (rs : List ℕ) :
    encodeRegs (r :: rs) = encodeReg r ++ encodeRegs rs := rfl

theorem encodeRegs_append (rs₁ rs₂ : List ℕ) :
    encodeRegs (rs₁ ++ rs₂) = encodeRegs rs₁ ++ encodeRegs rs₂ := by
  induction rs₁ with
  | nil => rfl
  | cons r rs₁ ih => simp [ih, List.append_assoc]

/-- The right half-tape encoding `regs` followed by blank zeros. -/
def regsTape (regs : List ℕ) : ListBlank (Fin 2) :=
  ListBlank.append (encodeRegs regs) default

@[simp]
theorem regsTape_nil : regsTape [] = default := rfl

theorem regsTape_cons (r : ℕ) (rs : List ℕ) :
    regsTape (r :: rs) = ListBlank.append (encodeReg r) (regsTape rs) := by
  simp [regsTape, ListBlank.append_assoc]

theorem regsTape_append (rs₁ rs₂ : List ℕ) :
    regsTape (rs₁ ++ rs₂) = ListBlank.append (encodeRegs rs₁) (regsTape rs₂) := by
  simp [regsTape, encodeRegs_append, ListBlank.append_assoc]

/-- Big-endian `k`-bit binary representation of `pc`. -/
def pcBits : ℕ → ℕ → List (Fin 2)
  | 0, _ => []
  | k + 1, pc => (if pc.testBit k then 1 else 0) :: pcBits k pc

@[simp]
theorem pcBits_zero (pc : ℕ) : pcBits 0 pc = [] := rfl

@[simp]
theorem pcBits_succ (k pc : ℕ) :
    pcBits (k + 1) pc = (if pc.testBit k then 1 else 0) :: pcBits k pc := rfl

@[simp]
theorem pcBits_length (k pc : ℕ) : (pcBits k pc).length = k := by
  induction k <;> simp [*]

/-- Canonical entry configuration at `!ENTRY` (State `0`), where the tape head sits on the `0`
immediately to the left of the 11-bit big-endian PC, followed by the `[0, 0]` fence and `regs`. -/
def entryCfg (pc : ℕ) (regs : List ℕ) : Cfg 744 2 :=
  ⟨0, Tape.mkL default (ListBlank.append (pcBits 11 pc ++ [0, 0]) (regsTape regs))⟩

/-- Configuration at `main()[]` (State `523`), 1 step after `entryCfg`, where the tape head sits
on the MSB (`bit 10`) of the 11-bit PC. -/
def mainCfg (pc : ℕ) (regs : List ℕ) : Cfg 744 2 :=
  ⟨523, Tape.mk' default (ListBlank.append (pcBits 11 pc ++ [0, 0]) (regsTape regs))⟩

/-- Configuration immediately after the 11-bit PC decision tree, with the tape head on the
first `0` of the `[0, 0]` fence. -/
def postPcCfg (q : Fin 744) (pc : ℕ) (regs : List ℕ) : Cfg 744 2 :=
  ⟨q, Tape.mk' (ListBlank.append (pcBits 11 pc).reverse default) ((regsTape regs).cons 0 |>.cons 0)⟩

theorem step_entryCfg (pc : ℕ) (regs : List ℕ) :
    step reference (entryCfg pc regs) = some (mainCfg pc regs) := by
  unfold entryCfg mainCfg
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  conv_lhs => rw [hdef]
  rw [step_mkL_right (by rfl), default_cons_zero]

theorem entryCfg_zero_nil : entryCfg 0 [] = init := by
  unfold entryCfg init
  have h13 : pcBits 11 0 ++ [0, 0] = List.replicate 13 0 := by decide
  rw [h13, regsTape_nil, append_replicate_zero_default, Tape.mkL_default, default_cons_zero]
  rfl

/-!
## 3. Return Scan Gadgets (`return.0/1` = States `565`/`566`, `return2.0/1` = States `567`/`568`)
-/

/-- State `566` (`return.1`) scans left across a single unary register `encodeReg r` in `r + 2`
steps, landing back in State `566`. -/
theorem return1_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (r + 2)
      ⟨566, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨566, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨566, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨565, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨565, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨566, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 566) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

/-- State `566` (`return.1`) scans left across any bank of registers `regs` in
`(encodeRegs regs).length` steps. -/
theorem return1_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (encodeRegs regs).length
      ⟨566, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨566, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return1_scan_reg, ListBlank.append_assoc]

/-- State `566` (`return.1`) scans left across `regs` and the `[0, 0]` fence to reach
State `9` (`dispatch.0.carry`). -/
theorem return1_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs regs).length + 2)
      ⟨566, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨9, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return1_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step reference
      ⟨566, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨565, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨565, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨9, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-- State `568` (`return2.1`) scans left across a single unary register `encodeReg r` in `r + 2`
steps, landing back in State `568`. -/
theorem return2_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (r + 2)
      ⟨568, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨568, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨568, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨567, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨567, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨568, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 568) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

/-- State `568` (`return2.1`) scans left across any bank of registers `regs` in
`(encodeRegs regs).length` steps. -/
theorem return2_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (encodeRegs regs).length
      ⟨568, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨568, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return2_scan_reg, ListBlank.append_assoc]

/-- State `568` (`return2.1`) scans left across `regs` and the `[0, 0]` fence to reach
State `524` (`nextstate_2`). -/
theorem return2_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs regs).length + 2)
      ⟨568, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨524, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return2_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step reference
      ⟨568, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨567, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨567, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨524, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-!
## 4. PC Carry/Return Chain (`States 9..29, 12, 13 → 0`)
-/

/-- The `dispatch.k` / `dispatch.k.carry` states for `0 ≤ order ≤ 10`, plus `0` (`!ENTRY`)
at `order = 11`. -/
def dispatchState (order : ℕ) (carry : Bool) : Fin 744 :=
  match order, carry with
  | 0, _ => 9
  | 1, false => 10
  | 1, true => 11
  | 2, false => 14
  | 2, true => 15
  | 3, false => 16
  | 3, true => 17
  | 4, false => 18
  | 4, true => 19
  | 5, false => 20
  | 5, true => 21
  | 6, false => 22
  | 6, true => 23
  | 7, false => 24
  | 7, true => 25
  | 8, false => 26
  | 8, true => 27
  | 9, false => 28
  | 9, true => 29
  | 10, false => 12
  | 10, true => 13
  | _, _ => 0

theorem testBit_zero_eq (m : ℕ) :
    (if m.testBit 0 then (1 : Fin 2) else 0) = if m % 2 = 1 then 1 else 0 := by
  rw [Nat.testBit_zero]
  by_cases h : m % 2 = 1 <;> simp [h]

theorem testBit_succ_div (m k : ℕ) : m.testBit (k + 1) = (m / 2).testBit k := by
  rw [Nat.testBit_succ]

theorem pcBits_succ_snoc (k m : ℕ) :
    pcBits (k + 1) m = pcBits k (m / 2) ++ [if m.testBit 0 then 1 else 0] := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    rw [pcBits_succ, ih m, ← List.cons_append, testBit_succ_div]
    rfl

theorem pcBits_succ_reverse (k m : ℕ) :
    (pcBits (k + 1) m).reverse =
      (if m.testBit 0 then 1 else 0) :: (pcBits k (m / 2)).reverse := by
  rw [pcBits_succ_snoc, List.reverse_append, List.reverse_singleton, List.singleton_append]

theorem append_pcBits_succ_reverse (k m : ℕ) (L : ListBlank (Fin 2)) :
    ListBlank.append (pcBits (k + 1) m).reverse L =
      (ListBlank.append (pcBits k (m / 2)).reverse L).cons (if m.testBit 0 then 1 else 0) := by
  rw [pcBits_succ_reverse, ListBlank.append]

theorem append_pcBits_succ_snoc (k m : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (pcBits k (m / 2)) (R.cons (if m.testBit 0 then 1 else 0)) =
      ListBlank.append (pcBits (k + 1) m) R := by
  rw [append_cons_snoc, ← pcBits_succ_snoc]

theorem testBit_div_pow (m b a : ℕ) : (m / 2 ^ b).testBit a = m.testBit (a + b) := by
  induction b generalizing m a with
  | zero => simp
  | succ b ih =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← testBit_succ_div, ih m (a + 1),
      Nat.add_right_comm, Nat.add_assoc]

theorem pcBits_add (a b pc : ℕ) :
    pcBits (a + b) pc = pcBits a (pc / 2 ^ b) ++ pcBits b pc := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, pcBits_succ, pcBits_succ, ih, List.cons_append, testBit_div_pow]


theorem dispatchState_trans_false_0 (d : ℕ) (hd : d ≤ 10) :
    d = 0 ∨ refTrans (dispatchState d false) 0 = some (0, .left, dispatchState (d + 1) false) := by
  revert d hd; decide

theorem dispatchState_trans_false_1 (d : ℕ) (hd : d ≤ 10) :
    d = 0 ∨ refTrans (dispatchState d false) 1 = some (1, .left, dispatchState (d + 1) false) := by
  revert d hd; decide

theorem dispatchState_trans_true_0 (d : ℕ) (hd : d ≤ 10) :
    d = 0 ∨ refTrans (dispatchState d true) 0 = some (1, .left, dispatchState (d + 1) false) := by
  revert d hd; decide

theorem dispatchState_trans_true_1 (d : ℕ) (hd : d ≤ 10) :
    d = 0 ∨ refTrans (dispatchState d true) 1 = some (0, .left, dispatchState (d + 1) true) := by
  revert d hd; decide

/-- One step in the PC carry chain at bit `0` of `m`: consumes the LSB of `m` from `L`,
pushes the LSB of `m + c.toNat` onto `R`, and updates the carry for `m / 2`. -/
theorem step_dispatch_bit (d : ℕ) (hd1 : 1 ≤ d) (hd10 : d ≤ 10) (c : Bool)
    (m : ℕ) (L R : ListBlank (Fin 2)) :
    let c' := c && decide (m % 2 = 1)
    step reference
      ⟨dispatchState d c,
        Tape.mkL (L.cons (if m.testBit 0 then 1 else 0)) R⟩ =
      some ⟨dispatchState (d + 1) c',
        Tape.mkL L (R.cons (if (m + c.toNat).testBit 0 then 1 else 0))⟩ := by
  intro c'
  have hd0 : d ≠ 0 := by omega
  have hf0 := (dispatchState_trans_false_0 d hd10).resolve_left hd0
  have hf1 := (dispatchState_trans_false_1 d hd10).resolve_left hd0
  have ht0 := (dispatchState_trans_true_0 d hd10).resolve_left hd0
  have ht1 := (dispatchState_trans_true_1 d hd10).resolve_left hd0
  rw [testBit_zero_eq m, testBit_zero_eq (m + c.toNat)]
  cases c with
  | false =>
    have hc' : c' = false := rfl
    rw [hc']
    by_cases hm : m % 2 = 1
    · simp only [Bool.toNat_false, Nat.add_zero, hm, ↓reduceIte]
      exact step_mkL_left hf1 L R
    · simp only [Bool.toNat_false, Nat.add_zero, hm, ↓reduceIte]
      exact step_mkL_left hf0 L R
  | true =>
    by_cases hm : m % 2 = 1
    · have hm1 : ¬((m + 1) % 2 = 1) := by omega
      have hc' : c' = true := by simp [c', hm]
      rw [hc']
      simp only [Bool.toNat_true, hm, ↓reduceIte, hm1]
      exact step_mkL_left ht1 L R
    · have hm1 : (m + 1) % 2 = 1 := by omega
      have hc' : c' = false := by simp [c', hm]
      rw [hc']
      simp only [Bool.toNat_true, hm, ↓reduceIte, hm1]
      exact step_mkL_left ht0 L R

theorem div2_add_carry (m : ℕ) (c : Bool) :
    (m + c.toNat) / 2 = m / 2 + (c && decide (m % 2 = 1)).toNat := by
  cases c <;> by_cases hm : m % 2 = 1 <;> simp [hm] <;> omega

/-- General PC carry chain theorem: starting at `dispatchState (11 - k) c` with `k` bits of `m`
reversed on the left tape (`1 ≤ k ≤ 10`), `reference` runs for `k` steps to reach State `0`
(`!ENTRY`) with `pcBits k (m + c.toNat)` prepended to `R`. -/
theorem dispatch_chain (k : ℕ) (hk1 : 1 ≤ k) (hk10 : k ≤ 10) (c : Bool) (m : ℕ)
    (L R : ListBlank (Fin 2)) :
    nSteps reference k
      ⟨dispatchState (11 - k) c, Tape.mkL (ListBlank.append (pcBits k m).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (pcBits k (m + c.toNat)) R)⟩ := by
  induction k generalizing c m R with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      rw [append_pcBits_succ_reverse, pcBits_zero, List.reverse_nil, ListBlank.append]
      have hstep := step_dispatch_bit 10 (by decide) (by decide) c m L R
      simpa [dispatchState, append_pcBits_succ_snoc] using step_one hstep
    · have hk_ge : 1 ≤ k := by omega
      have hk_le : k ≤ 10 := by omega
      have hd1 : 1 ≤ 11 - (k + 1) := by omega
      have hd10 : 11 - (k + 1) ≤ 10 := by omega
      have hd_succ : 11 - (k + 1) + 1 = 11 - k := by omega
      rw [append_pcBits_succ_reverse]
      have hstep := step_dispatch_bit (11 - (k + 1)) hd1 hd10 c m
        (ListBlank.append (pcBits k (m / 2)).reverse L) R
      rw [hd_succ] at hstep
      have hrest := ih hk_ge hk_le (c && decide (m % 2 = 1)) (m / 2)
        (R.cons (if (m + c.toNat).testBit 0 then 1 else 0))
      rw [← div2_add_carry, append_pcBits_succ_snoc] at hrest
      exact step_nSteps hstep hrest

/-- Full 11-bit PC increment from State `9` (`dispatch.0.carry`). -/
theorem dispatch_from_0_carry (pc : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference 11
      ⟨9, Tape.mkL (ListBlank.append (pcBits 11 pc).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (pcBits 11 (pc + 1)) R)⟩ := by
  rw [append_pcBits_succ_reverse 10 pc L]
  have h1 : step reference
      ⟨9, Tape.mkL ((ListBlank.append (pcBits 10 (pc / 2)).reverse L).cons
        (if pc.testBit 0 then 1 else 0)) R⟩ =
      some ⟨dispatchState 1 (true && decide (pc % 2 = 1)),
        Tape.mkL (ListBlank.append (pcBits 10 (pc / 2)).reverse L)
          (R.cons (if (pc + 1).testBit 0 then 1 else 0))⟩ := by
    rw [testBit_zero_eq pc, testBit_zero_eq (pc + 1)]
    by_cases hm : pc % 2 = 1
    · have hm1 : ¬((pc + 1) % 2 = 1) := by omega
      simp only [hm, decide_true, Bool.true_and, ↓reduceIte, hm1]
      exact step_mkL_left (by rfl) _ _
    · have hm1 : (pc + 1) % 2 = 1 := by omega
      simp only [hm, decide_false, Bool.true_and, ↓reduceIte, hm1]
      exact step_mkL_left (by rfl) _ _
  have hrest := dispatch_chain 10 (by decide) (by decide)
    (true && decide (pc % 2 = 1)) (pc / 2) L (R.cons (if (pc + 1).testBit 0 then 1 else 0))
  have hdiv := div2_add_carry pc true
  simp only [Bool.toNat_true] at hdiv
  rw [← hdiv, append_pcBits_succ_snoc] at hrest
  exact step_nSteps h1 hrest

/-- Full 11-bit PC `+ 2` increment from State `524` (`nextstate_2`). -/
theorem dispatch_from_524 (pc : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference 11
      ⟨524, Tape.mkL (ListBlank.append (pcBits 11 pc).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (pcBits 11 (pc + 2)) R)⟩ := by
  rw [append_pcBits_succ_reverse 10 pc L]
  have h1 : step reference
      ⟨524, Tape.mkL ((ListBlank.append (pcBits 10 (pc / 2)).reverse L).cons
        (if pc.testBit 0 then 1 else 0)) R⟩ =
      some ⟨dispatchState 1 true,
        Tape.mkL (ListBlank.append (pcBits 10 (pc / 2)).reverse L)
          (R.cons (if pc.testBit 0 then 1 else 0))⟩ :=
    step_mkL_left_any (by rfl) (by rfl) _ _ _
  have hbit0 : (if (pc + 2).testBit 0 then (1 : Fin 2) else 0) = if pc.testBit 0 then 1 else 0 := by
    rw [testBit_zero_eq, testBit_zero_eq]
    have hmod : (pc + 2) % 2 = pc % 2 := by omega
    rw [hmod]
  have hdiv2 : (pc + 2) / 2 = pc / 2 + 1 := by omega
  have hsnoc := append_pcBits_succ_snoc 10 (pc + 2) R
  rw [hdiv2, hbit0] at hsnoc
  have hrest := dispatch_chain 10 (by decide) (by decide)
    true (pc / 2) L (R.cons (if pc.testBit 0 then 1 else 0))
  simp only [Bool.toNat_true] at hrest
  rw [hsnoc] at hrest
  exact step_nSteps h1 hrest

theorem dispatch_from_9_entryCfg (pc : ℕ) (regs : List ℕ) :
    nSteps reference 11
      ⟨9, Tape.mkL (ListBlank.append (pcBits 11 pc).reverse default)
        ((regsTape regs).cons 0 |>.cons 0)⟩ =
      some (entryCfg (pc + 1) regs) := by
  have h := dispatch_from_0_carry pc default ((regsTape regs).cons 0 |>.cons 0)
  simpa [entryCfg, ListBlank.append_assoc] using h

theorem dispatch_from_524_entryCfg (pc : ℕ) (regs : List ℕ) :
    nSteps reference 11
      ⟨524, Tape.mkL (ListBlank.append (pcBits 11 pc).reverse default)
        ((regsTape regs).cons 0 |>.cons 0)⟩ =
      some (entryCfg (pc + 2) regs) := by
  have h := dispatch_from_524 pc default ((regsTape regs).cons 0 |>.cons 0)
  simpa [entryCfg, ListBlank.append_assoc] using h

/-!
## 5. Primitive Register Operations (`reg_init`, `reg_incr`, `reg_decr`)
-/

/-!
### 5.1 `reg_init` (States `32..35`)
-/

theorem init_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (r + 2)
      ⟨34, Tape.mk' L (ListBlank.append (encodeReg r) R)⟩ =
      some ⟨34, Tape.mk' (ListBlank.append (encodeReg r).reverse L) R⟩ := by
  rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨34, Tape.mk' L ((ListBlank.append (List.replicate r 1) (R.cons 0)).cons 1)⟩ =
      some ⟨35, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate r 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 35) (a := 1) (b := 1) (by rfl) r (L.cons 1) (R.cons 0)
  have h2 : step reference
      ⟨35, Tape.mk' (ListBlank.append (List.replicate r 1) (L.cons 1)) (R.cons 0)⟩ =
      some ⟨34, Tape.mk' ((ListBlank.append (List.replicate r 1) (L.cons 1)).cons 0) R⟩ :=
    step_mk'_right (by rfl) _ _
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  rw [append_replicate_cons, ← append_encodeReg_reverse] at hcomb
  simpa [Nat.add_assoc] using hcomb

theorem init_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (encodeRegs regs).length
      ⟨34, Tape.mk' L (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨34, Tape.mk' (ListBlank.append (encodeRegs regs).reverse L) R⟩ := by
  induction regs generalizing L with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.length_append, ListBlank.append_assoc, nSteps_add,
      encodeReg_length, init_scan_reg, Option.bind_some, ih,
      List.reverse_append, ListBlank.append_assoc]

/-- `reg_init` gadget evaluation: from `postPcCfg 32 pc regs`, `reference` appends a new
zero-initialized register (`regs ++ [0]`) and advances to `entryCfg (pc + 1) (regs ++ [0])`. -/
theorem reg_init_eval (pc : ℕ) (regs : List ℕ) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg 32 pc regs) =
      some (entryCfg (pc + 1) (regs ++ [0])) := by
  set L_pc := ListBlank.append (pcBits 11 pc).reverse default
  have h1 : step reference (postPcCfg 32 pc regs) =
      some ⟨33, Tape.mk' (L_pc.cons 0) ((regsTape regs).cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference ⟨33, Tape.mk' (L_pc.cons 0) ((regsTape regs).cons 0)⟩ =
      some ⟨34, Tape.mk' ((L_pc.cons 0).cons 0) (regsTape regs)⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := init_scan_regs regs ((L_pc.cons 0).cons 0) default
  have h3 : step reference
      ⟨34, Tape.mk' (ListBlank.append (encodeRegs regs).reverse ((L_pc.cons 0).cons 0)) default⟩ =
      some ⟨566, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L_pc.cons 0).cons 0))
        (regsTape [0])⟩ := by
    have hdef : (default : ListBlank (Fin 2)) =
        ListBlank.cons 0 (ListBlank.cons 0 default) := by simp
    conv_lhs => rw [hdef]
    exact step_mk'_left (by rfl) _ (ListBlank.cons 0 default)
  have hret := return1_scan_fence regs L_pc (regsTape [0])
  rw [← regsTape_append] at hret
  have hdisp := dispatch_from_9_entryCfg pc (regs ++ [0])
  have htotal := step_nSteps h1 (step_nSteps h2
    (nSteps_bind_eq hscan (step_nSteps h3 (nSteps_bind_eq hret hdisp))))
  exact ⟨_, by omega, htotal⟩

/-!
### 5.2 `reg_incr` (`regIncrState k`, States `30, 31`)
-/

/-- Entry state for incrementing register `k` (`0 ≤ k < 16`). -/
def regIncrState : ℕ → Fin 744
  | 0 => 551
  | 1 => 188
  | 2 => 558
  | 3 => 648
  | 4 => 559
  | 5 => 560
  | 6 => 561
  | 7 => 562
  | 8 => 563
  | 9 => 564
  | 10 => 552
  | 11 => 553
  | 12 => 554
  | 13 => 555
  | 14 => 556
  | 15 => 557
  | _ => 550

/-- Chain of `reg_incr` states where `0 ↦ 550` (`reg_incr(-1)`) and `k + 1 ↦ regIncrState k`. -/
def regIncrChain : ℕ → Fin 744
  | 0 => 550
  | k + 1 => regIncrState k

theorem regIncrChain_trans_one (m : ℕ) (hm : m ≤ 16) :
    refTrans (regIncrChain m) 1 = some (1, .right, regIncrChain m) := by
  revert m hm; decide

theorem regIncrChain_trans_zero (m : ℕ) (hm : m < 16) :
    refTrans (regIncrChain (m + 1)) 0 = some (0, .right, regIncrChain m) := by
  revert m hm; decide

theorem regIncrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 15)
    (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs pref).length + 1)
      ⟨regIncrChain pref.length, Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨31, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length < 16 := by omega
    have hrs_le : rs.length ≤ 15 := by omega
    have h0 : step reference
        ⟨regIncrChain (rs.length + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨regIncrChain rs.length,
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (regIncrChain_trans_zero rs.length hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan (regIncrChain_trans_one rs.length (by omega))
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

/-- Rightward shift and return scan in States `30`/`31` (`inc.shift_0`/`inc.shift_1`). -/
theorem inc_shift_eval (suff : List ℕ) (m : ℕ) (L_prev : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨30, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev) (regsTape suff)⟩ =
      some ⟨566, Tape.mkL L_prev (regsTape (m :: suff))⟩ := by
  induction suff generalizing m L_prev with
  | nil =>
    rw [regsTape_nil, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨30, Tape.mk' ((ListBlank.append (List.replicate m 1) L_prev).cons 1) default⟩ =
        some ⟨565, Tape.mkL ((ListBlank.append (List.replicate m 1) L_prev).cons 1)
          (ListBlank.cons 0 default)⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      exact step_mk'_left (by rfl) _ default
    have h2 : step reference
        ⟨565, Tape.mkL ((ListBlank.append (List.replicate m 1) L_prev).cons 1)
          (ListBlank.cons 0 default)⟩ =
        some ⟨566, Tape.mkL (ListBlank.append (List.replicate m 1) L_prev)
          (ListBlank.cons 1 (ListBlank.cons 0 default))⟩ :=
      step_mkL_left (by rfl) _ _
    have hscan := nSteps_mkL_left_scan (q := 566) (a := 1) (b := 1) (by rfl)
      m L_prev (ListBlank.cons 1 (ListBlank.cons 0 default))
    have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
    rw [append_replicate_cons, ← append_encodeReg, ← regsTape_nil, ← regsTape_cons] at hcomb
    exact ⟨m + 2, by omega, hcomb⟩
  | cons r rs ih =>
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨30, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨31, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) L_prev).cons 0)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    rw [← append_encodeReg_reverse] at h1
    have hscan := nSteps_mk'_right_scan (q := 31) (a := 1) (b := 1) (by rfl)
      r (ListBlank.append (encodeReg m).reverse L_prev) ((regsTape rs).cons 0)
    have h2 : step reference
        ⟨31, Tape.mk' (ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)) ((regsTape rs).cons 0)⟩ =
        some ⟨30, Tape.mk' ((ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)).cons 1) (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcons1 : (ListBlank.append (List.replicate r 1)
        (ListBlank.append (encodeReg m).reverse L_prev)).cons 1 =
        ListBlank.append (List.replicate (r + 1) 1)
          (ListBlank.append (encodeReg m).reverse L_prev) := by
      rw [List.replicate_succ, ListBlank.append]
    rw [hcons1] at h2
    obtain ⟨s, hs1, hs⟩ := ih r (ListBlank.append (encodeReg m).reverse L_prev)
    have hret := return1_scan_reg m L_prev (regsTape (r :: rs))
    rw [← regsTape_cons] at hret
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan
      (step_nSteps h2 (nSteps_bind_eq hs hret)))
    exact ⟨_, by omega, hcomb⟩

theorem list_take_cons_drop (regs : List ℕ) (k : ℕ) (hk : k < regs.length) :
    regs.take k ++ regs[k] :: regs.drop (k + 1) = regs := by
  induction regs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k => simp

theorem list_take_set_drop (regs : List ℕ) (k v : ℕ) (hk : k < regs.length) :
    regs.take k ++ v :: regs.drop (k + 1) = regs.set k v := by
  induction regs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, List.set_cons_succ]
      congr 1
      exact ih k hk

/-- `reg_incr` gadget evaluation: from `postPcCfg (regIncrState k) pc regs` (`k < 16`,
`k < regs.length`), `reference` increments `regs[k]` by `1` and advances to
`entryCfg (pc + 1) (regs.set k (regs[k] + 1))`. -/
theorem reg_incr_eval (k : ℕ) (hk16 : k < 16) (pc : ℕ) (regs : List ℕ)
    (hk : k < regs.length) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg (regIncrState k) pc regs) =
      some (entryCfg (pc + 1) (regs.set k (regs[k] + 1))) := by
  set L_pc := ListBlank.append (pcBits 11 pc).reverse default
  set pref := regs.take k
  set r := regs[k]
  set suff := regs.drop (k + 1)
  have hpref_len : pref.length = k := List.length_take_of_le (by omega)
  have hregs_split : regsTape regs = ListBlank.append (encodeRegs pref) (regsTape (r :: suff)) := by
    rw [← regsTape_append, list_take_cons_drop regs k hk]
  have h0 : step reference (postPcCfg (regIncrState k) pc regs) =
      some ⟨regIncrChain pref.length,
        Tape.mk' (L_pc.cons 0) ((ListBlank.append (encodeRegs pref) (regsTape (r :: suff))).cons
          0)⟩ := by
    unfold postPcCfg
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regIncrChain_trans_zero k hk16) L_pc _
  have hpref_scan := regIncrChain_scan_pref pref (by omega) (L_pc.cons 0) (regsTape (r :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_pc.cons 0).cons 0)
  have hr_scan : nSteps reference ((r + 1) + 1)
      ⟨31, Tape.mk' L_pref (regsTape (r :: suff))⟩ =
      some ⟨30, Tape.mk' (ListBlank.append (List.replicate (r + 2) 1) L_pref) (regsTape suff)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    have hones := nSteps_mk'_right_scan (q := 31) (a := 1) (b := 1) (by rfl)
      (r + 1) L_pref ((regsTape suff).cons 0)
    have hzero : step reference
        ⟨31, Tape.mk' (ListBlank.append (List.replicate (r +
          1) 1) L_pref) ((regsTape suff).cons 0)⟩ =
        some ⟨30, Tape.mk' ((ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := nSteps_bind_eq hones (step_one hzero)
    have hcons : (ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1 =
        ListBlank.append (List.replicate (r + 2) 1) L_pref := by
      rw [← ListBlank.append, ← List.replicate_succ]
    rw [hcons] at hcomb
    exact hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := inc_shift_eval suff (r + 1) L_pref
  have hret := return1_scan_fence pref L_pc (regsTape ((r + 1) :: suff))
  rw [← regsTape_append, list_take_set_drop regs k (r + 1) hk] at hret
  have hdisp := dispatch_from_9_entryCfg pc (regs.set k (r + 1))
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (nSteps_bind_eq hr_scan (nSteps_bind_eq hshift (nSteps_bind_eq hret hdisp))))
  exact ⟨_, by omega, htotal⟩

/-!
### 5.3 `reg_decr` (`regDecrState k`, States `1..8`)
-/

/-- Entry state for decrementing register `k` (`0 ≤ k < 16`). -/
def regDecrState : ℕ → Fin 744
  | 0 => 534
  | 1 => 535
  | 2 => 542
  | 3 => 543
  | 4 => 544
  | 5 => 545
  | 6 => 546
  | 7 => 547
  | 8 => 548
  | 9 => 549
  | 10 => 536
  | 11 => 537
  | 12 => 538
  | 13 => 539
  | 14 => 540
  | 15 => 541
  | _ => 533

/-- Chain of `reg_decr` states where `0 ↦ 533` (`reg_decr(-1)`) and `k + 1 ↦ regDecrState k`. -/
def regDecrChain : ℕ → Fin 744
  | 0 => 533
  | k + 1 => regDecrState k

theorem regDecrChain_trans_one (m : ℕ) (hm : m ≤ 16) :
    refTrans (regDecrChain m) 1 = some (1, .right, regDecrChain m) := by
  revert m hm; decide

theorem regDecrChain_trans_zero (m : ℕ) (hm : m < 16) :
    refTrans (regDecrChain (m + 1)) 0 = some (0, .right, regDecrChain m) := by
  revert m hm; decide

theorem regDecrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 15)
    (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs pref).length + 1)
      ⟨regDecrChain pref.length, Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨2, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length < 16 := by omega
    have hrs_le : rs.length ≤ 15 := by omega
    have h0 : step reference
        ⟨regDecrChain (rs.length + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨regDecrChain rs.length,
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (regDecrChain_trans_zero rs.length hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan (regDecrChain_trans_one rs.length (by omega))
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

/-- Leftward shift of a single register `m` in States `7`/`8` (`dec.shift_0`/`dec.shift_1`). -/
theorem dec_shift_reg (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (m + 2)
      ⟨7, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ =
      some ⟨7, Tape.mkL L (ListBlank.append (encodeReg m) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨7, Tape.mkL ((ListBlank.append (List.replicate m 1) (L.cons 0)).cons 1) R⟩ =
      some ⟨8, Tape.mkL (ListBlank.append (List.replicate m 1) (L.cons 0)) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 8) (a := 1) (b := 1) (by rfl)
    m (L.cons 0) (R.cons 0)
  have h2 : step reference
      ⟨8, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ =
      some ⟨7, Tape.mkL L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcons : (ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1 =
      ListBlank.append (encodeReg m) R := by
    rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  rw [hcons] at h2
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  simpa [Nat.add_assoc] using hcomb

/-- Forward scan and leftward shift across `suff` in States `4, 5, 6, 7, 8`. -/
theorem dec_scan_and_shift (suff : List ℕ) (m : ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨4, Tape.mk' (ListBlank.append (encodeReg m).reverse (L.cons 0)) (regsTape suff)⟩ =
      some ⟨7, Tape.mkL L (regsTape (m :: suff))⟩ := by
  induction suff generalizing m L with
  | nil =>
    rw [regsTape_nil, append_encodeReg_reverse]
    have h1 : step reference
        ⟨4, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨6, Tape.mkL ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0)
          default⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      rw [step_mk'_left (by rfl), default_cons_zero]
    have h2 : step reference
        ⟨6, Tape.mkL ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨7, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default⟩ := by
      have h := step_mkL_left (q := 6) (q' := 7) (a := 0) (b := 0) (by rfl)
        (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default
      rw [default_cons_zero] at h
      exact h
    have hshift := dec_shift_reg m L default
    rw [← regsTape_nil, ← regsTape_cons] at hshift
    exact ⟨m + 4, by omega, step_nSteps h1 (step_nSteps h2 hshift)⟩
  | cons r rs ih =>
    let L' := ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)
    have hL' : ListBlank.append (encodeReg m).reverse (L.cons 0) = L'.cons 0 :=
      append_encodeReg_reverse m (L.cons 0)
    rw [hL', regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨4, Tape.mk' (L'.cons 0)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨5, Tape.mk' ((L'.cons 0).cons 1)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 5) (a := 1) (b := 1) (by rfl)
      r ((L'.cons 0).cons 1) ((regsTape rs).cons 0)
    have h2 : step reference
        ⟨5, Tape.mk' (ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1))
          ((regsTape rs).cons 0)⟩ =
        some ⟨4, Tape.mk' ((ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1)).cons 0)
          (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan_reg := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r (L'.cons 0)] at hscan_reg
    obtain ⟨s, hs1, hs⟩ := ih r L'
    have hshift := dec_shift_reg m L (regsTape (r :: rs))
    rw [← regsTape_cons] at hshift
    have hcomb := nSteps_bind_eq hscan_reg (nSteps_bind_eq hs hshift)
    exact ⟨_, by omega, hcomb⟩

theorem step_state7_eq_state568 (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    step reference ⟨7, Tape.mkL (ListBlank.append (encodeRegs regs).reverse (L.cons 0)) R⟩ =
      step reference ⟨568, Tape.mkL (ListBlank.append (encodeRegs regs).reverse (L.cons 0)) R⟩ := by
  induction regs using List.reverseRecOn with
  | nil =>
    simp only [encodeRegs_nil, List.reverse_nil, ListBlank.append]
    rw [step_mkL_left (by rfl), step_mkL_left (by rfl)]
  | append_singleton rs r _ =>
    rw [encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil,
      List.reverse_append, ListBlank.append_assoc, append_encodeReg_reverse]
    rw [step_mkL_left (by rfl), step_mkL_left (by rfl)]

theorem dec_return2_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs regs).length + 2)
      ⟨7, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨524, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have h568 := return2_scan_fence regs L R
  obtain ⟨m, hm⟩ : ∃ m, (encodeRegs regs).length + 2 = m + 1 :=
    ⟨(encodeRegs regs).length + 1, rfl⟩
  rw [hm, nSteps_succ, step_state7_eq_state568, ← nSteps_succ, ← hm, h568]

/-- `reg_decr` gadget evaluation when `regs[k] = 0`: from `postPcCfg (regDecrState k) pc regs`,
`reference` leaves `regs` unchanged and advances to `entryCfg (pc + 1) regs`. -/
theorem reg_decr_eval_zero (k : ℕ) (hk16 : k < 16) (pc : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hz : regs[k] = 0) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg (regDecrState k) pc regs) =
      some (entryCfg (pc + 1) regs) := by
  set L_pc := ListBlank.append (pcBits 11 pc).reverse default
  set pref := regs.take k
  set suff := regs.drop (k + 1)
  have hpref_len : pref.length = k := List.length_take_of_le (by omega)
  have hregs_split : regsTape regs = ListBlank.append (encodeRegs pref) (regsTape (0 :: suff)) := by
    rw [← regsTape_append, ← hz, list_take_cons_drop regs k hk]
  have h0 : step reference (postPcCfg (regDecrState k) pc regs) =
      some ⟨regDecrChain pref.length,
        Tape.mk' (L_pc.cons 0) ((ListBlank.append (encodeRegs pref) (regsTape (0 :: suff))).cons
          0)⟩ := by
    unfold postPcCfg
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecrChain_trans_zero k hk16) L_pc _
  have hpref_scan := regDecrChain_scan_pref pref (by omega) (L_pc.cons 0) (regsTape (0 :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_pc.cons 0).cons 0)
  have h1 : step reference ⟨2, Tape.mk' L_pref (regsTape (0 :: suff))⟩ =
      some ⟨1, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mk'_right (by rfl) L_pref ((regsTape suff).cons 0)
  have h2 : step reference ⟨1, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨3, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ :=
    step_mk'_left (by rfl) (L_pref.cons 0) (regsTape suff)
  have h3 : step reference ⟨3, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨566, Tape.mkL L_pref (regsTape (0 :: suff))⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mkL_left (by rfl) L_pref ((regsTape suff).cons 0)
  have hret := return1_scan_fence pref L_pc (regsTape (0 :: suff))
  rw [← hregs_split] at hret
  have hdisp := dispatch_from_9_entryCfg pc regs
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hret hdisp)))))
  exact ⟨_, by omega, htotal⟩

/-- `reg_decr` gadget evaluation when `regs[k] > 0`: from `postPcCfg (regDecrState k) pc regs`,
`reference` decrements `regs[k]` by `1` and advances to
`entryCfg (pc + 2) (regs.set k (regs[k] - 1))`. -/
theorem reg_decr_eval_pos (k : ℕ) (hk16 : k < 16) (pc : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hpos : 0 < regs[k]) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg (regDecrState k) pc regs) =
      some (entryCfg (pc + 2) (regs.set k (regs[k] - 1))) := by
  set L_pc := ListBlank.append (pcBits 11 pc).reverse default
  set pref := regs.take k
  set r' := regs[k] - 1
  set suff := regs.drop (k + 1)
  have hr_eq : regs[k] = r' + 1 := by omega
  have hpref_len : pref.length = k := List.length_take_of_le (by omega)
  have hregs_split : regsTape regs =
      ListBlank.append (encodeRegs pref) (regsTape ((r' + 1) :: suff)) := by
    rw [← regsTape_append, ← hr_eq, list_take_cons_drop regs k hk]
  have h0 : step reference (postPcCfg (regDecrState k) pc regs) =
      some ⟨regDecrChain pref.length,
        Tape.mk' (L_pc.cons 0) ((ListBlank.append (encodeRegs pref) (regsTape ((r' +
          1) :: suff))).cons 0)⟩ := by
    unfold postPcCfg
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecrChain_trans_zero k hk16) L_pc _
  have hpref_scan :=
      regDecrChain_scan_pref pref (by omega) (L_pc.cons 0) (regsTape ((r' + 1) :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_pc.cons 0).cons 0)
  have hinit : step reference ⟨2, Tape.mk' L_pref (regsTape ((r' + 1) :: suff))⟩ =
      some ⟨1, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ := by
    have hcons : regsTape ((r' + 1) :: suff) = (regsTape (r' :: suff)).cons 1 := by
      rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append,
        ← append_encodeReg, ← regsTape_cons]
    rw [hcons]
    exact step_mk'_right (by rfl) L_pref (regsTape (r' :: suff))
  have hr'_scan : nSteps reference (r' + 2)
      ⟨1, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ =
      some ⟨4, Tape.mk' (ListBlank.append (encodeReg r').reverse (L_pref.cons 0)) (regsTape suff)⟩
        := by
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨1, Tape.mk' (L_pref.cons 0)
          ((ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0)).cons 1)⟩ =
        some ⟨5, Tape.mk' ((L_pref.cons 0).cons 1)
          (ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 5) (a := 1) (b := 1) (by rfl)
      r' ((L_pref.cons 0).cons 1) ((regsTape suff).cons 0)
    have h2 : step reference
        ⟨5, Tape.mk' (ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1))
          ((regsTape suff).cons 0)⟩ =
        some ⟨4, Tape.mk' ((ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1)).cons 0)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r' (L_pref.cons 0)] at hcomb
    simpa [Nat.add_assoc] using hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := dec_scan_and_shift suff r' L_pref
  have hret := dec_return2_scan_fence pref L_pc (regsTape (r' :: suff))
  rw [← regsTape_append, list_take_set_drop regs k r' hk] at hret
  have hdisp := dispatch_from_524_entryCfg pc (regs.set k r')
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps hinit (nSteps_bind_eq hr'_scan
      (nSteps_bind_eq hshift (nSteps_bind_eq hret hdisp)))))
  exact ⟨_, by omega, htotal⟩

/-- Combined `reg_decr` gadget evaluation for any `k < 16` and `k < regs.length`. -/
theorem reg_decr_eval (k : ℕ) (hk16 : k < 16) (pc : ℕ) (regs : List ℕ)
    (hk : k < regs.length) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg (regDecrState k) pc regs) =
      some (if regs[k] = 0 then entryCfg (pc + 1) regs
            else entryCfg (pc + 2) (regs.set k (regs[k] - 1))) := by
  by_cases hz : regs[k] = 0
  · simp only [hz, ↓reduceIte]
    exact reg_decr_eval_zero k hk16 pc regs hk hz
  · simp only [hz, ↓reduceIte]
    exact reg_decr_eval_pos k hk16 pc regs hk (by omega)

end ConjectureMachines.Riemann543.Layer1
