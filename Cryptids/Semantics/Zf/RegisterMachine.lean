/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Zf.Soundness
public import Cryptids.Zf429
public import Mathlib.Tactic.Ring

/-!
# Layer 3: 11-Register Machine & Wff-Stack Verification for `zf_432_wade.tm` (`zf2.py`)

This module formalizes the Layer 3 register-machine verification of Stefan O'Rear's ZF proof
enumerator as compiled by Andrew Wade's `zf2.py` (prior to commit `10fcf152b3`) into the
432-state Turing machine `zf_432_wade.tm`:

1. **Cantor Pairing and Unpairing (`cantorStep`, `cantorUnpair`, `unpairLoop`, `pairLoop`)**:
   We prove the exact bijection between `cantorPair` and `cantorUnpair` (`cantorPair_cantorUnpair`
   and `cantorUnpair_cantorPair`), and prove that the register-machine loops
   `unpair(out1, out2, in)` and `pair(out, in1, in2)` compute `cantorUnpair` and `cantorPair`.

2. **RPN Wff-Stack Machine and 20-Clause Sequence (`WffState`, `weq..wa`, `select`, `cparam`)**:
   We formalize all reverse-Polish notation (RPN) stack manipulation subroutines of `zf_432_wade.tm`
   and prove that executing `v_0()` followed by all 20 clauses (`DET`, `GEN`, `B1`, `B2`, `B3`,
   `B4`, `B6b`, `B8b`, `B6a`, `B6b`, `B6c`, `B7`, `B8a`, `B8b`, `B8c`, `EXT`, `REP`, `POW`,
   `UNI`, `INF`) with `select()` computes `zfClauseDispatch`.

3. **Soundness and Completeness of `zfMainStep` (`mainLoopHalts_iff_wadeZFInconsistent`)**:
   - **Soundness**: Every formula on `(topwff, wffstack)` is `WadeZFProvable` (`StackAllProvable`),
     preserved by every proof step regardless of `prooflist`; hence halting (`topwff = 1`) implies
     `WadeZFInconsistent`.
   - **Completeness**: By induction on `WadeZFProvable φ`, every provable formula has a finite
     proof-step sequence `L` whose execution pushes `φ` onto any wff-stack `(topwff, wffstack)`.
     Since `nextproof` enumerates all natural numbers `0, 1, 2, ...` whenever `prooflist` drains
     to `0`, `WadeZFInconsistent` implies `MainLoopHalts`.
-/

@[expose] public section

namespace ConjectureMachines.Semantics.Zf

open Turing StateTransition

/-! ## Section 1: Cantor Pairing, Unpairing, and Register Loop Equivalence -/

/-- Equivalent `if`-form of `cantorStep` matching `unpair` in `zf_432_wade.tm`. -/
def unpairStep (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 > 0 then (p.1 + 1, p.2 - 1) else (0, p.1 + 1)

theorem unpairStep_eq_cantorStep (p : ℕ × ℕ) : unpairStep p = cantorStep p := by
  rcases p with ⟨x, _ | y⟩ <;> rfl

/-- Tail-recursive register loop of `unpair(out1, out2, in)` in `zf_432_wade.tm`:
decrements `z` to `0`, applying `unpairStep` at each iteration. -/
def unpairLoop : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | z + 1, p => unpairLoop z (unpairStep p)

theorem unpairLoop_cantorStep (z : ℕ) (p : ℕ × ℕ) :
    unpairLoop z (cantorStep p) = cantorStep (unpairLoop z p) := by
  induction z generalizing p with
  | zero => rfl
  | succ z ih =>
    simp only [unpairLoop, unpairStep_eq_cantorStep]
    exact ih (cantorStep p)

theorem unpairLoop_zero_zero (z : ℕ) :
    unpairLoop z (0, 0) = cantorUnpair z := by
  induction z with
  | zero => rfl
  | succ z ih =>
    simp only [unpairLoop, unpairStep_eq_cantorStep]
    rw [unpairLoop_cantorStep, ih, cantorUnpair_succ]

/-- Outer accumulation loop of `pair(out, in1, in2)` in `zf_432_wade.tm`:
for each `s` from `x + y` down to `1`, adds `1 + (s - 1)` to `out`. -/
def triLoop : ℕ → ℕ → ℕ
  | 0, acc => acc
  | s + 1, acc => triLoop s (acc + (s + 1))

theorem triLoop_eq (s acc : ℕ) :
    triLoop s acc = acc + s * (s + 1) / 2 := by
  induction s generalizing acc with
  | zero => simp [triLoop]
  | succ s ih =>
    rw [triLoop, ih, tri_succ]
    omega

/-- Register loop model of `pair(out, in1, in2)` in `zf_432_wade.tm`. -/
def pairLoop (out x y : ℕ) : ℕ :=
  triLoop (x + y) (out + x)

theorem pairLoop_eq_cantorPair (out x y : ℕ) :
    pairLoop out x y = out + cantorPair x y := by
  unfold pairLoop cantorPair
  rw [triLoop_eq]
  omega

/-! ## Section 2: RPN Wff-Stack Machine and 20-Clause Verification -/

/-- State of the formula-construction registers
`(topwff, wffstack, axiomcode, param1, param2, param3)` during a single iteration of `main()` in
`zf_432_wade.tm`. -/
structure WffState where
  topwff : ℕ
  wffstack : ℕ
  axiomcode : ℕ
  param1 : ℕ
  param2 : ℕ
  param3 : ℕ
  deriving DecidableEq, Repr

/-- `pushwff()` in `zf2.nql`: `pair(wffstack, topwff, wffstack)` (which zeros `topwff`). -/
def rpnPushwff (s : WffState) : WffState :=
  { s with topwff := 0, wffstack := cantorPair s.topwff s.wffstack }

/-- `popwff()` in `zf2.nql`: `unpair(topwff, wffstack, wffstack)`. -/
def rpnPopwff (s : WffState) : WffState :=
  let p := cantorUnpair s.wffstack
  { s with topwff := p.1, wffstack := p.2 }

/-- `v_k_()` in `zf2.nql`: `pushwff(); topwff = topwff + k`. -/
def rpnVk (k : ℕ) (s : WffState) : WffState :=
  { s with topwff := k, wffstack := cantorPair s.topwff s.wffstack }

/-- `cons()` in `zf2.nql`: `unpair(t2, wffstack, wffstack); pair(topwff, t2, topwff)`. -/
def rpnCons (s : WffState) : WffState :=
  let p := cantorUnpair s.wffstack
  { s with topwff := cantorPair p.1 s.topwff, wffstack := p.2 }

/-- `weq()` in `zf2.nql`: `cons(); v_0_(); cons()`. -/
def rpnWeq (s : WffState) : WffState :=
  rpnCons (rpnVk 0 (rpnCons s))

/-- `wel()` in `zf2.nql`: `cons(); v_1_(); cons()`. -/
def rpnWel (s : WffState) : WffState :=
  rpnCons (rpnVk 1 (rpnCons s))

/-- `wim()` in `zf2.nql`: `cons(); v_2_(); cons()`. -/
def rpnWim (s : WffState) : WffState :=
  rpnCons (rpnVk 2 (rpnCons s))

/-- `wn()` in `zf2.nql`: `v_3_(); cons()`. -/
def rpnWn (s : WffState) : WffState :=
  rpnCons (rpnVk 3 s)

/-- `wal()` in `zf2.nql`: `cons(); v_4_(); cons()`. -/
def rpnWal (s : WffState) : WffState :=
  rpnCons (rpnVk 4 (rpnCons s))

/-- `wex()` in `zf2.nql`: `wn(); wal(); wn()`. -/
def rpnWex (s : WffState) : WffState :=
  rpnWn (rpnWal (rpnWn s))

/-- `wa()` in `zf2.nql`: `wn(); wim(); wn()`. -/
def rpnWa (s : WffState) : WffState :=
  rpnWn (rpnWim (rpnWn s))

/-- `par1()` in `zf2.nql`: `pushwff(); topwff = param1`. -/
def rpnPar1 (s : WffState) : WffState :=
  { s with topwff := s.param1, wffstack := cantorPair s.topwff s.wffstack }

/-- `par2()` in `zf2.nql`: `pushwff(); topwff = param2`. -/
def rpnPar2 (s : WffState) : WffState :=
  { s with topwff := s.param2, wffstack := cantorPair s.topwff s.wffstack }

/-- `par3()` in `zf2.nql`: `pushwff(); topwff = param3`. -/
def rpnPar3 (s : WffState) : WffState :=
  { s with topwff := s.param3, wffstack := cantorPair s.topwff s.wffstack }

/-- `select()` in `zf2.nql`:
```
builtin_move(t2, topwff); popwff();
if (axiomcode > 0) { axiomcode = axiomcode - 1; builtin_move(topwff, t2); }
```
-/
def rpnSelect (s : WffState) : WffState :=
  let t2 := s.topwff
  let popped := cantorUnpair s.wffstack
  if s.axiomcode > 0 then
    { s with topwff := t2, wffstack := popped.2, axiomcode := s.axiomcode - 1 }
  else
    { s with topwff := popped.1, wffstack := popped.2 }

/-- `cparam(param2)` in `zf2.nql`: if `axiomcode == 1`, pops from `wffstack` into `param2`. -/
def rpnCparam2 (s : WffState) : WffState :=
  if s.axiomcode = 1 then
    let p := cantorUnpair s.wffstack
    { s with wffstack := p.2, param2 := p.1 }
  else s

/-- `cparam(param3)` in `zf2.nql`: if `axiomcode == 1`, pops from `wffstack` into `param3`. -/
def rpnCparam3 (s : WffState) : WffState :=
  if s.axiomcode = 1 then
    let p := cantorUnpair s.wffstack
    { s with wffstack := p.2, param3 := p.1 }
  else s

/-- `DET` equality check on `topwff` and `param2` in `zf_432_wade.tm`. -/
def rpnDetCheck (s : WffState) : WffState :=
  { s with topwff := if s.topwff = s.param2 then s.param1 else 0 }

/-- First variable-distinctness check in `B6a` (`zf_432_wade.tm`), where `main().n_140.1`
restores `scratch1` into `param1` instead of `param3`. -/
def rpnB6aCheck1 (s : WffState) : WffState :=
  { s with
    topwff := if s.param1 = s.param3 then 0 else s.topwff
    param1 := s.param1 + s.param3
    param3 := 0 }

/-- Second variable-distinctness check in `B6a` (`zf_432_wade.tm`). -/
def rpnB6aCheck2 (s : WffState) : WffState :=
  { s with
    topwff := if s.param2 = s.param3 then 0 else s.topwff
    param1 := s.param1 + s.param3
    param3 := 0 }

@[simp]
theorem rpnCons_cantorPair (x y stk ac p1 p2 p3 : ℕ) :
    rpnCons ⟨y, cantorPair x stk, ac, p1, p2, p3⟩ =
      ⟨cantorPair x y, stk, ac, p1, p2, p3⟩ := by
  simp [rpnCons]

@[simp]
theorem rpnWeq_eval (x y stk ac p1 p2 p3 : ℕ) :
    rpnWeq ⟨y, cantorPair x stk, ac, p1, p2, p3⟩ =
      ⟨zfEq x y, stk, ac, p1, p2, p3⟩ := by
  simp [rpnWeq, rpnVk, zfEq]

@[simp]
theorem rpnWel_eval (x y stk ac p1 p2 p3 : ℕ) :
    rpnWel ⟨y, cantorPair x stk, ac, p1, p2, p3⟩ =
      ⟨zfMem x y, stk, ac, p1, p2, p3⟩ := by
  simp [rpnWel, rpnVk, zfMem]

@[simp]
theorem rpnWim_eval (φ ψ stk ac p1 p2 p3 : ℕ) :
    rpnWim ⟨ψ, cantorPair φ stk, ac, p1, p2, p3⟩ =
      ⟨zfImp φ ψ, stk, ac, p1, p2, p3⟩ := by
  simp [rpnWim, rpnVk, zfImp]

@[simp]
theorem rpnWn_eval (φ stk ac p1 p2 p3 : ℕ) :
    rpnWn ⟨φ, stk, ac, p1, p2, p3⟩ =
      ⟨zfNot φ, stk, ac, p1, p2, p3⟩ := by
  simp [rpnWn, rpnVk, zfNot]

@[simp]
theorem rpnWal_eval (x φ stk ac p1 p2 p3 : ℕ) :
    rpnWal ⟨φ, cantorPair x stk, ac, p1, p2, p3⟩ =
      ⟨zfAll x φ, stk, ac, p1, p2, p3⟩ := by
  simp [rpnWal, rpnVk, zfAll]

@[simp]
theorem rpnWex_eval (x φ stk ac p1 p2 p3 : ℕ) :
    rpnWex ⟨φ, cantorPair x stk, ac, p1, p2, p3⟩ =
      ⟨zfEx x φ, stk, ac, p1, p2, p3⟩ := by
  simp [rpnWex, zfEx]

@[simp]
theorem rpnWa_eval (φ ψ stk ac p1 p2 p3 : ℕ) :
    rpnWa ⟨ψ, cantorPair φ stk, ac, p1, p2, p3⟩ =
      ⟨zfAnd φ ψ, stk, ac, p1, p2, p3⟩ := by
  simp [rpnWa, zfAnd]

@[simp]
theorem rpnSelect_eval (candidate prev stk ac p1 p2 p3 : ℕ) :
    rpnSelect ⟨candidate, cantorPair prev stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then candidate else prev, stk, ac - 1, p1, p2, p3⟩ := by
  cases ac <;> simp [rpnSelect]

/-- Exact functional specification of the 20-clause dispatch executed by `main()` in
`zf_432_wade.tm`, mapping `(topwff, wffstack, axiomcode, param1, param2, param3)` to the new
`(topwff', wffstack')`. -/
def zfClauseDispatch (topwff wffstack ac p1 p2 p3 : ℕ) : ℕ × ℕ :=
  let stk0 := cantorPair topwff wffstack
  match ac with
  | 0 => (0, stk0)
  | 1 =>
    -- DET (Modus Ponens): pops minor premise φ and major premise ψ_maj from stk0
    let pop1 := cantorUnpair stk0
    let φ := pop1.1
    let pop2 := cantorUnpair pop1.2
    let maj := pop2.1
    let stk2 := pop2.2
    if zfImp φ p1 = maj then (p1, stk2) else (0, stk2)
  | 2 =>
    -- GEN (Universal Generalization): pops premise φ from stk0, pushes ∀ v_{p1} φ
    let pop1 := cantorUnpair stk0
    (zfAll p1 pop1.1, pop1.2)
  | 3 => (axB1 p1 p2 p3, stk0)
  | 4 => (axB2 p1, stk0)
  | 5 => (axB3 p1 p2, stk0)
  | 6 => (axB4 p1 p2 p3, stk0)
  | 7 => (axB6b p1 p2 p3, stk0)
  | 8 => (axB8b p1 p2 p3, stk0)
  | 9 => if p1 = p3 ∨ p2 = 0 then (0, stk0) else (axB6a p1 p2 p3, stk0)
  | 10 => (axB6b (p1 + p3) p2 0, stk0)
  | 11 => (axB6c (p1 + p3) p2, stk0)
  | 12 => (axB7 (p1 + p3) p2, stk0)
  | 13 => (axB8a (p1 + p3) p2 0, stk0)
  | 14 => (axB8b (p1 + p3) p2 0, stk0)
  | 15 => (axB8c (p1 + p3) p2 0, stk0)
  | 16 => (axExt, stk0)
  | 17 => (axRep (p1 + p3), stk0)
  | 18 => (axPow, stk0)
  | 19 => (axUni, stk0)
  | _ + 20 => (axInf, stk0)

/-! ### RPN Clause Definitions and Equivalence with `zfClauseDispatch` -/

/-- Clause `DET` in `zf_432_wade.tm`. -/
def rpnClauseDET (s : WffState) : WffState :=
  rpnSelect (rpnDetCheck (rpnWim (rpnPar1 (rpnPar3 (rpnCparam2 (rpnCparam3 s))))))

/-- Clause `GEN` in `zf_432_wade.tm`. -/
def rpnClauseGEN (s : WffState) : WffState :=
  rpnSelect (rpnWal (rpnPar3 (rpnPar1 (rpnCparam3 s))))

/-- Clause `B1` in `zf_432_wade.tm`. -/
def rpnClauseB1 (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnWim (rpnWim (rpnPar3 (rpnPar1 (rpnWim
    (rpnPar3 (rpnPar2 (rpnWim (rpnPar2 (rpnPar1 s)))))))))))

/-- Clause `B2` in `zf_432_wade.tm`. -/
def rpnClauseB2 (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnPar1 (rpnWim (rpnPar1 (rpnWn (rpnPar1 s))))))

/-- Clause `B3` in `zf_432_wade.tm`. -/
def rpnClauseB3 (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnWim (rpnPar2 (rpnWn (rpnPar1 (rpnPar1 s))))))

/-- Clause `B4` in `zf_432_wade.tm`. -/
def rpnClauseB4 (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnWim (rpnWal (rpnPar3 (rpnPar1 (rpnWal
    (rpnPar2 (rpnPar1 (rpnWal (rpnWim (rpnPar3 (rpnPar2 (rpnPar1 s)))))))))))))

/-- Clause `B6a` in `zf_432_wade.tm`. -/
def rpnClauseB6a (s : WffState) : WffState :=
  let s1 := rpnWim (rpnWal (rpnWeq (rpnPar2 (rpnPar1 (rpnPar3 (rpnWeq (rpnPar2 (rpnPar1 s))))))))
  let s2 := rpnWa (rpnWim (rpnWal (rpnWel (rpnPar2 (rpnPar1
    (rpnPar3 (rpnWel (rpnPar2 (rpnPar1 s1)))))))))
  rpnSelect (rpnB6aCheck2 (rpnB6aCheck1 s2))

/-- Clause `B6b` in `zf_432_wade.tm`. -/
def rpnClauseB6b (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnWal (rpnWal (rpnPar3 (rpnPar1 (rpnPar2
    (rpnWal (rpnWal (rpnPar3 (rpnPar2 (rpnPar1 s)))))))))))

/-- Clause `B6c` in `zf_432_wade.tm`. -/
def rpnClauseB6c (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnPar2 (rpnWex (rpnWal (rpnPar2 (rpnPar1 (rpnPar1 s)))))))

/-- Clause `B7` in `zf_432_wade.tm`. -/
def rpnClauseB7 (s : WffState) : WffState :=
  rpnSelect (rpnWex (rpnWeq (rpnPar2 (rpnPar1 (rpnPar1 s)))))

/-- Clause `B8a` in `zf_432_wade.tm`. -/
def rpnClauseB8a (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnWim (rpnWeq (rpnPar3 (rpnPar2 (rpnWeq
    (rpnPar3 (rpnPar1 (rpnWeq (rpnPar2 (rpnPar1 s)))))))))))

/-- Clause `B8b` in `zf_432_wade.tm`. -/
def rpnClauseB8b (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnWim (rpnWel (rpnPar3 (rpnPar2 (rpnWel
    (rpnPar3 (rpnPar1 (rpnWeq (rpnPar2 (rpnPar1 s)))))))))))

/-- Clause `B8c` in `zf_432_wade.tm`. -/
def rpnClauseB8c (s : WffState) : WffState :=
  rpnSelect (rpnWim (rpnWim (rpnWel (rpnPar2 (rpnPar3 (rpnWel
    (rpnPar1 (rpnPar3 (rpnWeq (rpnPar2 (rpnPar1 s)))))))))))

/-- Clause `EXT` in `zf_432_wade.tm`. -/
def rpnClauseEXT (s : WffState) : WffState :=
  let s1 := rpnWim (rpnWel (rpnVk 1 (rpnVk 2 (rpnWel (rpnVk 0 (rpnVk 2 (rpnVk 2 s)))))))
  let s2 := rpnWa (rpnWim (rpnWel (rpnVk 0 (rpnVk 2 (rpnWel (rpnVk 1 (rpnVk 2 s1)))))))
  rpnSelect (rpnWim (rpnWeq (rpnVk 1 (rpnVk 0 (rpnWal s2)))))

/-- Clause `REP` in `zf_432_wade.tm`. -/
def rpnClauseREP (s : WffState) : WffState :=
  let s1 := rpnWal (rpnWex (rpnWal (rpnWim (rpnWeq (rpnVk 1 (rpnVk 2
    (rpnWal (rpnPar1 (rpnVk 1 (rpnVk 2 (rpnVk 1 (rpnVk 3 s))))))))))))
  let s2 := rpnWel (rpnVk 1 (rpnVk 2 (rpnVk 2 (rpnVk 1 s1))))
  let s3 := rpnWim (rpnWex (rpnWa (rpnWal (rpnPar1 (rpnVk 1
    (rpnWel (rpnVk 0 (rpnVk 3 (rpnVk 3 s2)))))))))
  let s4 := rpnWex (rpnWa (rpnWal (rpnPar1 (rpnVk 1
    (rpnWel (rpnVk 0 (rpnVk 3 (rpnVk 3 s3))))))))
  let s5 := rpnWa (rpnWim (rpnWel (rpnVk 1 (rpnVk 2 s4))))
  rpnSelect (rpnWim (rpnWex (rpnWal s5)))

/-- Clause `POW` in `zf_432_wade.tm`. -/
def rpnClausePOW (s : WffState) : WffState :=
  let s1 := rpnWal (rpnWim (rpnWel (rpnVk 0 (rpnVk 3 (rpnWel
    (rpnVk 2 (rpnVk 3 (rpnVk 3 (rpnVk 2 (rpnVk 1 s))))))))))
  rpnSelect (rpnWex (rpnWal (rpnWim (rpnWel (rpnVk 1 (rpnVk 2 s1))))))

/-- Clause `UNI` in `zf_432_wade.tm`. -/
def rpnClauseUNI (s : WffState) : WffState :=
  let s1 := rpnWex (rpnWa (rpnWel (rpnVk 0 (rpnVk 3 (rpnWel
    (rpnVk 3 (rpnVk 2 (rpnVk 3 (rpnVk 2 (rpnVk 1 s))))))))))
  rpnSelect (rpnWex (rpnWal (rpnWim (rpnWel (rpnVk 1 (rpnVk 2 s1))))))

/-- Clause `INF` in `zf_432_wade.tm`. -/
def rpnClauseINF (s : WffState) : WffState :=
  let s1 := rpnWel (rpnVk 1 (rpnVk 2 (rpnVk 2 (rpnWel (rpnVk 1
    (rpnVk 0 (rpnVk 0 (rpnWel (rpnVk 1 (rpnVk 0 (rpnVk 1 s)))))))))))
  let s2 := rpnWim (rpnWeq (rpnVk 0 (rpnVk 1 (rpnWel (rpnVk 2 (rpnVk 1 (rpnVk 1 s1)))))))
  let s3 := rpnWal (rpnWa (rpnWim (rpnWel (rpnVk 2 (rpnVk 1 (rpnWeq (rpnVk 0 (rpnVk 1 s2))))))))
  rpnSelect (rpnWex (rpnWa (rpnWal (rpnWim (rpnWex (rpnWa s3))))))

/-- Full sequence of `v_0()` followed by all 20 RPN clauses in `main()` of `zf_432_wade.tm`. -/
def rpnAllClauses (topwff wffstack ac p1 p2 p3 : ℕ) : WffState :=
  let s0 : WffState := rpnVk 0 ⟨topwff, wffstack, ac, p1, p2, p3⟩
  rpnClauseINF (rpnClauseUNI (rpnClausePOW (rpnClauseREP (rpnClauseEXT
    (rpnClauseB8c (rpnClauseB8b (rpnClauseB8a (rpnClauseB7 (rpnClauseB6c
      (rpnClauseB6b (rpnClauseB6a (rpnClauseB8b (rpnClauseB6b (rpnClauseB4
        (rpnClauseB3 (rpnClauseB2 (rpnClauseB1 (rpnClauseGEN (rpnClauseDET s0)))))))))))))))))))

@[simp]
theorem rpnClauseB1_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB1 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB1 p1 p2 p3 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB1, rpnPar1, rpnPar2, rpnPar3, axB1]

@[simp]
theorem rpnClauseB2_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB2 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB2 p1 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB2, rpnPar1, axB2]

@[simp]
theorem rpnClauseB3_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB3 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB3 p1 p2 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB3, rpnPar1, rpnPar2, axB3]

@[simp]
theorem rpnClauseB4_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB4 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB4 p1 p2 p3 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB4, rpnPar1, rpnPar2, rpnPar3, axB4]

@[simp]
theorem rpnClauseB6a_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB6a ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then (if p1 = p3 ∨ p2 = 0 then 0 else axB6a p1 p2 p3) else top,
       stk, ac - 1, p1 + p3, p2, 0⟩ := by
  by_cases hp1 : p1 = p3 <;> by_cases hp2 : p2 = 0 <;>
    simp [rpnClauseB6a, rpnB6aCheck1, rpnB6aCheck2, rpnPar1, rpnPar2, rpnPar3, axB6a, hp1, hp2]

@[simp]
theorem rpnClauseB6b_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB6b ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB6b p1 p2 p3 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB6b, rpnPar1, rpnPar2, rpnPar3, axB6b]

@[simp]
theorem rpnClauseB6c_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB6c ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB6c p1 p2 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB6c, rpnPar1, rpnPar2, axB6c]

@[simp]
theorem rpnClauseB7_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB7 ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB7 p1 p2 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB7, rpnPar1, rpnPar2, axB7]

@[simp]
theorem rpnClauseB8a_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB8a ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB8a p1 p2 p3 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB8a, rpnPar1, rpnPar2, rpnPar3, axB8a]

@[simp]
theorem rpnClauseB8b_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB8b ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB8b p1 p2 p3 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB8b, rpnPar1, rpnPar2, rpnPar3, axB8b]

@[simp]
theorem rpnClauseB8c_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseB8c ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axB8c p1 p2 p3 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseB8c, rpnPar1, rpnPar2, rpnPar3, axB8c]

@[simp]
theorem rpnClauseEXT_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseEXT ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axExt else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseEXT, rpnVk, axExt]

@[simp]
theorem rpnClauseREP_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseREP ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axRep p1 else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseREP, rpnVk, rpnPar1, axRep, axRepRhs]

@[simp]
theorem rpnClausePOW_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClausePOW ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axPow else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClausePOW, rpnVk, axPow]

@[simp]
theorem rpnClauseUNI_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseUNI ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axUni else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseUNI, rpnVk, axUni]

@[simp]
theorem rpnClauseINF_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnClauseINF ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then axInf else top, stk, ac - 1, p1, p2, p3⟩ := by
  simp [rpnClauseINF, rpnVk, axInf, axInfSingleton]

/-- Complete equivalence between the 20-clause RPN execution `rpnAllClauses` and the
functional specification `zfClauseDispatch`. -/
theorem rpnAllClauses_eq_zfClauseDispatch (topwff wffstack ac p1 p2 p3 : ℕ) :
    let out := rpnAllClauses topwff wffstack ac p1 p2 p3
    (out.topwff, out.wffstack) = zfClauseDispatch topwff wffstack ac p1 p2 p3 := by
  unfold rpnAllClauses zfClauseDispatch
  rcases ac with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ac
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
    split_ifs <;> rfl
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
    split_ifs <;> rfl
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  · simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]

/-! ## Section 3: Main Loop Step (`ZfMainCfg`, `zfMainStep`, `MainLoopHalts`) -/

/-- Persistent state of the outer loop `main()` in `zf_432_wade.tm`. -/
structure ZfMainCfg where
  prooflist : ℕ
  nextproof : ℕ
  topwff : ℕ
  wffstack : ℕ
  deriving DecidableEq, Repr

/-- Initial state of `main()` with all persistent registers zeroed. -/
def zfMainInit : ZfMainCfg := ⟨0, 0, 0, 0⟩

/-- Unconditional next state of one iteration of `main()` (before the halt check
`topwff == 1`), following the compiled machine `zf_432_wade.tm` exactly: the loop head is
`if_not_decnz(prooflist)`, i.e. if `prooflist ≠ 0` it is decremented, otherwise it is reloaded
from `nextproof` (which is then incremented) *without* a subsequent decrement. -/
def zfMainNext (c : ZfMainCfg) : ZfMainCfg :=
  let prooflist₁ := if c.prooflist = 0 then c.nextproof else c.prooflist - 1
  let nextproof' := if c.prooflist = 0 then c.nextproof + 1 else c.nextproof
  let u1 := cantorUnpair prooflist₁
  let ac := u1.1
  let u2 := cantorUnpair u1.2
  let p1 := u2.1
  let u3 := cantorUnpair u2.2
  let p2 := u3.1
  let u4 := cantorUnpair u3.2
  let p3 := u4.1
  let prooflist' := u4.2
  let res := zfClauseDispatch c.topwff c.wffstack ac p1 p2 p3
  ⟨prooflist', nextproof', res.1, res.2⟩

/-- One full iteration of `main()` in `zf_432_wade.tm`: updates the state via `zfMainNext` and halts
(`none`) if `topwff' = 1` (`zfMem 0 0`). -/
def zfMainStep (c : ZfMainCfg) : Option ZfMainCfg :=
  if (zfMainNext c).topwff = 1 then none else some (zfMainNext c)

/-- `n`-step execution of `zfMainStep`. -/
def zfMainNSteps : ℕ → ZfMainCfg → Option ZfMainCfg
  | 0, c => some c
  | n + 1, c => (zfMainStep c).bind (zfMainNSteps n)

@[simp]
theorem zfMainNSteps_zero (c : ZfMainCfg) : zfMainNSteps 0 c = some c := rfl

@[simp]
theorem zfMainNSteps_succ (n : ℕ) (c : ZfMainCfg) :
    zfMainNSteps (n + 1) c = (zfMainStep c).bind (zfMainNSteps n) := rfl

theorem zfMainNSteps_add (m n : ℕ) (c : ZfMainCfg) :
    zfMainNSteps (m + n) c = (zfMainNSteps m c).bind (zfMainNSteps n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, zfMainNSteps_succ, zfMainNSteps_succ]
    cases zfMainStep c with
    | none => rfl
    | some c' => exact ih c'

theorem zfMainNSteps_bind_eq {m n : ℕ} {c₁ c₂ c₃ : ZfMainCfg}
    (h₁ : zfMainNSteps m c₁ = some c₂) (h₂ : zfMainNSteps n c₂ = some c₃) :
    zfMainNSteps (m + n) c₁ = some c₃ := by
  rw [zfMainNSteps_add, h₁, Option.bind_some, h₂]

/-- The main loop of `zf_432_wade.tm` halts starting from `zfMainInit`. -/
def MainLoopHalts : Prop :=
  (eval zfMainStep zfMainInit).Dom

theorem mem_eval_zfMainStep_iff_zfMainNSteps {c₀ ch : ZfMainCfg} :
    ch ∈ eval zfMainStep c₀ ↔ ∃ n, zfMainNSteps n c₀ = some ch ∧ zfMainStep ch = none := by
  constructor
  · intro h
    refine StateTransition.evalInduction h fun a ha ih => ?_
    rcases hs : zfMainStep a with _ | a'
    · have hmem : a ∈ eval zfMainStep a :=
        StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hs⟩
      have heq : ch = a := Part.mem_unique ha hmem
      subst heq
      exact ⟨0, rfl, hs⟩
    · obtain ⟨n, hn, hnone⟩ := ih a' hs
      exact ⟨n + 1, by simp [zfMainNSteps, hs, hn], hnone⟩
  · rintro ⟨n, hn, hnone⟩
    have hreach : Reaches zfMainStep c₀ ch := by
      induction n generalizing c₀ with
      | zero =>
        injection hn with h'
        subst h'
        exact Relation.ReflTransGen.refl
      | succ n ih =>
        unfold zfMainNSteps at hn
        rcases hs : zfMainStep c₀ with _ | c'
        · rw [hs] at hn; cases hn
        · rw [hs, Option.bind_some] at hn
          exact Relation.ReflTransGen.head hs (ih hn)
    exact StateTransition.mem_eval.mpr ⟨hreach, hnone⟩

theorem mainLoopHalts_iff_exists_zfMainNSteps :
    MainLoopHalts ↔ ∃ n c, zfMainNSteps n zfMainInit = some c ∧ zfMainStep c = none := by
  unfold MainLoopHalts
  rw [Part.dom_iff_mem]
  simp only [mem_eval_zfMainStep_iff_zfMainNSteps]
  exact ⟨fun ⟨c, n, h⟩ => ⟨n, c, h⟩, fun ⟨n, c, h⟩ => ⟨c, n, h⟩⟩

/-! ## Section 4: `WadeZFProvable` and Soundness of `zfMainStep` -/

/-- The `n`-th formula stored on the wff-stack `(topwff, wffstack)`, unpacked via repeated
`cantorUnpair`. -/
def stackGet : ℕ → ℕ → ℕ → ℕ
  | 0, top, _ => top
  | n + 1, _, stk => stackGet n (cantorUnpair stk).1 (cantorUnpair stk).2

@[simp]
theorem stackGet_zero (top stk : ℕ) : stackGet 0 top stk = top := rfl

@[simp]
theorem stackGet_succ (n top stk : ℕ) :
    stackGet (n + 1) top stk = stackGet n (cantorUnpair stk).1 (cantorUnpair stk).2 := rfl

/-- Invariant stating that `topwff` and every formula encoded in `wffstack` is `WadeZFProvable`. -/
def StackAllProvable (top stk : ℕ) : Prop :=
  ∀ n : ℕ, WadeZFProvable (stackGet n top stk)

theorem StackAllProvable.top {top stk : ℕ} (h : StackAllProvable top stk) :
    WadeZFProvable top :=
  h 0

theorem StackAllProvable.push {φ top stk : ℕ} (hφ : WadeZFProvable φ)
    (h : StackAllProvable top stk) :
    StackAllProvable φ (cantorPair top stk) := by
  intro n
  cases n with
  | zero => exact hφ
  | succ n =>
    simp only [stackGet_succ, cantorUnpair_cantorPair]
    exact h n

theorem StackAllProvable.pop {top stk : ℕ} (h : StackAllProvable top stk) :
    StackAllProvable (cantorUnpair stk).1 (cantorUnpair stk).2 := by
  intro n
  exact h (n + 1)

theorem stackGet_zero_zero (n : ℕ) : stackGet n 0 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem stackAllProvable_init : StackAllProvable 0 0 := by
  intro n
  rw [stackGet_zero_zero]
  exact WadeZFProvable.moot

theorem zfClauseDispatch_preserves_provable {topwff wffstack : ℕ}
    (h : StackAllProvable topwff wffstack) (ac p1 p2 p3 : ℕ) :
    let res := zfClauseDispatch topwff wffstack ac p1 p2 p3
    StackAllProvable res.1 res.2 := by
  have hmoot : WadeZFProvable 0 := WadeZFProvable.moot
  have hpush0 : StackAllProvable 0 (cantorPair topwff wffstack) := h.push hmoot
  rcases ac with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ac
  · exact hpush0
  · -- ac = 1 (DET)
    dsimp only [zfClauseDispatch]
    have hpop1 := hpush0.pop
    have hφ : WadeZFProvable (cantorUnpair (cantorPair topwff wffstack)).1 := hpop1.top
    have hpop2 := hpop1.pop
    have hmaj : WadeZFProvable (cantorUnpair (cantorUnpair (cantorPair topwff wffstack)).2).1 :=
      hpop2.top
    split_ifs with hmp
    · rw [← hmp] at hmaj
      have hp1 : WadeZFProvable p1 := WadeZFProvable.mp hφ hmaj
      intro n
      cases n with
      | zero => exact hp1
      | succ n => exact hpop2 (n + 1)
    · intro n
      cases n with
      | zero => exact hmoot
      | succ n => exact hpop2 (n + 1)
  · -- ac = 2 (GEN)
    dsimp only [zfClauseDispatch]
    have hpop1 := hpush0.pop
    have hall : WadeZFProvable (zfAll p1 (cantorUnpair (cantorPair topwff wffstack)).1) :=
      WadeZFProvable.gen p1 hpop1.top
    intro n
    cases n with
    | zero => exact hall
    | succ n => exact hpop1 (n + 1)
  · exact h.push (WadeZFProvable.b1 p1 p2 p3)
  · exact h.push (WadeZFProvable.b2 p1)
  · exact h.push (WadeZFProvable.b3 p1 p2)
  · exact h.push (WadeZFProvable.b4 p1 p2 p3)
  · exact h.push (WadeZFProvable.b6b p1 p2 p3)
  · exact h.push (WadeZFProvable.b8b p1 p2 p3)
  · -- ac = 9 (B6a)
    dsimp only [zfClauseDispatch]
    split_ifs with h6a
    · exact hpush0
    · rcases not_or.mp h6a with ⟨hne1, hne2⟩
      exact h.push (WadeZFProvable.b6a_wade p1 p2 p3 hne1 hne2)
  · exact h.push (WadeZFProvable.b6b (p1 + p3) p2 0)
  · exact h.push (WadeZFProvable.b6c (p1 + p3) p2)
  · exact h.push (WadeZFProvable.b7 (p1 + p3) p2)
  · exact h.push (WadeZFProvable.b8a_zero (p1 + p3) p2)
  · exact h.push (WadeZFProvable.b8b (p1 + p3) p2 0)
  · exact h.push (WadeZFProvable.b8c_zero (p1 + p3) p2)
  · exact h.push WadeZFProvable.ext
  · exact h.push (WadeZFProvable.rep (p1 + p3))
  · exact h.push WadeZFProvable.pow
  · exact h.push WadeZFProvable.uni
  · exact h.push WadeZFProvable.inf

theorem zfMainNext_preserves_provable {c : ZfMainCfg}
    (h : StackAllProvable c.topwff c.wffstack) :
    StackAllProvable (zfMainNext c).topwff (zfMainNext c).wffstack := by
  unfold zfMainNext
  exact zfClauseDispatch_preserves_provable h _ _ _ _

theorem zfMainNSteps_preserves_provable {n : ℕ} {c₁ c₂ : ZfMainCfg}
    (h : StackAllProvable c₁.topwff c₁.wffstack)
    (hsteps : zfMainNSteps n c₁ = some c₂) :
    StackAllProvable c₂.topwff c₂.wffstack := by
  induction n generalizing c₁ with
  | zero =>
    injection hsteps with h'
    subst h'
    exact h
  | succ n ih =>
    unfold zfMainNSteps at hsteps
    rcases hs : zfMainStep c₁ with _ | c'
    · rw [hs] at hsteps; cases hsteps
    · rw [hs, Option.bind_some] at hsteps
      unfold zfMainStep at hs
      split_ifs at hs with h1
      injection hs with hs'
      subst hs'
      exact ih (zfMainNext_preserves_provable h) hsteps

/-- **Soundness of `zfMainStep`**: if `MainLoopHalts`, then `WadeZFInconsistent` holds. -/
theorem wadeZFInconsistent_of_mainLoopHalts (hHalts : MainLoopHalts) : WadeZFInconsistent := by
  obtain ⟨n, c, hn, hnone⟩ := mainLoopHalts_iff_exists_zfMainNSteps.mp hHalts
  have hprov : StackAllProvable c.topwff c.wffstack :=
    zfMainNSteps_preserves_provable stackAllProvable_init hn
  have hnext : StackAllProvable (zfMainNext c).topwff (zfMainNext c).wffstack :=
    zfMainNext_preserves_provable hprov
  unfold zfMainStep at hnone
  split_ifs at hnone with htop1
  have h1 : WadeZFProvable (zfMainNext c).topwff := hnext.top
  rw [htop1] at h1
  exact h1

/-! ## Section 5: Completeness of `zfMainStep` (`WadeZFInconsistent → MainLoopHalts`) -/

/-- A single proof step `(axiomcode, param1, param2, param3)`. -/
abbrev ProofStep := ℕ × ℕ × ℕ × ℕ

/-- Execute a single `ProofStep` on `(topwff, wffstack)`. -/
def execProofStep (s : ProofStep) (p : ℕ × ℕ) : ℕ × ℕ :=
  zfClauseDispatch p.1 p.2 s.1 s.2.1 s.2.2.1 s.2.2.2

/-- Execute a list of `ProofStep`s sequentially on `(topwff, wffstack)`. -/
def execProofList : List ProofStep → ℕ × ℕ → ℕ × ℕ
  | [], p => p
  | s :: rest, p => execProofList rest (execProofStep s p)

@[simp]
theorem execProofList_nil (p : ℕ × ℕ) : execProofList [] p = p := rfl

@[simp]
theorem execProofList_cons (s : ProofStep) (rest : List ProofStep) (p : ℕ × ℕ) :
    execProofList (s :: rest) p = execProofList rest (execProofStep s p) := rfl

@[simp]
theorem execProofList_append (L₁ L₂ : List ProofStep) (p : ℕ × ℕ) :
    execProofList (L₁ ++ L₂) p = execProofList L₂ (execProofList L₁ p) := by
  induction L₁ generalizing p with
  | nil => rfl
  | cons s rest ih => exact ih (execProofStep s p)

/-- By induction on `WadeZFProvable φ`, every provable formula `φ` has a non-empty list of proof
steps `L` that pushes `φ` onto any initial wff-stack `(top, stk)`. -/
theorem exists_proofList_of_wadeZFProvable {φ : ℕ} (h : WadeZFProvable φ) :
    ∃ L : List ProofStep, L ≠ [] ∧
      ∀ top stk : ℕ, execProofList L (top, stk) = (φ, cantorPair top stk) := by
  induction h with
  | moot =>
    exact ⟨[(0, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | @mp φ ψ hφ himp ihφ ihimp =>
    obtain ⟨L_imp, _, himp_eval⟩ := ihimp
    obtain ⟨L_φ, _, hφ_eval⟩ := ihφ
    refine ⟨L_imp ++ L_φ ++ [(1, ψ, 0, 0)], by simp, fun top stk => ?_⟩
    rw [execProofList_append, execProofList_append, himp_eval, hφ_eval]
    simp [execProofStep, zfClauseDispatch]
  | @gen x φ hφ ihφ =>
    obtain ⟨L_φ, _, hφ_eval⟩ := ihφ
    refine ⟨L_φ ++ [(2, x, 0, 0)], by simp, fun top stk => ?_⟩
    rw [execProofList_append, hφ_eval]
    simp [execProofStep, zfClauseDispatch]
  | b1 φ ψ χ =>
    exact ⟨[(3, φ, ψ, χ)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b2 φ =>
    exact ⟨[(4, φ, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b3 φ ψ =>
    exact ⟨[(5, φ, ψ, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b4 x φ ψ =>
    exact ⟨[(6, x, φ, ψ)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b6a_wade x y z hxz hy =>
    refine ⟨[(9, x, y, z)], List.cons_ne_nil _ _, fun top stk => ?_⟩
    have hcond : ¬ (x = z ∨ y = 0) := not_or.mpr ⟨hxz, hy⟩
    simp [execProofList, execProofStep, zfClauseDispatch, hcond]
  | b6b x y φ =>
    exact ⟨[(7, x, y, φ)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b6c x φ =>
    refine ⟨[(11, x, φ, 0)], List.cons_ne_nil _ _, fun top stk => ?_⟩
    simp [execProofList, execProofStep, zfClauseDispatch]
  | b7 x y =>
    refine ⟨[(12, x, y, 0)], List.cons_ne_nil _ _, fun top stk => ?_⟩
    simp [execProofList, execProofStep, zfClauseDispatch]
  | b8a_zero x y =>
    refine ⟨[(13, x, y, 0)], List.cons_ne_nil _ _, fun top stk => ?_⟩
    simp [execProofList, execProofStep, zfClauseDispatch]
  | b8b x y z =>
    exact ⟨[(8, x, y, z)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b8c_zero x y =>
    refine ⟨[(15, x, y, 0)], List.cons_ne_nil _ _, fun top stk => ?_⟩
    simp [execProofList, execProofStep, zfClauseDispatch]
  | ext =>
    exact ⟨[(16, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | rep φ =>
    refine ⟨[(17, φ, 0, 0)], List.cons_ne_nil _ _, fun top stk => ?_⟩
    simp [execProofList, execProofStep, zfClauseDispatch]
  | pow =>
    exact ⟨[(18, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | uni =>
    exact ⟨[(19, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | inf =>
    exact ⟨[(20, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩

/-- Pack a single `ProofStep` and continuation `rest : ℕ` into a `prooflist` value. -/
def packProofStep (s : ProofStep) (rest : ℕ) : ℕ :=
  cantorPair s.1 (cantorPair s.2.1 (cantorPair s.2.2.1 (cantorPair s.2.2.2 rest))) + 1

/-- Encode a list of `ProofStep`s into a single natural number for `prooflist`. -/
def encodeProofList : List ProofStep → ℕ
  | [] => 0
  | s :: rest => packProofStep s (encodeProofList rest)

@[simp]
theorem encodeProofList_nil : encodeProofList [] = 0 := rfl

@[simp]
theorem encodeProofList_cons (s : ProofStep) (rest : List ProofStep) :
    encodeProofList (s :: rest) = packProofStep s (encodeProofList rest) := rfl

theorem zfMainNext_packProofStep (s : ProofStep) (rest np top stk : ℕ) :
    zfMainNext ⟨packProofStep s rest, np, top, stk⟩ =
      ⟨rest, np, (execProofStep s (top, stk)).1, (execProofStep s (top, stk)).2⟩ := by
  unfold zfMainNext
  simp [packProofStep, execProofStep]

theorem zfMainNext_zero_prooflist (P top stk : ℕ) :
    zfMainNext ⟨0, P, top, stk⟩ = zfMainNext ⟨P + 1, P + 1, top, stk⟩ := by
  unfold zfMainNext
  simp

theorem zfMainNext_prooflist_lt {c : ZfMainCfg} (hpos : 0 < c.prooflist) :
    (zfMainNext c).prooflist < c.prooflist ∧ (zfMainNext c).nextproof = c.nextproof := by
  have hne : c.prooflist ≠ 0 := by omega
  simp only [zfMainNext, hne, ↓reduceIte]
  have h1 := cantorUnpair_snd_le (c.prooflist - 1)
  have h2 := cantorUnpair_snd_le (cantorUnpair (c.prooflist - 1)).2
  have h3 := cantorUnpair_snd_le (cantorUnpair (cantorUnpair (c.prooflist - 1)).2).2
  have h4 :=
    cantorUnpair_snd_le (cantorUnpair (cantorUnpair (cantorUnpair (c.prooflist - 1)).2).2).2
  exact ⟨by omega, trivial⟩

/-- If `MainLoopHalts` is false, then `zfMainStep` never halts on any configuration reachable
from `zfMainInit`. -/
private theorem step_some_of_not_halts {n : ℕ} {c : ZfMainCfg}
    (hNotHalts : ¬ MainLoopHalts) (hn : zfMainNSteps n zfMainInit = some c) :
    zfMainStep c = some (zfMainNext c) := by
  rcases hs : zfMainStep c with _ | c'
  · exfalso
    exact hNotHalts (mainLoopHalts_iff_exists_zfMainNSteps.mpr ⟨n, c, hn, hs⟩)
  · unfold zfMainStep at hs
    split_ifs at hs with h1
    exact hs.symm

/-- Under `¬ MainLoopHalts`, any reachable configuration `c` eventually drains `c.prooflist` to `0`
without changing `c.nextproof`. -/
private theorem drain_prooflist_of_not_halts (hNotHalts : ¬ MainLoopHalts) (pl : ℕ) :
    ∀ {n : ℕ} {c : ZfMainCfg},
      zfMainNSteps n zfMainInit = some c →
      c.prooflist = pl →
      ∃ m c',
        zfMainNSteps m zfMainInit = some c' ∧ c'.prooflist = 0 ∧ c'.nextproof = c.nextproof := by
  induction pl using Nat.strong_induction_on with
  | h pl ih =>
    intro n c hn hpl
    by_cases hzero : pl = 0
    · exact ⟨n, c, hn, hpl.trans hzero, rfl⟩
    · have hpos : 0 < c.prooflist := by omega
      have hstep : zfMainStep c = some (zfMainNext c) := step_some_of_not_halts hNotHalts hn
      have hn1 : zfMainNSteps (n + 1) zfMainInit = some (zfMainNext c) :=
        zfMainNSteps_bind_eq hn (by simp [zfMainNSteps, hstep])
      obtain ⟨hlt, hnp⟩ := zfMainNext_prooflist_lt hpos
      rw [hpl] at hlt
      obtain ⟨m, c', hm, hpl', hnp'⟩ := ih (zfMainNext c).prooflist hlt hn1 rfl
      exact ⟨m, c', hm, hpl', hnp'.trans hnp⟩

/-- Under `¬ MainLoopHalts`, for every `N : ℕ`, the machine eventually reaches a configuration `c`
with `c.prooflist = 0` and `c.nextproof = N`. -/
private theorem reaches_nextproof_of_not_halts (hNotHalts : ¬ MainLoopHalts) (N : ℕ) :
    ∃ n c, zfMainNSteps n zfMainInit = some c ∧ c.prooflist = 0 ∧ c.nextproof = N := by
  induction N with
  | zero => exact ⟨0, zfMainInit, rfl, rfl, rfl⟩
  | succ N ih =>
    obtain ⟨n, c, hn, hpl0, hnp⟩ := ih
    have hstep : zfMainStep c = some (zfMainNext c) := step_some_of_not_halts hNotHalts hn
    have hn1 : zfMainNSteps (n + 1) zfMainInit = some (zfMainNext c) :=
      zfMainNSteps_bind_eq hn (by simp [zfMainNSteps, hstep])
    have hnp_next : (zfMainNext c).nextproof = N + 1 := by
      unfold zfMainNext
      simp [hpl0, hnp]
    obtain ⟨m, c', hm, hpl', hnp'⟩ :=
      drain_prooflist_of_not_halts hNotHalts (zfMainNext c).prooflist hn1 rfl
    exact ⟨m, c', hm, hpl', hnp'.trans hnp_next⟩

/-- Under `¬ MainLoopHalts`, executing `encodeProofList L` from a reachable configuration evaluates
`execProofList L` on `(topwff, wffstack)`. -/
private theorem exec_encodeProofList_of_not_halts (hNotHalts : ¬ MainLoopHalts)
    (L : List ProofStep) :
    ∀ {n : ℕ} {np top stk : ℕ},
      zfMainNSteps n zfMainInit = some ⟨encodeProofList L, np, top, stk⟩ →
      zfMainNSteps (n + L.length) zfMainInit =
        some ⟨0, np, (execProofList L (top, stk)).1, (execProofList L (top, stk)).2⟩ := by
  induction L with
  | nil =>
    intro n np top stk hn
    simpa using hn
  | cons s rest ih =>
    intro n np top stk hn
    have hstep : zfMainStep ⟨encodeProofList (s :: rest), np, top, stk⟩ =
        some (zfMainNext ⟨encodeProofList (s :: rest), np, top, stk⟩) :=
      step_some_of_not_halts hNotHalts hn
    rw [encodeProofList_cons, zfMainNext_packProofStep] at hstep
    have hn1 : zfMainNSteps (n + 1) zfMainInit =
        some ⟨encodeProofList rest, np,
          (execProofStep s (top, stk)).1, (execProofStep s (top, stk)).2⟩ :=
      zfMainNSteps_bind_eq hn (by simp [zfMainNSteps, hstep])
    have hrest := ih hn1
    have hlen : n + 1 + rest.length = n + (s :: rest).length := by simp; omega
    rwa [hlen] at hrest

/-- **Completeness of `zfMainStep`**: if `WadeZFInconsistent` holds, then `MainLoopHalts`. -/
theorem mainLoopHalts_of_wadeZFInconsistent (hInc : WadeZFInconsistent) : MainLoopHalts := by
  by_contra hNotHalts
  obtain ⟨L, hL_ne, hL_eval⟩ := exists_proofList_of_wadeZFProvable hInc
  let s₀ : ProofStep := (0, 0, 0, 0)
  let P : ℕ := encodeProofList (s₀ :: L) - 1
  have hP_succ : P + 1 = packProofStep s₀ (encodeProofList L) := by
    simp only [P, encodeProofList_cons, packProofStep]; omega
  obtain ⟨n, c, hn, hpl0, hnp⟩ := reaches_nextproof_of_not_halts hNotHalts P
  have hc_eq : c = ⟨0, P, c.topwff, c.wffstack⟩ := by
    cases c
    dsimp at hpl0 hnp
    subst hpl0 hnp
    rfl
  rw [hc_eq] at hn
  have hstep0 : zfMainStep ⟨0, P, c.topwff, c.wffstack⟩ =
      some (zfMainNext ⟨0, P, c.topwff, c.wffstack⟩) :=
    step_some_of_not_halts hNotHalts hn
  have hnext0 : zfMainNext ⟨0, P, c.topwff, c.wffstack⟩ =
      ⟨encodeProofList L, P + 1, (execProofStep s₀ (c.topwff, c.wffstack)).1,
        (execProofStep s₀ (c.topwff, c.wffstack)).2⟩ := by
    rw [zfMainNext_zero_prooflist, hP_succ]
    exact zfMainNext_packProofStep s₀ (encodeProofList L) (P + 1) c.topwff c.wffstack
  rw [hnext0] at hstep0
  have hn1 : zfMainNSteps (n + 1) zfMainInit =
      some ⟨encodeProofList L, P + 1, (execProofStep s₀ (c.topwff, c.wffstack)).1,
            (execProofStep s₀ (c.topwff, c.wffstack)).2⟩ :=
    zfMainNSteps_bind_eq hn (by simp [zfMainNSteps, hstep0])
  have hL_ne_nil : ∃ LInit sLast, L = LInit ++ [sLast] := by
    refine ⟨L.dropLast, L.getLast hL_ne, (List.dropLast_append_getLast hL_ne).symm⟩
  obtain ⟨LInit, sLast, rfl⟩ := hL_ne_nil
  have hn_all := exec_encodeProofList_of_not_halts hNotHalts (LInit ++ [sLast]) hn1
  rw [hL_eval] at hn_all
  have hlen_split : n + 1 + (LInit ++ [sLast]).length = (n + 1 + LInit.length) + 1 := by
    simp; omega
  rw [hlen_split, zfMainNSteps_add] at hn_all
  rcases hmid : zfMainNSteps (n + 1 + LInit.length) zfMainInit with _ | cmid
  · rw [hmid] at hn_all; cases hn_all
  · rw [hmid, Option.bind_some, zfMainNSteps_succ] at hn_all
    unfold zfMainStep at hn_all
    split_ifs at hn_all with h1
    · cases hn_all
    · simp only [Option.bind_some, zfMainNSteps_zero, Option.some.injEq] at hn_all
      have htop : (zfMainNext cmid).topwff = zfMem 0 0 := by rw [hn_all]
      exact h1 htop

/-- **Main Theorem of Layer 3**: the `zf_432_wade.tm` main loop halts if and only if the
20-clause Hilbert system `WadeZFProvable` is inconsistent (`WadeZFInconsistent`). -/
theorem mainLoopHalts_iff_wadeZFInconsistent :
    MainLoopHalts ↔ WadeZFInconsistent :=
  ⟨wadeZFInconsistent_of_mainLoopHalts, mainLoopHalts_of_wadeZFInconsistent⟩

/-! ## Section 6: 11-Register Bank Subroutine Verification (`zf_432_wade.tm`) -/

/-- Register indices of the 11 registers in `zf_432_wade.tm`. -/
abbrev regProoflist : ℕ := 0
abbrev regNextproof : ℕ := 1
abbrev regTopwff : ℕ := 2
abbrev regWffstack : ℕ := 3
abbrev regAxiomcode : ℕ := 4
abbrev regParam1 : ℕ := 5
abbrev regParam2 : ℕ := 6
abbrev regParam3 : ℕ := 7
abbrev regScratch1 : ℕ := 8
abbrev regScratch2 : ℕ := 9
abbrev regScratch3 : ℕ := 10

/-- Project the 4 persistent registers `(prooflist, nextproof, topwff, wffstack)` from an
11-register bank `regs : List ℕ`. -/
def regsToMainCfg (regs : List ℕ) : ZfMainCfg :=
  ⟨regs.getD 0 0, regs.getD 1 0, regs.getD 2 0, regs.getD 3 0⟩

/-- Embed a `ZfMainCfg` into the canonical 11-register bank with zeroed temporary registers
`4..10`. -/
def mainCfgToRegs (c : ZfMainCfg) : List ℕ :=
  [c.prooflist, c.nextproof, c.topwff, c.wffstack, 0, 0, 0, 0, 0, 0, 0]

@[simp]
theorem mainCfgToRegs_length (c : ZfMainCfg) : (mainCfgToRegs c).length = 11 := rfl

@[simp]
theorem regsToMainCfg_mainCfgToRegs (c : ZfMainCfg) :
    regsToMainCfg (mainCfgToRegs c) = c := by
  cases c; rfl

@[simp]
theorem regsToMainCfg_init :
    regsToMainCfg (List.replicate 11 0) = zfMainInit := rfl

/-- Functional specification of `pair(out, in1, in2)` on an 11-register bank `regs : List ℕ`. -/
def regPairOp (out r1 r2 : ℕ) (regs : List ℕ) : List ℕ :=
  let v1 := regs.getD r1 0
  let v2 := regs.getD r2 0
  let vout := regs.getD out 0
  ((regs.set r1 0).set r2 0).set out (pairLoop vout v1 v2)

theorem regPairOp_eq_cantorPair (out r1 r2 : ℕ) (regs : List ℕ) :
    regPairOp out r1 r2 regs =
      ((regs.set r1 0).set r2 0).set out
        (regs.getD out 0 + cantorPair (regs.getD r1 0) (regs.getD r2 0)) := by
  simp [regPairOp, pairLoop_eq_cantorPair]

/-- Functional specification of `unpair(out1, out2, in)` on an 11-register bank `regs : List ℕ`
when `out1` and `out2` are initially `0`. -/
def regUnpairOp (out1 out2 rin : ℕ) (regs : List ℕ) : List ℕ :=
  let vin := regs.getD rin 0
  let p := unpairLoop vin (0, 0)
  ((regs.set rin 0).set out1 p.1).set out2 p.2

theorem regUnpairOp_eq_cantorUnpair (out1 out2 rin : ℕ) (regs : List ℕ) :
    regUnpairOp out1 out2 rin regs =
      let p := cantorUnpair (regs.getD rin 0)
      ((regs.set rin 0).set out1 p.1).set out2 p.2 := by
  simp [regUnpairOp, unpairLoop_zero_zero]

end ConjectureMachines.Semantics.Zf
