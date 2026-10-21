/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Challenge

/-!
# Independence Challenge Specification (`IndependenceChallenge`)

`Challenge.lean` states `Halts zf393 ↔ ZFInconsistent`. Lean proves both sides false
(`Zf393.not_halts_zf393`, `Semantics.Zf.not_zfInconsistent`), so a biconditional of that shape
holds for *every* machine that Lean proves non-halting, including the one-state machine that moves
right forever. It cannot certify that `zf393` is special.

This file states the claim the ZF machines are meant to witness, in the form Flypitch used for the
continuum hypothesis: ZF proves neither `⌜M halts⌝` nor `⌜M never halts⌝`.

* `haltsSentence M` is one closed sentence of set theory per machine, built uniformly from the
  transition table as a space-time diagram indexed by `ω`.
* `Independent ZFProvable (haltsSentence M)` is *false* for every machine without a halting
  entry, because ZF refutes its halting sentence in pure logic (`not_independent_of_total`). So it
  cannot be proved by appeal to `Con(ZF)`, and no axiom whitelist is needed: proofs may use
  `Classical.choice`.
* The easy half (ZF does not prove `zf393` halts) follows from soundness in `ZFSet.{0}`
  (`not_zfProvable_haltsSentence`). The hard half (ZF does not prove `zf393` runs forever) needs
  Gödel's second incompleteness theorem for ZF and an internal proof of the reduction.

The targets and companion theorems below are open. The reductions at the end are proved in
`Cryptids.Independence` and audited by `comparator/independence.json`.
-/

@[expose] public section
namespace ConjectureMachines

/-- Tarski satisfaction of a `ZFFormula` in an arbitrary `∈`-structure `(V, E)` under the
assignment `v`. `ZFFormula.Holds` is the special case `V = ZFSet`, `E = (· ∈ ·)`. -/
def ZFFormula.HoldsIn {V : Type*} (E : V → V → Prop) (v : ℕ → V) : ZFFormula → Prop
  | .eq x y => v x = v y
  | .mem x y => E (v x) (v y)
  | .imp φ ψ => φ.HoldsIn E v → ψ.HoldsIn E v
  | .not φ => ¬ φ.HoldsIn E v
  | .all x φ => ∀ a : V, φ.HoldsIn E (Function.update v x a)

namespace Independence

/-- `Prov` proves neither `φ` nor `¬ φ` (Flypitch's `independent`). -/
def Independent (Prov : ℕ → Prop) (φ : ZFFormula) : Prop :=
  ¬ Prov φ.code ∧ ¬ Prov (ZFFormula.not φ).code

/-- Completeness of O'Rear's calculus: a formula that holds in every `∈`-structure satisfying
all `ZFProvable` formulas is itself `ZFProvable`. -/
def ZFProvableComplete : Prop :=
  ∀ φ : ZFFormula,
    (∀ (V : Type) (E : V → V → Prop),
      (∀ ψ : ZFFormula, ZFProvable ψ.code → ∀ v : ℕ → V, ψ.HoldsIn E v) →
      ∀ v : ℕ → V, φ.HoldsIn E v) →
    ZFProvable φ.code

/-! ### Capture-free formula builder

An `FB` is a formula waiting for its first unused variable index. A binder takes that index as
its variable and hands the next index to its body, so no variable can be captured. -/

/-- A formula awaiting its first unused variable index. -/
abbrev FB := ℕ → ZFFormula

namespace FB
/-- `x ∈ y`. -/ def mem (x y : ℕ) : FB := fun _ => .mem x y
/-- `x = y`. -/ def eq (x y : ℕ) : FB := fun _ => .eq x y
/-- `φ → ψ`. -/ def imp (φ ψ : FB) : FB := fun n => .imp (φ n) (ψ n)
/-- `¬ φ`. -/ def neg (φ : FB) : FB := fun n => .not (φ n)
/-- `∀ x, φ x`. -/ def all (φ : ℕ → FB) : FB := fun n => .all n (φ n (n + 1))
/-- `∃ x, φ x`. -/ def ex (φ : ℕ → FB) : FB := neg (all fun x => neg (φ x))
/-- `φ ∧ ψ`. -/ def conj (φ ψ : FB) : FB := neg (imp φ (neg ψ))
/-- `φ ∨ ψ`. -/ def disj (φ ψ : FB) : FB := imp (neg φ) ψ
/-- `φ ↔ ψ`. -/ def iff (φ ψ : FB) : FB := conj (imp φ ψ) (imp ψ φ)
/-- `⊤`. -/ def verum : FB := all fun x => eq x x
/-- `⊥`. -/ def falsum : FB := neg verum
/-- Finite conjunction. -/ def conjs (l : List FB) : FB := l.foldr conj verum
/-- Finite disjunction. -/ def disjs (l : List FB) : FB := l.foldr disj falsum
/-- `∀ x ∈ a, φ x`. -/ def allIn (a : ℕ) (φ : ℕ → FB) : FB := all fun x => imp (mem x a) (φ x)
/-- `∃ x ∈ a, φ x`. -/ def exIn (a : ℕ) (φ : ℕ → FB) : FB := ex fun x => conj (mem x a) (φ x)
/-- `∃ x₀ … x_{m-1}, φ x`. -/
def exMany : (m : ℕ) → ((Fin m → ℕ) → FB) → FB
  | 0, φ => φ Fin.elim0
  | m + 1, φ => ex fun x => exMany m fun xs => φ (Fin.cons x xs)
/-- Exactly one of `φ 0, …, φ (m - 1)` holds. -/
def exactlyOne {m : ℕ} (φ : Fin m → FB) : FB :=
  conj (disjs ((List.finRange m).map φ))
    (conjs ((List.finRange m).flatMap fun i => (List.finRange m).map fun j =>
      if i = j then verum else imp (φ i) (neg (φ j))))
end FB

open FB

/-! ### Textbook `∈`-definitions -/

/-- `x = ∅`. -/
def isEmptySet (x : ℕ) : FB := all fun z => neg (mem z x)
/-- `y = x ∪ {x}`. -/
def isSucc (x y : ℕ) : FB := all fun z => iff (mem z y) (disj (mem z x) (eq z x))
/-- `u` contains `∅` and is closed under successor. -/
def isInductive (u : ℕ) : FB :=
  conj (all fun e => imp (isEmptySet e) (mem e u))
    (allIn u fun x => all fun y => imp (isSucc x y) (mem y u))
/-- `w = ω`, the least inductive set (correct without Foundation). -/
def isOmega (w : ℕ) : FB :=
  conj (isInductive w) (all fun u => imp (isInductive u) (allIn w fun x => mem x u))
/-- `p = (x, y) = {{x}, {x, y}}`. -/
def isPair (p x y : ℕ) : FB :=
  all fun z => iff (mem z p)
    (disj (all fun a => iff (mem a z) (eq a x))
      (all fun a => iff (mem a z) (disj (eq a x) (eq a y))))
/-- `(x, y) ∈ r`. -/
def pairIn (x y r : ℕ) : FB := ex fun p => conj (isPair p x y) (mem p r)

/-! ### `⌜M halts⌝` as a space-time diagram

Times and cells are elements of `ω`. In the sentence below, `t ∈ S q` says the machine is in
state `q` at time `t`, `(t, x) ∈ A a` says cell `x` holds symbol `a` at time `t`, and
`(t, x) ∈ Hd` says the head is on cell `x` at time `t`. The head starts on cell `N`, so it never
leaves `ω` during the `N` steps. The machine enters only through `M.transition q a`, inside
finite conjunctions and disjunctions. -/

variable {s k : ℕ} [NeZero s] [NeZero k]

/-- The step from time `t` to `t' = t + 1` when the head is on cell `x` in state `q` reading `a`.
A halting entry gives `⊥`: the machine does not halt before the final time `N`. -/
def stepClause (M : Machine s k) (w : ℕ) (S : Fin s → ℕ) (A : Fin k → ℕ)
    (Hd t t' x : ℕ) (q : Fin s) (a : Fin k) : FB :=
  match M.transition q a with
  | none => falsum
  | some (b, d, q') => conjs
    [ mem t' (S q'),
      pairIn t' x (A b),
      allIn w fun y => imp (neg (eq y x)) <| conjs <| (List.finRange k).map fun c =>
        imp (pairIn t y (A c)) (pairIn t' y (A c)),
      match d with
      | .left => ex fun y => conj (isSucc y x) (pairIn t' y Hd)
      | .right => ex fun y => conj (isSucc x y) (pairIn t' y Hd) ]

/-- `S`, `A`, `Hd` describe a run of `M` from the blank tape up to time `N ∈ w`. -/
def isRun (M : Machine s k) (w N : ℕ) (S : Fin s → ℕ) (A : Fin k → ℕ) (Hd : ℕ) : FB :=
  conjs
    [ all fun z => imp (isEmptySet z) <| conjs
        [mem z (S 0), allIn w fun x => pairIn z x (A 0), pairIn z N Hd],
      allIn w fun t => imp (disj (mem t N) (eq t N)) <| conjs
        [ exactlyOne fun q => mem t (S q),
          allIn w fun x => exactlyOne fun a => pairIn t x (A a),
          allIn w fun x => allIn w fun y =>
            imp (pairIn t x Hd) (imp (pairIn t y Hd) (eq x y)) ],
      allIn N fun t => all fun t' => imp (isSucc t t') <| allIn w fun x =>
        imp (pairIn t x Hd) <| conjs <| (List.finRange s).flatMap fun q =>
          (List.finRange k).map fun a =>
            imp (conj (mem t (S q)) (pairIn t x (A a))) (stepClause M w S A Hd t t' x q a) ]

/-- At time `N` the head reads a symbol for which the current state has no transition. -/
def haltsAt (M : Machine s k) (w N : ℕ) (S : Fin s → ℕ) (A : Fin k → ℕ) (Hd : ℕ) : FB :=
  exIn w fun x => conj (pairIn N x Hd) <| disjs <| (List.finRange s).flatMap fun q =>
    (List.finRange k).map fun a =>
      match M.transition q a with
      | none => conj (mem N (S q)) (pairIn N x (A a))
      | some _ => falsum

/-- `⌜M halts from the blank tape⌝`: one closed sentence of set theory per machine, built the
same way from every transition table. -/
def haltsSentence (M : Machine s k) : ZFFormula :=
  (ex fun w => conj (isOmega w) <| exIn w fun N =>
    exMany s fun S => exMany k fun A => ex fun Hd =>
      conj (isRun M w N S A Hd) (haltsAt M w N S A Hd)) 0

/-- Negative control: the one-state machine `0R0 0R0`, which moves right forever. -/
def rightForever : Machine 1 2 := ⟨fun _ _ => some (0, .right, 0)⟩

/-! ## Targets

The headline theorems. `ZFProvable` is O'Rear's `zf2.nql` calculus, already trusted by
`Challenge.lean`; `zf432` is measured against the same calculus so that all three statements are
about one object theory. -/

/-- ZF proves neither that `zf393` halts nor that it runs forever. -/
theorem zf393_independent : Independent ZFProvable (haltsSentence Machines.zf393) := by sorry
/-- ZF proves neither that `zf380` halts nor that it runs forever. -/
theorem zf380_independent : Independent ZFProvable (haltsSentence Machines.zf380) := by sorry
/-- ZF proves neither that `zf432` halts nor that it runs forever. -/
theorem zf432_independent : Independent ZFProvable (haltsSentence Machines.zf432) := by sorry

/-! ## Companion theorems

These pin down what `haltsSentence` and `ZFProvable` mean. A reviewer still has to read the
definitions above (as with Flypitch's `CH_f`); the companions catch transcription errors. -/

/-- The sentence says exactly that `M` halts, in the standard model. -/
theorem haltsSentence_holds_iff (M : Machine s k) (v : ℕ → ZFSet.{0}) :
    (haltsSentence M).Holds v ↔ ConjectureMachines.Halts M := by sorry
/-- ZF proves the sentence for every machine that halts (Σ₁-completeness). -/
theorem zfProvable_haltsSentence (M : Machine s k) (h : ConjectureMachines.Halts M) :
    ZFProvable (haltsSentence M).code := by sorry
/-- O'Rear's calculus is complete. -/
theorem zfProvable_complete : ZFProvableComplete := by sorry

/-! ## Reductions proved today (`Cryptids.Independence`) -/

/-- A machine with no halting entry provably never halts, in pure logic: its halting sentence
fails in every `∈`-structure. -/
theorem not_holdsIn_haltsSentence_of_total (M : Machine s k)
    (hM : ∀ q a, (M.transition q a).isSome) {V : Type} (E : V → V → Prop) (v : ℕ → V) :
    ¬ (haltsSentence M).HoldsIn E v := by
  sorry

/-- Non-vacuity: if `ZFProvable` is complete, the independence statement is *false* for every
machine without a halting entry. -/
theorem not_independent_of_total (hc : ZFProvableComplete) (M : Machine s k)
    (hM : ∀ q a, (M.transition q a).isSome) :
    ¬ Independent ZFProvable (haltsSentence M) := by
  sorry

/-- In particular it is false for `rightForever`, which `Halts M ↔ ZFInconsistent` cannot rule
out once Lean proves `¬ ZFInconsistent`. -/
theorem not_independent_rightForever (hc : ZFProvableComplete) :
    ¬ Independent ZFProvable (haltsSentence rightForever) := by
  sorry

/-- The easy half, given the first companion theorem: ZF does not prove that a non-halting
machine halts. This uses soundness of `ZFProvable` in `ZFSet.{0}` (Lean's own `Con(ZF)`), which
is legitimate here because the claim is about derivations, not a biconditional. -/
theorem not_zfProvable_haltsSentence (M : Machine s k)
    (h₁ : ∀ v : ℕ → ZFSet.{0}, (haltsSentence M).Holds v ↔ ConjectureMachines.Halts M)
    (hM : ¬ ConjectureMachines.Halts M) :
    ¬ ZFProvable (haltsSentence M).code := by
  sorry

/-- Given the first companion theorem, independence of `zf393` is exactly the hard half: ZF does
not prove that `zf393` runs forever. -/
theorem zf393_independent_iff
    (h₁ : ∀ v : ℕ → ZFSet.{0},
      (haltsSentence Machines.zf393).Holds v ↔ ConjectureMachines.Halts Machines.zf393) :
    Independent ZFProvable (haltsSentence Machines.zf393) ↔
      ¬ ZFProvable (ZFFormula.not (haltsSentence Machines.zf393)).code := by
  sorry

end Independence
end ConjectureMachines
