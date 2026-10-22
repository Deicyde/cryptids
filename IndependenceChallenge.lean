/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Challenge
public import Mathlib.ModelTheory.Semantics

/-!
# Independence Challenge Specification (`IndependenceChallenge`)

**Claim.** Whether `zf393` halts is independent of ZFC.

**How it is stated.** By Gödel's completeness theorem, "ZFC proves neither `σ` nor `¬ σ`" is the
same as "some model of ZFC satisfies `σ`, and some model of ZFC satisfies `¬ σ`". This file states
the second form, so the reader never has to decode a proof calculus or a Gödel numbering:

* §1–2 `IsZFC V`: the axioms of ZFC, one Lean field per axiom, for a type `V` with a membership
  relation `x ∈ y`. `Model IsZFC` bundles such a `V`.
* §3 `HaltsIn V M`: `V` contains a halting run of the Turing machine `M`, i.e. `V` thinks `M`
  halts.
* §4 the target:
  `(∃ V : Model IsZFC, HaltsIn V zf393) ∧ (∃ V : Model IsZFC, ¬ HaltsIn V zf393)`.

**Why "first-order" matters, and where it is enforced.** `zf393` really runs forever. A model of
ZFC in which it halts must therefore have *nonstandard* natural numbers, and its run there has
nonstandard length. Such models exist only for *first-order* ZFC, so two things are needed:

* The Separation and Replacement schemas range only over properties that are defined by a
  first-order formula of `{∈}` with parameters (`Definable`, §1), not over all Lean predicates.
  With all Lean predicates every model has the true `ω`, and the first half of the target would
  be false.
* `HaltsIn` quantifies only over elements of `V` and over the finite types `Fin s`, `Fin k`,
  `Turing.Dir`. It never quantifies over Lean's `ℕ`, so it describes runs *inside* `V`, including
  runs of nonstandard length. `haltsIn_firstOrder` states that `HaltsIn V M` is one first-order
  sentence.

**Why this is not vacuous.** Lean can prove `Con(ZF)`, so any statement only about the standard
model would be trivial. The target is not of that kind: its first half asks for a model in which a
machine that does not really halt does halt. For the machine `rightForever` (`0R0 0R0`) no such
model exists, and this is proved below (`rightForever_not_independent_of_ZFC`). The same holds for
`haltOnOne` (`0R0 ---`), and the target is also false for every machine that really halts
(§7, from companion theorems).

**What the proof of each half needs.**

* Easy half (a model of ZFC in which `zf393` runs forever): take `ZFSet`, Mathlib's model of ZFC
  (`easy_half`, from the companions `isZFC_zfSet` and `haltsIn_zfSet_iff` and `Challenge`'s
  `Zf393.not_halts_zf393`).
* Hard half (a model of ZFC in which `zf393` halts):
  * prove, inside every model of ZF without Foundation, that `zf393` halts iff O'Rear's calculus
    is inconsistent;
  * prove Gödel's second incompleteness theorem for O'Rear's calculus;
  * prove a completeness theorem to turn its consistency with "`zf393` halts" into a model
    (Mathlib has none);
  * `zf393` searches ZF *without* Foundation and Choice, so also turn that model into a model of
    ZFC in which `zf393` still halts (for example Gödel's `L` built inside it; halting is
    arithmetical, hence absolute).

  The weaker form `zf393_independent_of_ZF_without_Foundation` (§5) matches the machine's theory
  exactly and skips the last step. It already implies that O'Rear's calculus proves neither
  `⌜zf393 halts⌝` nor its negation (`not_zfProvable_of_independent`), with no completeness theorem.

**Trusted reading.** §1–§4: about 80 lines of code. Everything after §4 is a companion, a
reduction or a control. Companions marked *(open)* have no proof yet. The others are proved for
exactly these definitions in the solution-side proof file.
-/

@[expose] public section

universe u

namespace ConjectureMachines

/-- Tarski satisfaction of a `ZFFormula` (O'Rear's syntax, from `Challenge`) in an `∈`-structure
`(V, E)` under the assignment `v`. Used only in §5 to relate the target to `ZFProvable`. -/
def ZFFormula.HoldsIn {V : Type*} (E : V → V → Prop) (v : ℕ → V) : ZFFormula → Prop
  | .eq x y => v x = v y
  | .mem x y => E (v x) (v y)
  | .imp φ ψ => φ.HoldsIn E v → ψ.HoldsIn E v
  | .not φ => ¬ φ.HoldsIn E v
  | .all x φ => ∀ a : V, φ.HoldsIn E (Function.update v x a)

namespace Independence

open FirstOrder FirstOrder.Language

/-! ## 1. The language `{∈}` and first-order definability -/

/-- The only non-logical symbol of set theory: the binary relation symbol `∈`. -/
inductive SetRel : ℕ → Type
  | mem : SetRel 2

/-- The first-order language of set theory: no function symbols, one binary relation symbol `∈`
(equality is part of the logic). -/
def setLang : Language := ⟨fun _ => Empty, SetRel⟩

/-- A type with a membership relation is a `{∈}`-structure, with the symbol read as `∈`. -/
scoped instance setStructure {V : Type*} [Membership V V] : setLang.Structure V where
  funMap f := Empty.elim f
  RelMap | .mem => fun xs => xs 0 ∈ xs 1

section Definability
variable {V : Type u} [Membership V V]

/-- `P` is **first-order definable with parameters**: for some formula `φ(x₀, x₁, …, xₙ)` of
`{∈}` and some parameters `p₁, …, pₙ ∈ V`, `P x` holds iff `V ⊨ φ(x, p₁, …, pₙ)`. -/
def Definable (P : V → Prop) : Prop :=
  ∃ (n : ℕ) (φ : setLang.Formula (Fin (n + 1))) (p : Fin n → V),
    ∀ x, P x ↔ φ.Realize (Fin.cons x p)

/-- `R` is first-order definable with parameters: `R x y ↔ V ⊨ φ(x, y, p₁, …, pₙ)`. -/
def Definable₂ (R : V → V → Prop) : Prop :=
  ∃ (n : ℕ) (φ : setLang.Formula (Fin (n + 2))) (p : Fin n → V),
    ∀ x y, R x y ↔ φ.Realize (Fin.cons x (Fin.cons y p))

end Definability

/-! ## 2. The axioms of ZFC

The axioms are written with ordinary Lean quantifiers over `V` and the model's own `x ∈ y`. Only
Separation and Replacement are schemas, and they range over `Definable` properties. This is the
first-order theory ZFC (Kunen's list), and every one of its models counts, including models
with nonstandard natural numbers. -/

section Axioms
variable {V : Type u} [Membership V V]

/-- `e = ∅`. -/
def IsEmptySet (e : V) : Prop := ∀ z, z ∉ e

/-- `y = x ∪ {x}` (on natural numbers: `y = x + 1`). -/
def IsSucc (x y : V) : Prop := ∀ z, z ∈ y ↔ z ∈ x ∨ z = x

/-- `w` contains `∅` and is closed under `x ↦ x ∪ {x}`. -/
def IsInductive (w : V) : Prop :=
  (∀ e, IsEmptySet e → e ∈ w) ∧ ∀ x ∈ w, ∀ y, IsSucc x y → y ∈ w

end Axioms

/-- `(V, ∈)` satisfies the axioms of **ZF without Foundation**. This is the theory whose
theorems `zf393` enumerates. O'Rear's `zf2.nql` calculus (`Challenge.ZFProvable`) states
Extensionality, Replacement, Power Set, Union and Infinity in its own forms; Pairing and
Separation are derivable from them. -/
structure IsZFWithoutFoundation (V : Type u) [Membership V V] : Prop where
  extensionality : ∀ x y : V, (∀ z, z ∈ x ↔ z ∈ y) → x = y
  pairing : ∀ x y : V, ∃ p : V, ∀ z, z ∈ p ↔ z = x ∨ z = y
  union : ∀ x : V, ∃ u : V, ∀ z, z ∈ u ↔ ∃ y ∈ x, z ∈ y
  powerset : ∀ x : V, ∃ p : V, ∀ y, y ∈ p ↔ ∀ z ∈ y, z ∈ x
  infinity : ∃ w : V, IsInductive w
  /-- Separation schema: `{z ∈ x | P z}` exists for every definable `P`. -/
  separation : ∀ P : V → Prop, Definable P → ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ z ∈ x ∧ P z
  /-- Replacement schema: the image of a set under a definable class function is contained in
  a set. -/
  replacement : ∀ R : V → V → Prop, Definable₂ R →
    ∀ x : V, (∀ y ∈ x, ∃! z, R y z) → ∃ w : V, ∀ y ∈ x, ∃ z ∈ w, R y z

/-- `(V, ∈)` satisfies the axioms of **ZF**. -/
structure IsZF (V : Type u) [Membership V V] : Prop extends IsZFWithoutFoundation V where
  /-- Foundation: every nonempty set has an `∈`-minimal element. -/
  foundation : ∀ x : V, (∃ y, y ∈ x) → ∃ y ∈ x, ∀ z ∈ y, z ∉ x

/-- `(V, ∈)` satisfies the axioms of **ZFC**. -/
structure IsZFC (V : Type u) [Membership V V] : Prop extends IsZF V where
  /-- Choice: a set of nonempty, pairwise disjoint sets has a set meeting each of them in exactly
  one element. -/
  choice : ∀ x : V, (∀ y ∈ x, ∃ z, z ∈ y) → (∀ y ∈ x, ∀ y' ∈ x, y ≠ y' → ∀ z ∈ y, z ∉ y') →
    ∃ c : V, ∀ y ∈ x, ∃! z, z ∈ y ∧ z ∈ c

/-- A **model** of the set theory `T` (for example `Model IsZFC`): a type of "sets" with a
membership relation, satisfying `T`.

The sets live in `Type 1` because Mathlib's standard model `ZFSet.{0}` lives there. The universe
does not change the meaning of the target: `IsZFC` and `HaltsIn` are first-order, so by
Löwenheim–Skolem a model can be replaced by a countable one satisfying the same sentences, and a
countable model can be moved to any universe with `ULift`. -/
structure Model (T : ∀ (V : Type 1) [Membership V V], Prop) : Type 2 where
  /-- The sets of the model. -/
  Carrier : Type 1
  /-- The membership relation of the model, written `x ∈ y`. -/
  [mem : Membership Carrier Carrier]
  /-- The model satisfies `T`. -/
  sat : T Carrier

instance {T : ∀ (V : Type 1) [Membership V V], Prop} : CoeSort (Model T) (Type 1) :=
  ⟨Model.Carrier⟩

attribute [instance] Model.mem

/-! ## 3. "`M` halts", evaluated inside a model

A run of `M` is a space-time diagram whose times `t = 0, 1, …, N` and tape cells
`x = 0, 1, 2, …` are the natural numbers *of `V`* (von Neumann: `0 = ∅`, `n + 1 = n ∪ {n}`,
and `t < N` means `t ∈ N`). It is recorded by `s + k` sets of ordered pairs:

* `(t, x) ∈ head q`: at time `t` the machine is in state `q` with its head on cell `x`;
* `(t, x) ∈ tape a`: at time `t` cell `x` holds symbol `a`.

Conventions match `Challenge.step`:
* the machine starts in state `0` on the all-`0` tape;
* the entry `some (b, d, q')` writes `b`, then moves in direction `d`, then enters state `q'`;
* the entry `none` halts.

`Challenge`'s tape is two-way infinite. Here the cells are `0, 1, 2, …` and the head starts on
cell `N`, which leaves room for `N` moves to the left. Soundness does not rest on this choice: a
run that moved left from cell `0` would have no head position at the next time, so it could not be
completed. -/

section Halting
variable {V : Type u} [Membership V V]

/-- `n` is a natural number of `V`: it belongs to every inductive set. -/
def IsNat (n : V) : Prop := ∀ w : V, IsInductive w → n ∈ w

/-- `p` is the ordered pair `(x, y) = {{x}, {x, y}}`. -/
def IsOrderedPair (p x y : V) : Prop :=
  ∀ z, z ∈ p ↔ (∀ w, w ∈ z ↔ w = x) ∨ (∀ w, w ∈ z ↔ w = x ∨ w = y)

/-- `(x, y) ∈ r`. -/
def PairIn (x y r : V) : Prop := ∃ p ∈ r, IsOrderedPair p x y

/-- Moving in direction `d` takes the head from cell `x` to cell `y`. -/
def Moves : Turing.Dir → V → V → Prop
  | .left, x, y => IsSucc y x
  | .right, x, y => IsSucc x y

variable {s k : ℕ} [NeZero s] [NeZero k]

/-- `head` and `tape` record a run of `M` from the blank tape that halts at time `N`. Row `0`
is given exactly (`↔`), and so is each row `t + 1` given row `t`. By induction, row `t` is
therefore the configuration after `t` steps. -/
structure IsHaltingRun (M : Machine s k) (N : V) (head : Fin s → V) (tape : Fin k → V) :
    Prop where
  /-- Time `0`: state `0`, head on cell `N`, every cell blank (`0`). -/
  start : ∀ z, IsEmptySet z →
    (∀ q x, PairIn z x (head q) ↔ q = 0 ∧ x = N) ∧
    (∀ x, IsNat x → ∀ a, PairIn z x (tape a) ↔ a = 0)
  /-- From time `t < N` to `t' = t + 1`: in state `q` on cell `x` reading `a`, `M` has the entry
  `(b, d, q')`. At time `t'` it is in state `q'` on the neighbour of `x` in direction `d`, cell
  `x` holds `b`, and every other cell is unchanged. -/
  step : ∀ t ∈ N, ∀ t', IsSucc t t' →
    ∃ (q : Fin s) (x : V) (a b : Fin k) (d : Turing.Dir) (q' : Fin s),
      PairIn t x (head q) ∧ PairIn t x (tape a) ∧ M.transition q a = some (b, d, q') ∧
      (∀ r y, PairIn t' y (head r) ↔ r = q' ∧ Moves d x y) ∧
      (∀ y, IsNat y → ∀ c,
        PairIn t' y (tape c) ↔ (y = x ∧ c = b) ∨ (y ≠ x ∧ PairIn t y (tape c)))
  /-- Time `N`: `M` has no entry for its current state and the symbol under its head. -/
  halt : ∃ (q : Fin s) (x : V) (a : Fin k),
    PairIn N x (head q) ∧ PairIn N x (tape a) ∧ M.transition q a = none

variable (V) in
/-- **`V` thinks that `M` halts**: `V` contains a halting run of `M` from the blank tape, of
some length `N` that is a natural number of `V` (possibly a nonstandard one). -/
def HaltsIn (M : Machine s k) : Prop :=
  ∃ (N : V) (head : Fin s → V) (tape : Fin k → V), IsNat N ∧ IsHaltingRun M N head tape

end Halting

/-! ## 4. Targets

`zf432` is not a target: it enumerates Wade's earlier calculus `WadeZFProvable`, which has no
models, so `zf432` is expected to halt. -/

/-- **`zf393` is independent of ZFC.** Some model of ZFC thinks `zf393` halts, and some model of
ZFC thinks it runs forever. By Gödel's completeness theorem, this says that ZFC proves neither
"`zf393` halts" nor "`zf393` runs forever", where "`zf393` halts" is the first-order sentence
that `HaltsIn` expresses (`haltsIn_firstOrder`). -/
theorem zf393_independent_of_ZFC :
    (∃ V : Model IsZFC, HaltsIn V Machines.zf393) ∧
    (∃ V : Model IsZFC, ¬ HaltsIn V Machines.zf393) := by
  sorry

/-- **`zf380` is independent of ZFC.** -/
theorem zf380_independent_of_ZFC :
    (∃ V : Model IsZFC, HaltsIn V Machines.zf380) ∧
    (∃ V : Model IsZFC, ¬ HaltsIn V Machines.zf380) := by
  sorry

variable {s k : ℕ} [NeZero s] [NeZero k]

/-! ## 5. The theory `zf393` actually searches

`zf393` looks for a contradiction in O'Rear's ZF without Foundation (and without Choice). The form
below is the target for exactly that theory. The ZFC target implies it
(`independent_without_Foundation_of_ZFC`, proved), and it implies the syntactic statement about
O'Rear's calculus (`not_zfProvable_of_independent`, proved from two companions, with no
completeness theorem). -/

/-- `zf393` is independent of ZF without Foundation (weaker than `zf393_independent_of_ZFC`). -/
theorem zf393_independent_of_ZF_without_Foundation :
    (∃ V : Model IsZFWithoutFoundation, HaltsIn V Machines.zf393) ∧
    (∃ V : Model IsZFWithoutFoundation, ¬ HaltsIn V Machines.zf393) := by
  sorry

/-- A model of ZFC is a model of ZF without Foundation. -/
def Model.toZFWithoutFoundation (V : Model IsZFC) : Model IsZFWithoutFoundation where
  Carrier := V.Carrier
  sat := V.sat.toIsZFWithoutFoundation

/-- Independence of ZFC implies independence of ZF without Foundation (proved). -/
theorem independent_without_Foundation_of_ZFC (M : Machine s k)
    (h : (∃ V : Model IsZFC, HaltsIn V M) ∧ (∃ V : Model IsZFC, ¬ HaltsIn V M)) :
    (∃ V : Model IsZFWithoutFoundation, HaltsIn V M) ∧
    (∃ V : Model IsZFWithoutFoundation, ¬ HaltsIn V M) :=
  ⟨⟨h.1.choose.toZFWithoutFoundation, h.1.choose_spec⟩,
    ⟨h.2.choose.toZFWithoutFoundation, h.2.choose_spec⟩⟩

/-- Companion (open): soundness of O'Rear's calculus. Every `ZFProvable` formula holds in every
model of ZF without Foundation. -/
theorem zfProvable_sound {V : Type u} [Membership V V] (hV : IsZFWithoutFoundation V)
    (φ : ZFFormula) (h : ZFProvable φ.code) (v : ℕ → V) : φ.HoldsIn (· ∈ ·) v := by
  sorry

/-- Companion: `HaltsIn V M` is expressed by one formula of O'Rear's syntax, uniformly in every
`∈`-structure. This is `haltsIn_firstOrder` (§6) restated in `ZFFormula` syntax. -/
theorem haltsIn_zfFormula (M : Machine s k) :
    ∃ φ : ZFFormula, ∀ (V : Type u) [Membership V V] (v : ℕ → V),
      φ.HoldsIn (· ∈ ·) v ↔ HaltsIn V M := by
  sorry

/-- The model-theoretic target implies the syntactic one (proved from the two companions above):
O'Rear's calculus proves neither `⌜M halts⌝` nor `⌜M runs forever⌝`. -/
theorem not_zfProvable_of_independent (M : Machine s k)
    (h : (∃ V : Model IsZFWithoutFoundation, HaltsIn V M) ∧
      (∃ V : Model IsZFWithoutFoundation, ¬ HaltsIn V M)) :
    ∃ φ : ZFFormula, (∀ (V : Type 1) [Membership V V] (v : ℕ → V),
        φ.HoldsIn (· ∈ ·) v ↔ HaltsIn V M) ∧
      ¬ ZFProvable φ.code ∧ ¬ ZFProvable (ZFFormula.not φ).code := by
  obtain ⟨φ, hφ⟩ := haltsIn_zfFormula.{1} M
  obtain ⟨⟨V, hV⟩, ⟨W, hW⟩⟩ := h
  obtain ⟨v, -⟩ := V.sat.infinity
  obtain ⟨w, -⟩ := W.sat.infinity
  refine ⟨φ, hφ, fun hp => hW ((hφ W fun _ => w).1 (zfProvable_sound W.sat φ hp _)), fun hp => ?_⟩
  exact zfProvable_sound V.sat _ hp (fun _ => v) ((hφ V fun _ => v).2 hV)

/-! ## 6. Companion theorems: what `IsZFC` and `HaltsIn` mean -/

/-- Mathlib's `ZFSet` is a model of ZFC, so the axioms as written are consistent. -/
theorem isZFC_zfSet : IsZFC ZFSet.{u} := by
  sorry

/-- In the standard model `ZFSet`, `HaltsIn` is `Challenge`'s `Halts`. -/
theorem haltsIn_zfSet_iff (M : Machine s k) :
    HaltsIn ZFSet.{u} M ↔ ConjectureMachines.Halts M := by
  sorry

/-- `HaltsIn V M` is one first-order sentence `σ` of `{∈}`, the same in every `∈`-structure. -/
theorem haltsIn_firstOrder (M : Machine s k) :
    ∃ σ : setLang.Sentence, ∀ (V : Type u) [Membership V V], HaltsIn V M ↔ V ⊨ σ := by
  sorry

/-- Σ₁-completeness (open): a machine that really halts halts in every model of ZF without
Foundation. -/
theorem haltsIn_of_halts {V : Type u} [Membership V V] (hV : IsZFWithoutFoundation V)
    (M : Machine s k) (h : ConjectureMachines.Halts M) : HaltsIn V M := by
  sorry

/-- The easy half of the target, from `Challenge`'s `Zf393.not_halts_zf393`: `ZFSet` is a model
of ZFC in which `zf393` runs forever. -/
theorem easy_half (h : ¬ ConjectureMachines.Halts Machines.zf393) :
    ∃ V : Model IsZFC, ¬ HaltsIn V Machines.zf393 :=
  ⟨⟨ZFSet.{0}, isZFC_zfSet⟩, fun h' => h ((haltsIn_zfSet_iff _).1 h')⟩

/-! ## 7. Negative controls: the target is false for machines that run forever for trivial
reasons -/

/-- `0R0 0R0`: moves right forever. -/
def rightForever : Machine 1 2 := ⟨fun _ _ => some (0, .right, 0)⟩

/-- `0R0 ---`: halts on reading `1`, but only ever writes `0`, so it runs forever. Seeing this
needs induction along the run. -/
def haltOnOne : Machine 1 2 := ⟨fun _ a => if a = 0 then some (0, .right, 0) else none⟩

/-- A machine with no halting entry halts in no `∈`-structure at all (proved). -/
theorem not_haltsIn_of_total (V : Type u) [Membership V V] (M : Machine s k)
    (hM : ∀ q a, (M.transition q a).isSome) : ¬ HaltsIn V M := by
  rintro ⟨N, head, tape, -, run⟩
  obtain ⟨q, x, a, -, -, h⟩ := run.halt
  simpa [h] using hM q a

/-- For any set theory `T`, the target is false for a machine with no halting entry (proved). -/
theorem not_independent_of_total {T : ∀ (V : Type 1) [Membership V V], Prop} (M : Machine s k)
    (hM : ∀ q a, (M.transition q a).isSome) :
    ¬ ((∃ V : Model T, HaltsIn V M) ∧ (∃ V : Model T, ¬ HaltsIn V M)) := by
  rintro ⟨⟨V, hV⟩, -⟩
  exact not_haltsIn_of_total V M hM hV

/-- **Non-vacuity (proved).** The target, stated for `rightForever`, is false. -/
theorem rightForever_not_independent_of_ZFC :
    ¬ ((∃ V : Model IsZFC, HaltsIn V rightForever) ∧
      (∃ V : Model IsZFC, ¬ HaltsIn V rightForever)) :=
  not_independent_of_total rightForever fun _ _ => rfl

/-- Companion: `haltOnOne` halts in no model of ZF without Foundation. The proof uses Separation
for a definable invariant and Infinity to induct along the run. -/
theorem not_haltsIn_haltOnOne {V : Type u} [Membership V V] (hV : IsZFWithoutFoundation V) :
    ¬ HaltsIn V haltOnOne := by
  sorry

/-- The target, stated for `haltOnOne`, is false (from `not_haltsIn_haltOnOne`). -/
theorem haltOnOne_not_independent_of_ZFC :
    ¬ ((∃ V : Model IsZFC, HaltsIn V haltOnOne) ∧
      (∃ V : Model IsZFC, ¬ HaltsIn V haltOnOne)) := by
  rintro ⟨⟨V, hV⟩, -⟩
  exact not_haltsIn_haltOnOne V.sat.toIsZFWithoutFoundation hV

/-- The target is false for every machine that really halts (from `haltsIn_of_halts`). -/
theorem not_independent_of_halts (M : Machine s k) (h : ConjectureMachines.Halts M) :
    ¬ ((∃ V : Model IsZFC, HaltsIn V M) ∧ (∃ V : Model IsZFC, ¬ HaltsIn V M)) := by
  rintro ⟨-, ⟨V, hV⟩⟩
  exact hV (haltsIn_of_halts V.sat.toIsZFWithoutFoundation M h)

end Independence
end ConjectureMachines
