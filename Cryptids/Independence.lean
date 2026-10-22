/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Propositions
public import Mathlib.ModelTheory.Semantics

/-!
# Independence of the ZF Machines (`Cryptids.Independence`)

Solution-side mirror of `IndependenceChallenge`. The statement definitions (§1–§3: `setLang`,
`Definable`, `IsZFC`, `Model`, `HaltsIn`) are copied verbatim from the challenge, as
`Cryptids.Machines` mirrors `Challenge`; the proof machinery sits between §4 and §5.

Proved here, for exactly those definitions:

* `isZFC_zfSet`: Mathlib's `ZFSet` satisfies `IsZFC`.
* `haltsIn_zfSet_iff`: in `ZFSet`, `HaltsIn` is `Challenge`'s `Halts`.
* `haltsIn_firstOrder`, `haltsIn_zfFormula`: `HaltsIn V M` is one first-order sentence of `{∈}`
  (and one `ZFFormula`), the same in every `∈`-structure.
* `not_haltsIn_haltOnOne`: `haltOnOne` halts in no model of ZF without Foundation.
* The reductions and controls `easy_half`, `independent_without_Foundation_of_ZFC`,
  `not_independent_of_total`, `rightForever_not_independent_of_ZFC`,
  `haltOnOne_not_independent_of_ZFC`.

The targets, the open companions `zfProvable_sound` and `haltsIn_of_halts`, and the two
reductions that use them (`not_zfProvable_of_independent`, `not_independent_of_halts`) are left
out, so this module has no `sorry`.
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

variable {s k : ℕ} [NeZero s] [NeZero k]


/-! ## Proof machinery (proof file only; not part of the statement) -/

section FO

/-- `P` is expressed by one and the same formula of `{∈}` in every `∈`-structure. -/
class FO {α : Type} (P : ∀ (V : Type u) [Membership V V], (α → V) → Prop) : Prop where
  out : ∃ φ : setLang.Formula α, ∀ (V : Type u) [Membership V V] (v : α → V), P V v ↔ φ.Realize v

instance (priority := high) FO.const {α : Type} (p : Prop) :
    FO.{u} (α := α) fun (V : Type u) [Membership V V] (_ : α → V) => p := by
  by_cases hp : p
  · exact ⟨⊤, by simp [hp]⟩
  · exact ⟨⊥, by simp [hp]⟩

instance FO.mem {α : Type} (i j : α) :
    FO.{u} fun (V : Type u) [Membership V V] (v : α → V) => v i ∈ v j :=
  ⟨⟨Relations.formula₂ (SetRel.mem : setLang.Relations 2) (Term.var i) (Term.var j),
    fun _ _ _ => Iff.rfl⟩⟩

instance FO.eq {α : Type} (i j : α) :
    FO.{u} fun (V : Type u) [Membership V V] (v : α → V) => v i = v j :=
  ⟨⟨Term.equal (Term.var i) (Term.var j), fun _ _ _ => by simp⟩⟩

instance FO.and {α : Type} {P Q : ∀ (V : Type u) [Membership V V], (α → V) → Prop}
    [hP : FO P] [hQ : FO Q] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => P V v ∧ Q V v := by
  obtain ⟨φ, hφ⟩ := hP.out; obtain ⟨ψ, hψ⟩ := hQ.out
  exact ⟨⟨φ ⊓ ψ, fun V _ v => by simp [hφ, hψ]⟩⟩

instance FO.or {α : Type} {P Q : ∀ (V : Type u) [Membership V V], (α → V) → Prop}
    [hP : FO P] [hQ : FO Q] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => P V v ∨ Q V v := by
  obtain ⟨φ, hφ⟩ := hP.out; obtain ⟨ψ, hψ⟩ := hQ.out
  exact ⟨⟨φ ⊔ ψ, fun V _ v => by simp [hφ, hψ]⟩⟩

instance FO.not {α : Type} {P : ∀ (V : Type u) [Membership V V], (α → V) → Prop}
    [hP : FO P] : FO fun (V : Type u) [Membership V V] (v : α → V) => ¬ P V v := by
  obtain ⟨φ, hφ⟩ := hP.out
  exact ⟨⟨φ.not, fun V _ v => by simp [hφ]⟩⟩

instance FO.imp {α : Type} {P Q : ∀ (V : Type u) [Membership V V], (α → V) → Prop}
    [hP : FO P] [hQ : FO Q] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => P V v → Q V v := by
  obtain ⟨φ, hφ⟩ := hP.out; obtain ⟨ψ, hψ⟩ := hQ.out
  exact ⟨⟨φ.imp ψ, fun V _ v => by simp [hφ, hψ]⟩⟩

instance FO.iff {α : Type} {P Q : ∀ (V : Type u) [Membership V V], (α → V) → Prop}
    [hP : FO P] [hQ : FO Q] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => P V v ↔ Q V v := by
  obtain ⟨φ, hφ⟩ := hP.out; obtain ⟨ψ, hψ⟩ := hQ.out
  exact ⟨⟨φ.iff ψ, fun V _ v => by simp [hφ, hψ]⟩⟩

instance FO.ne {α : Type} (i j : α) :
    FO.{u} fun (V : Type u) [Membership V V] (v : α → V) => v i ≠ v j :=
  FO.not (P := fun (V : Type u) [Membership V V] (v : α → V) => v i = v j)

instance FO.exists {α : Type} {P : ∀ (V : Type u) [Membership V V], (α → V) → V → Prop}
    [h : FO fun (V : Type u) [Membership V V] (w : α ⊕ Unit → V) =>
      P V (fun i => w (Sum.inl i)) (w (Sum.inr ()))] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => ∃ x, P V v x := by
  obtain ⟨φ, hφ⟩ := h.out
  refine ⟨⟨φ.iExs Unit, fun V _ v => ?_⟩⟩
  simp only [Formula.realize_iExs, ← hφ, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩, fun ⟨u, hu⟩ => ⟨u (), hu⟩⟩

instance FO.forall {α : Type} {P : ∀ (V : Type u) [Membership V V], (α → V) → V → Prop}
    [h : FO fun (V : Type u) [Membership V V] (w : α ⊕ Unit → V) =>
      P V (fun i => w (Sum.inl i)) (w (Sum.inr ()))] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => ∀ x, P V v x := by
  obtain ⟨φ, hφ⟩ := h.out
  refine ⟨⟨φ.iAlls Unit, fun V _ v => ?_⟩⟩
  simp only [Formula.realize_iAlls, ← hφ, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun hx u => hx (u ()), fun hu x => hu fun _ => x⟩

instance FO.existsTuple {α β : Type} [Finite β]
    {P : ∀ (V : Type u) [Membership V V], (α → V) → (β → V) → Prop}
    [h : FO fun (V : Type u) [Membership V V] (w : α ⊕ β → V) =>
      P V (fun i => w (Sum.inl i)) (fun j => w (Sum.inr j))] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => ∃ f : β → V, P V v f := by
  obtain ⟨φ, hφ⟩ := h.out
  refine ⟨⟨φ.iExs β, fun V _ v => ?_⟩⟩
  simp only [Formula.realize_iExs, ← hφ, Sum.elim_inl, Sum.elim_inr]

instance FO.forallFinite {α : Type} {ι : Type*} [Finite ι]
    {P : ∀ (V : Type u) [Membership V V], (α → V) → ι → Prop}
    [h : ∀ i, FO fun (V : Type u) [Membership V V] (v : α → V) => P V v i] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => ∀ i, P V v i := by
  choose φ hφ using fun i => (h i).out
  exact ⟨⟨Formula.iInf φ, fun V _ v => by simp [hφ]⟩⟩

instance FO.existsFinite {α : Type} {ι : Type*} [Finite ι]
    {P : ∀ (V : Type u) [Membership V V], (α → V) → ι → Prop}
    [h : ∀ i, FO fun (V : Type u) [Membership V V] (v : α → V) => P V v i] :
    FO fun (V : Type u) [Membership V V] (v : α → V) => ∃ i, P V v i := by
  choose φ hφ using fun i => (h i).out
  exact ⟨⟨Formula.iSup φ, fun V _ v => by simp [hφ]⟩⟩

instance : Finite Turing.Dir :=
  Finite.of_surjective (fun b : Bool => if b then Turing.Dir.left else .right)
    (by intro d; cases d; exacts [⟨true, rfl⟩, ⟨false, rfl⟩])

instance FO.isEmptySet {α : Type} (i : α) :
    FO.{u} fun (V : Type u) [Membership V V] (v : α → V) => IsEmptySet (v i) := by
  unfold IsEmptySet; infer_instance

instance FO.isSucc {α : Type} (i j : α) :
    FO.{u} fun (V : Type u) [Membership V V] (v : α → V) => IsSucc (v i) (v j) := by
  unfold IsSucc; infer_instance

instance FO.isNat {α : Type} (i : α) :
    FO.{u} fun (V : Type u) [Membership V V] (v : α → V) => IsNat (v i) := by
  unfold IsNat IsInductive; infer_instance

instance FO.pairIn {α : Type} (i j l : α) :
    FO.{u} fun (V : Type u) [Membership V V] (v : α → V) => PairIn (v i) (v j) (v l) := by
  unfold PairIn IsOrderedPair; infer_instance

instance FO.moves {α : Type} (d : Turing.Dir) (i j : α) :
    FO.{u} fun (V : Type u) [Membership V V] (v : α → V) => Moves d (v i) (v j) := by
  cases d
  · exact FO.isSucc.{u} j i
  · exact FO.isSucc.{u} i j

end FO

section RunIff
variable {V : Type u} [Membership V V]

/-- `IsHaltingRun` as a plain conjunction (so that the `FO` instances can see through it). -/
theorem isHaltingRun_iff (M : Machine s k) (N : V) (head : Fin s → V) (tape : Fin k → V) :
    IsHaltingRun M N head tape ↔
      (∀ z, IsEmptySet z →
        (∀ q x, PairIn z x (head q) ↔ q = 0 ∧ x = N) ∧
        (∀ x, IsNat x → ∀ a, PairIn z x (tape a) ↔ a = 0)) ∧
      (∀ t ∈ N, ∀ t', IsSucc t t' →
        ∃ (q : Fin s) (x : V) (a b : Fin k) (d : Turing.Dir) (q' : Fin s),
          PairIn t x (head q) ∧ PairIn t x (tape a) ∧ M.transition q a = some (b, d, q') ∧
          (∀ r y, PairIn t' y (head r) ↔ r = q' ∧ Moves d x y) ∧
          (∀ y, IsNat y → ∀ c,
            PairIn t' y (tape c) ↔ (y = x ∧ c = b) ∨ (y ≠ x ∧ PairIn t y (tape c)))) ∧
      (∃ (q : Fin s) (x : V) (a : Fin k),
        PairIn N x (head q) ∧ PairIn N x (tape a) ∧ M.transition q a = none) :=
  ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

end RunIff

section ToZF

/-- Variable index of a term of `{∈}` (a variable, since `{∈}` has no function symbols). -/
def termIdx {n : ℕ} : setLang.Term (Empty ⊕ Fin n) → ℕ
  | .var (.inl e) => e.elim
  | .var (.inr i) => i
  | .func f _ => (f : Empty).elim

/-- Translation of a `{∈}`-formula into O'Rear's syntax; bound variable `i` becomes `vᵢ`. -/
def toZF : ∀ {n : ℕ}, setLang.BoundedFormula Empty n → ZFFormula
  | _, .falsum => .not (.eq 0 0)
  | _, .equal t₁ t₂ => .eq (termIdx t₁) (termIdx t₂)
  | _, .rel .mem ts => .mem (termIdx (ts 0)) (termIdx (ts 1))
  | _, .imp φ ψ => .imp (toZF φ) (toZF ψ)
  | n, .all φ => .all n (toZF φ)

variable {V : Type u} [Membership V V]

theorem realize_termIdx {n : ℕ} (t : setLang.Term (Empty ⊕ Fin n)) (v : Empty → V)
    (xs : Fin n → V) (w : ℕ → V) (hw : ∀ i : Fin n, w i = xs i) :
    t.realize (Sum.elim v xs) = w (termIdx t) := by
  cases t with
  | var a =>
    cases a with
    | inl e => exact e.elim
    | inr i => simp [termIdx, hw]
  | func f _ => exact (f : Empty).elim

theorem realize_toZF : ∀ {n : ℕ} (φ : setLang.BoundedFormula Empty n) (v : Empty → V)
    (xs : Fin n → V) (w : ℕ → V), (∀ i : Fin n, w i = xs i) →
    (φ.Realize v xs ↔ (toZF φ).HoldsIn (· ∈ ·) w)
  | _, .falsum, v, xs, w, hw => by simp [toZF, ZFFormula.HoldsIn, BoundedFormula.Realize]
  | _, .equal t₁ t₂, v, xs, w, hw => by
    simp only [toZF, ZFFormula.HoldsIn, BoundedFormula.Realize, realize_termIdx _ v xs w hw]
  | _, .rel .mem ts, v, xs, w, hw => by
    change (ts 0).realize (Sum.elim v xs) ∈ (ts 1).realize (Sum.elim v xs) ↔ _
    rw [realize_termIdx _ v xs w hw, realize_termIdx _ v xs w hw]; rfl
  | _, .imp φ ψ, v, xs, w, hw => by
    simp only [toZF, ZFFormula.HoldsIn, BoundedFormula.Realize, realize_toZF φ v xs w hw,
      realize_toZF ψ v xs w hw]
  | n, .all φ, v, xs, w, hw => by
    simp only [toZF, ZFFormula.HoldsIn, BoundedFormula.Realize]
    refine forall_congr' fun a => realize_toZF φ v (Fin.snoc xs a) (Function.update w n a) ?_
    intro i
    by_cases h : (i : ℕ) = n
    · have : i = Fin.last n := Fin.ext h
      subst this; simp
    · have hi : (i : ℕ) < n := lt_of_le_of_ne (Nat.lt_succ_iff.1 i.2) h
      obtain ⟨j, rfl⟩ : ∃ j : Fin n, j.castSucc = i := ⟨⟨i, hi⟩, rfl⟩
      rw [Fin.snoc_castSucc, Fin.val_castSucc, Function.update_of_ne (by simpa using h), hw]

end ToZF

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search assembles the defining formula of `HaltsIn` clause by clause, which needs a
-- larger instance budget than the default.
set_option synthInstance.maxSize 2000 in
theorem haltsIn_firstOrder_aux (M : Machine s k) :
    ∃ σ : setLang.Sentence, ∀ (V : Type u) [Membership V V], HaltsIn V M ↔ V ⊨ σ := by
  have h : FO.{u} (α := Empty) fun (V : Type u) [Membership V V] (_ : Empty → V) =>
      HaltsIn V M := by
    simp only [HaltsIn, isHaltingRun_iff]
    infer_instance
  obtain ⟨φ, hφ⟩ := h.out
  exact ⟨φ, fun V _ => hφ V default⟩

section ZFSetModel

/-! ### Natural numbers and pairs in `ZFSet` -/

/-- The von Neumann numeral `n` in `ZFSet`. -/
def vN : ℕ → ZFSet.{u}
  | 0 => ∅
  | n + 1 => insert (vN n) (vN n)

theorem mem_vN {x : ZFSet.{u}} {n : ℕ} : x ∈ vN n ↔ ∃ m < n, x = vN m := by
  induction n with
  | zero => simp [vN, ZFSet.notMem_empty]
  | succ n ih =>
    rw [vN, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (rfl | ⟨m, hm, rfl⟩)
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · exact ⟨m, Nat.lt_succ_of_lt hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
      · exact Or.inr ⟨m, h, rfl⟩
      · exact Or.inl rfl

theorem vN_injective : Function.Injective vN.{u} := by
  intro m n h
  by_contra hmn
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hlt
  · have : vN.{u} m ∈ vN n := mem_vN.2 ⟨m, hlt, rfl⟩
    rw [← h] at this; exact ZFSet.mem_irrefl _ this
  · have : vN.{u} n ∈ vN m := mem_vN.2 ⟨n, hlt, rfl⟩
    rw [h] at this; exact ZFSet.mem_irrefl _ this

theorem vN_inj {m n : ℕ} : vN.{u} m = vN n ↔ m = n := vN_injective.eq_iff

theorem vN_mem_vN {m n : ℕ} : vN.{u} m ∈ vN n ↔ m < n := by
  rw [mem_vN]
  constructor
  · rintro ⟨m', hm', h⟩; rw [vN_inj] at h; omega
  · intro h; exact ⟨m, h, rfl⟩

theorem isEmptySet_iff {e : ZFSet.{u}} : IsEmptySet e ↔ e = vN 0 := by
  rw [vN, ZFSet.eq_empty]; rfl

theorem isSucc_iff {x y : ZFSet.{u}} : IsSucc x y ↔ y = insert x x := by
  rw [ZFSet.ext_iff]
  simp only [IsSucc, ZFSet.mem_insert_iff, or_comm]

theorem isSucc_vN_left {n : ℕ} {y : ZFSet.{u}} : IsSucc (vN n) y ↔ y = vN (n + 1) := by
  rw [isSucc_iff]; rfl

theorem isSucc_vN_right {n : ℕ} {y : ZFSet.{u}} :
    IsSucc y (vN n) ↔ ∃ m, n = m + 1 ∧ y = vN m := by
  constructor
  · intro h
    obtain ⟨m, -, rfl⟩ := mem_vN.1 ((h y).2 (Or.inr rfl))
    refine ⟨m, ?_, rfl⟩
    rw [isSucc_vN_left, vN_inj] at h; omega
  · rintro ⟨m, rfl, rfl⟩; exact isSucc_vN_left.2 rfl

theorem isNat_vN (n : ℕ) : IsNat (vN.{u} n) := by
  intro w ⟨h0, hs⟩
  induction n with
  | zero => exact h0 _ (isEmptySet_iff.2 rfl)
  | succ n ih => exact hs _ ih _ (isSucc_vN_left.2 rfl)

theorem isNat_iff {x : ZFSet.{u}} : IsNat x ↔ ∃ n, x = vN n := by
  refine ⟨fun hx => ?_, fun ⟨n, h⟩ => h ▸ isNat_vN n⟩
  have := hx (ZFSet.sep (fun x => ∃ n, x = vN n) ZFSet.omega) ⟨?_, ?_⟩
  · exact (ZFSet.mem_sep.1 this).2
  · intro e he; rw [isEmptySet_iff] at he; subst he
    exact ZFSet.mem_sep.2 ⟨ZFSet.omega_zero, 0, rfl⟩
  · intro x hx y hy
    obtain ⟨hxo, n, rfl⟩ := ZFSet.mem_sep.1 hx
    rw [isSucc_vN_left] at hy; subst hy
    exact ZFSet.mem_sep.2 ⟨ZFSet.omega_succ hxo, n + 1, rfl⟩

theorem eq_singleton_iff' {z x : ZFSet.{u}} : z = {x} ↔ ∀ w, w ∈ z ↔ w = x := by
  rw [ZFSet.ext_iff]; simp only [ZFSet.mem_singleton]

theorem eq_pair_iff' {z x y : ZFSet.{u}} : z = {x, y} ↔ ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  rw [ZFSet.ext_iff]; simp only [ZFSet.mem_pair]

theorem pairIn_iff {x y r : ZFSet.{u}} : PairIn x y r ↔ ZFSet.pair x y ∈ r := by
  have key : ∀ p : ZFSet.{u}, (∀ z, z ∈ p ↔ (∀ w, w ∈ z ↔ w = x) ∨ (∀ w, w ∈ z ↔ w = x ∨ w = y))
      ↔ p = ZFSet.pair x y := by
    intro p
    rw [ZFSet.ext_iff]
    simp only [ZFSet.pair, ZFSet.mem_pair, eq_singleton_iff', eq_pair_iff']
  simp only [PairIn, IsOrderedPair, key]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro h; exact ⟨_, h, rfl⟩

/-- The set of pairs `(m, j)` of numerals with `P (m, j)`. -/
noncomputable def pairsOf (P : ℕ × ℕ → Prop) : ZFSet.{u} :=
  ZFSet.range fun i : {mj : ℕ × ℕ // P mj} => ZFSet.pair (vN i.1.1) (vN i.1.2)

theorem pairIn_pairsOf {P : ℕ × ℕ → Prop} {x y : ZFSet.{u}} :
    PairIn x y (pairsOf P) ↔ ∃ m j, x = vN m ∧ y = vN j ∧ P (m, j) := by
  rw [pairIn_iff, pairsOf, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨m, j⟩, hP⟩, h⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 h
    exact ⟨m, j, rfl, rfl, hP⟩
  · rintro ⟨m, j, rfl, rfl, hP⟩
    exact ⟨⟨(m, j), hP⟩, rfl⟩

theorem pairIn_vN_pairsOf {P : ℕ × ℕ → Prop} {m j : ℕ} :
    PairIn (vN.{u} m) (vN j) (pairsOf P) ↔ P (m, j) := by
  rw [pairIn_pairsOf]
  constructor
  · rintro ⟨m', j', h1, h2, hP⟩
    rw [vN_inj] at h1 h2; subst h1; subst h2; exact hP
  · intro hP; exact ⟨m, j, rfl, rfl, hP⟩

/-! ### Runs of `M` with the head position -/

open StateTransition

theorem blank_nth (i : ℤ) : (Turing.Tape.mk₁ ([] : List (Fin k))).nth i = 0 := by
  rcases i with (_ | n) | n <;>
    simp [Turing.Tape.nth, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk',
      Turing.ListBlank.nth_mk]

omit [NeZero s] in
theorem step_eq (M : Machine s k) (c : Cfg s k) :
    step M c = (M.transition c.state c.tape.head).map
      fun r => ⟨r.2.2, (c.tape.write r.1).move r.2.1⟩ := by
  obtain ⟨q, T⟩ := c; rfl

/-- `+1` for a move to the right, `-1` for a move to the left. -/
def dirOffset : Turing.Dir → ℤ
  | .left => -1
  | .right => 1

theorem nth_move (T : Turing.Tape (Fin k)) (d : Turing.Dir) (i : ℤ) :
    (T.move d).nth i = T.nth (i + dirOffset d) := by
  cases d
  · simp [dirOffset, sub_eq_add_neg]
  · simp [dirOffset]

/-- One step of `M`, also tracking the absolute head position. -/
def stepPos (M : Machine s k) (cp : Cfg s k × ℤ) : Option (Cfg s k × ℤ) :=
  (M.transition cp.1.state cp.1.tape.head).map fun r =>
    (⟨r.2.2, (cp.1.tape.write r.1).move r.2.1⟩, cp.2 + dirOffset r.2.1)

/-- Configuration and head position after `t` steps (`none` after a halt). -/
def arun (M : Machine s k) : ℕ → Option (Cfg s k × ℤ)
  | 0 => some (init, 0)
  | t + 1 => (arun M t).bind (stepPos M)

omit [NeZero s] in
theorem stepPos_eq_some {M : Machine s k} {c c' : Cfg s k} {p p' : ℤ}
    (h : stepPos M (c, p) = some (c', p')) : ∃ b d q',
      M.transition c.state c.tape.head = some (b, d, q') ∧
      c' = ⟨q', (c.tape.write b).move d⟩ ∧ p' = p + dirOffset d := by
  unfold stepPos at h
  cases ht : M.transition c.state c.tape.head with
  | none => simp [ht] at h
  | some r =>
    obtain ⟨b, d, q'⟩ := r
    simp only [ht, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨b, d, q', rfl, h.1.symm, h.2.symm⟩

theorem arun_succ_eq_some {M : Machine s k} {t : ℕ} {c' : Cfg s k} {p' : ℤ}
    (h : arun M (t + 1) = some (c', p')) :
    ∃ c p, arun M t = some (c, p) ∧ stepPos M (c, p) = some (c', p') := by
  simp only [arun, Option.bind_eq_some_iff] at h
  obtain ⟨⟨c, p⟩, h1, h2⟩ := h
  exact ⟨c, p, h1, h2⟩

theorem arun_bounds (M : Machine s k) :
    ∀ t c p, arun M t = some (c, p) → -(t : ℤ) ≤ p ∧ p ≤ t
  | 0, c, p, h => by simp [arun] at h; omega
  | t + 1, c', p', h => by
    obtain ⟨c, p, h1, h2⟩ := arun_succ_eq_some h
    obtain ⟨-, d, -, -, -, rfl⟩ := stepPos_eq_some h2
    have := arun_bounds M t c p h1
    cases d <;> simp [dirOffset] <;> omega

theorem arun_isSome_of_le (M : Machine s k) {m n : ℕ} (hmn : m ≤ n)
    (h : (arun M n).isSome) : (arun M m).isSome := by
  induction n with
  | zero => obtain rfl : m = 0 := by omega
            exact h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hmn) with h' | rfl
    · apply ih (by omega)
      obtain ⟨⟨c', p'⟩, hc⟩ := Option.isSome_iff_exists.1 h
      obtain ⟨c, p, h1, -⟩ := arun_succ_eq_some hc
      simp [h1]
    · exact h

theorem halts_iff_arun (M : Machine s k) : ConjectureMachines.Halts M ↔
    ∃ n c p, arun M n = some (c, p) ∧ M.transition c.state c.tape.head = none := by
  have reach : ∀ c, Reaches (step M) init c ↔ ∃ n p, arun M n = some (c, p) := by
    intro c
    constructor
    · intro h
      induction h with
      | refl => exact ⟨0, 0, rfl⟩
      | @tail b c _ hbc ih =>
        obtain ⟨n, p, hn⟩ := ih
        have hs := Option.mem_def.1 hbc
        rw [step_eq, Option.map_eq_some_iff] at hs
        obtain ⟨⟨b', d, q'⟩, ht, rfl⟩ := hs
        refine ⟨n + 1, p + dirOffset d, ?_⟩
        simp [arun, hn, stepPos, ht]
    · rintro ⟨n, p, hn⟩
      induction n generalizing c p with
      | zero =>
        simp only [arun, Option.some.injEq, Prod.mk.injEq] at hn
        obtain ⟨rfl, rfl⟩ := hn
        exact Relation.ReflTransGen.refl
      | succ n ih =>
        obtain ⟨b, p0, h1, h2⟩ := arun_succ_eq_some hn
        obtain ⟨b', d, q', ht, rfl, -⟩ := stepPos_eq_some h2
        refine Relation.ReflTransGen.tail (ih b p0 h1) ?_
        show _ ∈ step M b
        rw [step_eq, ht]; rfl
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Part.dom_iff_mem.1 h
    obtain ⟨hreach, hnone⟩ := mem_eval.1 hc
    obtain ⟨n, p, hn⟩ := (reach c).1 hreach
    rw [step_eq, Option.map_eq_none_iff] at hnone
    exact ⟨n, c, p, hn, hnone⟩
  · rintro ⟨n, c, p, hn, hnone⟩
    refine Part.dom_iff_mem.2 ⟨c, mem_eval.2 ⟨(reach c).2 ⟨n, p, hn⟩, ?_⟩⟩
    rw [step_eq, hnone]; rfl

/-! ### Soundness: a diagram in `ZFSet` is a real run -/

theorem halts_of_haltsIn_zfSet (M : Machine s k) (h : HaltsIn ZFSet.{u} M) :
    ConjectureMachines.Halts M := by
  obtain ⟨N, head, tape, hN, hstart, hstep, hhalt⟩ := h
  obtain ⟨n, rfl⟩ := isNat_iff.1 hN
  -- every row up to `n` has a head
  have hasHead : ∀ m ≤ n, ∃ q y, PairIn (vN.{u} m) y (head q) := by
    intro m hm
    rcases Nat.lt_or_eq_of_le hm with hm | rfl
    · obtain ⟨q, x, -, -, -, -, h, -⟩ :=
        hstep (vN m) (vN_mem_vN.2 hm) (vN (m + 1)) (isSucc_vN_left.2 rfl)
      exact ⟨q, x, h⟩
    · obtain ⟨q, x, -, h, -⟩ := hhalt; exact ⟨q, x, h⟩
  -- row `m` is the configuration `c` with the head on cell `x`
  have key : ∀ m ≤ n, ∃ (c : Cfg s k) (x : ℕ), Reaches (step M) init c ∧
      (∀ r y, PairIn (vN.{u} m) y (head r) ↔ r = c.state ∧ y = vN x) ∧
      (∀ j a, PairIn (vN.{u} m) (vN j) (tape a) ↔ c.tape.nth ((j : ℤ) - x) = a) := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨hh, ht⟩ := hstart (vN 0) (isEmptySet_iff.2 rfl)
      refine ⟨init, n, Relation.ReflTransGen.refl, fun r y => hh r y, fun j a => ?_⟩
      rw [ht _ (isNat_vN j), init, blank_nth, eq_comm]
    | succ m ih =>
      intro hm
      obtain ⟨c, x, hreach, hhd, htp⟩ := ih (by omega)
      obtain ⟨q, x0, a, b, d, q', hq, ha, htr, hhd', htp'⟩ :=
        hstep (vN m) (vN_mem_vN.2 (by omega)) (vN (m + 1)) (isSucc_vN_left.2 rfl)
      obtain ⟨rfl, rfl⟩ := (hhd q x0).1 hq
      have ha' : c.tape.head = a := by simpa using (htp x a).1 ha
      subst ha'
      have hs : step M c = some ⟨q', (c.tape.write b).move d⟩ := by
        rw [step_eq, htr]; rfl
      -- the new head cell
      obtain ⟨x', hx', hmv⟩ : ∃ x' : ℕ, (x' : ℤ) = x + dirOffset d ∧
          ∀ y, Moves d (vN.{u} x) y ↔ y = vN x' := by
        cases d with
        | right => exact ⟨x + 1, by simp [dirOffset], fun y => isSucc_vN_left⟩
        | left =>
          rcases x with _ | x
          · exfalso
            obtain ⟨r, y, hy⟩ := hasHead (m + 1) hm
            obtain ⟨-, hy⟩ := (hhd' r y).1 hy
            obtain ⟨m', hm', -⟩ := isSucc_vN_right.1 hy
            omega
          · refine ⟨x, by simp [dirOffset], fun y => ?_⟩
            change IsSucc y (vN (x + 1)) ↔ _
            rw [isSucc_vN_right]
            constructor
            · rintro ⟨m', hm', rfl⟩; rw [show m' = x by omega]
            · rintro rfl; exact ⟨x, rfl, rfl⟩
      refine ⟨⟨q', (c.tape.write b).move d⟩, x', Relation.ReflTransGen.tail hreach hs,
        fun r y => by rw [hhd' r y, hmv], fun j e => ?_⟩
      rw [htp' _ (isNat_vN j), htp, vN_inj, nth_move, Turing.Tape.write_nth]
      have : (j : ℤ) - x' + dirOffset d = j - x := by omega
      rw [this]
      by_cases hj : j = x
      · subst hj; simp [eq_comm]
      · have : (j : ℤ) - x ≠ 0 := by omega
        simp [hj, this, vN_inj]
  obtain ⟨c, x, hreach, hhd, htp⟩ := key n le_rfl
  obtain ⟨q, y, a, hq, ha, htr⟩ := hhalt
  obtain ⟨rfl, rfl⟩ := (hhd q y).1 hq
  have ha' : c.tape.head = a := by simpa using (htp x a).1 ha
  subst ha'
  refine Part.dom_iff_mem.2 ⟨c, mem_eval.2 ⟨hreach, ?_⟩⟩
  rw [step_eq, htr]; rfl

/-! ### Completeness: a real halting run gives a diagram in `ZFSet` -/

/-- Pairs `(t, x)`: at time `t ≤ n` the head is on cell `x = n + p` in state `q`. -/
def headPairs (M : Machine s k) (n : ℕ) (q : Fin s) (mj : ℕ × ℕ) : Prop :=
  mj.1 ≤ n ∧ ∃ c p, arun M mj.1 = some (c, p) ∧ c.state = q ∧ (mj.2 : ℤ) = n + p

/-- Pairs `(t, x)`: at time `t ≤ n` cell `x` holds `a`. -/
def tapePairs (M : Machine s k) (n : ℕ) (a : Fin k) (mj : ℕ × ℕ) : Prop :=
  mj.1 ≤ n ∧ ∃ c p, arun M mj.1 = some (c, p) ∧ c.tape.nth ((mj.2 : ℤ) - n - p) = a

theorem headPairs_iff {M : Machine s k} {n m j : ℕ} {q : Fin s} {c : Cfg s k} {p : ℤ}
    (h : arun M m = some (c, p)) :
    headPairs M n q (m, j) ↔ m ≤ n ∧ c.state = q ∧ (j : ℤ) = n + p := by
  unfold headPairs
  constructor
  · rintro ⟨hm, c', p', h', hq, hj⟩
    rw [h] at h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨hm, hq, hj⟩
  · rintro ⟨hm, hq, hj⟩; exact ⟨hm, c, p, h, hq, hj⟩

theorem tapePairs_iff {M : Machine s k} {n m j : ℕ} {a : Fin k} {c : Cfg s k} {p : ℤ}
    (h : arun M m = some (c, p)) :
    tapePairs M n a (m, j) ↔ m ≤ n ∧ c.tape.nth ((j : ℤ) - n - p) = a := by
  unfold tapePairs
  constructor
  · rintro ⟨hm, c', p', h', ha⟩
    rw [h] at h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨hm, ha⟩
  · rintro ⟨hm, ha⟩; exact ⟨hm, c, p, h, ha⟩

theorem haltsIn_zfSet_of_halts (M : Machine s k) (h : ConjectureMachines.Halts M) :
    HaltsIn ZFSet.{u} M := by
  obtain ⟨n, cN, pN, hN, hhaltN⟩ := (halts_iff_arun M).1 h
  have hsome : ∀ m ≤ n, ∃ c p, arun M m = some (c, p) := by
    intro m hm
    obtain ⟨⟨c, p⟩, hc⟩ := Option.isSome_iff_exists.1
      (arun_isSome_of_le M hm (by simp [hN]))
    exact ⟨c, p, hc⟩
  have h0 : arun M 0 = some (init, 0) := rfl
  refine ⟨vN n, fun q => pairsOf (headPairs M n q), fun a => pairsOf (tapePairs M n a),
    isNat_vN n, ?_, ?_, ?_⟩
  · -- time `0`
    intro z hz
    rw [isEmptySet_iff] at hz; subst hz
    refine ⟨fun q y => ?_, fun x hx a => ?_⟩
    · rw [pairIn_pairsOf]
      constructor
      · rintro ⟨m, j, hm, rfl, hP⟩
        rw [vN_inj] at hm; subst hm
        obtain ⟨-, hq, hj⟩ := (headPairs_iff h0).1 hP
        refine ⟨hq.symm, ?_⟩
        rw [vN_inj]; omega
      · rintro ⟨rfl, rfl⟩
        exact ⟨0, n, rfl, rfl, (headPairs_iff h0).2 ⟨Nat.zero_le _, rfl, by simp⟩⟩
    · obtain ⟨j, rfl⟩ := isNat_iff.1 hx
      rw [pairIn_vN_pairsOf, tapePairs_iff h0]
      change (0 ≤ n ∧ (Turing.Tape.mk₁ []).nth _ = a) ↔ a = 0
      rw [blank_nth]
      exact ⟨fun h => h.2.symm, fun h => ⟨Nat.zero_le _, h.symm⟩⟩
  · -- from time `t < n` to `t + 1`
    intro t ht t' ht'
    obtain ⟨m, hm, rfl⟩ := mem_vN.1 ht
    rw [isSucc_vN_left] at ht'; subst ht'
    have hm1 : m + 1 ≤ n := hm
    obtain ⟨c', p', h'⟩ := hsome (m + 1) hm1
    obtain ⟨c, p, h1, h2⟩ := arun_succ_eq_some h'
    obtain ⟨b, d, q', htr, rfl, rfl⟩ := stepPos_eq_some h2
    have hb := arun_bounds M m c p h1
    obtain ⟨X, hX⟩ : ∃ X : ℕ, (X : ℤ) = n + p := ⟨(n + p).toNat, by omega⟩
    refine ⟨c.state, vN X, c.tape.head, b, d, q', ?_, ?_, htr, fun r y => ?_, fun y hy e => ?_⟩
    · rw [pairIn_vN_pairsOf, headPairs_iff h1]; exact ⟨hm.le, rfl, hX⟩
    · rw [pairIn_vN_pairsOf, tapePairs_iff h1]
      refine ⟨hm.le, ?_⟩
      rw [show (X : ℤ) - n - p = 0 by omega]; rfl
    · rw [pairIn_pairsOf]
      constructor
      · rintro ⟨m', j, hm', rfl, hP⟩
        rw [vN_inj] at hm'; subst hm'
        obtain ⟨-, hq, hj⟩ := (headPairs_iff h').1 hP
        refine ⟨hq.symm, ?_⟩
        cases d with
        | right =>
          change IsSucc (vN X) (vN j)
          rw [isSucc_vN_left, vN_inj]; simp only [dirOffset] at hj; omega
        | left =>
          change IsSucc (vN j) (vN X)
          rw [isSucc_vN_right]; refine ⟨j, ?_, rfl⟩; simp only [dirOffset] at hj; omega
      · rintro ⟨rfl, hmv⟩
        cases d with
        | right =>
          rw [show Moves .right (vN X) y = IsSucc (vN X) y from rfl, isSucc_vN_left] at hmv
          subst hmv
          exact ⟨m + 1, X + 1, rfl, rfl,
            (headPairs_iff h').2 ⟨hm1, rfl, by simp only [dirOffset]; push_cast; omega⟩⟩
        | left =>
          rw [show Moves .left (vN X) y = IsSucc y (vN X) from rfl, isSucc_vN_right] at hmv
          obtain ⟨j, hj, rfl⟩ := hmv
          exact ⟨m + 1, j, rfl, rfl,
            (headPairs_iff h').2 ⟨hm1, rfl, by simp only [dirOffset]; omega⟩⟩
    · obtain ⟨j, rfl⟩ := isNat_iff.1 hy
      rw [pairIn_vN_pairsOf, pairIn_vN_pairsOf, tapePairs_iff h', tapePairs_iff h1]
      simp only [vN_inj, ne_eq]
      show (m + 1 ≤ n ∧ ((c.tape.write b).move d).nth ((j : ℤ) - n - (p + dirOffset d)) = e) ↔ _
      rw [nth_move, Turing.Tape.write_nth,
        show (j : ℤ) - n - (p + dirOffset d) + dirOffset d = j - n - p by ring]
      by_cases hj : j = X
      · have h0 : (X : ℤ) - n - p = 0 := by omega
        simp only [hj, h0, ↓reduceIte]
        simp [hm1, eq_comm]
      · have h0 : ¬ ((j : ℤ) - n - p = 0) := by omega
        simp [h0, hj, hm1, hm.le]
  · -- time `n`
    have hb := arun_bounds M n cN pN hN
    obtain ⟨X, hX⟩ : ∃ X : ℕ, (X : ℤ) = n + pN := ⟨(n + pN).toNat, by omega⟩
    refine ⟨cN.state, vN X, cN.tape.head, ?_, ?_, hhaltN⟩
    · rw [pairIn_vN_pairsOf, headPairs_iff hN]; exact ⟨le_rfl, rfl, hX⟩
    · rw [pairIn_vN_pairsOf, tapePairs_iff hN]
      refine ⟨le_rfl, ?_⟩
      rw [show (X : ℤ) - n - pN = 0 by omega]; rfl

end ZFSetModel

section HaltOnOne

/-- Infinity and Separation (first-order, with parameters): the part of ZF used below. -/
structure InfSep (V : Type u) [Membership V V] : Prop where
  infinity : ∃ w : V, IsInductive w
  separation : ∀ {β : Type} [Finite β] (φ : setLang.Formula (Unit ⊕ β)) (b : β → V) (x : V),
    ∃ y : V, ∀ z, z ∈ y ↔ z ∈ x ∧ φ.Realize (Sum.elim (fun _ => z) b)

variable {V : Type u} [Membership V V]

theorem IsNat.of_isEmptySet {e : V} (he : IsEmptySet e) : IsNat e := fun _ hw => hw.1 e he

theorem IsNat.succ {x y : V} (hx : IsNat x) (hy : IsSucc x y) : IsNat y :=
  fun w hw => hw.2 x (hx w hw) y hy

/-- Induction over the natural numbers of `V`, for a first-order property with parameters `b`. -/
theorem InfSep.induction (hV : InfSep V) {β : Type} [Finite β]
    (P : ∀ (W : Type u) [Membership W W], (Unit ⊕ β → W) → Prop) [hP : FO P] (b : β → V)
    (h0 : ∀ e, IsEmptySet e → P V (Sum.elim (fun _ => e) b))
    (hs : ∀ x y, IsNat x → P V (Sum.elim (fun _ => x) b) → IsSucc x y →
      P V (Sum.elim (fun _ => y) b)) :
    ∀ n, IsNat n → P V (Sum.elim (fun _ => n) b) := by
  have hQ : FO.{u} fun (W : Type u) [Membership W W] (v : Unit ⊕ β → W) =>
      IsNat (v (Sum.inl ())) ∧ P W v := inferInstance
  obtain ⟨φ, hφ⟩ := hQ.out
  obtain ⟨w, hw0, hws⟩ := hV.infinity
  obtain ⟨u, hu⟩ := hV.separation φ b w
  have hu' : ∀ z, z ∈ u ↔ z ∈ w ∧ IsNat z ∧ P V (Sum.elim (fun _ => z) b) := fun z => by
    rw [hu, ← hφ]; rfl
  intro n hn
  have hnu : n ∈ u := hn u ⟨fun e he => (hu' e).2 ⟨hw0 e he, IsNat.of_isEmptySet he, h0 e he⟩,
    fun x hx y hy => by
      obtain ⟨hxw, hxn, hxP⟩ := (hu' x).1 hx
      exact (hu' y).2 ⟨hws x hxw y hy, hxn.succ hy, hs x y hxn hxP hy⟩⟩
  exact ((hu' n).1 hnu).2.2

/-- Natural numbers are transitive sets. -/
theorem InfSep.isNat_trans (hV : InfSep V) :
    ∀ n : V, IsNat n → ∀ a ∈ n, ∀ c ∈ a, c ∈ n :=
  hV.induction (β := Empty)
    (fun (W : Type u) [Membership W W] (v : Unit ⊕ Empty → W) =>
      ∀ a ∈ v (Sum.inl ()), ∀ c ∈ a, c ∈ v (Sum.inl ())) Empty.elim
    (fun e he a ha => absurd ha (he a))
    (fun x y _ ih hy a ha c hc => by
      rcases (hy a).1 ha with ha | rfl
      · exact (hy c).2 (Or.inl (ih a ha c hc))
      · exact (hy c).2 (Or.inl hc))



/-- A formula with parameters defines a `Definable` property. -/
theorem definable_of_formula {β : Type} [Finite β]
    (φ : setLang.Formula (Unit ⊕ β)) (b : β → V) :
    Definable fun z => φ.Realize (Sum.elim (fun _ => z) b) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin β
  refine ⟨n, φ.relabel (Sum.elim (fun _ : Unit => (0 : Fin (n + 1))) fun j => (e j).succ),
    b ∘ e.symm, fun z => ?_⟩
  rw [Formula.realize_relabel]
  have : (Fin.cons z (b ∘ e.symm) : Fin (n + 1) → V) ∘
      Sum.elim (fun _ : Unit => (0 : Fin (n + 1))) (fun j => (e j).succ) =
      Sum.elim (fun _ : Unit => z) b := by
    funext i; rcases i with _ | j <;> simp
  rw [this]

theorem IsZFWithoutFoundation.toInfSep (h : IsZFWithoutFoundation V) : InfSep V :=
  ⟨h.infinity, fun φ b x => h.separation _ (definable_of_formula φ b) x⟩

end HaltOnOne

/-! ## 5. The theory `zf393` actually searches

`zf393` looks for a contradiction in O'Rear's ZF without Foundation (and without Choice). The form
below is the target for exactly that theory. The ZFC target implies it
(`independent_without_Foundation_of_ZFC`, proved), and it implies the syntactic statement about
O'Rear's calculus (`not_zfProvable_of_independent`, proved from two companions, with no
completeness theorem). -/

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

/-- Companion: `HaltsIn V M` is expressed by one formula of O'Rear's syntax, uniformly in every
`∈`-structure. This is `haltsIn_firstOrder` (§6) restated in `ZFFormula` syntax. -/
theorem haltsIn_zfFormula (M : Machine s k) :
    ∃ φ : ZFFormula, ∀ (V : Type u) [Membership V V] (v : ℕ → V),
      φ.HoldsIn (· ∈ ·) v ↔ HaltsIn V M := by
  obtain ⟨σ, hσ⟩ := haltsIn_firstOrder_aux.{u} M
  exact ⟨toZF σ, fun V _ v =>
    ((hσ V).trans (realize_toZF σ default default v fun i => i.elim0)).symm⟩

/-! ## 6. Companion theorems: what `IsZFC` and `HaltsIn` mean -/

/-- Mathlib's `ZFSet` is a model of ZFC, so the axioms as written are consistent. -/
theorem isZFC_zfSet : IsZFC ZFSet.{u} where
  extensionality x y h := ZFSet.ext h
  foundation x := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hm, hmx⟩ := ZFSet.regularity x (fun h => by simp [h] at hy)
    refine ⟨m, hm, fun z hz hzx => ?_⟩
    have : z ∈ x ∩ m := ZFSet.mem_inter.2 ⟨hzx, hz⟩
    simp [hmx] at this
  pairing x y := ⟨{x, y}, fun z => by simp⟩
  union x := ⟨ZFSet.sUnion x, fun z => by simp⟩
  powerset x := ⟨ZFSet.powerset x, fun y => by simp [ZFSet.subset_def]⟩
  infinity := by
    refine ⟨ZFSet.omega, fun e he => ?_, fun x hx y hy => ?_⟩
    · have : e = ∅ := (ZFSet.eq_empty e).2 he
      exact this ▸ ZFSet.omega_zero
    · have : y = insert x x := ZFSet.ext fun z => by rw [hy z]; simp [or_comm]
      exact this ▸ ZFSet.omega_succ hx
  separation P _ x := ⟨ZFSet.sep P x, fun z => by simp⟩
  replacement R _ x h := by
    refine ⟨ZFSet.range fun y : x => (h y.1 y.2).exists.choose, fun y hy => ?_⟩
    exact ⟨_, ZFSet.mem_range_self ⟨y, hy⟩, (h y hy).exists.choose_spec⟩
  choice x hne hdisj := by
    refine ⟨ZFSet.range fun y : x => (hne y.1 y.2).choose, fun y hy => ?_⟩
    refine ⟨(hne y hy).choose, ⟨(hne y hy).choose_spec, ZFSet.mem_range.2 ⟨⟨y, hy⟩, rfl⟩⟩, ?_⟩
    rintro z ⟨hzy, hzc⟩
    obtain ⟨i, hi⟩ := ZFSet.mem_range.1 hzc
    obtain ⟨y', hy'⟩ := i
    subst hi
    by_cases hyy : y = y'
    · subst hyy; rfl
    · exact absurd (hne y' hy').choose_spec (hdisj y hy y' hy' hyy _ hzy)

/-- In the standard model `ZFSet`, `HaltsIn` is `Challenge`'s `Halts`. -/
theorem haltsIn_zfSet_iff (M : Machine s k) :
    HaltsIn ZFSet.{u} M ↔ ConjectureMachines.Halts M :=
  ⟨halts_of_haltsIn_zfSet M, haltsIn_zfSet_of_halts M⟩

/-- `HaltsIn V M` is one first-order sentence `σ` of `{∈}`, the same in every `∈`-structure. -/
theorem haltsIn_firstOrder (M : Machine s k) :
    ∃ σ : setLang.Sentence, ∀ (V : Type u) [Membership V V], HaltsIn V M ↔ V ⊨ σ :=
  haltsIn_firstOrder_aux M

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
  have hV := hV.toInfSep
  rintro ⟨N, head, tape, hN, hstart, hstep, hhalt⟩
  -- invariant at every time `t ≤ N`: all cells hold `0`, and the head is on a natural number
  have key := hV.induction (β := Fin 4)
    (fun (W : Type u) [Membership W W] (v : Unit ⊕ Fin 4 → W) =>
      (v (.inl ()) ∈ v (.inr 0) ∨ v (.inl ()) = v (.inr 0)) →
        (∀ x, IsNat x → PairIn (v (.inl ())) x (v (.inr 2)) ∧
          ¬ PairIn (v (.inl ())) x (v (.inr 3))) ∧
        ∀ y, PairIn (v (.inl ())) y (v (.inr 1)) → IsNat y)
    ![N, head 0, tape 0, tape 1] ?_ ?_
  · obtain ⟨q, x, a, hq, ha, htr⟩ := hhalt
    obtain ⟨hcells, hheads⟩ := key N hN (Or.inr rfl)
    have hq0 : q = 0 := Subsingleton.elim _ _
    subst hq0
    have ha1 : a = 1 := by
      revert htr; fin_cases a <;> simp [haltOnOne]
    subst ha1
    exact (hcells x (hheads x hq)).2 ha
  · -- time `0`
    intro e he _
    dsimp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val]
    obtain ⟨hh, ht⟩ := hstart e he
    refine ⟨fun x hx => ⟨(ht x hx 0).2 rfl, fun h => absurd ((ht x hx 1).1 h) (by decide)⟩,
      fun y hy => ?_⟩
    obtain ⟨-, rfl⟩ := (hh 0 y).1 hy
    exact hN
  · -- from `t` to `t' = t + 1`
    intro t t' _ ih hsucc ht'
    dsimp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val] at ih ht' ⊢
    have htN : t ∈ N := by
      rcases ht' with h | h
      · exact hV.isNat_trans N hN t' h t ((hsucc t).2 (Or.inr rfl))
      · rw [← h]; exact (hsucc t).2 (Or.inr rfl)
    obtain ⟨hcells, hheads⟩ := ih (Or.inl htN)
    obtain ⟨q, x, a, b, d, q', hq, ha, htr, hh', ht'⟩ := hstep t htN t' hsucc
    have hq0 : q = 0 := Subsingleton.elim _ _
    subst hq0
    have hxn : IsNat x := hheads x hq
    have ha0 : a = 0 := by
      by_contra hne
      have : a = 1 := by omega
      exact (hcells x hxn).2 (this ▸ ha)
    subst ha0
    simp only [haltOnOne, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at htr
    obtain ⟨rfl, rfl, rfl⟩ := htr
    refine ⟨fun y hy => ⟨?_, ?_⟩, fun y hy => ?_⟩
    · rw [ht' y hy 0]
      by_cases hyx : y = x
      · exact Or.inl ⟨hyx, rfl⟩
      · exact Or.inr ⟨hyx, (hcells y hy).1⟩
    · rw [ht' y hy 1]
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact absurd h (by decide)
      · exact (hcells y hy).2 h
    · obtain ⟨-, hmv⟩ := (hh' 0 y).1 hy
      exact hxn.succ hmv


/-- The target, stated for `haltOnOne`, is false (from `not_haltsIn_haltOnOne`). -/
theorem haltOnOne_not_independent_of_ZFC :
    ¬ ((∃ V : Model IsZFC, HaltsIn V haltOnOne) ∧
      (∃ V : Model IsZFC, ¬ HaltsIn V haltOnOne)) := by
  rintro ⟨⟨V, hV⟩, -⟩
  exact not_haltsIn_haltOnOne V.sat.toIsZFWithoutFoundation hV

end Independence
end ConjectureMachines
