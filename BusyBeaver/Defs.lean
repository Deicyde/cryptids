/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic

/-!
# Busy Beaver Holdout Definitions (`BusyBeaver.Defs`)

Canonical Post-Turing machine execution model and behavioral goal predicates for Busy Beaver
holdouts:

- `IsHalt` — `M` eventually reaches a halting configuration from the blank tape (`init []`).
- `IsNotHalt` (`IsDoesNotHalt`) — `M` never halts from the blank tape.
- `HasCollatzReduction` — `M` is governed by a closed accelerated regular-expression tape pattern
  set.
- `HasStackedCollatzReduction` — `M` is governed by a closed accelerated stack-word tape pattern
  set.
-/

@[expose] public section

namespace BusyBeaver

open Relation Turing

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- A Turing machine statement writing `symbol` and moving the tape head in direction `dir`. -/
structure Stmt (Γ : Type*) where
  /-- Construct a write-and-move statement. -/
  write ::
  /-- Symbol written to the tape cell under the head. -/
  symbol : Γ
  /-- Direction in which the tape head moves after writing. -/
  dir : Dir
  deriving Inhabited

/-- A Post-Turing machine with symbol type `Γ` and state label type `Λ`. -/
@[nolint unusedArguments]
def Machine (Γ Λ : Type*) [Inhabited Λ] :=
  Λ → Γ → Option (Option Λ × Stmt Γ)

omit [Inhabited Γ] in
instance Machine.inhabited : Inhabited (Machine Γ Λ) := by
  unfold Machine; infer_instance

/-- Instantaneous configuration of a Turing machine: optional control state `q` and `tape`. -/
@[ext]
structure Cfg (Γ Λ : Type*) [Inhabited Γ] where
  /-- Current control state (`none` represents an explicit terminal state). -/
  q : Option Λ
  /-- Current doubly-infinite tape centered at the head. -/
  tape : Tape Γ

instance Cfg.inhabited : Inhabited (Cfg Γ Λ) := ⟨⟨default, default⟩⟩

/-- Configuration in state `q` with the tape head reading the first symbol of `r`. -/
def Cfg.headRight {Γ Λ : Type*} [Inhabited Γ] (q : Λ) (l r : ListBlank Γ) : Cfg Γ Λ :=
  ⟨some q, ⟨r.head, l, r.tail⟩⟩

/-- Configuration in state `q` with the tape head reading the first symbol of `l`. -/
def Cfg.headLeft {Γ Λ : Type*} [Inhabited Γ] (q : Λ) (l r : ListBlank Γ) : Cfg Γ Λ :=
  ⟨some q, ⟨l.head, l.tail, r⟩⟩

/-- Single-step execution semantics of a `BusyBeaver.Machine`. -/
def step (M : Machine Γ Λ) : Cfg Γ Λ → Option (Cfg Γ Λ)
  | ⟨none, _⟩ => none
  | ⟨some q, T⟩ =>
    (M q T.1).map fun ⟨q', a⟩ ↦
      ⟨q', match a with | Stmt.write a d => (T.write a).move d⟩

/-- Initial configuration on tape prefix `l` (all-blank tape when `l = []`). -/
def init (l : List Γ) : Cfg Γ Λ := ⟨some default, Tape.mk₁ l⟩

/-- Multi-step execution semantics (`n` steps). -/
def multiStep (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) : Option (Cfg Γ Λ) :=
  (Option.bind · (step M))^[n] config

/-- Exact `n`-step reachability (`multiStep M c₁ n = some c₂`). -/
def ReachesIn (M : Machine Γ Λ) (n : ℕ) (c₁ c₂ : Cfg Γ Λ) : Prop :=
  multiStep M c₁ n = some c₂

/-- Reflexive-transitive multi-step reachability (`∃ n, multiStep M c₁ n = some c₂`). -/
def ReachesStar (M : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) : Prop :=
  ∃ n, multiStep M c₁ n = some c₂

/-- Non-empty transitive multi-step reachability (`∃ n > 0, multiStep M c₁ n = some c₂`). -/
def ReachesPlus (M : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) : Prop :=
  ∃ n > 0, multiStep M c₁ n = some c₂

/-- Repeat finite list `l` `n` times (`l ^ n`). -/
instance instHPowListNat : HPow (List Γ) ℕ (List Γ) :=
  ⟨fun l n => (List.replicate n l).flatten⟩

/-- A configuration is halting for `M` if no next transition is defined. -/
def IsHaltingConfiguration (M : Machine Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  (step M cfg).isNone

/-- `M` eventually reaches a halting configuration when started on the blank tape (`init []`). -/
def IsHalt (M : Machine Γ Λ) : Prop :=
  ∃ cfg : Cfg Γ Λ, ReachesStar M (init []) cfg ∧ (step M cfg).isNone

/-- `M` never halts when started on the blank tape (`init []`). -/
def IsNotHalt (M : Machine Γ Λ) : Prop :=
  ∀ cfg : Cfg Γ Λ, ReachesStar M (init []) cfg → (step M cfg).isSome

/-- Alias for `IsNotHalt`. -/
abbrev IsDoesNotHalt (M : Machine Γ Λ) : Prop := IsNotHalt M

/-- Parametric regular-expression half-tape expressions for `HasCollatzReduction`. -/
inductive TapeExpr (Γ : Type*) where
  /-- All-blank tail (`default : ListBlank Γ`). -/
  | default : TapeExpr Γ
  /-- Single symbol `a` followed by `rest`. -/
  | sym (a : Γ) (rest : TapeExpr Γ)
  /-- Finite block `blk` repeated `vars var_idx` times followed by `rest`. -/
  | rep (blk : List Γ) (var_idx : ℕ) (rest : TapeExpr Γ)

/-- Evaluate a `TapeExpr Γ` under variable assignment `vars : ℕ → ℕ`. -/
def evalTapeExpr {Γ : Type*} [Inhabited Γ] : TapeExpr Γ → (ℕ → ℕ) → ListBlank Γ
  | .default, _ => default
  | .sym a rest, vars => ListBlank.cons a (evalTapeExpr rest vars)
  | .rep blk v rest, vars => ListBlank.append (blk ^ vars v) (evalTapeExpr rest vars)

/-- Parametric full-tape configuration pattern. -/
structure TapePattern (Γ Λ : Type*) where
  /-- Left half-tape expression. -/
  left : TapeExpr Γ
  /-- Control state (`some q` or `none`). -/
  head : Option Λ
  /-- Right half-tape expression (whose head is under the tape head). -/
  right : TapeExpr Γ

/-- Evaluate a `TapePattern Γ Λ` under variable assignment `vars : ℕ → ℕ`. -/
def evalTapePattern {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (p : TapePattern Γ Λ) (vars : ℕ → ℕ) : Cfg Γ Λ :=
  let r := evalTapeExpr p.right vars
  ⟨p.head, ⟨r.head, evalTapeExpr p.left vars, r.tail⟩⟩

/-- Guard condition over `ℕ`-valued pattern variables. -/
inductive VarCond where
  /-- `vars idx ≥ val`. -/
  | ge_const (idx : ℕ) (val : ℕ)
  /-- `vars idx1 ≥ vars idx2`. -/
  | ge_var (idx1 idx2 : ℕ)
  /-- Conjunction of conditions. -/
  | and (c1 c2 : VarCond)
  /-- Disjunction of conditions. -/
  | or (c1 c2 : VarCond)
  /-- Negation of a condition. -/
  | not (c : VarCond)
  /-- Trivially satisfied condition. -/
  | true

/-- Evaluate a `VarCond` under variable assignment `vars : ℕ → ℕ`. -/
def evalVarCond : VarCond → (ℕ → ℕ) → Prop
  | .ge_const idx val, vars => vars idx ≥ val
  | .ge_var idx1 idx2, vars => vars idx1 ≥ vars idx2
  | .and c1 c2, vars => evalVarCond c1 vars ∧ evalVarCond c2 vars
  | .or c1 c2, vars => evalVarCond c1 vars ∨ evalVarCond c2 vars
  | .not c, vars => ¬ evalVarCond c vars
  | .true, _ => True

/-- Finite list of guarded tape patterns. -/
abbrev TapePatternSet (Γ Λ : Type*) := List (TapePattern Γ Λ × VarCond)

/-- Membership of configuration `cfg` in a `TapePatternSet`. -/
def IsInPatternSet {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (ps : TapePatternSet Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  ∃ entry : TapePattern Γ Λ × VarCond, entry ∈ ps ∧
    ∃ vars : ℕ → ℕ, cfg = evalTapePattern entry.1 vars ∧ evalVarCond entry.2 vars

/-- `ps` is a closed accelerated `TapePatternSet` for `M` if `M`'s blank-tape trajectory enters
`ps` and every member configuration of `ps` steps in `ReachesPlus` (`n > 0` steps) either to
another member of `ps` or to a halting configuration. -/
def IsClosedPatternSet (M : Machine Γ Λ) (ps : TapePatternSet Γ Λ) : Prop :=
  (∃ cfg₀, ReachesStar M (init []) cfg₀ ∧ IsInPatternSet ps cfg₀) ∧
  (∀ cfg, IsInPatternSet ps cfg →
    ∃ cfg', ReachesPlus M cfg cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step M cfg').isNone))

/-- `M`'s blank-tape trajectory enters a closed accelerated `TapePatternSet` in which every
member configuration steps in `ReachesPlus` either to another member or to a halting state. -/
def HasCollatzReduction (M : Machine Γ Λ) : Prop :=
  ∃ ps : TapePatternSet Γ Λ, IsClosedPatternSet M ps

/-- An abstract partial transition system `next : S → Option S` halts from `s₀ : S` if iterating
`next` from `some s₀` eventually produces `none`. -/
def CollatzHalts {S : Type*} (next : S → Option S) (s₀ : S) : Prop :=
  ∃ n : ℕ, ((Option.bind · next)^[n] (some s₀)).isNone

/-- `encode`, `next`, and `start` form a valid Collatz-like acceleration of `M` when:
1. `M` reaches `encode start` from the blank tape (`init []`),
2. Every defined step `next s = some s'` takes `M` from `encode s` to `encode s'` in `ReachesPlus`
   (at least one raw Turing machine step), and
3. Every undefined step `next s = none` means `M` reaches a halting configuration from
   `encode s`. -/
structure IsValidAcceleration (M : Machine Γ Λ) {S : Type*}
    (start : S) (encode : S → Cfg Γ Λ) (next : S → Option S) : Prop where
  /-- `M` reaches `encode start` from the blank tape (`init []`). -/
  init_reaches : ReachesStar M (init []) (encode start)
  /-- Every non-halting accelerated step takes at least one Turing machine step. -/
  step_some : ∀ s s', next s = some s' → ReachesPlus M (encode s) (encode s')
  /-- Every halting accelerated state reaches a halting Turing machine configuration. -/
  step_none : ∀ s, next s = none →
    ∃ cfg', ReachesStar M (encode s) cfg' ∧ (step M cfg').isNone

/-- Parametric half-tape segment for `HasStackedCollatzReduction`: in addition to single symbols
and repeated blocks, a `.word words stack_idx` segment expands a variable-length stack word
`stacks stack_idx : List ℕ` over a finite block vocabulary `words : List (List Γ)`. -/
inductive StackSeg (Γ : Type*) where
  /-- Single symbol `a`. -/
  | sym (a : Γ)
  /-- Finite block `blk` repeated `vars var_idx` times. -/
  | rep (blk : List Γ) (var_idx : ℕ)
  /-- Stack word `stacks stack_idx` expanded over block vocabulary `words`. -/
  | word (words : List (List Γ)) (stack_idx : ℕ)

/-- Whether a `StackSeg Γ` is a `.word` stack segment. -/
def StackSeg.isWord {Γ : Type*} : StackSeg Γ → Bool
  | .word _ _ => true
  | _ => false

/-- A `StackSeg Γ` is well-formed when every repeated block or stack-vocabulary block is non-empty
and contains no blank (`default`) symbols, and every `.word` vocabulary is non-empty. -/
def StackSeg.WellFormed {Γ : Type*} [Inhabited Γ] [DecidableEq Γ] : StackSeg Γ → Bool
  | .sym _ => true
  | .rep blk _ => !blk.isEmpty && blk.all (· != default)
  | .word words _ => !words.isEmpty && words.all (fun w => !w.isEmpty && w.all (· != default))

/-- Parametric stack-word half-tape expression (evaluated from head to blank tail). -/
abbrev StackExpr (Γ : Type*) := List (StackSeg Γ)

/-- Evaluate a single `StackSeg Γ` under counter assignment `vars : ℕ → ℕ` and stack assignment
`stks : ℕ → List ℕ`. -/
def evalStackSeg {Γ : Type*} : StackSeg Γ → (ℕ → ℕ) → (ℕ → List ℕ) → List Γ
  | .sym a, _, _ => [a]
  | .rep blk v, vars, _ => blk ^ vars v
  | .word words s, _, stks => ((stks s).map (fun d => words.getD d [])).flatten

/-- Evaluate a `StackExpr Γ` under counter assignment `vars : ℕ → ℕ` and stack assignment
`stks : ℕ → List ℕ`. -/
def evalStackExpr {Γ : Type*} [Inhabited Γ] :
    StackExpr Γ → (ℕ → ℕ) → (ℕ → List ℕ) → ListBlank Γ
  | [], _, _ => default
  | seg :: rest, vars, stks =>
      ListBlank.append (evalStackSeg seg vars stks) (evalStackExpr rest vars stks)

/-- Parametric stack-word full-tape configuration pattern. -/
structure StackPattern (Γ Λ : Type*) where
  /-- Left half-tape expression. -/
  left : StackExpr Γ
  /-- Control state (`some q` or `none`). -/
  head : Option Λ
  /-- Right half-tape expression (whose head is under the tape head). -/
  right : StackExpr Γ

/-- A `StackPattern Γ Λ` is well-formed when all segments on both half-tapes are well-formed
(non-empty and blank-free blocks), at least one half-tape is empty (single-sided tape boundary),
and at most one `.word` stack segment appears across the pattern. -/
def StackPattern.WellFormed {Γ Λ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (p : StackPattern Γ Λ) : Bool :=
  p.left.all StackSeg.WellFormed &&
  p.right.all StackSeg.WellFormed &&
  (p.left.isEmpty || p.right.isEmpty) &&
  (decide (p.left.countP StackSeg.isWord + p.right.countP StackSeg.isWord ≤ 1))

/-- Evaluate a `StackPattern Γ Λ` under counter assignment `vars : ℕ → ℕ` and stack assignment
`stks : ℕ → List ℕ`. -/
def evalStackPattern {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (p : StackPattern Γ Λ) (vars : ℕ → ℕ) (stks : ℕ → List ℕ) : Cfg Γ Λ :=
  let r := evalStackExpr p.right vars stks
  ⟨p.head, ⟨r.head, evalStackExpr p.left vars stks, r.tail⟩⟩

/-- Finite list of guarded stack-word tape patterns. -/
abbrev StackPatternSet (Γ Λ : Type*) := List (StackPattern Γ Λ × VarCond)

/-- A `StackPatternSet Γ Λ` is well-formed when it is non-empty and every pattern in it is
well-formed (`StackPattern.WellFormed`). -/
def IsWellFormedStackPatternSet {Γ Λ : Type*} [Inhabited Γ] [DecidableEq Γ]
    (ps : StackPatternSet Γ Λ) : Prop :=
  (!ps.isEmpty && ps.all (fun entry => entry.1.WellFormed)) = true

/-- Membership of configuration `cfg` in a `StackPatternSet`. -/
def IsInStackPatternSet {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (ps : StackPatternSet Γ Λ) (cfg : Cfg Γ Λ) : Prop :=
  ∃ entry : StackPattern Γ Λ × VarCond, entry ∈ ps ∧
    ∃ (vars : ℕ → ℕ) (stks : ℕ → List ℕ),
      cfg = evalStackPattern entry.1 vars stks ∧ evalVarCond entry.2 vars

/-- `ps` is a closed accelerated `StackPatternSet` for `M` if `ps` is well-formed
(`IsWellFormedStackPatternSet`), `M`'s blank-tape trajectory enters `ps`, and every member
configuration of `ps` steps in `ReachesPlus` (`n > 0` steps) either to another member of `ps` or
to a halting configuration.

In `BusyBeaverChallenge.lean`, `IsClosedStackPatternSet` pins an explicit `ps` and is always paired
with a concrete Level B finite-state transducer acceleration (`IsValidAcceleration`). -/
def IsClosedStackPatternSet [DecidableEq Γ] (M : Machine Γ Λ) (ps : StackPatternSet Γ Λ) : Prop :=
  IsWellFormedStackPatternSet ps ∧
  (∃ cfg₀, ReachesStar M (init []) cfg₀ ∧ IsInStackPatternSet ps cfg₀) ∧
  (∀ cfg, IsInStackPatternSet ps cfg →
    ∃ cfg', ReachesPlus M cfg cfg' ∧
      (IsInStackPatternSet ps cfg' ∨ (step M cfg').isNone))

/-- `M`'s blank-tape trajectory enters a well-formed closed accelerated `StackPatternSet` in which
every member configuration steps in `ReachesPlus` either to another member or to a halting state.
This existential summary is always paired in `BusyBeaverChallenge.lean` with a concrete `ps`
(`IsClosedStackPatternSet M ps`) and an explicit Level B finite-state transducer acceleration
(`IsValidAcceleration M start encode next`). -/
def HasStackedCollatzReduction [DecidableEq Γ] (M : Machine Γ Λ) : Prop :=
  ∃ ps : StackPatternSet Γ Λ, IsClosedStackPatternSet M ps

end BusyBeaver
