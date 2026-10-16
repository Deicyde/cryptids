/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
meta import Lean.Elab.Term

/-! # Busy Beaver Challenge Specification (`BusyBeaverChallenge`) -/

@[expose] public section

namespace ConjectureMachines
open Turing

/-- A Turing machine transition table over `states` states and `symbols` symbols. -/
structure Machine (states symbols : ℕ) where
  transition : Fin states → Fin symbols → Option (Fin symbols × Dir × Fin states)

variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- Build a `Machine states symbols` from a list of per-state transition rows. -/
def Machine.ofRows (rows : List (List (Option (Fin symbols × Dir × Fin states)))) :
    Machine states symbols := ⟨fun q a => (rows.getD q.val []).getD a.val none⟩

end ConjectureMachines
end

meta section
namespace BusyBeaver
open Lean Elab Term

private def parseRleBlock (block : String) : TermElabM (TSyntax `term) := do
  let chars := block.toList
  if chars.length == 0 || chars.length % 3 != 0 then
    throwError "Invalid RLE state block length: {block}"
  let numSymbols := chars.length / 3
  let mut cellStxs : Array (TSyntax `term) := #[]
  for i in [:numSymbols] do
    let wChar := chars[3 * i]!
    let dChar := chars[3 * i + 1]!
    let sChar := chars[3 * i + 2]!
    if wChar == '-' && dChar == '-' && sChar == '-' then
      cellStxs := cellStxs.push (← `(none))
    else
      if !wChar.isDigit then
        throwError "Invalid symbol character '{wChar}' in RLE block: {block}"
      let wLit := Syntax.mkNumLit (String.singleton wChar)
      let dirStx ← match dChar with
        | 'L' => `(Turing.Dir.left)
        | 'R' => `(Turing.Dir.right)
        | _ => throwError "Invalid direction '{dChar}' in RLE block: {block}"
      if sChar < 'A' || sChar > 'Z' then
        throwError "Invalid state letter '{sChar}' in RLE block: {block}"
      let stateIdx := sChar.toNat - 'A'.toNat
      let sLit := Syntax.mkNumLit (toString stateIdx)
      cellStxs := cellStxs.push (← `(some ($wLit, $dirStx, $sLit)))
  `([$cellStxs,*])

elab "load_rle_rows% " rle:str : term <= expectedType? => do
  let blocks := rle.getString.trimAscii.toString.splitOn "_"
  if blocks.isEmpty then
    throwError "Empty RLE string"
  let mut rowStxs : Array (TSyntax `term) := #[]
  for b in blocks do
    rowStxs := rowStxs.push (← parseRleBlock b)
  elabTerm (← `([$rowStxs,*])) expectedType?

elab "load_rle_machine% " rle:str : term <= expectedType? => do
  let blocks := rle.getString.trimAscii.toString.splitOn "_"
  if blocks.isEmpty then
    throwError "Empty RLE string"
  let mut rowStxs : Array (TSyntax `term) := #[]
  for b in blocks do
    rowStxs := rowStxs.push (← parseRleBlock b)
  elabTerm (← `(ConjectureMachines.Machine.ofRows [$rowStxs,*])) expectedType?

end BusyBeaver
end

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
  | default : TapeExpr Γ
  | sym (a : Γ) (rest : TapeExpr Γ)
  | rep (blk : List Γ) (var_idx : ℕ) (rest : TapeExpr Γ)

/-- Evaluate a `TapeExpr Γ` under variable assignment `vars : ℕ → ℕ`. -/
def evalTapeExpr {Γ : Type*} [Inhabited Γ] : TapeExpr Γ → (ℕ → ℕ) → ListBlank Γ
  | .default, _ => default
  | .sym a rest, vars => ListBlank.cons a (evalTapeExpr rest vars)
  | .rep blk v rest, vars => ListBlank.append (blk ^ vars v) (evalTapeExpr rest vars)

/-- Parametric full-tape configuration pattern. -/
structure TapePattern (Γ Λ : Type*) where
  left : TapeExpr Γ
  head : Option Λ
  right : TapeExpr Γ

/-- Evaluate a `TapePattern Γ Λ` under variable assignment `vars : ℕ → ℕ`. -/
def evalTapePattern {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (p : TapePattern Γ Λ) (vars : ℕ → ℕ) : Cfg Γ Λ :=
  let r := evalTapeExpr p.right vars
  ⟨p.head, ⟨r.head, evalTapeExpr p.left vars, r.tail⟩⟩

/-- Guard condition over `ℕ`-valued pattern variables. -/
inductive VarCond where
  | ge_const (idx : ℕ) (val : ℕ)
  | ge_var (idx1 idx2 : ℕ)
  | and (c1 c2 : VarCond)
  | or (c1 c2 : VarCond)
  | not (c : VarCond)
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

namespace SixState

/-- State `A` (`0 : Fin 6`), the initial state. -/
abbrev A : Fin 6 := 0
/-- State `B` (`1 : Fin 6`). -/
abbrev B : Fin 6 := 1
/-- State `C` (`2 : Fin 6`). -/
abbrev C : Fin 6 := 2
/-- State `D` (`3 : Fin 6`). -/
abbrev D : Fin 6 := 3
/-- State `E` (`4 : Fin 6`). -/
abbrev E : Fin 6 := 4
/-- State `F` (`5 : Fin 6`). -/
abbrev F : Fin 6 := 5

end SixState

/-- Canonical `NeZero 2` instance for `(states, 2)` Turing machines. -/
instance (priority := high) instNeZeroTwo : @NeZero ℕ Zero.ofOfNat0 2 := Nat.instNeZeroSucc

/-- Canonical `NeZero 6` instance for `(6, symbols)` Turing machines. -/
instance (priority := high) instNeZeroSix : @NeZero ℕ Zero.ofOfNat0 6 := Nat.instNeZeroSucc

end BusyBeaver

namespace ConjectureMachines
variable {states symbols : ℕ} [NeZero states] [NeZero symbols]

/-- Convert a `ConjectureMachines.Machine states symbols` into a
`BusyBeaver.Machine (Fin symbols) (Fin states)`. -/
def Machine.toBB (M : Machine states symbols) :
    BusyBeaver.Machine (Fin symbols) (Fin states) :=
  fun q s => (M.transition q s).map fun (a, d, q') => (some q', BusyBeaver.Stmt.write a d)

end ConjectureMachines

namespace BusyBeaver
open Turing SixState

namespace M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .rep [1] 0 .default
      head := some SixState.A
      right := .sym 0 (.rep [1, 1] 1 (.sym 0 (.rep [1] 2 .default))) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | E (a k c : ℕ)
  | M_1 (a k d : ℕ)
  | M_0 (n z : ℕ)

def start : State := .E 3 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .E a k c =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1] : List (Fin 2)) ^ a) default)
      (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ c) default))))
  | .M_1 a k d =>
    Cfg.headRight SixState.C
      (ListBlank.append [0] (ListBlank.append [1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ a) default)))))
      (ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) default)
  | .M_0 n z =>
    Cfg.headRight SixState.C
      (ListBlank.append [0] (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ n) default)))
      (ListBlank.append (([1] : List (Fin 2)) ^ z) default)

def next : State → Option State
  | .E a 0 c => some (.M_0 a c)
  | .E a 1 c =>
    if c % 2 = 0 then some (.E (a + 3) (c / 2) 0)
    else if c = 1 then none
    else some (.M_0 (a + 5) (c - 3))
  | .E a (k + 2) 0 => some (.M_0 (a + 2) (2 * k + 1))
  | .E a (k + 2) (d + 1) => some (.M_1 (a + 3) k d)
  | .M_1 a k d =>
    if d % 2 = 0 then some (.E (a + 3) k (d + 1))
    else if d = 1 then some (.E a 1 (2 * k + 2))
    else some (.E (a + 3) (k + 1) (d - 1))
  | .M_0 n 0 => some (.E 3 0 (n + 2))
  | .M_0 n (d + 1) =>
    if d % 2 = 0 then
      if n % 2 = 0 then some (.E 3 (n / 2) (d + 1))
      else some (.E 4 (n / 2 + 1) (d + 1))
    else if d = 1 then
      if n % 2 = 0 then some (.E 0 1 (n + 2))
      else some (.E 1 1 (n + 3))
    else
      if n % 2 = 0 then some (.E 3 (n / 2 + 1) (d - 1))
      else some (.E 4 (n / 2 + 2) (d - 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA

namespace M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .rep [1, 0] 0 (.rep [1] 1 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .ge_const 1 1)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C (a b : ℕ)
  | P (k n p : ℕ)

def start : State := .C 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b =>
    Cfg.headRight SixState.E default
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 1)) default))
  | .P k n p =>
    Cfg.headLeft SixState.A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) default)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ n)
        (ListBlank.append (([1] : List (Fin 2)) ^ (p + 1)) default))

def next : State → Option State
  | .C a 0 => some (.C 2 (2 * a + 1))
  | .C _ 1 => none
  | .C a (d + 2) => some (.P a 0 (d + 2))
  | .P 0 n 0 => some (.C (n + 1) 2)
  | .P 0 n 1 => some (.C (n + 1) 0)
  | .P 0 n (p + 2) => some (.C (n + 2) p)
  | .P (k + 1) n 0 => some (.P k (n + 1) 2)
  | .P (k + 1) n 1 => some (.P k (n + 1) 0)
  | .P (k + 1) n (p + 2) => some (.P k (n + 2) p)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

namespace M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))))
      head := some SixState.A
      right := .sym 1 (.sym 1 (.rep [0, 1] 1 (.rep [1] 2 (.sym 0 (.sym 1 .default))))) }, .true),
   ({ left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
      head := some SixState.E
      right := .sym 1 (.rep [1, 1, 0, 1] 1
        (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
          (.rep [1, 1] 2 (.sym 0 (.sym 1 .default)))))))))) }, .true),
   ({ left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
      head := some SixState.E
      right := .sym 1 (.rep [1, 1, 0, 1] 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 .default))))) }, .true),
   ({ left := .rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))))
      head := some SixState.E
      right := .sym 1 (.rep [1, 1, 0, 1] 1
        (.sym 1 (.sym 1 (.sym 1 (.rep [0, 1] 2
          (.sym 0 (.sym 1 (.sym 0 (.sym 0 (.sym 1 .default)))))))))) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | J (u v w : ℕ)
  | S_E (b m k : ℕ)
  | S_E0 (b m : ℕ)
  | S_E1 (b m n : ℕ)

def start : State := .J 0 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .J u v w =>
    Cfg.headRight SixState.A
      (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ u)
          (ListBlank.append [1, 1, 1, 1, 1] default)))
      (ListBlank.append [1, 1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ v)
          (ListBlank.append (([1] : List (Fin 2)) ^ w)
            (ListBlank.append [0, 1] default))))
  | .S_E b m k =>
    Cfg.headRight SixState.E
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1, 1, 1, 1] default))
      (ListBlank.append [1]
        (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 1, 1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
              (ListBlank.append [0, 1] default)))))
  | .S_E0 b m =>
    Cfg.headRight SixState.E
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1, 1, 1, 1] default))
      (ListBlank.append [1]
        (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 0, 1] default)))
  | .S_E1 b m n =>
    Cfg.headRight SixState.E
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [1, 1, 1, 1, 1] default))
      (ListBlank.append [1]
        (ListBlank.append (([1, 1, 0, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ n)
              (ListBlank.append [0, 1, 0, 0, 1] default)))))

def next : State → Option State
  | .J 0 v 0 => some (.S_E0 (v + 3) 0)
  | .J 0 v 1 => some (.S_E1 (v + 2) 0 0)
  | .J 0 v 2 => some (.S_E (v + 2) 0 0)
  | .J 0 v (w + 3) => some (.J (v + 3) 0 w)
  | .J 1 v 0 => some (.S_E 0 0 (v + 3))
  | .J (u + 2) v 0 => some (.S_E1 u 0 (v + 2))
  | .J 1 _ 1 => none
  | .J (u + 2) v 1 => some (.S_E u 0 (v + 2))
  | .J (u + 1) v (w + 2) => some (.J u (v + 2) w)
  | .S_E 0 0 k => some (.J 0 0 (2 * k + 6))
  | .S_E 0 (m + 1) k => some (.J 2 (2 * m + 4) (2 * k + 1))
  | .S_E 1 m k => some (.J 0 (2 * m + 3) (2 * k + 1))
  | .S_E (b + 2) m k => some (.S_E b (m + 1) k)
  | .S_E0 0 m => some (.S_E 2 0 (2 * m))
  | .S_E0 1 m => some (.S_E 0 0 (2 * m + 1))
  | .S_E0 (b + 2) m => some (.S_E0 b (m + 1))
  | .S_E1 0 m n => some (.S_E 2 0 (2 * m + n + 2))
  | .S_E1 1 m n => some (.S_E 0 0 (2 * m + n + 3))
  | .S_E1 (b + 2) m n => some (.S_E1 b (m + 1) n)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

namespace M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left  := .sym 1 (.rep [1] 0 .default)
      head  := some SixState.C
      right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                (.rep [1] 1 (.rep [0, 1] 2
                  (.sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.sym 1 .default))))))))))))) }, .true),
   ({ left  := .sym 1 (.rep [1] 0 .default)
      head  := some SixState.C
      right := .sym 0 (.sym 0 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                (.rep [1] 1 (.rep [0, 1] 2
                  (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1 (.sym 1
                    (.sym 0 (.sym 1 (.sym 1 .default)))))))))))))))) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C_3 (a b c : ℕ)
  | C_6 (a b c : ℕ)
  | M_3 (a : Bool) (b c : ℕ)
  | M_6_pos (a : Bool) (b c : ℕ)
  | L_3 (a : Bool) (b : ℕ)
  | L_6 (a : Bool) (b : ℕ)

def start : State := .C_3 4 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C_3 a b c =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default)))))
  | .C_6 a b c =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) default)
      (ListBlank.append [0, 0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0, 1, 1] default)))))
  | .M_3 a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append [1] (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
            (ListBlank.append (([1] : List (Fin 2)) ^ 3)
              (ListBlank.append [0, 1, 1] default)))))
  | .M_6_pos a b c =>
    Cfg.headRight SixState.A
      (ListBlank.append [1] (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ (b + 4))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 1))
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0, 1, 1] default)))))
  | .L_3 a b =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ ((b + 1) + 6))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ 3)
          (ListBlank.append [0, 1, 1] default)))
  | .L_6 a b =>
    Cfg.headRight SixState.C
      (ListBlank.append (([1] : List (Fin 2)) ^ (b + 6))
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ ((if a then 1 else 0) + 3)) default)))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ 6)
          (ListBlank.append [0, 1, 1] default)))

def next : State → Option State
  | .C_3 0 b c => some (.M_3 false b c)
  | .C_3 1 b c => some (.M_3 true b c)
  | .C_3 (a + 2) b c => some (.C_3 a (b + 3) c)
  | .C_6 0 b 0 => some (.M_3 false (b + 3) 0)
  | .C_6 1 b 0 => some (.M_3 true (b + 3) 0)
  | .C_6 0 b (c + 1) => some (.M_6_pos false b c)
  | .C_6 1 b (c + 1) => some (.M_6_pos true b c)
  | .C_6 (a + 2) b c => some (.C_6 a (b + 3) c)
  | .M_3 a b 0 => some (.L_3 a b)
  | .M_3 a b 1 => some (.L_6 a b)
  | .M_3 a b (c + 2) => some (.C_3 (b + 4 + if a then 1 else 0) 3 c)
  | .M_6_pos a b 0 => some (.C_3 (b + 4 + if a then 1 else 0) 0 3)
  | .M_6_pos a b (c + 1) => some (.C_6 (b + 4 + if a then 1 else 0) 3 c)
  | .L_3 a b =>
    if b % 2 = 0 then some (.C_3 (if a then 1 else 0) 0 (b / 2 + 3))
    else if a then some (.C_3 6 3 (b / 2))
    else none
  | .L_6 a b =>
    if b % 2 = 1 then some (.C_6 (if a then 1 else 0) 0 (b / 2 + 3))
    else if !a then none
    else if b = 0 then some (.C_3 6 0 3)
    else some (.C_6 6 3 (b / 2 - 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA

namespace M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .rep [0, 1] 1 (.rep [1] 0 .default)
      head := some SixState.A
      right := .rep [0, 1] 2 (.rep [1] 3 .default) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | A (a b c d : ℕ)

def start : State := .A 0 0 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a b c d =>
    Cfg.headRight SixState.A
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
        (ListBlank.append (([1] : List (Fin 2)) ^ a) default))
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ c)
        (ListBlank.append (([1] : List (Fin 2)) ^ d) default))

def next : State → Option State
  | .A a b (c + 1) d => some (.A a (b + 1) c d)
  | .A a b 0 0 => some (.A (a + 1) 0 0 (2 * b + 2))
  | .A (a + 3) b 0 (d + 1) => some (.A a (b + 2) 0 d)
  | .A 2 b 0 (d + 1) => some (.A 0 0 (b + 1) d)
  | .A 1 (b + 1) 0 (d + 1) => some (.A 1 1 (b + 2) d)
  | .A 1 0 0 (d + 1) => some (.A 0 0 0 (d + 3))
  | .A 0 0 0 1 => some (.A 0 0 2 5)
  | .A 0 (b + 1) 0 1 => some (.A 0 0 2 (2 * b + 3))
  | .A 0 b 0 (d + 2) =>
    if b ≥ d + 1 then some (.A (3 * d + 2) 1 2 (2 * b - 2 * d - 1))
    else if d = b then none
    else if d = b + 1 then some (.A (3 * b + 2) 0 0 6)
    else if d = b + 2 then some (.A (3 * b + 4) 0 0 4)
    else some (.A (3 * b + 3) 2 0 (d - b - 3))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD

namespace M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.rep [0, 1] 1 .default)))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

def pat_E : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.rep [0, 1] 1 .default)))
    head := some E
    right := .sym 1 (.rep [1] 2 .default) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .true), (pat_E, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | D (a b c : ℕ)
  | E (a b c : ℕ)

def start : State := .D 1 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .D a b c =>
    evalTapePattern pat_D fun k => match k with | 0 => a | 1 => b | 2 => c | _ => 0
  | .E a b c =>
    evalTapePattern pat_E fun k => match k with | 0 => a | 1 => b | 2 => c | _ => 0

def next : State → Option State
  | .D (a + 1) b c => some (.D a b (c + 2))
  | .D 0 0 0 => some (.D 2 0 0)
  | .D 0 0 (c + 1) => some (.E 1 0 (c + 1))
  | .D 0 1 0 => some (.D 0 2 0)
  | .D 0 1 1 => some (.D 1 2 0)
  | .D 0 1 2 => some (.D 2 2 0)
  | .D 0 1 (c + 3) => some (.E 1 2 (c + 1))
  | .D 0 (b + 2) c => some (.E 1 b (c + 2))
  | .E (a + 1) b 0 => some (.E a b 1)
  | .E 0 0 0 => some (.D 0 0 1)
  | .E 0 (b + 1) 0 => some (.D 1 b 0)
  | .E a 0 1 => some (.D (a + 1) 0 1)
  | .E a 0 2 => some (.D (a + 2) 0 1)
  | .E _ 0 3 => none
  | .E a 0 4 => some (.D 0 (a + 3) 0)
  | .E a 0 5 => some (.D 1 (a + 3) 0)
  | .E a 0 6 => some (.D 2 (a + 3) 0)
  | .E a 0 (c + 7) => some (.E 1 (a + 3) (c + 1))
  | .E a (b + 1) 1 => some (.D (a + 2) b 0)
  | .E a (b + 1) 2 => some (.D (a + 3) b 0)
  | .E a (b + 1) (c + 3) => some (.E (a + 2) b (c + 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE

namespace M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.sym 1 .default))
    head := some A
    right := .rep [1, 1] 0 (.sym 0 (.rep [1] 1 .default)) }

def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_C, .ge_const 1 6)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C (a b : ℕ)
  | M_3 (a c d : ℕ)
  | M_4 (a b c d : ℕ)

def start : State := .C 0 3

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1] default)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (b + 6)) default)))
  | .M_3 a c d =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1] default)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))
  | .M_4 a b c d =>
    Cfg.headRight SixState.A
      (ListBlank.append [0, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
        (ListBlank.append [0, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ d) default)))))

def next : State → Option State
  | .C 0 b =>
    if b % 2 = 0 then some (.C (b / 2 + 1) 3)
    else some (.C (b / 2 + 3) 0)
  | .C (a + 1) b =>
    if b % 2 = 0 then some (.M_4 a (b / 2 + 1) 4 0)
    else some (.M_3 a (b / 2 + 2) 6)
  | .M_3 0 0 _ => none
  | .M_3 1 0 _ => none
  | .M_3 (a + 2) 0 d => some (.C (a + 1) (d + 3))
  | .M_3 0 (c + 1) d => some (.C (c + 1) d)
  | .M_3 (a + 1) (c + 1) d => some (.M_3 a c (d + 6))
  | .M_4 a 0 c d => some (.C (a + c + 1) d)
  | .M_4 0 1 0 _ => none
  | .M_4 (a + 1) 1 0 d => some (.C (a + 1) (d + 6))
  | .M_4 a (b + 2) 0 d => some (.M_3 a b (d + 9))
  | .M_4 a (b + 1) (c + 1) d => some (.M_4 a b c (d + 6))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA

namespace M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .sym 0 (.rep [1, 1] 1 (.sym 0 (.rep [1, 1] 0 .default)))
      head := some SixState.D
      right := .sym 1 (.rep [1] 2 .default) },
    .and (.ge_const 0 1) (.and (.ge_const 1 1) (.ge_const 2 1)))]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C (k m f : ℕ)

def start : State := .C 2 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C k m f =>
    Cfg.headRight SixState.D
      (ListBlank.append [0]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1))
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default))))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1)) default))

def next : State → Option State
  | .C 0 0 _ => none
  | .C 0 1 _ => none
  | .C 0 2 f =>
    if f % 2 = 0 then some (.C (f / 2 + 3) 2 4)
    else some (.C (f / 2 + 5) 0 1)
  | .C 0 (m + 3) f =>
    if f % 2 = 0 then some (.C m (f / 2 + 5) 1)
    else some (.C m (f / 2 + 5) 4)
  | .C 1 0 f =>
    if f % 2 = 0 then some (.C (f / 2 + 3) 0 1)
    else some (.C (f / 2 + 2) 2 4)
  | .C (k + 2) 0 f =>
    if f % 2 = 0 then some (.C k (f / 2 + 3) 4)
    else some (.C k (f / 2 + 4) 1)
  | .C (k + 1) (m + 1) f =>
    if k < m then some (.C 0 (m - k) (f + 6 * (k + 1)))
    else if m < k then some (.C (k - m) 0 (f + 6 * (m + 1)))
    else some (.C 0 0 (f + 6 * (k + 1)))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE

namespace M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
      head := some SixState.E
      right := .sym 1 (.sym 1 (.rep [1, 1] 1 (.sym 0 (.sym 1 (.sym 1
        (.rep [1, 1] 2 .default)))))) }, .true),
   ({ left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
      head := some SixState.E
      right := .sym 1 (.sym 1 (.rep [1, 1] 1 (.sym 0 (.sym 1 (.sym 1
        (.rep [1, 1] 2 .default)))))) }, .true)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | C_0 (a b c : ℕ)
  | C_1 (a b c : ℕ)

def start : State := .C_1 2 2 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .C_0 a b c =>
    Cfg.headRight SixState.E
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default))))
  | .C_1 a b c =>
    Cfg.headRight SixState.E
      (ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ b)
          (ListBlank.append [0, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ c) default))))

def next : State → Option State
  | .C_0 _ 0 0 => none
  | .C_0 a 0 1 => some (.C_1 2 2 (a + 1))
  | .C_0 a 0 (d + 2) => some (.C_0 1 (a + 3) d)
  | .C_0 a (b + 1) 0 => some (.C_1 (a + 1) 0 b)
  | .C_0 a (b + 1) (c + 1) => some (.C_0 (a + 3) b c)
  | .C_1 _ 0 0 => none
  | .C_1 a 0 1 => some (.C_0 1 0 (a + 3))
  | .C_1 a 0 (d + 2) => some (.C_1 2 (a + 3) d)
  | .C_1 a (b + 1) 0 => some (.C_0 (a + 2) 0 b)
  | .C_1 a (b + 1) (c + 1) => some (.C_1 (a + 3) b c)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD

namespace M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .default
      head := some SixState.C
      right := .sym 0 (.rep [1] 0 .default) }, .ge_const 0 1),
   ({ left := .sym 1 (.rep [0, 1] 0 .default)
      head := some SixState.C
      right := .sym 0 (.rep [1] 1 .default) }, .ge_const 1 1)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | P_1 (c : ℕ)
  | P_2 (a c : ℕ)
  | D_0_odd (k w : ℕ)
  | D_0_even (k w : ℕ)
  | D_succ_odd (a k w : ℕ)

def start : State := .P_1 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 c =>
    Cfg.headRight SixState.C default
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .P_2 a c =>
    Cfg.headRight SixState.C
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .D_0_odd k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_0_even k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_succ_odd a k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))

def next : State → Option State
  | .P_1 0 => some (.P_1 2)
  | .P_1 (w + 1) => some (.D_0_odd 0 w)
  | .P_2 a 0 => some (.P_2 a 2)
  | .P_2 a (w + 1) => some (.D_succ_odd a 0 w)
  | .D_0_odd k 0 => some (.P_1 (2 * k + 3))
  | .D_0_odd k 1 => some (.P_1 (2 * k + 5))
  | .D_0_odd k (w + 2) => some (.D_0_even (k + 1) w)
  | .D_0_even _ 0 => none
  | .D_0_even k 1 => some (.P_2 k 2)
  | .D_0_even k 2 => some (.P_2 k 4)
  | .D_0_even k 3 => some (.P_2 k 6)
  | .D_0_even k (w + 4) => some (.D_succ_odd k 2 w)
  | .D_succ_odd 0 k 0 => some (.P_1 (2 * k + 4))
  | .D_succ_odd 0 k 1 => some (.P_1 (2 * k + 6))
  | .D_succ_odd (a + 1) k 0 => some (.P_2 a (2 * k + 4))
  | .D_succ_odd (a + 1) k 1 => some (.P_2 a (2 * k + 6))
  | .D_succ_odd 0 k (w + 2) => some (.D_0_odd (k + 2) w)
  | .D_succ_odd (a + 1) k (w + 2) => some (.D_succ_odd a (k + 2) w)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

namespace M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .default
      head := some SixState.C
      right := .sym 0 (.rep [1] 0 .default) }, .ge_const 0 1),
   ({ left := .sym 1 (.rep [0, 1] 0 .default)
      head := some SixState.C
      right := .sym 0 (.rep [1] 1 .default) }, .ge_const 1 1)]

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by sorry
theorem has_collatz_reduction : HasCollatzReduction target := by sorry

inductive State where
  | P_1 (c : ℕ)
  | P_2 (a c : ℕ)
  | D_1_0_odd (k w : ℕ)
  | D_1_0_even (k w : ℕ)
  | D_1_succ_odd (a k w : ℕ)

def start : State := .P_1 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 c =>
    Cfg.headRight SixState.C default
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .P_2 a c =>
    Cfg.headRight SixState.C
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ a) default))
      (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (c + 1)) default))
  | .D_1_0_odd k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_1_0_even k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 2))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ 0) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))
  | .D_1_succ_odd a k w =>
    Cfg.headRight SixState.D
      (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k + 1))
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 1)) default))
      (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ w) default))

def next : State → Option State
  | .P_1 0 => some (.P_1 3)
  | .P_1 (w + 1) => some (.D_1_0_even 0 w)
  | .P_2 0 0 => some (.P_1 4)
  | .P_2 (a + 1) 0 => some (.P_2 a 4)
  | .P_2 0 (w + 1) => some (.D_1_0_odd 1 w)
  | .P_2 (a + 1) (w + 1) => some (.D_1_succ_odd a 1 w)
  | .D_1_0_odd k 0 => some (.P_1 (2 * k + 3))
  | .D_1_0_odd k 1 => some (.P_1 (2 * k + 5))
  | .D_1_0_odd k (w + 2) => some (.D_1_0_even (k + 1) w)
  | .D_1_0_even _ 0 => none
  | .D_1_0_even k 1 => some (.P_2 k 2)
  | .D_1_0_even k 2 => some (.P_2 k 4)
  | .D_1_0_even k 3 => some (.P_2 k 6)
  | .D_1_0_even k (w + 4) => some (.D_1_succ_odd k 2 w)
  | .D_1_succ_odd 0 k 0 => some (.P_1 (2 * k + 4))
  | .D_1_succ_odd 0 k 1 => some (.P_1 (2 * k + 6))
  | .D_1_succ_odd (a + 1) k 0 => some (.P_2 a (2 * k + 4))
  | .D_1_succ_odd (a + 1) k 1 => some (.P_2 a (2 * k + 6))
  | .D_1_succ_odd 0 k (w + 2) => some (.D_1_0_odd (k + 2) w)
  | .D_1_succ_odd (a + 1) k (w + 2) => some (.D_1_succ_odd a (k + 2) w)

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by sorry
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start := by sorry
end M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE

end BusyBeaver
