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

/-- Canonical `NeZero 2` instance for `(states, 2)` Turing machines. -/
instance (priority := high) instNeZeroTwo : @NeZero ℕ Zero.ofOfNat0 2 := Nat.instNeZeroSucc

/-- Canonical `NeZero 6` instance for `(6, symbols)` Turing machines. -/
instance (priority := high) instNeZeroSix : @NeZero ℕ Zero.ofOfNat0 6 := Nat.instNeZeroSucc

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

/-- Parametric regular-expression half-tape expressions for `IsCryptid`. -/
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

/-- `M`'s blank-tape trajectory enters a closed accelerated `TapePatternSet` in which every
member configuration steps in `ReachesPlus` either to another member or to a halting state. -/
def IsCryptid (M : Machine Γ Λ) : Prop :=
  ∃ ps : TapePatternSet Γ Λ,
    (∃ cfg₀, ReachesStar M (init []) cfg₀ ∧ IsInPatternSet ps cfg₀) ∧
    (∀ cfg, IsInPatternSet ps cfg →
      ∃ cfg', ReachesPlus M cfg cfg' ∧
        (IsInPatternSet ps cfg' ∨ (step M cfg').isNone))

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

namespace M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA

namespace M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

namespace M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

namespace M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA

namespace M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD

namespace M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE

namespace M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA

namespace M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE

namespace M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD

namespace M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

namespace M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE"
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB
theorem is_cryptid : IsCryptid target := by sorry
end M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE

end BusyBeaver
