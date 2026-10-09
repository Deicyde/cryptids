/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public meta import Lean.Elab.Term

/-!
# Elaboration-Time Turing Machine Table Loader

Provides the `load_machine_rows% "<path>"` term elaborator, which reads a canonical 2-symbol
Turing machine transition table `.txt` file at elaboration time and elaborates directly into a pure
`List (List (Option (Fin 2 × Dir × Fin N)))` expression in the Lean kernel, eliminating any
duplication between the canonical `.txt` files and the Lean machine definitions.
-/

public meta section

namespace ConjectureMachines.Machines

open Lean Elab Term

private def parseCellStx (cell : String) : TermElabM (TSyntax `term) := do
  if cell == "---" then
    `(none)
  else
    match cell.toList with
    | wChar :: dChar :: rest =>
      if rest.isEmpty then
        throwError "Malformed transition cell: {cell}"
      let wLit := Syntax.mkNumLit (String.singleton wChar)
      let dirStx ← match dChar with
        | 'L' => `(Turing.Dir.left)
        | 'R' => `(Turing.Dir.right)
        | _ => throwError "Invalid direction in transition cell: {cell}"
      let nxtLit := Syntax.mkNumLit (String.ofList rest)
      `(some ($wLit, $dirStx, $nxtLit))
    | _ => throwError "Malformed transition cell: {cell}"

/-- Term elaborator that reads a canonical 2-symbol Turing machine `.txt` table at elaboration time
and elaborates into its `List (List (Option (Fin 2 × Dir × Fin N)))` row list. -/
elab "load_machine_rows% " path:str : term <= expectedType? => do
  let filePath : System.FilePath := path.getString
  let contents ← liftM (m := IO) (IO.FS.readFile filePath)
  let mut rowStxs : Array (TSyntax `term) := #[]
  for rawLine in contents.splitOn "\n" do
    let line := ((rawLine.splitOn "#").headD "").trimAscii.toString
    if !line.isEmpty then
      let cells := (line.splitOn " ").filter (fun s => !s.isEmpty)
      match cells with
      | [c0, c1] =>
        let s0 ← parseCellStx c0
        let s1 ← parseCellStx c1
        let rowStx ← `([$s0, $s1])
        rowStxs := rowStxs.push rowStx
      | _ => throwError "Expected 2 columns in transition table line: {rawLine}"
  let listStx ← `([$rowStxs,*])
  elabTerm listStx expectedType?

end ConjectureMachines.Machines
