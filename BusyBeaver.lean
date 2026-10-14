/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs
public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdouts & Cryptids (`BusyBeaver`)

Formal Lean 4 specifications and kernel-verified behavioral proofs (`IsHalt`, `IsNotHalt`,
`IsCryptid`) for Busy Beaver holdout and cryptid Turing machines, connected to
`ConjectureMachines.Machine` via `BusyBeaver.Bridge`.
-/
