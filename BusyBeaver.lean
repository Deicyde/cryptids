/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs
public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Machines.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA
public import BusyBeaver.Machines.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
public import BusyBeaver.Machines.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
public import BusyBeaver.Machines.M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA

/-!
# Busy Beaver Holdouts & Cryptids (`BusyBeaver`)

Formal Lean 4 specifications and kernel-verified behavioral proofs (`IsHalt`, `IsNotHalt`,
`IsCryptid`) for Busy Beaver holdout and cryptid Turing machines, connected to
`ConjectureMachines.Machine` via `BusyBeaver.Bridge`.
-/
