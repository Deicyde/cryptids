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
public import BusyBeaver.Machines.M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD
public import BusyBeaver.Machines.M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE
public import BusyBeaver.Machines.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA
public import BusyBeaver.Machines.M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE
public import BusyBeaver.Machines.M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD
public import BusyBeaver.Machines.M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE

/-!
# Busy Beaver Holdouts & Cryptids (`BusyBeaver`)

Formal Lean 4 specifications and kernel-verified behavioral proofs (`IsHalt`, `IsNotHalt`,
`IsCryptid`) for Busy Beaver holdout and cryptid Turing machines, connected to
`ConjectureMachines.Machine` via `BusyBeaver.Bridge`.
-/
