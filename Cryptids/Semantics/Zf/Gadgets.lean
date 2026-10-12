/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Semantics.Riemann.Gadgets

/-!
# Layer 1: Tape Layout, Boot, & Register Gadgets for `zf_432_wade.tm` (`Machines.zf432`)

This file formalizes the Layer 1 infrastructure of the 432-state ZF Turing machine
`ConjectureMachines.Semantics.Zf.Machines.zf432` (`zf_432_wade.tm`):

1. **State Mapping & `nSteps` Scan Primitives (`0..95`, `126`)**:
   - `0a.boot1.A..E` = States `0..4`
   - `0b.boot2.0..2` = States `5..7`
   - `1b.reg.prep_1..2` = States `8..9`
   - `2b.reg.-1, -2, 0..10.dec/inc` and `2b.reg.dec/inc.*` = States `10..42`
   - `2c.reg.return_0_1..return_1_2` = States `43..46`
   - `2e.reg.cleanup_1..2` = States `47..48`
   - `3.<reg>.decnz/inc` = States `49..70`
   - `4.dispatch.0..14, scan` = States `71..86`
   - `5.root.1, 5.root.1.1` = States `87..88`
   - `6.break.0..2, 6.continue.0..3` = States `89..95`
   - `main().0` = State `126`

2. **Canonical Tape Layout at `main().0` (State `126`)**:
   - `zfRootCfg`: at the start of every outer cycle in `main().0` (State `126`),
     `Tape.left = (default.cons 1 |>.cons 1 |>.cons 0)` (`[1, 1, 0]` root prefix), and
     to the right of the head is the call-stack `stack : List (Fin 2)`, followed by
     `padTotal - stack.length` zeros, the `[1, 0]` marker (`encodeReg 0`), and the unary
     registers `regs : List ℕ` (`regsTape regs`).
   - `zfPrepCfg`: the configuration at `main().0` (State `126`) after Pass 1 (`1b.reg.prep_1/2`),
     where the `pad` zeros + `[1, 0]` marker have been converted into `[1, 0]` (the Pass-2
     marker + separator) followed by `encodeReg (pad - 2)` (the `-1` register).

3. **Pass 1 & Pass 2 Register Gadgets (`1b`, `2b`, `2c`, `2e`, `3`, `4`, `5`, `6`)**:
   - `4.dispatch.14..0 -> 4.dispatch.scan -> 5.root.1 -> 5.root.1.1 -> main().0` return scan
     (`dispatch_return_to_main`, `continue0_return`, `continue1_return`, `continue2_return`,
     `continue3_return`).
   - Pass 1 (`1b.reg.prep_1/2`): `prep_pass1_eval` and `stage3_pass1_from_stack`.
   - Pass 2 (`2b.reg.<k>.inc/dec` & `2c.reg.return_*`): `stage3_inc_pass2`,
     `stage3_decnz_pass2_zero`, `stage3_decnz_pass2_pos`.
   - Cleanup & Break (`6.break.0..2 -> 2e.reg.cleanup_1/2 -> 0b.boot2.0 -> 6.continue.0`):
     `cleanup_to_main`, `break0_cleanup_to_main`, `break1_cleanup_to_main`,
     `break2_cleanup_to_main`.
   - Full Pass 2 + Cleanup to `zfRootCfg`: `stage3_inc_pass2_to_root`,
     `stage3_decnz_pass2_zero_to_root`, `stage3_decnz_pass2_pos_to_root`.
-/

@[expose] public section

namespace ConjectureMachines.Semantics.Zf.Layer1

open Turing StateTransition ConjectureMachines.Semantics.Zf

open ConjectureMachines.Riemann543.Layer1
  (nSteps nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_reaches nSteps_eval_dom nSteps_of_halt mem_eval_iff_nSteps
   mk_append_replicate_zero default_eq_mk_nil
   default_cons_zero append_replicate_zero_default fin2_cases
   Tape.mkL Tape.mkL_cons Tape.mk'_cons Tape.mkL_default
   append_replicate_cons append_cons_snoc append_reverse_cons
   encodeReg encodeReg_length encodeReg_reverse append_encodeReg_reverse append_encodeReg
   encodeRegs encodeRegs_nil encodeRegs_cons encodeRegs_append
   regsTape regsTape_nil regsTape_cons regsTape_append
   list_take_cons_drop list_take_set_drop)

/-!
## 1. State Mapping & `nSteps` Scan Primitives for `Machines.zf432`
-/

set_option maxRecDepth 200000

/-- Fast binary-search transition function for `ConjectureMachines.Semantics.Zf.Machines.zf432`. -/
def refTrans (q : Fin 432) (a : Fin 2) : Option (Fin 2 × Dir × Fin 432) :=
  (if q.val < 216 then (if q.val < 108 then (if q.val < 54 then (if q.val < 27 then (if q.val < 13
    then (if q.val < 6 then (if q.val < 3 then (if q.val < 1 then (if a.val == 0 then some (1,
      .right, 1) else some (1, .left, 2)) else (if q.val < 2 then (if a.val == 0 then some (0,
        .left, 0) else some (0, .left, 3)) else (if a.val == 0 then some (1, .left,
          0) else some (1, .right, 60)))) else (if q.val < 4 then (if a.val == 0 then some (1,
            .left, 1) else some (1, .right,
              4)) else (if q.val < 5 then (if a.val == 0 then some (0, .right, 3) else some (0,
                .right, 1)) else (if a.val == 0 then some (1, .left, 92) else some (1, .right,
                  6))))) else (if q.val < 9 then (if q.val < 7 then (if a.val == 0 then some (0,
                    .right, 5) else some (1, .right,
                      7)) else (if q.val < 8 then (if a.val == 0 then some (0, .right,
                        60) else some (1, .right, 59)) else (if a.val == 0 then some (0, .right,
                          9) else none))) else (if q.val < 11 then (if q.val < 10 then (if a.val ==
                            0 then some (1, .right, 9) else some (1, .left,
                              92)) else (if a.val == 0 then some (0, .right, 12) else some (1,
                                .right, 10))) else (if q.val < 12 then (if a.val == 0 then some (0,
                                  .right, 13) else some (1, .right,
                                    11)) else (if a.val == 0 then some (1, .left,
                                      45) else some (0, .right,
                                        36)))))) else (if q.val < 20 then (if q.val < 16 then (if
                                          q.val < 14 then (if a.val == 0 then some (1, .right,
                                            41) else some (1, .right,
                                              13)) else (if q.val < 15 then (if a.val == 0 then
                                                some (0, .right, 10) else some (1, .right,
                                                  14)) else (if a.val == 0 then some (0, .right,
                                                    11) else some (1, .right,
                                                      15)))) else (if q.val < 18 then (if q.val <
                                                        17 then (if a.val == 0 then some (0,
                                                          .right, 14) else some (1, .right,
                                                            16)) else (if a.val == 0 then some (0,
                                                              .right, 15) else some (1, .right,
                                                                17))) else (if q.val < 19 then (if
                                                                  a.val == 0 then some (0, .right,
                                                                    34) else some (1, .right,
                                                                      18)) else (if a.val == 0 then
                                                                        some (0, .right,
                                                                          35) else some (1,
                                                                            .right, 19))))) else
                                                                              (if q.val < 23 then
                                                                                (if q.val < 21 then
                                                                                  (if a.val == 0
                                                                                    then some (0,
                                                                                      .right, 16)
                                                                                        else some
                                                                                          (1,
                                                                                            .right,
                                                                                              20))
                                                                                                else
  (if q.val < 22 then (if a.val == 0 then some (0, .right, 17) else some (1, .right, 21)) else (if
  a.val == 0 then some (0, .right, 20) else some (1, .right, 22)))) else (if q.val < 25 then (if
  q.val < 24 then (if a.val == 0 then some (0, .right, 21) else some (1, .right, 23)) else (if a.val
  == 0 then some (0, .right, 22) else some (1, .right, 24))) else (if q.val < 26 then (if a.val == 0
  then some (0, .right, 23) else some (1, .right, 25)) else (if a.val == 0 then some (0, .right, 24)
  else some (1, .right, 26))))))) else (if q.val < 40 then (if q.val < 33 then (if q.val < 30 then
  (if q.val < 28 then (if a.val == 0 then some (0, .right, 25) else some (1, .right, 27)) else (if
  q.val < 29 then (if a.val == 0 then some (0, .right, 26) else some (1, .right, 28)) else (if a.val
  == 0 then some (0, .right, 27) else some (1, .right, 29)))) else (if q.val < 31 then (if a.val ==
  0 then some (0, .right, 28) else some (1, .right, 30)) else (if q.val < 32 then (if a.val == 0
  then some (0, .right, 29) else some (1, .right, 31)) else (if a.val == 0 then some (0, .right, 30)
  else some (1, .right, 32))))) else (if q.val < 36 then (if q.val < 34 then (if a.val == 0 then
  some (0, .right, 31) else some (1, .right, 33)) else (if q.val < 35 then (if a.val == 0 then some
  (0, .right, 32) else some (1, .right, 34)) else (if a.val == 0 then some (0, .right, 33) else some
  (1, .right, 35)))) else (if q.val < 38 then (if q.val < 37 then (if a.val == 0 then some (0,
  .left, 12) else some (1, .right, 37)) else (if a.val == 0 then some (0, .right, 38) else some (1,
  .right, 37))) else (if q.val < 39 then (if a.val == 0 then some (0, .left, 39) else some (1,
  .right, 37)) else (if a.val == 0 then some (1, .left, 40) else some (1, .left, 39)))))) else (if
  q.val < 47 then (if q.val < 43 then (if q.val < 41 then (if a.val == 0 then some (0, .left, 43)
  else some (0, .left, 39)) else (if q.val < 42 then (if a.val == 0 then some (0, .left, 43) else
  some (0, .right, 42)) else (if a.val == 0 then some (1, .right, 41) else some (1, .right, 42))))
  else (if q.val < 45 then (if q.val < 44 then (if a.val == 0 then some (0, .left, 44) else some (1,
  .left, 43)) else (if a.val == 0 then some (0, .left, 89) else some (1, .left, 43))) else (if q.val
  < 46 then (if a.val == 0 then some (0, .left, 46) else some (1, .left, 45)) else (if a.val == 0
  then some (0, .left, 90) else some (1, .left, 45))))) else (if q.val < 50 then (if q.val < 48 then
  (if a.val == 0 then some (0, .right, 47) else some (0, .right, 48)) else (if q.val < 49 then (if
  a.val == 0 then some (0, .left, 5) else some (0, .right, 48)) else (if a.val == 0 then some (1,
  .right, 8) else some (0, .right, 24)))) else (if q.val < 52 then (if q.val < 51 then (if a.val ==
  0 then some (1, .right, 8) else some (0, .right, 25)) else (if a.val == 0 then some (1, .right, 8)
  else some (0, .right, 16))) else (if q.val < 53 then (if a.val == 0 then some (1, .right, 8) else
  some (0, .right, 17)) else (if a.val == 0 then some (1, .right, 8) else some (0, .right,
  26)))))))) else (if q.val < 81 then (if q.val < 67 then (if q.val < 60 then (if q.val < 57 then
  (if q.val < 55 then (if a.val == 0 then some (1, .right, 8) else some (0, .right, 27)) else (if
  q.val < 56 then (if a.val == 0 then some (1, .right, 8) else some (0, .right, 28)) else (if a.val
  == 0 then some (1, .right, 8) else some (0, .right, 29)))) else (if q.val < 58 then (if a.val == 0
  then some (1, .right, 8) else some (0, .right, 30)) else (if q.val < 59 then (if a.val == 0 then
  some (1, .right, 8) else some (0, .right, 31)) else (if a.val == 0 then some (1, .right, 8) else
  some (0, .right, 14))))) else (if q.val < 63 then (if q.val < 61 then (if a.val == 0 then some (1,
  .right, 8) else some (0, .right, 15)) else (if q.val < 62 then (if a.val == 0 then some (1,
  .right, 8) else some (0, .right, 32)) else (if a.val == 0 then some (1, .right, 8) else some (0,
  .right, 33)))) else (if q.val < 65 then (if q.val < 64 then (if a.val == 0 then some (1, .right,
  8) else some (0, .right, 34)) else (if a.val == 0 then some (1, .right, 8) else some (0, .right,
  35))) else (if q.val < 66 then (if a.val == 0 then some (1, .right, 8) else some (0, .right, 18))
  else (if a.val == 0 then some (1, .right, 8) else some (0, .right, 19)))))) else (if q.val < 74
  then (if q.val < 70 then (if q.val < 68 then (if a.val == 0 then some (1, .right, 8) else some (0,
  .right, 20)) else (if q.val < 69 then (if a.val == 0 then some (1, .right, 8) else some (0,
  .right, 21)) else (if a.val == 0 then some (1, .right, 8) else some (0, .right, 22)))) else (if
  q.val < 72 then (if q.val < 71 then (if a.val == 0 then some (1, .right, 8) else some (0, .right,
  23)) else (if a.val == 0 then some (0, .left, 86) else some (1, .left, 71))) else (if q.val < 73
  then (if a.val == 0 then some (0, .left, 71) else some (1, .left, 72)) else (if a.val == 0 then
  some (0, .left, 85) else some (1, .left, 73))))) else (if q.val < 77 then (if q.val < 75 then (if
  a.val == 0 then some (0, .left, 73) else some (1, .left, 74)) else (if q.val < 76 then (if a.val
  == 0 then some (0, .left, 74) else some (1, .left, 75)) else (if a.val == 0 then some (0, .left,
  75) else some (1, .left, 76)))) else (if q.val < 79 then (if q.val < 78 then (if a.val == 0 then
  some (0, .left, 76) else some (1, .left, 77)) else (if a.val == 0 then some (0, .left, 72) else
  some (1, .left, 78))) else (if q.val < 80 then (if a.val == 0 then some (0, .left, 78) else some
  (1, .left, 79)) else (if a.val == 0 then some (0, .left, 79) else some (1, .left, 80))))))) else
  (if q.val < 94 then (if q.val < 87 then (if q.val < 84 then (if q.val < 82 then (if a.val == 0
  then some (0, .left, 80) else some (1, .left, 81)) else (if q.val < 83 then (if a.val == 0 then
  some (0, .left, 81) else some (1, .left, 82)) else (if a.val == 0 then some (0, .left, 82) else
  some (1, .left, 83)))) else (if q.val < 85 then (if a.val == 0 then some (0, .left, 83) else some
  (1, .left, 84)) else (if q.val < 86 then (if a.val == 0 then some (0, .left, 84) else some (1,
  .left, 85)) else (if a.val == 0 then some (0, .right, 86) else some (1, .right, 87))))) else (if
  q.val < 90 then (if q.val < 88 then (if a.val == 0 then some (0, .right, 5) else some (1, .right,
  88)) else (if q.val < 89 then some (0, .right, 126) else (if a.val == 0 then some (1, .right, 47)
  else some (0, .left, 89)))) else (if q.val < 92 then (if q.val < 91 then (if a.val == 0 then some
  (0, .left, 89) else some (0, .left, 90)) else (if a.val == 0 then some (0, .left, 90) else some
  (0, .left, 91))) else (if q.val < 93 then (if a.val == 0 then some (0, .left, 92) else some (1,
  .left, 77)) else (if a.val == 0 then some (0, .left, 93) else some (0, .left, 92)))))) else (if
  q.val < 101 then (if q.val < 97 then (if q.val < 95 then (if a.val == 0 then some (0, .left, 94)
  else some (0, .left, 93)) else (if q.val < 96 then (if a.val == 0 then some (0, .left, 95) else
  some (0, .left, 94)) else (if a.val == 0 then some (0, .right, 328) else some (1, .right, 97))))
  else (if q.val < 99 then (if q.val < 98 then (if a.val == 0 then some (0, .right, 333) else some
  (1, .right, 418)) else (if a.val == 0 then some (0, .right, 99) else some (0, .left, 90))) else
  (if q.val < 100 then (if a.val == 0 then some (0, .right, 49) else some (1, .right, 100)) else (if
  a.val == 0 then some (0, .right, 101) else some (1, .right, 104))))) else (if q.val < 104 then (if
  q.val < 102 then (if a.val == 0 then some (0, .right, 49) else some (1, .right, 102)) else (if
  q.val < 103 then (if a.val == 0 then some (0, .right, 103) else some (0, .left, 90)) else (if
  a.val == 0 then some (0, .right, 50) else some (1, .right, 50)))) else (if q.val < 106 then (if
  q.val < 105 then (if a.val == 0 then some (0, .right, 105) else some (0, .left, 90)) else (if
  a.val == 0 then some (0, .right, 50) else some (1, .right, 328))) else (if q.val < 107 then (if
  a.val == 0 then some (0, .right, 98) else some (1, .right, 107)) else (if a.val == 0 then some (0,
  .right, 391) else some (1, .right, 405))))))))) else (if q.val < 162 then (if q.val < 135 then (if
  q.val < 121 then (if q.val < 114 then (if q.val < 111 then (if q.val < 109 then (if a.val == 0
  then some (0, .right, 98) else some (1, .right, 109)) else (if q.val < 110 then (if a.val == 0
  then some (0, .right, 395) else some (1, .right, 407)) else (if a.val == 0 then some (0, .right,
  49) else some (1, .right, 111)))) else (if q.val < 112 then (if a.val == 0 then some (0, .right,
  421) else some (1, .right, 410)) else (if q.val < 113 then (if a.val == 0 then some (0, .right,
  113) else some (1, .right, 117)) else (if a.val == 0 then some (0, .right, 63) else some (1,
  .right, 114))))) else (if q.val < 117 then (if q.val < 115 then (if a.val == 0 then some (0,
  .right, 115) else some (1, .right, 116)) else (if q.val < 116 then (if a.val == 0 then some (0,
  .right, 65) else some (0, .left, 93)) else (if a.val == 0 then some (0, .right, 415) else some (0,
  .left, 91)))) else (if q.val < 119 then (if q.val < 118 then (if a.val == 0 then some (0, .right,
  65) else some (1, .right, 118)) else (if a.val == 0 then some (0, .right, 420) else some (0,
  .left, 90))) else (if q.val < 120 then (if a.val == 0 then some (0, .right, 112) else some (1,
  .right, 120)) else (if a.val == 0 then some (0, .right, 388) else some (1, .right, 403)))))) else
  (if q.val < 128 then (if q.val < 124 then (if q.val < 122 then (if a.val == 0 then some (0,
  .right, 112) else some (1, .right, 421)) else (if q.val < 123 then (if a.val == 0 then some (0,
  .right, 123) else some (1, .right, 124)) else (if a.val == 0 then some (0, .right, 59) else some
  (0, .left, 90)))) else (if q.val < 126 then (if q.val < 125 then (if a.val == 0 then some (0,
  .right, 382) else some (1, .right, 125)) else (if a.val == 0 then some (0, .right, 401) else some
  (1, .right, 52))) else (if q.val < 127 then (if a.val == 0 then some (0, .right, 122) else some
  (1, .right, 127)) else (if a.val == 0 then some (0, .right, 381) else some (1, .right, 176)))))
  else (if q.val < 131 then (if q.val < 129 then (if a.val == 0 then some (0, .right, 405) else some
  (1, .right, 139)) else (if q.val < 130 then (if a.val == 0 then some (0, .right, 277) else some
  (1, .right, 130)) else (if a.val == 0 then some (0, .right, 288) else some (1, .right, 131))))
  else (if q.val < 133 then (if q.val < 132 then (if a.val == 0 then some (0, .right, 362) else some
  (1, .right, 132)) else (if a.val == 0 then some (0, .right, 315) else some (1, .right, 133))) else
  (if q.val < 134 then (if a.val == 0 then some (0, .right, 320) else some (1, .right, 134)) else
  (if a.val == 0 then some (0, .right, 316) else some (1, .right, 135))))))) else (if q.val < 148
  then (if q.val < 141 then (if q.val < 138 then (if q.val < 136 then (if a.val == 0 then some (0,
  .right, 360) else some (1, .right, 136)) else (if q.val < 137 then (if a.val == 0 then some (0,
  .right, 317) else some (1, .right, 137)) else (if a.val == 0 then some (0, .right, 289) else some
  (1, .right, 138)))) else (if q.val < 139 then (if a.val == 0 then some (0, .right, 319) else some
  (1, .right, 140)) else (if q.val < 140 then (if a.val == 0 then some (0, .right, 310) else some
  (1, .right, 150)) else (if a.val == 0 then some (0, .right, 280) else some (1, .right, 141)))))
  else (if q.val < 144 then (if q.val < 142 then (if a.val == 0 then some (0, .right, 359) else some
  (1, .right, 142)) else (if q.val < 143 then (if a.val == 0 then some (0, .right, 317) else some
  (1, .right, 143)) else (if a.val == 0 then some (0, .right, 360) else some (1, .right, 144))))
  else (if q.val < 146 then (if q.val < 145 then (if a.val == 0 then some (0, .right, 289) else some
  (1, .right, 145)) else (if a.val == 0 then some (0, .right, 318) else some (1, .right, 146))) else
  (if q.val < 147 then (if a.val == 0 then some (0, .right, 280) else some (1, .right, 147)) else
  (if a.val == 0 then some (0, .right, 301) else some (1, .right, 148)))))) else (if q.val < 155
  then (if q.val < 151 then (if q.val < 149 then (if a.val == 0 then some (0, .right, 343) else some
  (1, .right, 149)) else (if q.val < 150 then (if a.val == 0 then some (0, .right, 301) else some
  (1, .right, 151)) else (if a.val == 0 then some (0, .right, 407) else some (1, .right, 161))))
  else (if q.val < 153 then (if q.val < 152 then (if a.val == 0 then some (0, .right, 290) else some
  (1, .right, 152)) else (if a.val == 0 then some (0, .right, 358) else some (1, .right, 153))) else
  (if q.val < 154 then (if a.val == 0 then some (0, .right, 316) else some (1, .right, 154)) else
  (if a.val == 0 then some (0, .right, 366) else some (1, .right, 155))))) else (if q.val < 158 then
  (if q.val < 156 then (if a.val == 0 then some (0, .right, 302) else some (1, .right, 156)) else
  (if q.val < 157 then (if a.val == 0 then some (0, .right, 429) else some (1, .right, 157)) else
  (if a.val == 0 then some (0, .right, 302) else some (1, .right, 158)))) else (if q.val < 160 then
  (if q.val < 159 then (if a.val == 0 then some (0, .right, 316) else some (1, .right, 159)) else
  (if a.val == 0 then some (0, .right, 291) else some (1, .right, 160))) else (if q.val < 161 then
  (if a.val == 0 then some (0, .right, 318) else some (1, .right, 162)) else (if a.val == 0 then
  some (0, .right, 343) else some (1, .right, 170)))))))) else (if q.val < 189 then (if q.val < 175
  then (if q.val < 168 then (if q.val < 165 then (if q.val < 163 then (if a.val == 0 then some (0,
  .right, 319) else some (1, .right, 163)) else (if q.val < 164 then (if a.val == 0 then some (0,
  .right, 318) else some (1, .right, 164)) else (if a.val == 0 then some (0, .right, 344) else some
  (1, .right, 165)))) else (if q.val < 166 then (if a.val == 0 then some (0, .right, 67) else some
  (1, .right, 166)) else (if q.val < 167 then (if a.val == 0 then some (0, .right, 167) else none)
  else (if a.val == 0 then some (0, .right, 67) else some (1, .right, 168))))) else (if q.val < 171
  then (if q.val < 169 then (if a.val == 0 then some (0, .right, 169) else some (0, .left, 90)) else
  (if q.val < 170 then (if a.val == 0 then some (0, .right, 68) else some (1, .right, 68)) else (if
  a.val == 0 then some (0, .right, 108) else some (1, .right, 171)))) else (if q.val < 173 then (if
  q.val < 172 then (if a.val == 0 then some (0, .right, 106) else some (1, .right, 172)) else (if
  a.val == 0 then some (0, .right, 341) else some (1, .right, 173))) else (if q.val < 174 then (if
  a.val == 0 then some (0, .right, 312) else some (1, .right, 174)) else (if a.val == 0 then some
  (0, .right, 427) else some (1, .right, 175)))))) else (if q.val < 182 then (if q.val < 178 then
  (if q.val < 176 then (if a.val == 0 then some (0, .right, 394) else some (1, .right, 177)) else
  (if q.val < 177 then (if a.val == 0 then some (0, .right, 385) else some (1, .right, 187)) else
  (if a.val == 0 then some (0, .right, 405) else some (1, .right, 178)))) else (if q.val < 180 then
  (if q.val < 179 then (if a.val == 0 then some (0, .right, 119) else some (1, .right, 179)) else
  (if a.val == 0 then some (0, .right, 344) else some (1, .right, 180))) else (if q.val < 181 then
  (if a.val == 0 then some (0, .right, 108) else some (1, .right, 181)) else (if a.val == 0 then
  some (0, .right, 296) else some (1, .right, 182))))) else (if q.val < 185 then (if q.val < 183
  then (if a.val == 0 then some (0, .right, 306) else some (1, .right, 183)) else (if q.val < 184
  then (if a.val == 0 then some (0, .right, 429) else some (1, .right, 184)) else (if a.val == 0
  then some (0, .right, 339) else some (1, .right, 185)))) else (if q.val < 187 then (if q.val < 186
  then (if a.val == 0 then some (0, .right, 311) else some (1, .right, 186)) else (if a.val == 0
  then some (0, .right, 337) else some (1, .right, 188))) else (if q.val < 188 then (if a.val == 0
  then some (0, .right, 391) else some (1, .right, 198)) else (if a.val == 0 then some (0, .right,
  311) else some (1, .right, 189))))))) else (if q.val < 202 then (if q.val < 195 then (if q.val <
  192 then (if q.val < 190 then (if a.val == 0 then some (0, .right, 295) else some (1, .right,
  190)) else (if q.val < 191 then (if a.val == 0 then some (0, .right, 431) else some (1, .right,
  191)) else (if a.val == 0 then some (0, .right, 312) else some (1, .right, 192)))) else (if q.val
  < 193 then (if a.val == 0 then some (0, .right, 337) else some (1, .right, 193)) else (if q.val <
  194 then (if a.val == 0 then some (0, .right, 294) else some (1, .right, 194)) else (if a.val == 0
  then some (0, .right, 431) else some (1, .right, 195))))) else (if q.val < 198 then (if q.val <
  196 then (if a.val == 0 then some (0, .right, 339) else some (1, .right, 196)) else (if q.val <
  197 then (if a.val == 0 then some (0, .right, 287) else some (1, .right, 197)) else (if a.val == 0
  then some (0, .right, 311) else some (1, .right, 199)))) else (if q.val < 200 then (if q.val < 199
  then (if a.val == 0 then some (0, .right, 395) else some (1, .right, 209)) else (if a.val == 0
  then some (0, .right, 364) else some (1, .right, 200))) else (if q.val < 201 then (if a.val == 0
  then some (0, .right, 321) else some (1, .right, 201)) else (if a.val == 0 then some (0, .right,
  364) else some (1, .right, 202)))))) else (if q.val < 209 then (if q.val < 205 then (if q.val <
  203 then (if a.val == 0 then some (0, .right, 296) else some (1, .right, 203)) else (if q.val <
  204 then (if a.val == 0 then some (0, .right, 429) else some (1, .right, 204)) else (if a.val == 0
  then some (0, .right, 429) else some (1, .right, 205)))) else (if q.val < 207 then (if q.val < 206
  then (if a.val == 0 then some (0, .right, 272) else some (1, .right, 206)) else (if a.val == 0
  then some (0, .right, 264) else some (1, .right, 207))) else (if q.val < 208 then (if a.val == 0
  then some (0, .right, 339) else some (1, .right, 208)) else (if a.val == 0 then some (0, .right,
  368) else some (1, .right, 210))))) else (if q.val < 212 then (if q.val < 210 then (if a.val == 0
  then some (0, .right, 310) else some (1, .right, 220)) else (if q.val < 211 then (if a.val == 0
  then some (0, .right, 313) else some (1, .right, 211)) else (if a.val == 0 then some (0, .right,
  297) else some (1, .right, 212)))) else (if q.val < 214 then (if q.val < 213 then (if a.val == 0
  then some (0, .right, 341) else some (1, .right, 213)) else (if a.val == 0 then some (0, .right,
  297) else some (1, .right, 214))) else (if q.val < 215 then (if a.val == 0 then some (0, .right,
  313) else some (1, .right, 215)) else (if a.val == 0 then some (0, .right, 362) else some (1,
  .right, 216)))))))))) else (if q.val < 324 then (if q.val < 270 then (if q.val < 243 then (if
  q.val < 229 then (if q.val < 222 then (if q.val < 219 then (if q.val < 217 then (if a.val == 0
  then some (0, .right, 386) else some (1, .right, 217)) else (if q.val < 218 then (if a.val == 0
  then some (0, .right, 403) else some (1, .right, 218)) else (if a.val == 0 then some (0, .right,
  298) else some (1, .right, 219)))) else (if q.val < 220 then (if a.val == 0 then some (0, .right,
  392) else some (1, .right, 221)) else (if q.val < 221 then (if a.val == 0 then some (0, .right,
  399) else some (1, .right, 231)) else (if a.val == 0 then some (0, .right, 405) else some (1,
  .right, 222))))) else (if q.val < 225 then (if q.val < 223 then (if a.val == 0 then some (0,
  .right, 298) else some (1, .right, 223)) else (if q.val < 224 then (if a.val == 0 then some (0,
  .right, 272) else some (1, .right, 224)) else (if a.val == 0 then some (0, .right, 286) else some
  (1, .right, 225)))) else (if q.val < 227 then (if q.val < 226 then (if a.val == 0 then some (0,
  .right, 315) else some (1, .right, 226)) else (if a.val == 0 then some (0, .right, 339) else some
  (1, .right, 227))) else (if q.val < 228 then (if a.val == 0 then some (0, .right, 286) else some
  (1, .right, 228)) else (if a.val == 0 then some (0, .right, 368) else some (1, .right, 229))))))
  else (if q.val < 236 then (if q.val < 232 then (if q.val < 230 then (if a.val == 0 then some (0,
  .right, 370) else some (1, .right, 230)) else (if q.val < 231 then (if a.val == 0 then some (0,
  .right, 283) else some (1, .right, 232)) else (if a.val == 0 then some (0, .right, 310) else some
  (1, .right, 242)))) else (if q.val < 234 then (if q.val < 233 then (if a.val == 0 then some (0,
  .right, 368) else some (1, .right, 233)) else (if a.val == 0 then some (0, .right, 324) else some
  (1, .right, 234))) else (if q.val < 235 then (if a.val == 0 then some (0, .right, 322) else some
  (1, .right, 235)) else (if a.val == 0 then some (0, .right, 264) else some (1, .right, 236)))))
  else (if q.val < 239 then (if q.val < 237 then (if a.val == 0 then some (0, .right, 366) else some
  (1, .right, 237)) else (if q.val < 238 then (if a.val == 0 then some (0, .right, 341) else some
  (1, .right, 238)) else (if a.val == 0 then some (0, .right, 339) else some (1, .right, 239))))
  else (if q.val < 241 then (if q.val < 240 then (if a.val == 0 then some (0, .right, 366) else some
  (1, .right, 240)) else (if a.val == 0 then some (0, .right, 305) else some (1, .right, 241))) else
  (if q.val < 242 then (if a.val == 0 then some (0, .right, 359) else some (1, .right, 243)) else
  (if a.val == 0 then some (0, .right, 403) else some (1, .right, 253))))))) else (if q.val < 256
  then (if q.val < 249 then (if q.val < 246 then (if q.val < 244 then (if a.val == 0 then some (0,
  .right, 314) else some (1, .right, 244)) else (if q.val < 245 then (if a.val == 0 then some (0,
  .right, 366) else some (1, .right, 245)) else (if a.val == 0 then some (0, .right, 288) else some
  (1, .right, 246)))) else (if q.val < 247 then (if a.val == 0 then some (0, .right, 304) else some
  (1, .right, 247)) else (if q.val < 248 then (if a.val == 0 then some (0, .right, 314) else some
  (1, .right, 248)) else (if a.val == 0 then some (0, .right, 291) else some (1, .right, 249)))))
  else (if q.val < 252 then (if q.val < 250 then (if a.val == 0 then some (0, .right, 343) else some
  (1, .right, 250)) else (if q.val < 251 then (if a.val == 0 then some (0, .right, 300) else some
  (1, .right, 251)) else (if a.val == 0 then some (0, .right, 344) else some (1, .right, 252))))
  else (if q.val < 254 then (if q.val < 253 then (if a.val == 0 then some (0, .right, 360) else some
  (1, .right, 254)) else (if a.val == 0 then some (0, .right, 310) else some (1, .right, 128))) else
  (if q.val < 255 then (if a.val == 0 then some (0, .right, 316) else some (1, .right, 255)) else
  (if a.val == 0 then some (0, .right, 308) else some (1, .right, 256)))))) else (if q.val < 263
  then (if q.val < 259 then (if q.val < 257 then (if a.val == 0 then some (0, .right, 359) else some
  (1, .right, 257)) else (if q.val < 258 then (if a.val == 0 then some (0, .right, 300) else some
  (1, .right, 258)) else (if a.val == 0 then some (0, .right, 315) else some (1, .right, 259))))
  else (if q.val < 261 then (if q.val < 260 then (if a.val == 0 then some (0, .right, 364) else some
  (1, .right, 260)) else (if a.val == 0 then some (0, .right, 358) else some (1, .right, 261))) else
  (if q.val < 262 then (if a.val == 0 then some (0, .right, 290) else some (1, .right, 262)) else
  (if a.val == 0 then some (0, .right, 277) else some (1, .right, 263))))) else (if q.val < 266 then
  (if q.val < 264 then (if a.val == 0 then some (0, .right, 429) else some (1, .right, 129)) else
  (if q.val < 265 then (if a.val == 0 then some (0, .right, 429) else some (1, .right, 265)) else
  (if a.val == 0 then some (0, .right, 283) else some (1, .right, 266)))) else (if q.val < 268 then
  (if q.val < 267 then (if a.val == 0 then some (0, .right, 366) else some (1, .right, 267)) else
  (if a.val == 0 then some (0, .right, 324) else some (1, .right, 268))) else (if q.val < 269 then
  (if a.val == 0 then some (0, .right, 366) else some (1, .right, 269)) else (if a.val == 0 then
  some (0, .right, 287) else some (1, .right, 270)))))))) else (if q.val < 297 then (if q.val < 283
  then (if q.val < 276 then (if q.val < 273 then (if q.val < 271 then (if a.val == 0 then some (0,
  .right, 368) else some (1, .right, 271)) else (if q.val < 272 then (if a.val == 0 then some (0,
  .right, 341) else some (1, .right, 337)) else (if a.val == 0 then some (0, .right, 306) else some
  (1, .right, 273)))) else (if q.val < 274 then (if a.val == 0 then some (0, .right, 325) else some
  (1, .right, 274)) else (if q.val < 275 then (if a.val == 0 then some (0, .right, 364) else some
  (1, .right, 275)) else (if a.val == 0 then some (0, .right, 339) else some (1, .right, 276)))))
  else (if q.val < 279 then (if q.val < 277 then (if a.val == 0 then some (0, .right, 296) else some
  (1, .right, 364)) else (if q.val < 278 then (if a.val == 0 then some (0, .right, 360) else some
  (1, .right, 278)) else (if a.val == 0 then some (0, .right, 307) else some (1, .right, 279))))
  else (if q.val < 281 then (if q.val < 280 then (if a.val == 0 then some (0, .right, 308) else some
  (1, .right, 318)) else (if a.val == 0 then some (0, .right, 288) else some (1, .right, 281))) else
  (if q.val < 282 then (if a.val == 0 then some (0, .right, 315) else some (1, .right, 282)) else
  (if a.val == 0 then some (0, .right, 344) else some (1, .right, 358)))))) else (if q.val < 290
  then (if q.val < 286 then (if q.val < 284 then (if a.val == 0 then some (0, .right, 306) else some
  (1, .right, 284)) else (if q.val < 285 then (if a.val == 0 then some (0, .right, 368) else some
  (1, .right, 285)) else (if a.val == 0 then some (0, .right, 337) else some (1, .right, 341))))
  else (if q.val < 288 then (if q.val < 287 then (if a.val == 0 then some (0, .right, 294) else some
  (1, .right, 339)) else (if a.val == 0 then some (0, .right, 295) else some (1, .right, 339))) else
  (if q.val < 289 then (if a.val == 0 then some (0, .right, 304) else some (1, .right, 429)) else
  (if a.val == 0 then some (0, .right, 366) else some (1, .right, 307))))) else (if q.val < 293 then
  (if q.val < 291 then (if a.val == 0 then some (0, .right, 359) else some (1, .right, 304)) else
  (if q.val < 292 then (if a.val == 0 then some (0, .right, 366) else some (1, .right, 292)) else
  (if a.val == 0 then some (0, .right, 429) else some (1, .right, 293)))) else (if q.val < 295 then
  (if q.val < 294 then (if a.val == 0 then some (0, .right, 362) else some (1, .right, 364)) else
  (if a.val == 0 then some (0, .right, 320) else some (1, .right, 326))) else (if q.val < 296 then
  (if a.val == 0 then some (0, .right, 305) else some (1, .right, 337)) else (if a.val == 0 then
  some (0, .right, 337) else some (1, .right, 325))))))) else (if q.val < 310 then (if q.val < 303
  then (if q.val < 300 then (if q.val < 298 then (if a.val == 0 then some (0, .right, 321) else some
  (1, .right, 366)) else (if q.val < 299 then (if a.val == 0 then some (0, .right, 397) else some
  (1, .right, 299)) else (if a.val == 0 then some (0, .right, 403) else some (1, .right, 121))))
  else (if q.val < 301 then (if a.val == 0 then some (0, .right, 358) else some (1, .right, 322))
  else (if q.val < 302 then (if a.val == 0 then some (0, .right, 343) else some (1, .right, 323))
  else (if a.val == 0 then some (0, .right, 358) else some (1, .right, 303))))) else (if q.val < 306
  then (if q.val < 304 then (if a.val == 0 then some (0, .right, 343) else some (1, .right, 368))
  else (if q.val < 305 then (if a.val == 0 then some (0, .right, 359) else some (1, .right, 323))
  else (if a.val == 0 then some (0, .right, 429) else some (1, .right, 320)))) else (if q.val < 308
  then (if q.val < 307 then (if a.val == 0 then some (0, .right, 344) else some (1, .right, 321))
  else (if a.val == 0 then some (0, .right, 360) else some (1, .right, 327))) else (if q.val < 309
  then (if a.val == 0 then some (0, .right, 358) else some (1, .right, 309)) else (if a.val == 0
  then some (0, .right, 337) else some (1, .right, 364)))))) else (if q.val < 317 then (if q.val <
  313 then (if q.val < 311 then (if a.val == 0 then some (0, .right, 352) else some (1, .right,
  416)) else (if q.val < 312 then (if a.val == 0 then some (0, .right, 341) else some (1, .right,
  429)) else (if a.val == 0 then some (0, .right, 337) else some (1, .right, 429)))) else (if q.val
  < 315 then (if q.val < 314 then (if a.val == 0 then some (0, .right, 364) else some (1, .right,
  429)) else (if a.val == 0 then some (0, .right, 359) else some (1, .right, 343))) else (if q.val <
  316 then (if a.val == 0 then some (0, .right, 364) else some (1, .right, 370)) else (if a.val == 0
  then some (0, .right, 358) else some (1, .right, 359))))) else (if q.val < 320 then (if q.val <
  318 then (if a.val == 0 then some (0, .right, 360) else some (1, .right, 359)) else (if q.val <
  319 then (if a.val == 0 then some (0, .right, 362) else some (1, .right, 370)) else (if a.val == 0
  then some (0, .right, 429) else some (1, .right, 364)))) else (if q.val < 322 then (if q.val < 321
  then (if a.val == 0 then some (0, .right, 429) else some (1, .right, 344)) else (if a.val == 0
  then some (0, .right, 337) else some (1, .right, 339))) else (if q.val < 323 then (if a.val == 0
  then some (0, .right, 368) else some (1, .right, 429)) else (if a.val == 0 then some (0, .right,
  358) else some (1, .right, 366))))))))) else (if q.val < 378 then (if q.val < 351 then (if q.val <
  337 then (if q.val < 330 then (if q.val < 327 then (if q.val < 325 then (if a.val == 0 then some
  (0, .right, 339) else some (1, .right, 341)) else (if q.val < 326 then (if a.val == 0 then some
  (0, .right, 341) else some (1, .right, 364)) else (if a.val == 0 then some (0, .right, 337) else
  some (1, .right, 337)))) else (if q.val < 328 then (if a.val == 0 then some (0, .right, 343) else
  some (1, .right, 366)) else (if q.val < 329 then (if a.val == 0 then some (0, .right, 353) else
  some (1, .right, 419)) else (if a.val == 0 then some (0, .right, 422) else some (1, .right,
  330))))) else (if q.val < 333 then (if q.val < 331 then (if a.val == 0 then some (0, .right, 69)
  else some (1, .right, 331)) else (if q.val < 332 then (if a.val == 0 then some (0, .right, 332)
  else some (0, .left, 94)) else (if a.val == 0 then some (0, .right, 62) else some (1, .right,
  428)))) else (if q.val < 335 then (if q.val < 334 then (if a.val == 0 then some (0, .right, 412)
  else some (1, .right, 334)) else (if a.val == 0 then some (0, .right, 67) else some (1, .right,
  335))) else (if q.val < 336 then (if a.val == 0 then some (0, .right, 336) else some (0, .left,
  94)) else (if a.val == 0 then some (0, .right, 64) else some (1, .right, 425)))))) else (if q.val
  < 344 then (if q.val < 340 then (if q.val < 338 then (if a.val == 0 then some (0, .right, 343)
  else some (1, .right, 338)) else (if q.val < 339 then (if a.val == 0 then some (0, .right, 387)
  else some (1, .right, 403)) else (if a.val == 0 then some (0, .right, 343) else some (1, .right,
  340)))) else (if q.val < 342 then (if q.val < 341 then (if a.val == 0 then some (0, .right, 393)
  else some (1, .right, 405)) else (if a.val == 0 then some (0, .right, 343) else some (1, .right,
  342))) else (if q.val < 343 then (if a.val == 0 then some (0, .right, 396) else some (1, .right,
  407)) else (if a.val == 0 then some (0, .right, 329) else some (1, .right, 411))))) else (if q.val
  < 347 then (if q.val < 345 then (if a.val == 0 then some (0, .right, 425) else some (1, .right,
  345)) else (if q.val < 346 then (if a.val == 0 then some (0, .right, 354) else some (1, .right,
  346)) else (if a.val == 0 then some (0, .right, 419) else some (1, .right, 347)))) else (if q.val
  < 349 then (if q.val < 348 then (if a.val == 0 then some (0, .right, 110) else some (1, .right,
  398)) else (if a.val == 0 then some (0, .right, 63) else some (0, .left, 94))) else (if q.val <
  350 then (if a.val == 0 then some (0, .right, 62) else some (1, .right, 350)) else (if a.val == 0
  then some (0, .right, 348) else some (1, .right, 351))))))) else (if q.val < 364 then (if q.val <
  357 then (if q.val < 354 then (if q.val < 352 then (if a.val == 0 then some (0, .right, 409) else
  some (0, .left, 95)) else (if q.val < 353 then (if a.val == 0 then some (0, .right, 59) else some
  (1, .right, 349)) else (if a.val == 0 then some (0, .right, 69) else some (1, .right, 349)))) else
  (if q.val < 355 then (if a.val == 0 then some (0, .right, 69) else some (1, .right, 355)) else (if
  q.val < 356 then (if a.val == 0 then some (0, .right, 68) else some (1, .right, 356)) else (if
  a.val == 0 then some (0, .right, 348) else some (1, .right, 357))))) else (if q.val < 360 then (if
  q.val < 358 then (if a.val == 0 then some (0, .right, 427) else some (0, .left, 95)) else (if
  q.val < 359 then (if a.val == 0 then some (0, .right, 343) else some (1, .right, 68)) else (if
  a.val == 0 then some (0, .right, 358) else some (1, .right, 68)))) else (if q.val < 362 then (if
  q.val < 361 then (if a.val == 0 then some (0, .right, 359) else some (1, .right, 68)) else (if
  a.val == 0 then some (0, .right, 360) else some (1, .right, 68))) else (if q.val < 363 then (if
  a.val == 0 then some (0, .right, 431) else some (1, .right, 363)) else (if a.val == 0 then some
  (0, .right, 429) else some (1, .right, 431)))))) else (if q.val < 371 then (if q.val < 367 then
  (if q.val < 365 then (if a.val == 0 then some (0, .right, 96) else some (1, .right, 365)) else (if
  q.val < 366 then (if a.val == 0 then some (0, .right, 361) else some (1, .right, 96)) else (if
  a.val == 0 then some (0, .right, 96) else some (1, .right, 367)))) else (if q.val < 369 then (if
  q.val < 368 then (if a.val == 0 then some (0, .right, 358) else some (1, .right, 96)) else (if
  a.val == 0 then some (0, .right, 96) else some (1, .right, 369))) else (if q.val < 370 then (if
  a.val == 0 then some (0, .right, 343) else some (1, .right, 96)) else (if a.val == 0 then some (0,
  .right, 431) else some (1, .right, 371))))) else (if q.val < 374 then (if q.val < 372 then (if
  a.val == 0 then some (0, .right, 364) else some (1, .right, 431)) else (if q.val < 373 then (if
  a.val == 0 then some (0, .right, 64) else some (0, .left, 93)) else (if a.val == 0 then some (0,
  .right, 374) else some (0, .left, 93)))) else (if q.val < 376 then (if q.val < 375 then (if a.val
  == 0 then some (0, .right, 62) else some (1, .right, 64)) else (if a.val == 0 then some (0,
  .right, 68) else some (0, .left, 93))) else (if q.val < 377 then (if a.val == 0 then some (0,
  .right, 377) else some (0, .left, 93)) else (if a.val == 0 then some (0, .right, 68) else some (1,
  .right, 62)))))))) else (if q.val < 405 then (if q.val < 391 then (if q.val < 384 then (if q.val <
  381 then (if q.val < 379 then (if a.val == 0 then some (0, .right, 70) else some (0, .left, 93))
  else (if q.val < 380 then (if a.val == 0 then some (0, .right, 380) else some (0, .left, 93)) else
  (if a.val == 0 then some (0, .right, 62) else some (1, .right, 66)))) else (if q.val < 382 then
  (if a.val == 0 then some (0, .right, 49) else some (0, .left, 92)) else (if q.val < 383 then (if
  a.val == 0 then some (0, .right, 51) else some (1, .right, 383)) else (if a.val == 0 then some (0,
  .right, 384) else some (0, .left, 93))))) else (if q.val < 387 then (if q.val < 385 then (if a.val
  == 0 then some (0, .right, 62) else some (1, .right, 60)) else (if q.val < 386 then (if a.val == 0
  then some (0, .right, 53) else some (0, .left, 92)) else (if a.val == 0 then some (0, .right, 53)
  else some (1, .right, 373)))) else (if q.val < 389 then (if q.val < 388 then (if a.val == 0 then
  some (0, .right, 53) else some (1, .right, 376)) else (if a.val == 0 then some (0, .right, 53)
  else some (1, .right, 389))) else (if q.val < 390 then (if a.val == 0 then some (0, .right, 390)
  else some (0, .left, 93)) else (if a.val == 0 then some (0, .right, 62) else some (1, .right,
  68)))))) else (if q.val < 398 then (if q.val < 394 then (if q.val < 392 then (if a.val == 0 then
  some (0, .right, 55) else some (0, .left, 92)) else (if q.val < 393 then (if a.val == 0 then some
  (0, .right, 55) else some (1, .right, 373)) else (if a.val == 0 then some (0, .right, 55) else
  some (1, .right, 376)))) else (if q.val < 396 then (if q.val < 395 then (if a.val == 0 then some
  (0, .right, 55) else some (1, .right, 379)) else (if a.val == 0 then some (0, .right, 57) else
  some (0, .left, 92))) else (if q.val < 397 then (if a.val == 0 then some (0, .right, 57) else some
  (1, .right, 376)) else (if a.val == 0 then some (0, .right, 57) else some (1, .right, 379)))))
  else (if q.val < 401 then (if q.val < 399 then (if a.val == 0 then some (0, .right, 61) else some
  (0, .left, 92)) else (if q.val < 400 then (if a.val == 0 then some (0, .right, 61) else some (1,
  .right, 400)) else (if a.val == 0 then some (0, .right, 50) else some (0, .left, 93)))) else (if
  q.val < 403 then (if q.val < 402 then (if a.val == 0 then some (0, .right, 61) else some (1,
  .right, 402)) else (if a.val == 0 then some (0, .right, 52) else some (0, .left, 93))) else (if
  q.val < 404 then (if a.val == 0 then some (0, .right, 61) else some (1, .right, 404)) else (if
  a.val == 0 then some (0, .right, 54) else some (0, .left, 93))))))) else (if q.val < 418 then (if
  q.val < 411 then (if q.val < 408 then (if q.val < 406 then (if a.val == 0 then some (0, .right,
  61) else some (1, .right, 406)) else (if q.val < 407 then (if a.val == 0 then some (0, .right, 56)
  else some (0, .left, 93)) else (if a.val == 0 then some (0, .right, 61) else some (1, .right,
  408)))) else (if q.val < 409 then (if a.val == 0 then some (0, .right, 58) else some (0, .left,
  93)) else (if q.val < 410 then (if a.val == 0 then some (0, .right, 61) else some (1, .right,
  372)) else (if a.val == 0 then some (0, .right, 61) else some (1, .right, 375))))) else (if q.val
  < 414 then (if q.val < 412 then (if a.val == 0 then some (0, .right, 61) else some (1, .right,
  378)) else (if q.val < 413 then (if a.val == 0 then some (0, .right, 61) else some (1, .right,
  413)) else (if a.val == 0 then some (0, .right, 414) else some (0, .left, 93)))) else (if q.val <
  416 then (if q.val < 415 then (if a.val == 0 then some (0, .right, 68) else some (1, .right, 64))
  else (if a.val == 0 then some (0, .right, 63) else some (0, .left, 92))) else (if q.val < 417 then
  (if a.val == 0 then some (0, .right, 63) else some (1, .right, 417)) else (if a.val == 0 then some
  (0, .right, 60) else some (0, .left, 93)))))) else (if q.val < 425 then (if q.val < 421 then (if
  q.val < 419 then (if a.val == 0 then some (0, .right, 63) else some (1, .right, 375)) else (if
  q.val < 420 then (if a.val == 0 then some (0, .right, 63) else some (1, .right, 378)) else (if
  a.val == 0 then some (0, .right, 65) else some (0, .left, 92)))) else (if q.val < 423 then (if
  q.val < 422 then (if a.val == 0 then some (0, .right, 67) else some (0, .left, 92)) else (if a.val
  == 0 then some (0, .right, 67) else some (1, .right, 423))) else (if q.val < 424 then (if a.val ==
  0 then some (0, .right, 424) else some (0, .left, 93)) else (if a.val == 0 then some (0, .right,
  70) else some (1, .right, 62))))) else (if q.val < 428 then (if q.val < 426 then (if a.val == 0
  then some (0, .right, 67) else some (1, .right, 426)) else (if q.val < 427 then (if a.val == 0
  then some (0, .right, 62) else some (0, .left, 93)) else (if a.val == 0 then some (0, .right, 67)
  else some (1, .right, 372)))) else (if q.val < 430 then (if q.val < 429 then (if a.val == 0 then
  some (0, .right, 69) else some (1, .right, 375)) else (if a.val == 0 then some (0, .right, 96)
  else some (1, .right, 430))) else (if q.val < 431 then (if a.val == 0 then some (0, .right, 359)
  else some (1, .right, 96)) else (if a.val == 0 then some (0, .right, 360) else some (1, .right,
  96)))))))))))

set_option maxHeartbeats 0 in
-- kernel `decide` over all 432 × 2 (state, symbol) pairs of `Machines.zf432.transition`
theorem refTrans_eq (q : Fin 432) (a : Fin 2) :
    Machines.zf432.transition q a = refTrans q a := by
  revert q a; decide


theorem step_mkL_left {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step Machines.zf432 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step Machines.zf432 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step Machines.zf432 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, refTrans_eq, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step Machines.zf432 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mkL_left_any {q q' : Fin 432}
    (h0 : refTrans q 0 = some (0, .left, q'))
    (h1 : refTrans q 1 = some (1, .left, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step Machines.zf432 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons a)⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mkL_left h0 L R
  · exact step_mkL_left h1 L R

theorem step_mk'_right_any {q q' : Fin 432}
    (h0 : refTrans q 0 = some (0, .right, q'))
    (h1 : refTrans q 1 = some (1, .right, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step Machines.zf432 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons a) R⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mk'_right h0 L R
  · exact step_mk'_right h1 L R

theorem step_mkL_left_const {q q' : Fin 432} {b : Fin 2}
    (h0 : refTrans q 0 = some (b, .left, q'))
    (h1 : refTrans q 1 = some (b, .left, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step Machines.zf432 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mkL_left h0 L R
  · exact step_mkL_left h1 L R

theorem move_right_append (l : List (Fin 2)) (L R : ListBlank (Fin 2))
    {q : Fin 432}
    (h0 : refTrans q 0 = some (0, .right, q))
    (h1 : refTrans q 1 = some (1, .right, q)) :
    nSteps Machines.zf432 l.length ⟨q, Tape.mk' L (ListBlank.append l R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append l.reverse L) R⟩ := by
  induction l generalizing L with
  | nil => rfl
  | cons a l ih =>
    have hstep : step Machines.zf432 ⟨q, Tape.mk' L ((ListBlank.append l R).cons a)⟩ =
        some ⟨q, Tape.mk' (L.cons a) (ListBlank.append l R)⟩ :=
      step_mk'_right_any h0 h1 a L (ListBlank.append l R)
    rw [List.length_cons, ListBlank.append, step_nSteps hstep (ih (L.cons a)), append_reverse_cons]

theorem move_left_append (l : List (Fin 2)) (L R : ListBlank (Fin 2))
    {q : Fin 432}
    (h0 : refTrans q 0 = some (0, .left, q))
    (h1 : refTrans q 1 = some (1, .left, q)) :
    nSteps Machines.zf432 l.length ⟨q, Tape.mkL (ListBlank.append l.reverse L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append l R)⟩ := by
  induction l using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
      ListBlank.append, List.length_append, List.length_singleton]
    have hstep : step Machines.zf432 ⟨q, Tape.mkL ((ListBlank.append l.reverse L).cons a) R⟩ =
        some ⟨q, Tape.mkL (ListBlank.append l.reverse L) (R.cons a)⟩ :=
      step_mkL_left_any h0 h1 a (ListBlank.append l.reverse L) R
    rw [step_nSteps hstep (ih (R.cons a)), append_cons_snoc]

theorem nSteps_mkL_left_scan {q : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {q : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

/-!
### Infrastructure State Constants (`Fin 432`)
-/

/-- `0a.boot1.A..E` = States `0..4`. -/
abbrev st_boot1_A : Fin 432 := 0
abbrev st_boot1_B : Fin 432 := 1
abbrev st_boot1_C : Fin 432 := 2
abbrev st_boot1_D : Fin 432 := 3
abbrev st_boot1_E : Fin 432 := 4

/-- `0b.boot2.0..2` = States `5..7`. -/
abbrev st_boot2_0 : Fin 432 := 5
abbrev st_boot2_1 : Fin 432 := 6
abbrev st_boot2_2 : Fin 432 := 7

/-- `1b.reg.prep_1..2` = States `8..9`. -/
abbrev st_reg_prep_1 : Fin 432 := 8
abbrev st_reg_prep_2 : Fin 432 := 9

/-- `2b.reg.dec.*` and `2b.reg.inc.*` = States `36..42`. -/
abbrev st_reg_dec_check : Fin 432 := 36
abbrev st_reg_dec_scan_1 : Fin 432 := 37
abbrev st_reg_dec_scan_2 : Fin 432 := 38
abbrev st_reg_dec_shift_1 : Fin 432 := 39
abbrev st_reg_dec_shift_2 : Fin 432 := 40
abbrev st_reg_inc_shift_1 : Fin 432 := 41
abbrev st_reg_inc_shift_2 : Fin 432 := 42

/-- `2c.reg.return_0_1..return_1_2` = States `43..46`. -/
abbrev st_reg_return_0_1 : Fin 432 := 43
abbrev st_reg_return_0_2 : Fin 432 := 44
abbrev st_reg_return_1_1 : Fin 432 := 45
abbrev st_reg_return_1_2 : Fin 432 := 46

/-- `2e.reg.cleanup_1..2` = States `47..48`. -/
abbrev st_reg_cleanup_1 : Fin 432 := 47
abbrev st_reg_cleanup_2 : Fin 432 := 48

/-- `4.dispatch.scan` = State `86`, `5.root.1` = State `87`, `5.root.1.1` = State `88`. -/
abbrev st_dispatch_scan : Fin 432 := 86
abbrev st_root_1 : Fin 432 := 87
abbrev st_root_1_1 : Fin 432 := 88

/-- `6.break.0..2` = States `89..91`, `6.continue.0..3` = States `92..95`. -/
abbrev st_break_0 : Fin 432 := 89
abbrev st_break_1 : Fin 432 := 90
abbrev st_break_2 : Fin 432 := 91
abbrev st_continue_0 : Fin 432 := 92
abbrev st_continue_1 : Fin 432 := 93
abbrev st_continue_2 : Fin 432 := 94
abbrev st_continue_3 : Fin 432 := 95

/-- `main().0` = State `126`. -/
abbrev st_main_0 : Fin 432 := 126

/-- `3.<reg_k>.inc` (States `49..70`) for register `0 ≤ k ≤ 10`:
`0 = prooflist`, `1 = nextproof`, `2 = topwff`, `3 = wffstack`, `4 = axiomcode`,
`5 = param1`, `6 = param2`, `7 = param3`, `8 = scratch1`, `9 = scratch2`, `10 = scratch3`. -/
def regIncStage3 : ℕ → Fin 432
  | 0 => 60
  | 1 => 52
  | 2 => 68
  | 3 => 70
  | 4 => 50
  | 5 => 54
  | 6 => 56
  | 7 => 58
  | 8 => 62
  | 9 => 64
  | 10 => 66
  | _ => 60

/-- `3.<reg_k>.decnz` (States `49..70`) for register `0 ≤ k ≤ 10`. -/
def regDecnzStage3 : ℕ → Fin 432
  | 0 => 59
  | 1 => 51
  | 2 => 67
  | 3 => 69
  | 4 => 49
  | 5 => 53
  | 6 => 55
  | 7 => 57
  | 8 => 61
  | 9 => 63
  | 10 => 65
  | _ => 59

/-- `2b.reg.<m-2>.inc` chain (`0 ↦ 2b.reg.-2.inc = 13`, `1 ↦ 2b.reg.-1.inc = 11`,
`k + 2 ↦ 2b.reg.<k>.inc` for `0 ≤ k ≤ 10`). -/
def zfRegIncrChain : ℕ → Fin 432
  | 0 => 13
  | 1 => 11
  | 2 => 15
  | 3 => 17
  | 4 => 21
  | 5 => 23
  | 6 => 25
  | 7 => 27
  | 8 => 29
  | 9 => 31
  | 10 => 33
  | 11 => 35
  | 12 => 19
  | _ => 13

/-- `2b.reg.<m-2>.dec` chain (`0 ↦ 2b.reg.-2.dec = 12`, `1 ↦ 2b.reg.-1.dec = 10`,
`k + 2 ↦ 2b.reg.<k>.dec` for `0 ≤ k ≤ 10`). -/
def zfRegDecrChain : ℕ → Fin 432
  | 0 => 12
  | 1 => 10
  | 2 => 14
  | 3 => 16
  | 4 => 20
  | 5 => 22
  | 6 => 24
  | 7 => 26
  | 8 => 28
  | 9 => 30
  | 10 => 32
  | 11 => 34
  | 12 => 18
  | _ => 12

/-- `4.dispatch` chain (`0 ↦ 4.dispatch.scan = 86`, `d + 1 ↦ 4.dispatch.<d>` for `0 ≤ d ≤ 14`). -/
def zfDispatchState : ℕ → Fin 432
  | 0 => 86
  | 1 => 71
  | 2 => 72
  | 3 => 78
  | 4 => 79
  | 5 => 80
  | 6 => 81
  | 7 => 82
  | 8 => 83
  | 9 => 84
  | 10 => 85
  | 11 => 73
  | 12 => 74
  | 13 => 75
  | 14 => 76
  | 15 => 77
  | _ => 86

/-!
## 2. Canonical Tape Layout at `main().0` (State `126`)
-/

/-- The `[1, 1, 0]` root prefix on the left half-tape at `main().0` (State `126`). -/
abbrev rootLeft : ListBlank (Fin 2) :=
  (default : ListBlank (Fin 2)).cons 1 |>.cons 1 |>.cons 0

theorem rootLeft_eq_append :
    rootLeft = ListBlank.append [1, 1, 0].reverse default := rfl

/-- Left half-tape after scanning right across `stack` from `main().0`. -/
def stackLeft (stack : List (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append stack.reverse rootLeft

theorem stackLeft_nil : stackLeft [] = rootLeft := rfl

theorem stackLeft_eq_append (stack : List (Fin 2)) :
    stackLeft stack = ListBlank.append ([1, 1, 0] ++ stack).reverse default := by
  rw [stackLeft, rootLeft_eq_append, List.reverse_append, ListBlank.append_assoc]

theorem stackLeft_append (s₁ s₂ : List (Fin 2)) :
    stackLeft (s₁ ++ s₂) = ListBlank.append s₂.reverse (stackLeft s₁) := by
  simp [stackLeft, ListBlank.append_assoc]

@[simp]
theorem stackLeft_append_singleton (w : List (Fin 2)) (a : Fin 2) :
    stackLeft (w ++ [a]) = (stackLeft w).cons a := by
  rw [stackLeft_append, List.reverse_singleton, ListBlank.append, ListBlank.append]

/-- Canonical configuration at `main().0` (State `126`):
- Left of head: `rootLeft = (default.cons 1 |>.cons 1 |>.cons 0)`.
- Right of head: `stack` followed by `padTotal - stack.length` zeros, the `[1, 0]` marker,
  the unary registers `encodeRegs regs`, and `extra` (which defaults to `default`). -/
def zfRootCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 432 2 :=
  ⟨126, Tape.mk' rootLeft
    (ListBlank.append
      (stack ++ List.replicate (padTotal - stack.length) 0 ++ [1, 0] ++ encodeRegs regs)
      extra)⟩

theorem zfRootCfg_default_eq (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    zfRootCfg padTotal stack regs default =
      ⟨126, Tape.mk' rootLeft
        (ListBlank.append stack
          (ListBlank.append (List.replicate (padTotal - stack.length) 0)
            (regsTape (0 :: regs))))⟩ := by
  unfold zfRootCfg
  simp only [List.append_assoc, ListBlank.append_assoc]
  rfl

/-- Prepared configuration at `main().0` (State `126`) after Pass 1 (`1b.reg.prep_1/2`):
the `pad` zeros (`pad = padTotal - stack.length ≥ 2`) and `[1, 0]` marker have been turned into
`[1, 0]` (the Pass-2 marker `1` and separator `0`) followed by `encodeReg (pad - 2)` (the `-1`
register) and `regs`. -/
def zfPrepCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 432 2 :=
  ⟨126, Tape.mk' rootLeft
    (ListBlank.append
      (stack ++ [1, 0] ++ encodeRegs ((padTotal - stack.length - 2) :: regs))
      extra)⟩

theorem zfPrepCfg_default_eq (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    zfPrepCfg padTotal stack regs default =
      ⟨126, Tape.mk' rootLeft
        (ListBlank.append stack
          ((regsTape ((padTotal - stack.length - 2) :: regs)).cons 0 |>.cons 1))⟩ := by
  unfold zfPrepCfg
  simp only [List.append_assoc, ListBlank.append_assoc]
  rfl

/-!
## 3. Return Scan via `4.dispatch`, `5.root`, and `6.continue`
-/

theorem zfDispatch_trans_zero (d : ℕ) (hd1 : 1 ≤ d) (hd15 : d ≤ 15) :
    refTrans (zfDispatchState d) 0 = some (0, .left, zfDispatchState (d - 1)) := by
  revert d hd1 hd15; decide

theorem zfDispatch_trans_one (d : ℕ) (hd1 : 1 ≤ d) (hd15 : d ≤ 15) :
    refTrans (zfDispatchState d) 1 = some (1, .left, zfDispatchState d) := by
  revert d hd1 hd15; decide

/-- One leftward step of `zfDispatchState d` (`1 ≤ d ≤ 15`) on symbol `a`: leaves `a` unchanged
and decrements `d` by `1` iff `a = 0`. -/
theorem step_zfDispatch (d : ℕ) (hd1 : 1 ≤ d) (hd15 : d ≤ 15) (a : Fin 2)
    (L R : ListBlank (Fin 2)) :
    step Machines.zf432 ⟨zfDispatchState d, Tape.mkL (L.cons a) R⟩ =
      some ⟨zfDispatchState (d - [a].count 0), Tape.mkL L (R.cons a)⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mkL_left (zfDispatch_trans_zero d hd1 hd15) L R
  · exact step_mkL_left (zfDispatch_trans_one d hd1 hd15) L R

/-- `zfDispatchState d` scans left across any bit-list `l` with `l.count 0 < d` and `d ≤ 15`
in `l.length` steps, leaving `l` unchanged and ending in `zfDispatchState (d - l.count 0)`. -/
theorem zfDispatch_scan_list (l : List (Fin 2)) (d : ℕ)
    (hcount : l.count 0 < d) (hd15 : d ≤ 15) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 l.length
      ⟨zfDispatchState d, Tape.mkL (ListBlank.append l.reverse L) R⟩ =
      some ⟨zfDispatchState (d - l.count 0), Tape.mkL L (ListBlank.append l R)⟩ := by
  induction l using List.reverseRecOn generalizing d R with
  | nil =>
    simp
  | append_singleton l a ih =>
    rw [List.count_append] at hcount
    have ha_le : [a].count 0 ≤ 1 := by rcases fin2_cases a with rfl | rfl <;> decide
    have hd1 : 1 ≤ d := by omega
    have hcount' : l.count 0 < d - [a].count 0 := by omega
    have hd15' : d - [a].count 0 ≤ 15 := by omega
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
      ListBlank.append, List.length_append, List.length_singleton]
    have hstep := step_zfDispatch d hd1 hd15 a (ListBlank.append l.reverse L) R
    have hrest := ih (d - [a].count 0) hcount' hd15' (R.cons a)
    have hsub : d - [a].count 0 - l.count 0 = d - (l ++ [a]).count 0 := by
      rw [List.count_append]; omega
    rw [hsub, append_cons_snoc] at hrest
    exact step_nSteps hstep hrest

/-- On the blank left tape `default`, `zfDispatchState k` (`1 ≤ k ≤ 15`) steps left `k` times
into `default` to reach `4.dispatch.scan` (`86`), then scans right `k + 1` times back to `R`. -/
theorem zfDispatch_bounce_default (k : ℕ) (_hk1 : 1 ≤ k) (hk15 : k ≤ 15)
    (R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (2 * k + 1)
      ⟨zfDispatchState k, Tape.mkL default R⟩ =
      some ⟨86, Tape.mk' default R⟩ := by
  have hleft : ∀ m, m ≤ 15 → ∀ R',
      nSteps Machines.zf432 m ⟨zfDispatchState m, Tape.mkL default R'⟩ =
        some ⟨86, Tape.mkL default (ListBlank.append (List.replicate m 0) R')⟩ := by
    intro m hm R'
    induction m generalizing R' with
    | zero => rfl
    | succ m ihm =>
      have hm1 : 1 ≤ m + 1 := by omega
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      have h1 : step Machines.zf432 ⟨zfDispatchState (m + 1), Tape.mkL default R'⟩ =
          some ⟨zfDispatchState m, Tape.mkL default (R'.cons 0)⟩ := by
        conv_lhs => rw [hdef]
        exact step_mkL_left (zfDispatch_trans_zero (m + 1) hm1 hm) default R'
      have hrest := ihm (by omega) (R'.cons 0)
      rw [append_replicate_cons] at hrest
      exact step_nSteps h1 hrest
  have hl := hleft k hk15 R
  conv at hl => rhs; rw [Tape.mkL_default]
  have hcons : (ListBlank.append (List.replicate k 0) R).cons 0 =
      ListBlank.append (List.replicate (k + 1) 0) R := by
    rw [List.replicate_succ, ListBlank.append]
  rw [hcons] at hl
  have hr := nSteps_mk'_right_scan (q := 86) (a := 0) (b := 0) (by rfl) (k + 1) default R
  rw [append_replicate_zero_default] at hr
  have hcomb := nSteps_bind_eq hl hr
  have hlen : k + (k + 1) = 2 * k + 1 := by omega
  rw [hlen] at hcomb
  exact hcomb

/-- From `4.dispatch.scan` (`86`) at `[1, 1, a]`, `Machines.zf432` takes 3 steps
(`86 -> 87 -> 88 -> 126`) to reach `main().0` (`126`) with `rootLeft` on the left tape. -/
theorem root_scan_to_main (a : Fin 2) (R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 3
      ⟨86, Tape.mk' default (ListBlank.append [1, 1, a] R)⟩ =
      some ⟨126, Tape.mk' rootLeft R⟩ := by
  simp only [ListBlank.append]
  have h1 : step Machines.zf432 ⟨86, Tape.mk' default (((R.cons a).cons 1).cons 1)⟩ =
      some ⟨87, Tape.mk' (ListBlank.cons 1 default) ((R.cons a).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step Machines.zf432 ⟨87, Tape.mk' (ListBlank.cons 1 default) ((R.cons a).cons 1)⟩ =
      some ⟨88, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons a)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step Machines.zf432 ⟨88, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons a)⟩ =
      some ⟨126, Tape.mk' rootLeft R⟩ := by
    rcases fin2_cases a with rfl | rfl
    · exact step_mk'_right (by rfl) _ _
    · exact step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- `0b.boot2.0/1` (`5`/`6`) scans right across a `[1, 0]` pair in 2 steps. -/
theorem boot2_scan_pair (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 2
      ⟨5, Tape.mk' L (ListBlank.append [1, 0] R)⟩ =
      some ⟨5, Tape.mk' ((L.cons 1).cons 0) R⟩ := by
  have h1 : step Machines.zf432 ⟨5, Tape.mk' L ((R.cons 0).cons 1)⟩ =
      some ⟨6, Tape.mk' (L.cons 1) (R.cons 0)⟩ :=
    step_mk'_right (by rfl) L (R.cons 0)
  have h2 : step Machines.zf432 ⟨6, Tape.mk' (L.cons 1) (R.cons 0)⟩ =
      some ⟨5, Tape.mk' ((L.cons 1).cons 0) R⟩ :=
    step_mk'_right (by rfl) (L.cons 1) R
  exact step_nSteps h1 (step_one h2)

/-- `0b.boot2.0..2` (`5 -> 6 -> 7`) on `[1, 1, 0]` transitions to `3.prooflist.inc` (`60`). -/
theorem boot2_to_inc0 (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 3
      ⟨5, Tape.mk' L (ListBlank.append [1, 1, 0] R)⟩ =
      some ⟨60, Tape.mk' (((L.cons 1).cons 1).cons 0) R⟩ := by
  have h1 : step Machines.zf432 ⟨5, Tape.mk' L (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (L.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step Machines.zf432 ⟨6, Tape.mk' (L.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨7, Tape.mk' ((L.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step Machines.zf432 ⟨7, Tape.mk' ((L.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨60, Tape.mk' (((L.cons 1).cons 1).cons 0) R⟩ :=
    step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- `0b.boot2.0..2` (`5 -> 6 -> 7`) on `[1, 1, 1]` transitions to `3.prooflist.decnz` (`59`). -/
theorem boot2_to_decnz0 (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 3
      ⟨5, Tape.mk' L (ListBlank.append [1, 1, 1] R)⟩ =
      some ⟨59, Tape.mk' (((L.cons 1).cons 1).cons 1) R⟩ := by
  have h1 : step Machines.zf432 ⟨5, Tape.mk' L (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨6, Tape.mk' (L.cons 1) ((R.cons 1).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step Machines.zf432 ⟨6, Tape.mk' (L.cons 1) ((R.cons 1).cons 1)⟩ =
      some ⟨7, Tape.mk' ((L.cons 1).cons 1) (R.cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step Machines.zf432 ⟨7, Tape.mk' ((L.cons 1).cons 1) (R.cons 1)⟩ =
      some ⟨59, Tape.mk' (((L.cons 1).cons 1).cons 1) R⟩ :=
    step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- From `zfDispatchState d` (`1 ≤ d ≤ 15`) with `stackLeft w` on the left tape and
`w.count 0 + 1 < d`, `Machines.zf432` returns all the way to `main().0` (State `126`) with
`rootLeft` on the left tape and `ListBlank.append w R` on the right tape. -/
theorem dispatch_return_to_main (w : List (Fin 2)) (d : ℕ)
    (hcount : w.count 0 + 1 < d) (hd15 : d ≤ 15) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨zfDispatchState d, Tape.mkL (stackLeft w) R⟩ =
      some ⟨126, Tape.mk' rootLeft (ListBlank.append w R)⟩ := by
  rw [stackLeft_eq_append]
  have hcnt : ([1, 1, 0] ++ w).count 0 < d := by
    rw [List.count_append]
    change 1 + w.count 0 < d
    omega
  have hscan := zfDispatch_scan_list ([1, 1, 0] ++ w) d hcnt hd15 default R
  set k := d - ([1, 1, 0] ++ w).count 0
  have hk1 : 1 ≤ k := by omega
  have hk15 : k ≤ 15 := by omega
  have hbounce := zfDispatch_bounce_default k hk1 hk15 (ListBlank.append ([1, 1, 0] ++ w) R)
  rw [ListBlank.append_assoc] at hbounce
  have hroot := root_scan_to_main 0 (ListBlank.append w R)
  have htotal := nSteps_bind_eq hscan (nSteps_bind_eq hbounce hroot)
  exact ⟨_, by omega, htotal⟩

/-- Return scan lemma from `6.continue.0` (State `92`): for any `w : List (Fin 2)` with
`w.count 0 ≤ 13`, `Machines.zf432` scans left across `stackLeft w` and returns to `main().0`
(State `126`) with `rootLeft` on the left tape and `ListBlank.append w R` on the right tape. -/
theorem continue0_return (w : List (Fin 2)) (hcount : w.count 0 ≤ 13) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨92, Tape.mkL (stackLeft w) R⟩ =
      some ⟨126, Tape.mk' rootLeft (ListBlank.append w R)⟩ := by
  induction w using List.reverseRecOn generalizing R with
  | nil =>
    rw [stackLeft_nil]
    have h1 : step Machines.zf432 ⟨92, Tape.mkL rootLeft R⟩ =
        some ⟨92, Tape.mkL ((ListBlank.cons 1 default).cons 1) (R.cons 0)⟩ :=
      step_mkL_left (by rfl) _ _
    have h2 : step Machines.zf432 ⟨92, Tape.mkL ((ListBlank.cons 1 default).cons 1) (R.cons 0)⟩ =
        some ⟨77, Tape.mkL (ListBlank.cons 1 default) ((R.cons 0).cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have h3 : step Machines.zf432 ⟨77, Tape.mkL (ListBlank.cons 1 default) ((R.cons 0).cons 1)⟩ =
        some ⟨77, Tape.mkL default (((R.cons 0).cons 1).cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have hbounce := zfDispatch_bounce_default 15 (by decide) (by decide)
      (((R.cons 0).cons 1).cons 1)
    have hroot := root_scan_to_main 0 R
    have htotal := step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hbounce hroot)))
    exact ⟨_, by omega, htotal⟩
  | append_singleton w a ih =>
    rw [stackLeft_append, List.reverse_singleton, ListBlank.append]
    rcases fin2_cases a with rfl | rfl
    · have hw : w.count 0 ≤ 13 := by
        rw [List.count_append] at hcount; omega
      have hstep : step Machines.zf432 ⟨92, Tape.mkL ((stackLeft w).cons 0) R⟩ =
          some ⟨92, Tape.mkL (stackLeft w) (R.cons 0)⟩ :=
        step_mkL_left (by rfl) _ _
      obtain ⟨s, hs1, hrest⟩ := ih hw (R.cons 0)
      rw [append_cons_snoc] at hrest
      exact ⟨s + 1, by omega, step_nSteps hstep hrest⟩
    · have hw : w.count 0 + 1 < 15 := by
        rw [List.count_append] at hcount
        change w.count 0 + 0 ≤ 13 at hcount
        omega
      have hstep : step Machines.zf432 ⟨92, Tape.mkL ((stackLeft w).cons 1) R⟩ =
          some ⟨zfDispatchState 15, Tape.mkL (stackLeft w) (R.cons 1)⟩ :=
        step_mkL_left (by rfl) _ _
      obtain ⟨s, hs1, hrest⟩ := dispatch_return_to_main w 15 hw (by decide) (R.cons 1)
      rw [append_cons_snoc] at hrest
      exact ⟨s + 1, by omega, step_nSteps hstep hrest⟩

/-- `6.continue.0` (`92`) scans left across `z` zeros in `z` steps. -/
theorem continue0_scan_zeros (z : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 z
      ⟨92, Tape.mkL (ListBlank.append (List.replicate z 0) L) R⟩ =
      some ⟨92, Tape.mkL L (ListBlank.append (List.replicate z 0) R)⟩ :=
  nSteps_mkL_left_scan (by rfl) z L R

/-- `6.continue.1` (`93`) scans left across `z` zeros, turns the preceding `1` into `0`, and
enters `6.continue.0` (`92`). -/
theorem continue1_step (z : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (z + 1)
      ⟨93, Tape.mkL (ListBlank.append (List.replicate z 0) (L.cons 1)) R⟩ =
      some ⟨92, Tape.mkL L (ListBlank.append (List.replicate (z + 1) 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 93) (a := 0) (b := 0) (by rfl) z (L.cons 1) R
  have h1 : step Machines.zf432
      ⟨93, Tape.mkL (L.cons 1) (ListBlank.append (List.replicate z 0) R)⟩ =
      some ⟨92, Tape.mkL L ((ListBlank.append (List.replicate z 0) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq hscan (step_one h1)
  rwa [List.replicate_succ, ListBlank.append]

/-- `6.continue.2` (`94`) scans left across `z` zeros, turns the preceding `1` into `0`, and
enters `6.continue.1` (`93`). -/
theorem continue2_step (z : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (z + 1)
      ⟨94, Tape.mkL (ListBlank.append (List.replicate z 0) (L.cons 1)) R⟩ =
      some ⟨93, Tape.mkL L (ListBlank.append (List.replicate (z + 1) 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 94) (a := 0) (b := 0) (by rfl) z (L.cons 1) R
  have h1 : step Machines.zf432
      ⟨94, Tape.mkL (L.cons 1) (ListBlank.append (List.replicate z 0) R)⟩ =
      some ⟨93, Tape.mkL L ((ListBlank.append (List.replicate z 0) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq hscan (step_one h1)
  rwa [List.replicate_succ, ListBlank.append]

/-- `6.continue.3` (`95`) scans left across `z` zeros, turns the preceding `1` into `0`, and
enters `6.continue.2` (`94`). -/
theorem continue3_step (z : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (z + 1)
      ⟨95, Tape.mkL (ListBlank.append (List.replicate z 0) (L.cons 1)) R⟩ =
      some ⟨94, Tape.mkL L (ListBlank.append (List.replicate (z + 1) 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 95) (a := 0) (b := 0) (by rfl) z (L.cons 1) R
  have h1 : step Machines.zf432
      ⟨95, Tape.mkL (L.cons 1) (ListBlank.append (List.replicate z 0) R)⟩ =
      some ⟨94, Tape.mkL L ((ListBlank.append (List.replicate z 0) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq hscan (step_one h1)
  rwa [List.replicate_succ, ListBlank.append]

/-- Full return from `6.continue.1` (`93`) when the left tape is `stackLeft (w ++ [1])`. -/
theorem continue1_return (w : List (Fin 2)) (hw : w.count 0 ≤ 13) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨93, Tape.mkL (stackLeft (w ++ [1])) R⟩ =
      some ⟨126, Tape.mk' rootLeft (ListBlank.append w (R.cons 0))⟩ := by
  rw [stackLeft_append_singleton]
  have h1 := continue1_step 0 (stackLeft w) R
  simp only [List.replicate, ListBlank.append, Nat.zero_add] at h1
  obtain ⟨s, hs1, hret⟩ := continue0_return w hw (R.cons 0)
  exact ⟨1 + s, by omega, nSteps_bind_eq h1 hret⟩

/-- Full return from `6.continue.2` (`94`) when the left tape is `stackLeft (w ++ [1, 1])`. -/
theorem continue2_return (w : List (Fin 2)) (hw : w.count 0 ≤ 13) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨94, Tape.mkL (stackLeft (w ++ [1, 1])) R⟩ =
      some ⟨126, Tape.mk' rootLeft (ListBlank.append w ((R.cons 0).cons 0))⟩ := by
  have heq : w ++ [1, 1] = (w ++ [1]) ++ [1] := by simp
  rw [heq, stackLeft_append_singleton]
  have h1 := continue2_step 0 (stackLeft (w ++ [1])) R
  simp only [List.replicate, ListBlank.append, Nat.zero_add] at h1
  obtain ⟨s, hs1, hret⟩ := continue1_return w hw (R.cons 0)
  exact ⟨1 + s, by omega, nSteps_bind_eq h1 hret⟩

/-- Full return from `6.continue.3` (`95`) when the left tape is `stackLeft (w ++ [1, 1, 1])`. -/
theorem continue3_return (w : List (Fin 2)) (hw : w.count 0 ≤ 13) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨95, Tape.mkL (stackLeft (w ++ [1, 1, 1])) R⟩ =
      some ⟨126, Tape.mk' rootLeft (ListBlank.append w (((R.cons 0).cons 0).cons 0))⟩ := by
  have heq : w ++ [1, 1, 1] = (w ++ [1, 1]) ++ [1] := by simp
  rw [heq, stackLeft_append_singleton]
  have h1 := continue3_step 0 (stackLeft (w ++ [1, 1])) R
  simp only [List.replicate, ListBlank.append, Nat.zero_add] at h1
  obtain ⟨s, hs1, hret⟩ := continue2_return w hw (R.cons 0)
  exact ⟨1 + s, by omega, nSteps_bind_eq h1 hret⟩

/-!
## 4. Pass 1 Register Prep Gadget (`1b.reg.prep_1/2`, States `8..9`)
-/

/-- `1b.reg.prep_1/2` evaluation: from State `8` (`1b.reg.prep_1`) with
`L = (stackLeft stack).cons 1` and `p + 1` zeros before `[1, 0] ++ R`, `Machines.zf432` leaves
the first `0`, turns the remaining `p` zeros into `1`s, bounces on the `1` of `[1, 0]` into
`6.continue.0` (`92`), and returns to `main().0` (`126`) with `stack ++ [1, 0] ++ encodeReg p` on
the right tape. -/
theorem prep_pass1_eval (stack : List (Fin 2)) (hstack : stack.count 0 ≤ 12)
    (p : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨8, Tape.mk' ((stackLeft stack).cons 1)
        (ListBlank.append (List.replicate (p + 1) 0) (ListBlank.append [1, 0] R))⟩ =
      some ⟨126, Tape.mk' rootLeft
        (ListBlank.append (stack ++ [1, 0] ++ encodeReg p) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step Machines.zf432
      ⟨8, Tape.mk' ((stackLeft stack).cons 1)
        ((ListBlank.append (List.replicate p 0) (ListBlank.append [1, 0] R)).cons 0)⟩ =
      some ⟨9, Tape.mk' (((stackLeft stack).cons 1).cons 0)
        (ListBlank.append (List.replicate p 0) (ListBlank.append [1, 0] R))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 9) (a := 0) (b := 1) (by rfl) p
    (((stackLeft stack).cons 1).cons 0) (ListBlank.append [1, 0] R)
  have h2 : step Machines.zf432
      ⟨9, Tape.mk' (ListBlank.append (List.replicate p 1) (((stackLeft stack).cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨92, Tape.mkL (ListBlank.append (List.replicate p 1) (((stackLeft stack).cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ :=
    step_mk'_left (by rfl) _ (R.cons 0)
  have hL_eq : ListBlank.append (List.replicate p 1) (((stackLeft stack).cons 1).cons 0) =
      stackLeft (stack ++ [1, 0] ++ List.replicate p 1) := by
    rw [stackLeft_append, stackLeft_append, List.reverse_replicate]
    rfl
  conv at h2 => rhs; rw [hL_eq]
  have hrep0 : (List.replicate p (1 : Fin 2)).count 0 = 0 := by
    rw [List.count_replicate]; rfl
  have hw_cnt : (stack ++ [1, 0] ++ List.replicate p 1).count 0 ≤ 13 := by
    rw [List.count_append, List.count_append, hrep0]
    change stack.count 0 + 1 + 0 ≤ 13
    omega
  obtain ⟨s_ret, hs1, hret⟩ := continue0_return (stack ++ [1, 0] ++ List.replicate p 1) hw_cnt
    (ListBlank.append [1, 0] R)
  have hR_eq : ListBlank.append (stack ++ [1, 0] ++ List.replicate p 1)
      (ListBlank.append [1, 0] R) =
      ListBlank.append (stack ++ [1, 0] ++ encodeReg p) R := by
    simp only [encodeReg, List.replicate_succ', List.append_assoc, ListBlank.append_assoc]
    rfl
  rw [hR_eq] at hret
  exact ⟨_, by omega, step_nSteps h1 (nSteps_bind_eq hscan (step_nSteps h2 hret))⟩

theorem regIncStage3_trans_zero (k : ℕ) (hk : k < 11) :
    refTrans (regIncStage3 k) 0 = some (1, .right, 8) := by
  revert k hk; decide

theorem regDecnzStage3_trans_zero (k : ℕ) (hk : k < 11) :
    refTrans (regDecnzStage3 k) 0 = some (1, .right, 8) := by
  revert k hk; decide

/-- Pass 1 from `3.<reg_k>.inc` or `3.<reg_k>.decnz` when the head is at the first `0` of
the `pad` zeros (`padTotal - stack.length ≥ 2`): writes `1`, prepares the `-1` register
`encodeReg (padTotal - stack.length - 2)`, and returns to `zfPrepCfg padTotal stack regs extra`. -/
theorem stage3_pass1_from_stack {q : Fin 432} (hq : refTrans q 0 = some (1, .right, 8))
    (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) (extra : ListBlank (Fin 2))
    (hpad : stack.length + 2 ≤ padTotal) (hstack : stack.count 0 ≤ 12) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨q, Tape.mk' (stackLeft stack)
        (ListBlank.append (List.replicate (padTotal - stack.length) 0 ++ [1, 0] ++ encodeRegs regs)
          extra)⟩ =
      some (zfPrepCfg padTotal stack regs extra) := by
  set p := padTotal - stack.length - 2
  have hp_eq : padTotal - stack.length = (p + 1) + 1 := by omega
  rw [hp_eq, List.replicate_succ, List.cons_append, List.cons_append, ListBlank.append]
  have h1 : step Machines.zf432
      ⟨q, Tape.mk' (stackLeft stack)
        ((ListBlank.append (List.replicate (p + 1) 0 ++ [1, 0] ++ encodeRegs regs) extra).cons 0)⟩ =
      some ⟨8, Tape.mk' ((stackLeft stack).cons 1)
        (ListBlank.append (List.replicate (p + 1) 0)
          (ListBlank.append [1, 0] (ListBlank.append (encodeRegs regs) extra)))⟩ := by
    simp only [List.append_assoc, ListBlank.append_assoc]
    exact step_mk'_right hq (stackLeft stack) _
  obtain ⟨s, hs1, hprep⟩ :=
      prep_pass1_eval stack hstack p (ListBlank.append (encodeRegs regs) extra)
  have hcomb := step_nSteps h1 hprep
  unfold zfPrepCfg
  simp only [List.append_assoc, ListBlank.append_assoc, encodeRegs_cons] at hcomb ⊢
  exact ⟨s + 1, by omega, hcomb⟩

/-!
## 5. Pass 2 Register Return Scans (`2c.reg.return_0_1/2` = `43/44`, `2c.reg.return_1_1/2` =
`45/46`)
-/

/-- State `43` (`2c.reg.return_0_1`) scans left across `encodeReg r` in `r + 2` steps. -/
theorem return0_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (r + 2)
      ⟨43, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨43, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step Machines.zf432
      ⟨43, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨44, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step Machines.zf432
      ⟨44, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨43, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 43) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

/-- State `43` (`2c.reg.return_0_1`) scans left across `encodeRegs regs`. -/
theorem return0_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (encodeRegs regs).length
      ⟨43, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨43, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return0_scan_reg, ListBlank.append_assoc]

/-- State `43` (`2c.reg.return_0_1`) scans left across `regs` and the `[0, 0]` fence to reach
State `89` (`6.break.0`). -/
theorem return0_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 ((encodeRegs regs).length + 2)
      ⟨43, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨89, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return0_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step Machines.zf432
      ⟨43, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨44, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step Machines.zf432
      ⟨44, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨89, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-- State `45` (`2c.reg.return_1_1`) scans left across `encodeReg r` in `r + 2` steps. -/
theorem return1_scan_reg_zf (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (r + 2)
      ⟨45, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨45, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step Machines.zf432
      ⟨45, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨46, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step Machines.zf432
      ⟨46, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨45, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 45) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

/-- State `45` (`2c.reg.return_1_1`) scans left across `encodeRegs regs`. -/
theorem return1_scan_regs_zf (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (encodeRegs regs).length
      ⟨45, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨45, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return1_scan_reg_zf, ListBlank.append_assoc]

/-- State `45` (`2c.reg.return_1_1`) scans left across `regs` and the `[0, 0]` fence to reach
State `90` (`6.break.1`). -/
theorem return1_scan_fence_zf (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 ((encodeRegs regs).length + 2)
      ⟨45, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨90, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return1_scan_regs_zf regs ((L.cons 0).cons 0) R
  have h1 : step Machines.zf432
      ⟨45, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨46, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step Machines.zf432
      ⟨46, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨90, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-!
## 6. Pass 2 Register Increment & Decrement (`2b.reg.*`, States `10..42`)
-/

theorem regIncStage3_trans_one (k : ℕ) (hk : k < 11) :
    refTrans (regIncStage3 k) 1 = some (0, .right, zfRegIncrChain (k + 2)) := by
  revert k hk; decide

theorem zfRegIncrChain_trans_one (m : ℕ) (hm : m ≤ 12) :
    refTrans (zfRegIncrChain m) 1 = some (1, .right, zfRegIncrChain m) := by
  revert m hm; decide

theorem zfRegIncrChain_trans_zero (m : ℕ) (hm : m < 12) :
    refTrans (zfRegIncrChain (m + 1)) 0 = some (0, .right, zfRegIncrChain m) := by
  revert m hm; decide

/-- `zfRegIncrChain` scans right across `pref` (`pref.length ≤ 11`) and lands in State `13`
(`2b.reg.-2.inc`). -/
theorem zfRegIncrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 11)
    (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 ((encodeRegs pref).length + 1)
      ⟨zfRegIncrChain (pref.length + 1),
        Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨13, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length + 1 < 12 := by omega
    have hrs_le : rs.length ≤ 11 := by omega
    have h0 : step Machines.zf432
        ⟨zfRegIncrChain (rs.length + 1 + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨zfRegIncrChain (rs.length + 1),
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (zfRegIncrChain_trans_zero (rs.length + 1) hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan (zfRegIncrChain_trans_one (rs.length + 1) (by omega))
      (r + 1) (L.cons 0) ((ListBlank.append (encodeRegs rs) R).cons 0)
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
      ← encodeRegs_cons] at hrest
    have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
    have hlen : (r + 1) + ((encodeRegs rs).length + 1) + 1 =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

/-- Rightward shift in States `41`/`42` (`2b.reg.inc.shift_1/2`) and return scan across `m` in
States `43`/`44` (`2c.reg.return_0_1/2`). -/
theorem inc_shift_eval_zf (suff : List ℕ) (m : ℕ) (L_prev : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨41, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev) (regsTape suff)⟩ =
      some ⟨43, Tape.mkL L_prev (regsTape (m :: suff))⟩ := by
  induction suff generalizing m L_prev with
  | nil =>
    rw [regsTape_nil, List.replicate_succ, ListBlank.append]
    have h1 : step Machines.zf432
        ⟨41, Tape.mk' ((ListBlank.append (List.replicate m 1) L_prev).cons 1) default⟩ =
        some ⟨43, Tape.mkL ((ListBlank.append (List.replicate m 1) L_prev).cons 1)
          (ListBlank.cons 0 default)⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      exact step_mk'_left (by rfl) _ default
    have hscan := nSteps_mkL_left_scan (q := 43) (a := 1) (b := 1) (by rfl)
      (m + 1) L_prev (ListBlank.cons 0 default)
    conv at hscan => lhs; rw [List.replicate_succ, ListBlank.append]
    have hcomb := step_nSteps h1 hscan
    rw [← append_encodeReg, ← regsTape_nil, ← regsTape_cons] at hcomb
    exact ⟨m + 2, by omega, hcomb⟩
  | cons r rs ih =>
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step Machines.zf432
        ⟨41, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨42, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) L_prev).cons 0)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    rw [← append_encodeReg_reverse] at h1
    have hscan := nSteps_mk'_right_scan (q := 42) (a := 1) (b := 1) (by rfl)
      r (ListBlank.append (encodeReg m).reverse L_prev) ((regsTape rs).cons 0)
    have h2 : step Machines.zf432
        ⟨42, Tape.mk' (ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)) ((regsTape rs).cons 0)⟩ =
        some ⟨41, Tape.mk' ((ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)).cons 1) (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcons1 : (ListBlank.append (List.replicate r 1)
        (ListBlank.append (encodeReg m).reverse L_prev)).cons 1 =
        ListBlank.append (List.replicate (r + 1) 1)
          (ListBlank.append (encodeReg m).reverse L_prev) := by
      rw [List.replicate_succ, ListBlank.append]
    rw [hcons1] at h2
    obtain ⟨s, hs1, hs⟩ := ih r (ListBlank.append (encodeReg m).reverse L_prev)
    have hret := return0_scan_reg m L_prev (regsTape (r :: rs))
    rw [← regsTape_cons] at hret
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan
      (step_nSteps h2 (nSteps_bind_eq hs hret)))
    exact ⟨_, by omega, hcomb⟩

/-- Pass 2 `3.<reg_k>.inc` evaluation: when `regIncStage3 k` (`k < 11`, `k < regs.length`) sees the
Pass-1 marker `1`, it erases the marker, increments `regs[k]` by `1`, and returns to State `89`
(`6.break.0`) at the end of `L_stack`. -/
theorem stage3_inc_pass2 (k : ℕ) (hk11 : k < 11) (p : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨89, Tape.mkL L_stack
        ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩ := by
  set pref := p :: regs.take k
  set r := regs[k]
  set suff := regs.drop (k + 1)
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape (r :: suff)) := by
    have hlist : p :: regs = pref ++ r :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step Machines.zf432
      ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨zfRegIncrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape (r :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regIncStage3_trans_one k hk11) L_stack _
  have hpref_scan := zfRegIncrChain_scan_pref pref (by omega)
    (L_stack.cons 0) (regsTape (r :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have hr_scan : nSteps Machines.zf432 ((r + 1) + 1)
      ⟨13, Tape.mk' L_pref (regsTape (r :: suff))⟩ =
      some ⟨41, Tape.mk' (ListBlank.append (List.replicate (r + 2) 1) L_pref) (regsTape suff)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    have hones := nSteps_mk'_right_scan (q := 13) (a := 1) (b := 1) (by rfl)
      (r + 1) L_pref ((regsTape suff).cons 0)
    have hzero : step Machines.zf432
        ⟨13, Tape.mk' (ListBlank.append (List.replicate (r +
          1) 1) L_pref) ((regsTape suff).cons 0)⟩ =
        some ⟨41, Tape.mk' ((ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := nSteps_bind_eq hones (step_one hzero)
    have hcons : (ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1 =
        ListBlank.append (List.replicate (r + 2) 1) L_pref := by
      rw [← ListBlank.append, ← List.replicate_succ]
    rw [hcons] at hcomb
    exact hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := inc_shift_eval_zf suff (r + 1) L_pref
  have hret := return0_scan_fence pref L_stack (regsTape ((r + 1) :: suff))
  have hset : ListBlank.append (encodeRegs pref) (regsTape ((r + 1) :: suff)) =
      regsTape (p :: regs.set k (r + 1)) := by
    rw [← regsTape_append]
    congr 1
    simp only [pref, List.cons_append]
    congr 1
    exact list_take_set_drop regs k (r + 1) hk
  rw [hset] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (nSteps_bind_eq hr_scan (nSteps_bind_eq hshift hret)))
  exact ⟨_, by omega, htotal⟩

/-!
### 6.2 Pass 2 Register Decrement (`2b.reg.<k>.dec`, States `10, 12, 14..40`)
-/

theorem regDecnzStage3_trans_one (k : ℕ) (hk : k < 11) :
    refTrans (regDecnzStage3 k) 1 = some (0, .right, zfRegDecrChain (k + 2)) := by
  revert k hk; decide

theorem zfRegDecrChain_trans_one (m : ℕ) (hm1 : 1 ≤ m) (hm12 : m ≤ 12) :
    refTrans (zfRegDecrChain m) 1 = some (1, .right, zfRegDecrChain m) := by
  revert m hm1 hm12; decide

theorem zfRegDecrChain_trans_zero (m : ℕ) (hm : m < 12) :
    refTrans (zfRegDecrChain (m + 1)) 0 = some (0, .right, zfRegDecrChain m) := by
  revert m hm; decide

/-- `zfRegDecrChain` scans right across `pref` (`pref.length ≤ 11`) and lands in State `12`
(`2b.reg.-2.dec`). -/
theorem zfRegDecrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 11)
    (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 ((encodeRegs pref).length + 1)
      ⟨zfRegDecrChain (pref.length + 1),
        Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨12, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length + 1 < 12 := by omega
    have hrs_le : rs.length ≤ 11 := by omega
    have h0 : step Machines.zf432
        ⟨zfRegDecrChain (rs.length + 1 + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨zfRegDecrChain (rs.length + 1),
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (zfRegDecrChain_trans_zero (rs.length + 1) hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan
      (zfRegDecrChain_trans_one (rs.length + 1) (by omega) (by omega))
      (r + 1) (L.cons 0) ((ListBlank.append (encodeRegs rs) R).cons 0)
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
      ← encodeRegs_cons] at hrest
    have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
    have hlen : (r + 1) + ((encodeRegs rs).length + 1) + 1 =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

/-- Leftward shift of a single register `m` in States `40`/`39` (`2b.reg.dec.shift_2/1`). -/
theorem dec_shift_reg_zf (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (m + 2)
      ⟨40, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ =
      some ⟨40, Tape.mkL L (ListBlank.append (encodeReg m) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step Machines.zf432
      ⟨40, Tape.mkL ((ListBlank.append (List.replicate m 1) (L.cons 0)).cons 1) R⟩ =
      some ⟨39, Tape.mkL (ListBlank.append (List.replicate m 1) (L.cons 0)) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 39) (a := 1) (b := 1) (by rfl)
    m (L.cons 0) (R.cons 0)
  have h2 : step Machines.zf432
      ⟨39, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ =
      some ⟨40, Tape.mkL L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcons : (ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1 =
      ListBlank.append (encodeReg m) R := by
    rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  rw [hcons] at h2
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  simpa [Nat.add_assoc] using hcomb

/-- Forward scan across `suff` in States `38`/`37` (`2b.reg.dec.scan_2/1`) and leftward shift
in States `39`/`40` (`2b.reg.dec.shift_1/2`), appending a new `0` register (`encodeReg 0 = [1, 0]`)
at the end of `suff`. -/
theorem dec_scan_and_shift_zf (suff : List ℕ) (m : ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨38, Tape.mk' (ListBlank.append (encodeReg m).reverse (L.cons 0)) (regsTape suff)⟩ =
      some ⟨40, Tape.mkL L (regsTape (m :: (suff ++ [0])))⟩ := by
  induction suff generalizing m L with
  | nil =>
    rw [regsTape_nil, append_encodeReg_reverse]
    have h1 : step Machines.zf432
        ⟨38, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨39, Tape.mkL ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0)
          default⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      rw [step_mk'_left (by rfl), default_cons_zero]
    have h2 : step Machines.zf432
        ⟨39, Tape.mkL ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨40, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0))
          (regsTape [0])⟩ := by
      have h := step_mkL_left (q := 39) (q' := 40) (a := 0) (b := 1) (by rfl)
        (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default
      have h0 : (default : ListBlank (Fin 2)).cons 1 = regsTape [0] := by
        rw [regsTape_cons, regsTape_nil, append_encodeReg, default_cons_zero]
        rfl
      rw [h0] at h
      exact h
    have hshift := dec_shift_reg_zf m L (regsTape [0])
    rw [← regsTape_cons] at hshift
    exact ⟨m + 4, by omega, step_nSteps h1 (step_nSteps h2 hshift)⟩
  | cons r rs ih =>
    let L' := ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)
    have hL' : ListBlank.append (encodeReg m).reverse (L.cons 0) = L'.cons 0 :=
      append_encodeReg_reverse m (L.cons 0)
    rw [hL', regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step Machines.zf432
        ⟨38, Tape.mk' (L'.cons 0)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨37, Tape.mk' ((L'.cons 0).cons 1)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 37) (a := 1) (b := 1) (by rfl)
      r ((L'.cons 0).cons 1) ((regsTape rs).cons 0)
    have h2 : step Machines.zf432
        ⟨37, Tape.mk' (ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1))
          ((regsTape rs).cons 0)⟩ =
        some ⟨38, Tape.mk' ((ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1)).cons 0)
          (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan_reg := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r (L'.cons 0)] at hscan_reg
    obtain ⟨s, hs1, hs⟩ := ih r L'
    have hshift := dec_shift_reg_zf m L (regsTape (r :: (rs ++ [0])))
    rw [← regsTape_cons] at hshift
    have hcomb := nSteps_bind_eq hscan_reg (nSteps_bind_eq hs hshift)
    exact ⟨_, by omega, hcomb⟩

/-- State `40` (`2b.reg.dec.shift_2`) scans left across `encodeReg r` in `r + 2` steps and
transitions to State `43` (`2c.reg.return_0_1`). -/
theorem dec_shift2_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (r + 2)
      ⟨40, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨43, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step Machines.zf432
      ⟨40, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨43, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step Machines.zf432
      ⟨43, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨43, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 43) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

/-- State `40` (`2b.reg.dec.shift_2`) scans left across any non-empty register prefix `p :: rs`
and the `[0, 0]` fence to reach State `89` (`6.break.0`). -/
theorem dec_return0_scan_fence (p : ℕ) (rs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 ((encodeRegs (p :: rs)).length + 2)
      ⟨40, Tape.mkL (ListBlank.append (encodeRegs (p :: rs)).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨89, Tape.mkL L ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0 |>.cons 0)⟩ := by
  have hscan_nonempty : ∀ (pref : List ℕ), pref ≠ [] → ∀ L' R',
      nSteps Machines.zf432 (encodeRegs pref).length
        ⟨40, Tape.mkL (ListBlank.append (encodeRegs pref).reverse L') R'⟩ =
        some ⟨43, Tape.mkL L' (ListBlank.append (encodeRegs pref) R')⟩ := by
    intro pref hne L' R'
    induction pref using List.reverseRecOn generalizing L' R' with
    | nil => contradiction
    | append_singleton xs x _ =>
      rw [encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil,
        List.reverse_append, ListBlank.append_assoc, List.length_append,
        Nat.add_comm, nSteps_add, encodeReg_length,
        dec_shift2_scan_reg, Option.bind_some, return0_scan_regs, ListBlank.append_assoc]
  have hregs := hscan_nonempty (p :: rs) (List.cons_ne_nil p rs) ((L.cons 0).cons 0) R
  have h1 : step Machines.zf432
      ⟨43, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs (p :: rs)) R)⟩ =
      some ⟨44, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step Machines.zf432
      ⟨44, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0)⟩ =
      some ⟨89, Tape.mkL L (((ListBlank.append (encodeRegs (p :: rs)) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-- Pass 2 `3.<reg_k>.decnz` evaluation when `regs[k] = 0`: leaves `regs` unchanged and returns
to State `90` (`6.break.1`) at the end of `L_stack`. -/
theorem stage3_decnz_pass2_zero (k : ℕ) (hk11 : k < 11) (p : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hz : regs[k] = 0) (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨90, Tape.mkL L_stack ((regsTape (p :: regs)).cons 0 |>.cons 0)⟩ := by
  set pref := p :: regs.take k
  set suff := regs.drop (k + 1)
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape (0 :: suff)) := by
    have hlist : p :: regs = pref ++ 0 :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      rw [← hz]
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step Machines.zf432
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨zfRegDecrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape (0 :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecnzStage3_trans_one k hk11) L_stack _
  have hpref_scan := zfRegDecrChain_scan_pref pref (by omega)
    (L_stack.cons 0) (regsTape (0 :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have h1 : step Machines.zf432 ⟨12, Tape.mk' L_pref (regsTape (0 :: suff))⟩ =
      some ⟨36, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mk'_right (by rfl) L_pref ((regsTape suff).cons 0)
  have h2 : step Machines.zf432 ⟨36, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨12, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ :=
    step_mk'_left (by rfl) (L_pref.cons 0) (regsTape suff)
  have h3 : step Machines.zf432 ⟨12, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨45, Tape.mkL L_pref (regsTape (0 :: suff))⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mkL_left (by rfl) L_pref ((regsTape suff).cons 0)
  have hret := return1_scan_fence_zf pref L_stack (regsTape (0 :: suff))
  rw [← hregs_split] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps h1 (step_nSteps h2 (step_nSteps h3 hret))))
  exact ⟨_, by omega, htotal⟩

/-- Pass 2 `3.<reg_k>.decnz` evaluation when `regs[k] > 0`: decrements `regs[k]` by `1`, appends
a zero register `[0]` to `regs`, and returns to State `89` (`6.break.0`) at the end of `L_stack`. -/
theorem stage3_decnz_pass2_pos (k : ℕ) (hk11 : k < 11) (p : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hpos : 0 < regs[k]) (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨89, Tape.mkL L_stack
        ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0)⟩ := by
  set pref := p :: regs.take k
  set r' := regs[k] - 1
  set suff := regs.drop (k + 1)
  have hr_eq : regs[k] = r' + 1 := by omega
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape ((r' + 1) :: suff)) := by
    have hlist : p :: regs = pref ++ (r' + 1) :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      rw [← hr_eq]
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step Machines.zf432
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨zfRegDecrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape ((r' + 1) :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecnzStage3_trans_one k hk11) L_stack _
  have hpref_scan := zfRegDecrChain_scan_pref pref (by omega) (L_stack.cons 0)
    (regsTape ((r' + 1) :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have hinit : step Machines.zf432 ⟨12, Tape.mk' L_pref (regsTape ((r' + 1) :: suff))⟩ =
      some ⟨36, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ := by
    have hcons : regsTape ((r' + 1) :: suff) = (regsTape (r' :: suff)).cons 1 := by
      rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append,
        ← append_encodeReg, ← regsTape_cons]
    rw [hcons]
    exact step_mk'_right (by rfl) L_pref (regsTape (r' :: suff))
  have hr'_scan : nSteps Machines.zf432 (r' + 2)
      ⟨36, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ =
      some ⟨38, Tape.mk' (ListBlank.append (encodeReg r').reverse (L_pref.cons 0)) (regsTape suff)⟩
        := by
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step Machines.zf432
        ⟨36, Tape.mk' (L_pref.cons 0)
          ((ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0)).cons 1)⟩ =
        some ⟨37, Tape.mk' ((L_pref.cons 0).cons 1)
          (ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 37) (a := 1) (b := 1) (by rfl)
      r' ((L_pref.cons 0).cons 1) ((regsTape suff).cons 0)
    have h2 : step Machines.zf432
        ⟨37, Tape.mk' (ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1))
          ((regsTape suff).cons 0)⟩ =
        some ⟨38, Tape.mk' ((ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1)).cons
          0)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r' (L_pref.cons 0)] at hcomb
    simpa [Nat.add_assoc] using hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := dec_scan_and_shift_zf suff r' L_pref
  have hret := dec_return0_scan_fence p (regs.take k) L_stack (regsTape (r' :: (suff ++ [0])))
  have hset : ListBlank.append (encodeRegs pref) (regsTape (r' :: (suff ++ [0]))) =
      regsTape (p :: (regs.set k r' ++ [0])) := by
    rw [← regsTape_append]
    congr 1
    have h1 : pref ++ r' :: (suff ++ [0]) = p :: ((regs.take k ++ r' :: suff) ++ [0]) := by
      simp [pref]
    rw [h1, list_take_set_drop regs k r' hk]
  rw [hset] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps hinit (nSteps_bind_eq hr'_scan (nSteps_bind_eq hshift hret))))
  exact ⟨_, by omega, htotal⟩

/-!
## 7. Break & Register Cleanup Gadgets (`6.break.0..2` = `89..91`, `2e.reg.cleanup_1/2` = `47/48`,
`0b.boot2.0` = `5`)
-/

/-- From `2e.reg.cleanup_1` (`47`) with `z` zeros followed by `encodeReg m` on the right tape,
`Machines.zf432` clears `encodeReg m` to `m` zeros followed by `[1, 0]` (via `0b.boot2.0` = `5`),
transitions to `6.continue.0` (`92`), and returns to `main().0` (`126`) with `z + m` zeros
before `[1, 0]`. -/
theorem cleanup_to_main (stack' : List (Fin 2)) (hstack' : stack'.count 0 ≤ 13)
    (z m : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨47, Tape.mk' (stackLeft stack')
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨126, Tape.mk' rootLeft
        (ListBlank.append stack'
          (ListBlank.append (List.replicate (z + m) 0) (ListBlank.append [1, 0] R)))⟩ := by
  have hscan_z := nSteps_mk'_right_scan (q := 47) (a := 0) (b := 0) (by rfl) z
    (stackLeft stack') (ListBlank.append (encodeReg m) R)
  conv at hscan_z => rhs; rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step Machines.zf432
      ⟨47, Tape.mk' (ListBlank.append (List.replicate z 0) (stackLeft stack'))
        ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ =
      some ⟨48, Tape.mk' ((ListBlank.append (List.replicate z 0) (stackLeft stack')).cons 0)
        (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan_m := nSteps_mk'_right_scan (q := 48) (a := 1) (b := 0) (by rfl) m
    ((ListBlank.append (List.replicate z 0) (stackLeft stack')).cons 0) (R.cons 0)
  have hzeros : ListBlank.append (List.replicate m 0)
      ((ListBlank.append (List.replicate z 0) (stackLeft stack')).cons 0) =
      (ListBlank.append (List.replicate (z + m) 0) (stackLeft stack')).cons 0 := by
    rw [append_replicate_cons, ← ListBlank.append_assoc, ← List.replicate_add]
    have hadd : m + 1 + z = (z + m) + 1 := by omega
    rw [hadd, List.replicate_succ, ListBlank.append]
  rw [hzeros] at hscan_m
  have h2 : step Machines.zf432
      ⟨48, Tape.mk' ((ListBlank.append (List.replicate (z + m) 0) (stackLeft stack')).cons 0)
        (R.cons 0)⟩ =
      some ⟨5, Tape.mkL ((ListBlank.append (List.replicate (z + m) 0) (stackLeft stack')).cons 0)
        (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ R
  have h3 : step Machines.zf432
      ⟨5, Tape.mkL ((ListBlank.append (List.replicate (z + m) 0) (stackLeft stack')).cons 0)
        (R.cons 0)⟩ =
      some ⟨92, Tape.mkL (ListBlank.append (List.replicate (z + m) 0) (stackLeft stack'))
        (ListBlank.append [1, 0] R)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan_back := continue0_scan_zeros (z + m) (stackLeft stack') (ListBlank.append [1, 0] R)
  obtain ⟨s_ret, hs1, hret⟩ := continue0_return stack' hstack'
    (ListBlank.append (List.replicate (z + m) 0) (ListBlank.append [1, 0] R))
  have htotal := nSteps_bind_eq hscan_z (step_nSteps h1 (nSteps_bind_eq hscan_m
    (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hscan_back hret)))))
  exact ⟨_, by omega, htotal⟩

/-- `6.break.0` (`89`) erases `c₀` ones on the left tape, turns the preceding `0` into `1`, and
moves right into `2e.reg.cleanup_1` (`47`). -/
theorem break0_step (c₀ : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (c₀ + 1)
      ⟨89, Tape.mkL (ListBlank.append (List.replicate c₀ 1) (L.cons 0)) R⟩ =
      some ⟨47, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate c₀ 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 89) (a := 1) (b := 0) (by rfl) c₀ (L.cons 0) R
  have h1 : step Machines.zf432
      ⟨89, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate c₀ 0) R)⟩ =
      some ⟨47, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate c₀ 0) R)⟩ :=
    step_mkL_right (by rfl) _ _
  exact nSteps_bind_eq hscan (step_one h1)

/-- `6.break.1` (`90`) erases `c₁` ones and the preceding `0` on the left tape, transitioning to
`6.break.0` (`89`). -/
theorem break1_step (c₁ : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (c₁ + 1)
      ⟨90, Tape.mkL (ListBlank.append (List.replicate c₁ 1) (L.cons 0)) R⟩ =
      some ⟨89, Tape.mkL L (ListBlank.append (List.replicate (c₁ + 1) 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 90) (a := 1) (b := 0) (by rfl) c₁ (L.cons 0) R
  have h1 : step Machines.zf432
      ⟨90, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate c₁ 0) R)⟩ =
      some ⟨89, Tape.mkL L ((ListBlank.append (List.replicate c₁ 0) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq hscan (step_one h1)
  rwa [List.replicate_succ, ListBlank.append]

/-- `6.break.2` (`91`) erases `c₂` ones and the preceding `0` on the left tape, transitioning to
`6.break.1` (`90`). -/
theorem break2_step (c₂ : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps Machines.zf432 (c₂ + 1)
      ⟨91, Tape.mkL (ListBlank.append (List.replicate c₂ 1) (L.cons 0)) R⟩ =
      some ⟨90, Tape.mkL L (ListBlank.append (List.replicate (c₂ + 1) 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 91) (a := 1) (b := 0) (by rfl) c₂ (L.cons 0) R
  have h1 : step Machines.zf432
      ⟨91, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate c₂ 0) R)⟩ =
      some ⟨90, Tape.mkL L ((ListBlank.append (List.replicate c₂ 0) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcomb := nSteps_bind_eq hscan (step_one h1)
  rwa [List.replicate_succ, ListBlank.append]

/-- Full `6.break.0 -> 2e.reg.cleanup_1/2 -> 0b.boot2.0 -> 6.continue.0 -> main().0` evaluation. -/
theorem break0_cleanup_to_main (stack' : List (Fin 2)) (hstack' : stack'.count 0 ≤ 13)
    (c₀ z m : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨89, Tape.mkL (stackLeft (stack' ++ [0] ++ List.replicate c₀ 1))
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨126, Tape.mk' rootLeft
        (ListBlank.append (stack' ++ [1])
          (ListBlank.append (List.replicate (c₀ + z + m) 0) (ListBlank.append [1, 0] R)))⟩ := by
  have hL : stackLeft (stack' ++ [0] ++ List.replicate c₀ 1) =
      ListBlank.append (List.replicate c₀ 1) ((stackLeft stack').cons 0) := by
    rw [stackLeft_append, List.reverse_replicate, stackLeft_append_singleton]
  rw [hL]
  have hb0 := break0_step c₀ (stackLeft stack')
    (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))
  have hL1 : (stackLeft stack').cons 1 = stackLeft (stack' ++ [1]) := by
    rw [stackLeft_append_singleton]
  have hR1 : ListBlank.append (List.replicate c₀ 0)
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R)) =
      ListBlank.append (List.replicate (c₀ + z) 0) (ListBlank.append (encodeReg m) R) := by
    rw [← ListBlank.append_assoc, ← List.replicate_add]
  rw [hL1, hR1] at hb0
  have hcnt1 : (stack' ++ [1]).count 0 ≤ 13 := by
    rw [List.count_append]; exact hstack'
  obtain ⟨s_cl, hs1, hcl⟩ := cleanup_to_main (stack' ++ [1]) hcnt1 (c₀ + z) m R
  exact ⟨_, by omega, nSteps_bind_eq hb0 hcl⟩

/-- Full `6.break.1 -> 6.break.0 -> 2e.reg.cleanup_1/2 -> 0b.boot2.0 -> 6.continue.0 -> main().0`
evaluation. -/
theorem break1_cleanup_to_main (stack' : List (Fin 2)) (hstack' : stack'.count 0 ≤ 13)
    (c₀ c₁ z m : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨90, Tape.mkL
        (stackLeft (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1))
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨126, Tape.mk' rootLeft
        (ListBlank.append (stack' ++ [1])
          (ListBlank.append (List.replicate (c₀ + (c₁ + 1 + z) + m) 0)
            (ListBlank.append [1, 0] R)))⟩ := by
  have hL : stackLeft (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1) =
      ListBlank.append (List.replicate c₁ 1)
        ((stackLeft (stack' ++ [0] ++ List.replicate c₀ 1)).cons 0) := by
    rw [stackLeft_append, List.reverse_replicate, stackLeft_append_singleton]
  rw [hL]
  have hb1 := break1_step c₁ (stackLeft (stack' ++ [0] ++ List.replicate c₀ 1))
    (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))
  have hR1 : ListBlank.append (List.replicate (c₁ + 1) 0)
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R)) =
      ListBlank.append (List.replicate (c₁ + 1 + z) 0) (ListBlank.append (encodeReg m) R) := by
    rw [← ListBlank.append_assoc, ← List.replicate_add]
  rw [hR1] at hb1
  obtain ⟨s_b0, hs1, hb0⟩ := break0_cleanup_to_main stack' hstack' c₀ (c₁ + 1 + z) m R
  exact ⟨_, by omega, nSteps_bind_eq hb1 hb0⟩

/-- Full `6.break.2 -> 6.break.1 -> 6.break.0 -> 2e.reg.cleanup_1/2 -> 0b.boot2.0 -> 6.continue.0
-> main().0`
evaluation. -/
theorem break2_cleanup_to_main (stack' : List (Fin 2)) (hstack' : stack'.count 0 ≤ 13)
    (c₀ c₁ c₂ z m : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨91, Tape.mkL
        (stackLeft (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1 ++
          [0] ++ List.replicate c₂ 1))
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨126, Tape.mk' rootLeft
        (ListBlank.append (stack' ++ [1])
          (ListBlank.append (List.replicate (c₀ + (c₁ + 1 + (c₂ + 1 + z)) + m) 0)
            (ListBlank.append [1, 0] R)))⟩ := by
  have hL : stackLeft (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1 ++
      [0] ++ List.replicate c₂ 1) =
      ListBlank.append (List.replicate c₂ 1)
        ((stackLeft (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1)).cons 0)
          := by
    rw [stackLeft_append, List.reverse_replicate, stackLeft_append_singleton]
  rw [hL]
  have hb2 := break2_step c₂
    (stackLeft (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1))
    (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))
  have hR2 : ListBlank.append (List.replicate (c₂ + 1) 0)
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R)) =
      ListBlank.append (List.replicate (c₂ + 1 + z) 0) (ListBlank.append (encodeReg m) R) := by
    rw [← ListBlank.append_assoc, ← List.replicate_add]
  rw [hR2] at hb2
  obtain ⟨s_b1, hs1, hb1⟩ := break1_cleanup_to_main stack' hstack' c₀ c₁ (c₂ + 1 + z) m R
  exact ⟨_, by omega, nSteps_bind_eq hb2 hb1⟩

/-!
## 8. End-to-End Pass 2 + Cleanup Lemmas Returning to `zfRootCfg`
-/

/-- Complete Pass 2 of `3.<reg_k>.inc`: from `regIncStage3 k` with `stack = stack' ++ [0] ++ 1^c₀`
on the left tape and the Pass-1 prepared registers on the right tape, `Machines.zf432` increments
`regs[k]` by `1`, performs `6.break.0` and `2e.reg.cleanup_1/2`, and returns to
`zfRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] + 1))`. -/
theorem stage3_inc_pass2_to_root (k : ℕ) (hk11 : k < 11) (padTotal : ℕ)
    (stack' : List (Fin 2)) (c₀ : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (hpad : (stack' ++ [0] ++ List.replicate c₀ 1).length + 2 ≤ padTotal)
    (hstack' : stack'.count 0 ≤ 13) :
    let stack := stack' ++ [0] ++ List.replicate c₀ 1
    let p := padTotal - stack.length - 2
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨regIncStage3 k, Tape.mk' (stackLeft stack) ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some (zfRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] + 1))) := by
  intro stack p
  obtain ⟨s₁, hs1, hp2⟩ := stage3_inc_pass2 k hk11 p regs hk (stackLeft stack)
  have hR_eq : ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0) =
      ListBlank.append (List.replicate 2 0)
        (ListBlank.append (encodeReg p) (regsTape (regs.set k (regs[k] + 1)))) := by
    rw [regsTape_cons]
    rfl
  rw [hR_eq] at hp2
  obtain ⟨s₂, hs2, hcl⟩ := break0_cleanup_to_main stack' hstack' c₀ 2 p
    (regsTape (regs.set k (regs[k] + 1)))
  have hpad_eq : c₀ + 2 + p = padTotal - (stack' ++ [1]).length := by
    simp only [stack, p, List.length_append, List.length_singleton, List.length_replicate] at hpad ⊢
    omega
  rw [hpad_eq] at hcl
  have hroot_eq : ⟨126, Tape.mk' rootLeft
      (ListBlank.append (stack' ++ [1])
        (ListBlank.append (List.replicate (padTotal - (stack' ++ [1]).length) 0)
          (ListBlank.append [1, 0] (regsTape (regs.set k (regs[k] + 1))))))⟩ =
      zfRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] + 1)) := by
    rw [zfRootCfg_default_eq, regsTape_cons]
    rfl
  rw [hroot_eq] at hcl
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hp2 hcl⟩

/-- Complete Pass 2 of `3.<reg_k>.decnz` when `regs[k] = 0`: from `regDecnzStage3 k` with
`stack = stack' ++ [0] ++ 1^c₀ ++ [0] ++ 1^c₁` on the left tape, `Machines.zf432` leaves `regs`
unchanged, performs `6.break.1` and `2e.reg.cleanup_1/2`, and returns to
`zfRootCfg padTotal (stack' ++ [1]) regs`. -/
theorem stage3_decnz_pass2_zero_to_root (k : ℕ) (hk11 : k < 11) (padTotal : ℕ)
    (stack' : List (Fin 2)) (c₀ c₁ : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (hz : regs[k] = 0)
    (hpad : (stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1).length +
      2 ≤ padTotal)
    (hstack' : stack'.count 0 ≤ 13) :
    let stack := stack' ++ [0] ++ List.replicate c₀ 1 ++ [0] ++ List.replicate c₁ 1
    let p := padTotal - stack.length - 2
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨regDecnzStage3 k, Tape.mk' (stackLeft stack) ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some (zfRootCfg padTotal (stack' ++ [1]) regs) := by
  intro stack p
  obtain ⟨s₁, hs1, hp2⟩ := stage3_decnz_pass2_zero k hk11 p regs hk hz (stackLeft stack)
  have hR_eq : ((regsTape (p :: regs)).cons 0 |>.cons 0) =
      ListBlank.append (List.replicate 2 0)
        (ListBlank.append (encodeReg p) (regsTape regs)) := by
    rw [regsTape_cons]
    rfl
  rw [hR_eq] at hp2
  obtain ⟨s₂, hs2, hcl⟩ := break1_cleanup_to_main stack' hstack' c₀ c₁ 2 p (regsTape regs)
  have hpad_eq : c₀ + (c₁ + 1 + 2) + p = padTotal - (stack' ++ [1]).length := by
    simp only [stack, p, List.length_append, List.length_singleton, List.length_replicate] at hpad ⊢
    omega
  rw [hpad_eq] at hcl
  have hroot_eq : ⟨126, Tape.mk' rootLeft
      (ListBlank.append (stack' ++ [1])
        (ListBlank.append (List.replicate (padTotal - (stack' ++ [1]).length) 0)
          (ListBlank.append [1, 0] (regsTape regs))))⟩ =
      zfRootCfg padTotal (stack' ++ [1]) regs := by
    rw [zfRootCfg_default_eq, regsTape_cons]
    rfl
  rw [hroot_eq] at hcl
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hp2 hcl⟩

/-- Complete Pass 2 of `3.<reg_k>.decnz` when `regs[k] > 0`: from `regDecnzStage3 k` with
`stack = stack' ++ [0] ++ 1^c₀` on the left tape, `Machines.zf432` decrements `regs[k]` by `1`,
appends a new zero register `[0]`, performs `6.break.0` and `2e.reg.cleanup_1/2`, and returns to
`zfRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] - 1) ++ [0])`. -/
theorem stage3_decnz_pass2_pos_to_root (k : ℕ) (hk11 : k < 11) (padTotal : ℕ)
    (stack' : List (Fin 2)) (c₀ : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (hpos : 0 < regs[k])
    (hpad : (stack' ++ [0] ++ List.replicate c₀ 1).length + 2 ≤ padTotal)
    (hstack' : stack'.count 0 ≤ 13) :
    let stack := stack' ++ [0] ++ List.replicate c₀ 1
    let p := padTotal - stack.length - 2
    ∃ s, 1 ≤ s ∧ nSteps Machines.zf432 s
      ⟨regDecnzStage3 k, Tape.mk' (stackLeft stack) ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some (zfRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] - 1) ++ [0])) := by
  intro stack p
  obtain ⟨s₁, hs1, hp2⟩ := stage3_decnz_pass2_pos k hk11 p regs hk hpos (stackLeft stack)
  have hR_eq : ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0) =
      ListBlank.append (List.replicate 2 0)
        (ListBlank.append (encodeReg p) (regsTape (regs.set k (regs[k] - 1) ++ [0]))) := by
    rw [regsTape_cons]
    rfl
  rw [hR_eq] at hp2
  obtain ⟨s₂, hs2, hcl⟩ := break0_cleanup_to_main stack' hstack' c₀ 2 p
    (regsTape (regs.set k (regs[k] - 1) ++ [0]))
  have hpad_eq : c₀ + 2 + p = padTotal - (stack' ++ [1]).length := by
    simp only [stack, p, List.length_append, List.length_singleton, List.length_replicate] at hpad ⊢
    omega
  rw [hpad_eq] at hcl
  have hroot_eq : ⟨126, Tape.mk' rootLeft
      (ListBlank.append (stack' ++ [1])
        (ListBlank.append (List.replicate (padTotal - (stack' ++ [1]).length) 0)
          (ListBlank.append [1, 0] (regsTape (regs.set k (regs[k] - 1) ++ [0])))))⟩ =
      zfRootCfg padTotal (stack' ++ [1]) (regs.set k (regs[k] - 1) ++ [0]) := by
    rw [zfRootCfg_default_eq, regsTape_cons]
    rfl
  rw [hroot_eq] at hcl
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hp2 hcl⟩

end ConjectureMachines.Semantics.Zf.Layer1

