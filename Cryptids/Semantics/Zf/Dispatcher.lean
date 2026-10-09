/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Zf429
public import Cryptids.Semantics.Riemann.Gadgets

/-!
# Layer 2: Call-Stack Dispatcher & Abstract Machine Simulation for `zf_432_wade.tm`

This module formalizes the unary call-stack decision tree (`States 96..431`), stack-popping
continuations (`6.continue.0..3`, `6.break.0..2`), and two-pass register dispatch (`3.<reg>.inc`,
`3.<reg>.decnz`) of the 432-state Turing machine `ConjectureMachines.Zf429.reference`
(`zf_432_wade.tm`), establishing the lockstep simulation and halting equivalence with the
11-register abstract machine `zfRegStep`.
-/

@[expose] public section

namespace ConjectureMachines.Zf429.Layer2

open Turing StateTransition ConjectureMachines.Zf429
open ConjectureMachines.Riemann543.Layer1
  (nSteps nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_reaches nSteps_eval_dom mk_append_replicate_zero default_eq_mk_nil
   default_cons_zero append_replicate_zero_default fin2_cases
   Tape.mkL Tape.mkL_cons Tape.mk'_cons Tape.mkL_default
   append_replicate_cons append_cons_snoc append_reverse_cons
   encodeReg encodeReg_length encodeReg_reverse append_encodeReg_reverse append_encodeReg
   encodeRegs encodeRegs_nil encodeRegs_cons encodeRegs_append
   regsTape regsTape_nil regsTape_cons regsTape_append
   list_take_cons_drop list_take_set_drop)

set_option maxRecDepth 200000

/-!
## 1. Fast Transition Lookup, Multi-Step Execution, and Canonical Tape Configurations
-/

/-- Fast binary-search transition function for `ConjectureMachines.Zf429.reference`. -/
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
-- kernel `decide` over all 432 × 2 (state, symbol) pairs of `reference.transition`
theorem refTrans_eq (q : Fin 432) (a : Fin 2) :
    reference.transition q a = refTrans q a := by
  revert q a; decide

section GeneralMachine

variable {K : ℕ} [NeZero K]

theorem nSteps_of_halt {M : Machine K 2} {c : Cfg K 2}
    (h : step M c = none) {k : ℕ} (hk : 1 ≤ k) :
    nSteps M k c = none := by
  cases k with
  | zero => omega
  | succ k => simp [nSteps_succ, h]

theorem mem_eval_iff_nSteps {M : Machine K 2} {c₀ ch : Cfg K 2} :
    ch ∈ eval (step M) c₀ ↔ ∃ N, nSteps M N c₀ = some ch ∧ step M ch = none := by
  constructor
  · intro h
    refine StateTransition.evalInduction h fun a ha ih => ?_
    rcases hs : step M a with _ | a'
    · have hmem : a ∈ eval (step M) a :=
        StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hs⟩
      have heq : ch = a := Part.mem_unique ha hmem
      subst heq
      exact ⟨0, rfl, hs⟩
    · obtain ⟨N, hN, hnone⟩ := ih a' hs
      exact ⟨N + 1, by rw [nSteps_succ, hs, Option.bind_some, hN], hnone⟩
  · rintro ⟨N, hN, hnone⟩
    exact StateTransition.mem_eval.mpr ⟨nSteps_reaches hN, hnone⟩

end GeneralMachine

theorem step_mk'_right {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, refTrans_eq, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_none {q : Fin 432} {a : Fin 2}
    (h : refTrans q a = none) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = none := by
  simp [step, refTrans_eq, h, Tape.mk']

theorem step_mkL_left {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem nSteps_mkL_left_scan {q : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {q : Fin 432} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

/-- The root prefix `[1, 1, 0]` to the left of the head at `main().0` (State `126`). -/
abbrev rootLeft : ListBlank (Fin 2) :=
  (default : ListBlank (Fin 2)).cons 1 |>.cons 1 |>.cons 0

abbrev zfRootLeft : ListBlank (Fin 2) := rootLeft

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

/-- `3.<reg_k>.inc` (States `49..70`) for register `0 ≤ k ≤ 10`. -/
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

/-- Canonical configuration at `main().0` (State `126`) with stack region of width `padTotal`
and arbitrary right-tape tail `R` starting at the `[1, 0]` `-2` marker. -/
def zfRootCfgR (padTotal : ℕ) (stack : List (Fin 2)) (R : ListBlank (Fin 2)) : Cfg 432 2 :=
  ⟨126, Tape.mk' rootLeft
    (ListBlank.append (stack ++ List.replicate (padTotal - stack.length) 0) R)⟩

/-- Canonical configuration at `main().0` (State `126`) with stack `stack`, register bank `regs`,
and trailing tape `extra` after `regs`. -/
def zfRootCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 432 2 :=
  ⟨126, Tape.mk' rootLeft
    (ListBlank.append
      (stack ++ List.replicate (padTotal - stack.length) 0 ++ [1, 0] ++ encodeRegs regs)
      extra)⟩

theorem zfRootCfg_eq_zfRootCfgR (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2)) :
    zfRootCfg padTotal stack regs extra =
      zfRootCfgR padTotal stack (ListBlank.append [1,
        0] (ListBlank.append (encodeRegs regs) extra)) := by
  simp [zfRootCfg, zfRootCfgR, List.append_assoc, ListBlank.append_assoc]

theorem zfRootCfg_default_eq (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    zfRootCfg padTotal stack regs default =
      zfRootCfgR padTotal stack (ListBlank.append [1, 0] (regsTape regs)) := by
  rw [zfRootCfg_eq_zfRootCfgR]; rfl

/-- Canonical configuration at `main().0` (State `126`) with `extraRegs` zero-initialized dummy
registers following the 11 active registers. -/
def zfRootCfgExtra (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extraRegs : ℕ) : Cfg 432 2 :=
  zfRootCfg padTotal stack (regs ++ List.replicate extraRegs 0) default

/-!
## 2. Call-Stack Bit Manipulation (`trimZeros`, `padTo`, `applyBreak`, `applyContinue`)
-/

/-- Removes leading `0`s from a bit list (used on reversed stacks to remove trailing `0`s). -/
def dropLeadingZeros : List (Fin 2) → List (Fin 2)
  | [] => []
  | b :: xs => if b == 0 then dropLeadingZeros xs else b :: xs

/-- Removes trailing `0`s from a call-stack bit list `bits`. -/
def trimZeros (bits : List (Fin 2)) : List (Fin 2) :=
  (dropLeadingZeros bits.reverse).reverse

@[simp]
theorem dropLeadingZeros_nil : dropLeadingZeros [] = [] := rfl

@[simp]
theorem dropLeadingZeros_zero (xs : List (Fin 2)) :
    dropLeadingZeros (0 :: xs) = dropLeadingZeros xs := rfl

@[simp]
theorem dropLeadingZeros_one (xs : List (Fin 2)) :
    dropLeadingZeros (1 :: xs) = 1 :: xs := rfl

@[simp]
theorem trimZeros_nil : trimZeros [] = [] := rfl

theorem dropLeadingZeros_length_le (xs : List (Fin 2)) :
    (dropLeadingZeros xs).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · simp; omega
    · simp

theorem eq_replicate_append_dropLeadingZeros (xs : List (Fin 2)) :
    xs = List.replicate (xs.length - (dropLeadingZeros xs).length) 0 ++ dropLeadingZeros xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · have hle := dropLeadingZeros_length_le xs
      have hsub : (0 :: xs).length - (dropLeadingZeros (0 :: xs)).length =
          (xs.length - (dropLeadingZeros xs).length) + 1 := by
        simp; omega
      rw [hsub, List.replicate_succ, List.cons_append, dropLeadingZeros_zero]
      exact congrArg (0 :: ·) ih
    · simp [dropLeadingZeros_one]

theorem trimZeros_length_le (bits : List (Fin 2)) :
    (trimZeros bits).length ≤ bits.length := by
  simpa [trimZeros] using dropLeadingZeros_length_le bits.reverse

theorem eq_trimZeros_append_replicate (bits : List (Fin 2)) :
    bits = trimZeros bits ++ List.replicate (bits.length - (trimZeros bits).length) 0 := by
  have h := congrArg List.reverse (eq_replicate_append_dropLeadingZeros bits.reverse)
  simpa [trimZeros, List.reverse_append, List.reverse_replicate] using h

theorem trimZeros_pad_eq (bits : List (Fin 2)) {padTotal : ℕ} (h : bits.length ≤ padTotal) :
    trimZeros bits ++ List.replicate (padTotal - (trimZeros bits).length) 0 =
      bits ++ List.replicate (padTotal - bits.length) 0 := by
  have hle := trimZeros_length_le bits
  have hsub : padTotal - (trimZeros bits).length =
      (bits.length - (trimZeros bits).length) + (padTotal - bits.length) := by omega
  rw [hsub, List.replicate_add, ← List.append_assoc, ← eq_trimZeros_append_replicate bits]

theorem zfRootCfgR_trimZeros (padTotal : ℕ) (bits : List (Fin 2)) (R : ListBlank (Fin 2))
    (h : bits.length ≤ padTotal) :
    zfRootCfgR padTotal (trimZeros bits) R = zfRootCfgR padTotal bits R := by
  simp [zfRootCfgR, trimZeros_pad_eq bits h]

/-- Pads or truncates `bits` with trailing `0`s to exact length `pos`. -/
def padTo (bits : List (Fin 2)) (pos : ℕ) : List (Fin 2) :=
  (bits ++ List.replicate (pos - bits.length) 0).take pos

@[simp]
theorem padTo_length (bits : List (Fin 2)) (pos : ℕ) :
    (padTo bits pos).length = pos := by
  simp [padTo]
  omega

theorem padTo_of_le {bits : List (Fin 2)} {pos : ℕ} (h : bits.length ≤ pos) :
    padTo bits pos = bits ++ List.replicate (pos - bits.length) 0 := by
  unfold padTo
  rw [List.take_of_length_le]
  simp; omega

theorem padTo_of_ge {bits : List (Fin 2)} {pos : ℕ} (h : pos ≤ bits.length) :
    padTo bits pos = bits.take pos := by
  unfold padTo
  have hsub : pos - bits.length = 0 := by omega
  rw [hsub, List.replicate_zero, List.append_nil]

theorem take_append_replicate_eq_padTo (bits : List (Fin 2)) {pos n : ℕ}
    (h : pos ≤ bits.length + n) :
    (bits ++ List.replicate n 0).take pos = padTo bits pos := by
  by_cases hle : pos ≤ bits.length
  · simp [padTo, List.take_append_of_le_length hle]
  · rw [padTo, List.take_append, List.take_append, List.take_replicate, List.take_replicate]
    congr 2
    omega

/-- Reversed-stack scanner for `6.break.k`: scans `rev` (from `pos - 1` down to `0`),
discarding `1`s and the first `k` `0`s, and replaces the `(k + 1)`-th `0` with `1`. -/
def popBreakRev : ℕ → List (Fin 2) → List (Fin 2)
  | _, [] => []
  | 0, b :: rest => if b == 0 then 1 :: rest else popBreakRev 0 rest
  | k + 1, b :: rest => if b == 0 then popBreakRev k rest else popBreakRev (k + 1) rest

/-- Reversed-stack scanner for `6.continue.k`: scans `rev` (from `pos - 1` down to `0`),
discarding `0`s and the first `k` `1`s, and stops at the `(k + 1)`-th `1`. -/
def popContinueRev : ℕ → List (Fin 2) → List (Fin 2)
  | _, [] => []
  | 0, b :: rest => if b == 1 then 1 :: rest else popContinueRev 0 rest
  | k + 1, b :: rest => if b == 1 then popContinueRev k rest else popContinueRev (k + 1) rest

@[simp]
theorem popBreakRev_nil (k : ℕ) : popBreakRev k [] = [] := by
  cases k <;> rfl

@[simp]
theorem popBreakRev_one (k : ℕ) (rest : List (Fin 2)) :
    popBreakRev k (1 :: rest) = popBreakRev k rest := by
  cases k <;> rfl

@[simp]
theorem popBreakRev_zero_zero (rest : List (Fin 2)) :
    popBreakRev 0 (0 :: rest) = 1 :: rest := rfl

@[simp]
theorem popBreakRev_succ_zero (k : ℕ) (rest : List (Fin 2)) :
    popBreakRev (k + 1) (0 :: rest) = popBreakRev k rest := rfl

@[simp]
theorem popContinueRev_nil (k : ℕ) : popContinueRev k [] = [] := by
  cases k <;> rfl

@[simp]
theorem popContinueRev_zero (k : ℕ) (rest : List (Fin 2)) :
    popContinueRev k (0 :: rest) = popContinueRev k rest := by
  cases k <;> rfl

@[simp]
theorem popContinueRev_zero_one (rest : List (Fin 2)) :
    popContinueRev 0 (1 :: rest) = 1 :: rest := rfl

@[simp]
theorem popContinueRev_succ_one (k : ℕ) (rest : List (Fin 2)) :
    popContinueRev (k + 1) (1 :: rest) = popContinueRev k rest := rfl

/-- Updates the call stack `bits` when `6.break.k` runs from index `pos` moving left. -/
def applyBreak (bits : List (Fin 2)) (pos : ℕ) (k : ℕ) : List (Fin 2) :=
  (popBreakRev k (padTo bits pos).reverse).reverse

/-- Updates the call stack `bits` when `6.continue.k` runs from index `pos` moving left. -/
def applyContinue (bits : List (Fin 2)) (pos : ℕ) (k : ℕ) : List (Fin 2) :=
  (popContinueRev k (padTo bits pos).reverse).reverse

theorem popBreakRev_suffix (k : ℕ) (rev : List (Fin 2)) :
    popBreakRev k rev = [] ∨
      ∃ rest, popBreakRev k rev = 1 :: rest ∧
        rest.length < rev.length ∧
        rev.reverse.take rest.length = rest.reverse := by
  induction rev generalizing k with
  | nil => exact Or.inl (popBreakRev_nil k)
  | cons b xs ih =>
    cases k with
    | zero =>
      rcases fin2_cases b with rfl | rfl
      · refine Or.inr ⟨xs, rfl, by simp, ?_⟩
        have hlen : xs.length ≤ xs.reverse.length := by simp
        simp [List.take_append_of_le_length hlen]
      · rcases ih 0 with hnil | ⟨rest, h1, hlt, htake⟩
        · exact Or.inl hnil
        · refine Or.inr ⟨rest, h1, by simp; omega, ?_⟩
          have hle : rest.length ≤ xs.reverse.length := by simp; omega
          rw [List.reverse_cons, List.take_append_of_le_length hle, htake]
    | succ k =>
      rcases fin2_cases b with rfl | rfl
      · rcases ih k with hnil | ⟨rest, h1, hlt, htake⟩
        · exact Or.inl hnil
        · refine Or.inr ⟨rest, h1, by simp; omega, ?_⟩
          have hle : rest.length ≤ xs.reverse.length := by simp; omega
          rw [List.reverse_cons, List.take_append_of_le_length hle, htake]
      · rcases ih (k + 1) with hnil | ⟨rest, h1, hlt, htake⟩
        · exact Or.inl hnil
        · refine Or.inr ⟨rest, h1, by simp; omega, ?_⟩
          have hle : rest.length ≤ xs.reverse.length := by simp; omega
          rw [List.reverse_cons, List.take_append_of_le_length hle, htake]

theorem popContinueRev_suffix (k : ℕ) (rev : List (Fin 2)) :
    popContinueRev k rev = [] ∨
      ∃ rest, popContinueRev k rev = 1 :: rest ∧
        rest.length < rev.length ∧
        rev.reverse.take rest.length = rest.reverse := by
  induction rev generalizing k with
  | nil => exact Or.inl (popContinueRev_nil k)
  | cons b xs ih =>
    cases k with
    | zero =>
      rcases fin2_cases b with rfl | rfl
      · rcases ih 0 with hnil | ⟨rest, h1, hlt, htake⟩
        · exact Or.inl hnil
        · refine Or.inr ⟨rest, h1, by simp; omega, ?_⟩
          have hle : rest.length ≤ xs.reverse.length := by simp; omega
          rw [List.reverse_cons, List.take_append_of_le_length hle, htake]
      · refine Or.inr ⟨xs, rfl, by simp, ?_⟩
        have hlen : xs.length ≤ xs.reverse.length := by simp
        simp [List.take_append_of_le_length hlen]
    | succ k =>
      rcases fin2_cases b with rfl | rfl
      · rcases ih (k + 1) with hnil | ⟨rest, h1, hlt, htake⟩
        · exact Or.inl hnil
        · refine Or.inr ⟨rest, h1, by simp; omega, ?_⟩
          have hle : rest.length ≤ xs.reverse.length := by simp; omega
          rw [List.reverse_cons, List.take_append_of_le_length hle, htake]
      · rcases ih k with hnil | ⟨rest, h1, hlt, htake⟩
        · exact Or.inl hnil
        · refine Or.inr ⟨rest, h1, by simp; omega, ?_⟩
          have hle : rest.length ≤ xs.reverse.length := by simp; omega
          rw [List.reverse_cons, List.take_append_of_le_length hle, htake]

theorem popBreakRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (popBreakRev k rev).length ≤ rev.length := by
  rcases popBreakRev_suffix k rev with hnil | ⟨rest, h1, hlt, _⟩
  · simp [hnil]
  · simp [h1]; omega

theorem popContinueRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (popContinueRev k rev).length ≤ rev.length := by
  rcases popContinueRev_suffix k rev with hnil | ⟨rest, h1, hlt, _⟩
  · simp [hnil]
  · simp [h1]; omega

theorem popBreakRev_count_zero_le (k : ℕ) (rev : List (Fin 2)) :
    (popBreakRev k rev).reverse.count 0 ≤ rev.count 0 := by
  rcases popBreakRev_suffix k rev with hnil | ⟨rest, h1, _, htake⟩
  · simp [hnil]
  · have hcnt : (rev.reverse.take rest.length).count 0 ≤ rev.reverse.count 0 := by
      conv_rhs => rw [← List.take_append_drop rest.length rev.reverse, List.count_append]
      omega
    rw [htake] at hcnt
    rw [h1, List.reverse_cons, List.count_append]
    simp only [List.count_reverse] at hcnt ⊢
    change rest.count 0 + 0 ≤ rev.count 0
    omega

theorem popContinueRev_count_zero_le (k : ℕ) (rev : List (Fin 2)) :
    (popContinueRev k rev).reverse.count 0 ≤ rev.count 0 := by
  rcases popContinueRev_suffix k rev with hnil | ⟨rest, h1, _, htake⟩
  · simp [hnil]
  · have hcnt : (rev.reverse.take rest.length).count 0 ≤ rev.reverse.count 0 := by
      conv_rhs => rw [← List.take_append_drop rest.length rev.reverse, List.count_append]
      omega
    rw [htake] at hcnt
    rw [h1, List.reverse_cons, List.count_append]
    simp only [List.count_reverse] at hcnt ⊢
    change rest.count 0 + 0 ≤ rev.count 0
    omega

@[simp]
theorem trimZeros_applyBreak (bits : List (Fin 2)) (pos k : ℕ) :
    trimZeros (applyBreak bits pos k) = applyBreak bits pos k := by
  unfold trimZeros applyBreak
  rw [List.reverse_reverse]
  rcases popBreakRev_suffix k (padTo bits pos).reverse with hnil | ⟨rest, h1, _, _⟩
  · simp [hnil]
  · simp [h1]

@[simp]
theorem trimZeros_applyContinue (bits : List (Fin 2)) (pos k : ℕ) :
    trimZeros (applyContinue bits pos k) = applyContinue bits pos k := by
  unfold trimZeros applyContinue
  rw [List.reverse_reverse]
  rcases popContinueRev_suffix k (padTo bits pos).reverse with hnil | ⟨rest, h1, _, _⟩
  · simp [hnil]
  · simp [h1]

/-!
## 3. Computable Call-Stack Dispatcher (`ZfInstr`, `walkTape`, `evalStack`)
-/

/-- Abstract instruction of the `zf_432_wade.tm` register machine at `main().0`. -/
inductive ZfInstr where
  | halt
  | jump (stack' : List (Fin 2))
  | inc (r : ℕ) (stack_succ : List (Fin 2))
  | decnz (r : ℕ) (stack_succ stack_fail : List (Fin 2))
  deriving DecidableEq, Repr

/-- Register index `r ∈ {0..10}` associated with a leaf state `q ∈ {49..70}`. -/
def leafReg (q : Fin 432) : ℕ :=
  match q.val with
  | 49 | 50 => 4
  | 51 | 52 => 1
  | 53 | 54 => 5
  | 55 | 56 => 6
  | 57 | 58 => 7
  | 59 | 60 => 0
  | 61 | 62 => 8
  | 63 | 64 => 9
  | 65 | 66 => 10
  | 67 | 68 => 2
  | 69 | 70 => 3
  | _ => 0

theorem leafReg_lt_11 (q : Fin 432) : leafReg q < 11 := by
  revert q; decide

/-- Whether a leaf state `q ∈ {49..70}` is a register increment (`true`) or `decnz` (`false`). -/
def isLeafInc (q : Fin 432) : Bool :=
  49 ≤ q.val && q.val ≤ 70 && q.val % 2 == 0

/-- Outcome of walking the call-stack decision tree (`States 96..431`) on a bit tape. -/
inductive TreeOutcome where
  | halt (q : Fin 432) (walked rem : List (Fin 2))
  | jumpLeft (q' : Fin 432) (walked rem' : List (Fin 2))
  | regLeaf (q' : Fin 432) (walked rem' : List (Fin 2))
  | outOfFuel
  deriving DecidableEq, Repr

/-- Walks the decision tree starting at state `q` with already-traversed prefix `walked`
and remaining tape suffix `rem`. -/
def walkTape (q : Fin 432) (walked : List (Fin 2)) : List (Fin 2) → TreeOutcome
  | [] => .outOfFuel
  | b :: rem' =>
    match refTrans q b with
    | none => .halt q walked (b :: rem')
    | some (w, d, q') =>
      match d with
      | .left =>
        if w == 0 then .jumpLeft q' walked rem' else .outOfFuel
      | .right =>
        if w == b then
          if 49 ≤ q'.val && q'.val ≤ 70 then
            .regLeaf q' (walked ++ [b]) rem'
          else
            walkTape q' (walked ++ [b]) rem'
        else
          .outOfFuel

/-- Decodes a `TreeOutcome` into a `ZfInstr` for call stack `bits`. -/
def outcomeToInstr (bits : List (Fin 2)) : TreeOutcome → ZfInstr
  | .halt _ _ _ => .halt
  | .jumpLeft q' walked _ =>
    if q'.val ≤ 91 then
      .jump (applyBreak bits walked.length (q'.val - 89))
    else
      .jump (applyContinue bits walked.length (q'.val - 92))
  | .regLeaf q' walked _ =>
    if isLeafInc q' then
      .inc (leafReg q') (applyBreak bits walked.length 0)
    else
      .decnz (leafReg q') (applyBreak bits walked.length 0) (applyBreak bits walked.length 1)
  | .outOfFuel => .halt

/-- Computable call-stack dispatcher: evaluates `bits` from `main().0` (State `126`)
with 12 trailing zeros of padding. -/
def evalStack (bits : List (Fin 2)) : ZfInstr :=
  outcomeToInstr bits (walkTape 126 [] (bits ++ List.replicate 12 0))

/-!
## 4. Universal Tree-Walk Soundness and DAG Invariant (`validStack`)
-/

theorem walkTape_append (q : Fin 432) (walked rem extra : List (Fin 2)) :
    match walkTape q walked rem with
    | .halt q_h w_h r_h => walkTape q walked (rem ++ extra) = .halt q_h w_h (r_h ++ extra)
    | .jumpLeft q' w_j r' => walkTape q walked (rem ++ extra) = .jumpLeft q' w_j (r' ++ extra)
    | .regLeaf q' w_l r' => walkTape q walked (rem ++ extra) = .regLeaf q' w_l (r' ++ extra)
    | .outOfFuel => True := by
  induction rem generalizing q walked with
  | nil => trivial
  | cons b rem' ih =>
    simp only [walkTape, List.cons_append]
    rcases htr : refTrans q b with _ | ⟨w, d, q'⟩
    · rfl
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true <;> simp [hw]
      | right =>
        by_cases hw : (w == b) = true
        · simp only [hw, ↓reduceIte]
          by_cases hleaf : (49 ≤ q'.val && q'.val ≤ 70) = true
          · simp [hleaf]
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            exact ih q' (walked ++ [b])
        · simp [hw]

/-- Configuration during the rightward decision-tree walk. -/
def treeWalkCfg (q : Fin 432) (walked rem : List (Fin 2)) (L₀ R_tail : ListBlank (Fin 2)) :
    Cfg 432 2 :=
  ⟨q, Tape.mk' (ListBlank.append walked.reverse L₀) (ListBlank.append rem R_tail)⟩

/-- Universal Tree-Walk Soundness Theorem: for any `q`, `walked`, `rem`, `L₀`, and `R_tail`,
`nSteps reference` executes `walkTape q walked rem` on the tape without touching `L₀` or
`R_tail`. -/
theorem walkTape_sound (q : Fin 432) (walked rem : List (Fin 2)) (L₀ R_tail : ListBlank (Fin 2)) :
    match walkTape q walked rem with
    | .halt q_h walked_h rem_h =>
      walked_h ++ rem_h = walked ++ rem ∧
      ∃ s ch,
        ch = treeWalkCfg q_h walked_h rem_h L₀ R_tail ∧
        nSteps reference s (treeWalkCfg q walked rem L₀ R_tail) = some ch ∧
        step reference ch = none
    | .jumpLeft q' walked_j rem' =>
      (∃ b, walked_j ++ (b :: rem') = walked ++ rem) ∧
      ∃ s, 1 ≤ s ∧ nSteps reference s (treeWalkCfg q walked rem L₀ R_tail) =
        some ⟨q', Tape.mkL (ListBlank.append walked_j.reverse L₀) (ListBlank.append (0 :: rem')
          R_tail)⟩
    | .regLeaf q' walked_l rem' =>
      walked_l ++ rem' = walked ++ rem ∧
      49 ≤ q'.val ∧ q'.val ≤ 70 ∧
      ∃ s, 1 ≤ s ∧ nSteps reference s (treeWalkCfg q walked rem L₀ R_tail) =
        some (treeWalkCfg q' walked_l rem' L₀ R_tail)
    | .outOfFuel => True := by
  induction rem generalizing q walked with
  | nil => trivial
  | cons b rem' ih =>
    simp only [walkTape]
    rcases htr : refTrans q b with _ | ⟨w, d, q'⟩
    · refine ⟨rfl, 0, treeWalkCfg q walked (b :: rem') L₀ R_tail, rfl, rfl, ?_⟩
      exact step_mk'_none htr (ListBlank.append walked.reverse L₀) (ListBlank.append rem' R_tail)
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp only [hw, ↓reduceIte]
          have hw0 : w = 0 := beq_iff_eq.mp hw
          subst hw0
          refine ⟨⟨b, rfl⟩, 1, le_refl 1, ?_⟩
          exact step_one (step_mk'_left htr (ListBlank.append walked.reverse L₀)
            (ListBlank.append rem' R_tail))
        · simp [hw]
      | right =>
        by_cases hw : (w == b) = true
        · simp only [hw, ↓reduceIte]
          have hwb : w = b := beq_iff_eq.mp hw
          subst hwb
          have hstep1 : step reference (treeWalkCfg q walked (w :: rem') L₀ R_tail) =
              some (treeWalkCfg q' (walked ++ [w]) rem' L₀ R_tail) := by
            simpa [treeWalkCfg, append_reverse_cons] using
              step_mk'_right htr (ListBlank.append walked.reverse L₀) (ListBlank.append rem' R_tail)
          by_cases hleaf : (49 ≤ q'.val && q'.val ≤ 70) = true
          · simp only [hleaf, ↓reduceIte]
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hleaf
            exact ⟨by simp, hleaf.1, hleaf.2, 1, le_refl 1, step_one hstep1⟩
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            have hrec := ih q' (walked ++ [w])
            rcases hout : walkTape q' (walked ++ [w]) rem' with
              ⟨q_h, w_h, r_h⟩ | ⟨q_j, w_j, r_j⟩ | ⟨q_l, w_l, r_l⟩ | _
            · rw [hout] at hrec
              obtain ⟨heq, s, ch, hch, hs, hnone⟩ := hrec
              exact ⟨by simpa using heq, s + 1, ch, hch, step_nSteps hstep1 hs, hnone⟩
            · rw [hout] at hrec
              obtain ⟨⟨b', heq⟩, s, hs_pos, hs⟩ := hrec
              exact ⟨⟨b', by simpa using heq⟩, s + 1, by omega, step_nSteps hstep1 hs⟩
            · rw [hout] at hrec
              obtain ⟨heq, h49, h70, s, hs_pos, hs⟩ := hrec
              exact ⟨by simpa using heq, h49, h70, s + 1, by omega, step_nSteps hstep1 hs⟩
            · trivial
        · simp [hw]

/-- DAG topological height (max path length in `96..431` from `q`). -/
def nodeMaxLen (q : Fin 432) : ℕ :=
  (if q.val < 216 then (if q.val < 108 then (if q.val < 54 then 0 else (if q.val < 81 then 0 else
    (if q.val < 94 then 0 else (if q.val < 101 then (if q.val < 97 then (if q.val < 95 then 0 else
      (if q.val < 96 then 0 else 7)) else (if q.val < 99 then (if q.val < 98 then 6 else 11) else
        (if q.val < 100 then 10 else 9))) else (if q.val < 104 then (if q.val < 102 then 2 else (if
          q.val < 103 then 1 else 0)) else (if q.val < 106 then (if q.val < 105 then 8 else 7) else
            (if q.val < 107 then 12 else 2))))))) else (if q.val < 162 then (if q.val < 135 then
              (if q.val < 121 then (if q.val < 114 then (if q.val < 111 then (if q.val < 109 then
                12 else (if q.val < 110 then 2 else 3)) else (if q.val < 112 then 2 else (if q.val
                  < 113 then 4 else 3))) else (if q.val < 117 then (if q.val < 115 then 2 else (if
                    q.val < 116 then 0 else 1)) else (if q.val < 119 then (if q.val < 118 then 2
                      else 1) else (if q.val < 120 then 5 else 3)))) else (if q.val < 128 then (if
                        q.val < 124 then (if q.val < 122 then 5 else (if q.val < 123 then 4 else
                          0)) else (if q.val < 126 then (if q.val < 125 then 3 else 2) else (if
                            q.val < 127 then 147 else 146))) else (if q.val < 131 then (if q.val <
                              129 then 137 else (if q.val < 130 then 47 else 46)) else (if q.val <
                                133 then (if q.val < 132 then 45 else 44) else (if q.val < 134 then
                                  43 else 42))))) else (if q.val < 148 then (if q.val < 141 then
                                    (if q.val < 138 then (if q.val < 136 then 41 else (if q.val <
                                      137 then 40 else 39)) else (if q.val < 139 then 38 else (if
                                        q.val < 140 then 136 else 37))) else (if q.val < 144 then
                                          (if q.val < 142 then 36 else (if q.val < 143 then 35 else
                                            34)) else (if q.val < 146 then (if q.val < 145 then 33
                                              else 32) else (if q.val < 147 then 31 else 30))))
                                                else (if q.val < 155 then (if q.val < 151 then (if
                                                  q.val < 149 then 29 else (if q.val < 150 then 28
                                                    else 135)) else (if q.val < 153 then (if q.val
                                                      < 152 then 27 else 26) else (if q.val < 154
                                                        then 25 else 24))) else (if q.val < 158
                                                          then (if q.val < 156 then 23 else (if
                                                            q.val < 157 then 22 else 21)) else (if
                                                              q.val < 160 then (if q.val < 159 then
                                                                20 else 19) else (if q.val < 161
                                                                  then 18 else 134)))))) else (if
                                                                    q.val < 189 then (if q.val <
                                                                      175 then (if q.val < 168 then
                                                                        (if q.val < 165 then (if
                                                                          q.val < 163 then 17 else
                                                                            (if q.val < 164 then 16
                                                                              else 8)) else (if
                                                                                q.val < 166 then 4
                                                                                  else (if q.val <
                                                                                    167 then 3 else
                                                                                      2))) else (if
                                                                                        q.val < 171
                                                                                          then (if
                                                                                            q.val <
                                                                                              169
                                                                                                then
                                                                                                  1

  else (if q.val < 170 then 0 else 133)) else (if q.val < 173 then (if q.val < 172 then 132 else
  131) else (if q.val < 174 then 130 else 129)))) else (if q.val < 182 then (if q.val < 178 then (if
  q.val < 176 then 128 else (if q.val < 177 then 145 else 127)) else (if q.val < 180 then (if q.val
  < 179 then 126 else 125) else (if q.val < 181 then 124 else 123))) else (if q.val < 185 then (if
  q.val < 183 then 122 else (if q.val < 184 then 121 else 120)) else (if q.val < 187 then (if q.val
  < 186 then 119 else 118) else (if q.val < 188 then 144 else 117))))) else (if q.val < 202 then (if
  q.val < 195 then (if q.val < 192 then (if q.val < 190 then 116 else (if q.val < 191 then 115 else
  114)) else (if q.val < 193 then 113 else (if q.val < 194 then 112 else 111))) else (if q.val < 198
  then (if q.val < 196 then 110 else (if q.val < 197 then 109 else 108)) else (if q.val < 200 then
  (if q.val < 199 then 143 else 107) else (if q.val < 201 then 106 else 105)))) else (if q.val < 209
  then (if q.val < 205 then (if q.val < 203 then 104 else (if q.val < 204 then 103 else 102)) else
  (if q.val < 207 then (if q.val < 206 then 101 else 100) else (if q.val < 208 then 99 else 98)))
  else (if q.val < 212 then (if q.val < 210 then 142 else (if q.val < 211 then 97 else 96)) else (if
  q.val < 214 then (if q.val < 213 then 95 else 94) else (if q.val < 215 then 93 else 92))))))))
  else (if q.val < 324 then (if q.val < 270 then (if q.val < 243 then (if q.val < 229 then (if q.val
  < 222 then (if q.val < 219 then (if q.val < 217 then 91 else (if q.val < 218 then 90 else 89))
  else (if q.val < 220 then 88 else (if q.val < 221 then 141 else 87))) else (if q.val < 225 then
  (if q.val < 223 then 86 else (if q.val < 224 then 85 else 84)) else (if q.val < 227 then (if q.val
  < 226 then 83 else 82) else (if q.val < 228 then 81 else 80)))) else (if q.val < 236 then (if
  q.val < 232 then (if q.val < 230 then 79 else (if q.val < 231 then 78 else 140)) else (if q.val <
  234 then (if q.val < 233 then 77 else 76) else (if q.val < 235 then 75 else 74))) else (if q.val <
  239 then (if q.val < 237 then 73 else (if q.val < 238 then 72 else 71)) else (if q.val < 241 then
  (if q.val < 240 then 70 else 69) else (if q.val < 242 then 68 else 139))))) else (if q.val < 256
  then (if q.val < 249 then (if q.val < 246 then (if q.val < 244 then 67 else (if q.val < 245 then
  66 else 65)) else (if q.val < 247 then 64 else (if q.val < 248 then 63 else 62))) else (if q.val <
  252 then (if q.val < 250 then 61 else (if q.val < 251 then 60 else 59)) else (if q.val < 254 then
  (if q.val < 253 then 58 else 138) else (if q.val < 255 then 57 else 56)))) else (if q.val < 263
  then (if q.val < 259 then (if q.val < 257 then 55 else (if q.val < 258 then 54 else 53)) else (if
  q.val < 261 then (if q.val < 260 then 52 else 51) else (if q.val < 262 then 50 else 49))) else (if
  q.val < 266 then (if q.val < 264 then 48 else (if q.val < 265 then 20 else 19)) else (if q.val <
  268 then (if q.val < 267 then 18 else 17) else (if q.val < 269 then 16 else 15)))))) else (if
  q.val < 297 then (if q.val < 283 then (if q.val < 276 then (if q.val < 273 then (if q.val < 271
  then 10 else (if q.val < 272 then 8 else 19)) else (if q.val < 274 then 18 else (if q.val < 275
  then 17 else 16))) else (if q.val < 279 then (if q.val < 277 then 15 else (if q.val < 278 then 18
  else 17)) else (if q.val < 281 then (if q.val < 280 then 16 else 17) else (if q.val < 282 then 16
  else 8)))) else (if q.val < 290 then (if q.val < 286 then (if q.val < 284 then 11 else (if q.val <
  285 then 10 else 8)) else (if q.val < 288 then (if q.val < 287 then 13 else 14) else 12)) else (if
  q.val < 293 then (if q.val < 291 then 12 else (if q.val < 292 then 15 else 14)) else (if q.val <
  295 then (if q.val < 294 then 13 else 12) else (if q.val < 296 then 13 else 14))))) else (if q.val
  < 310 then (if q.val < 303 then (if q.val < 300 then (if q.val < 298 then 10 else (if q.val < 299
  then 7 else 6)) else (if q.val < 301 then 12 else 11)) else (if q.val < 306 then (if q.val < 304
  then 10 else (if q.val < 305 then 11 else 12)) else (if q.val < 308 then (if q.val < 307 then 9
  else 11) else (if q.val < 309 then 14 else 13)))) else (if q.val < 317 then (if q.val < 313 then
  (if q.val < 311 then 6 else 11) else (if q.val < 315 then (if q.val < 314 then 13 else 9) else (if
  q.val < 316 then 15 else 9))) else (if q.val < 320 then (if q.val < 318 then 10 else (if q.val <
  319 then 15 else 13)) else (if q.val < 322 then (if q.val < 321 then 11 else 8) else (if q.val <
  323 then 11 else 10))))))) else (if q.val < 378 then (if q.val < 351 then (if q.val < 337 then (if
  q.val < 330 then (if q.val < 327 then (if q.val < 325 then 8 else (if q.val < 326 then 13 else 8))
  else (if q.val < 328 then 10 else (if q.val < 329 then 6 else 5))) else (if q.val < 333 then (if
  q.val < 331 then 4 else (if q.val < 332 then 3 else 2)) else (if q.val < 335 then (if q.val < 334
  then 5 else 4) else (if q.val < 336 then 3 else 2)))) else (if q.val < 344 then (if q.val < 340
  then (if q.val < 338 then 7 else (if q.val < 339 then 3 else 7)) else (if q.val < 342 then (if
  q.val < 341 then 3 else 7) else (if q.val < 343 then 3 else 6))) else (if q.val < 347 then (if
  q.val < 345 then 7 else (if q.val < 346 then 6 else 5)) else (if q.val < 349 then (if q.val < 348
  then 4 else 0) else (if q.val < 350 then 4 else 3))))) else (if q.val < 364 then (if q.val < 357
  then (if q.val < 354 then (if q.val < 352 then 2 else 5) else (if q.val < 355 then 5 else (if
  q.val < 356 then 4 else 3))) else (if q.val < 360 then (if q.val < 358 then 2 else (if q.val < 359
  then 7 else 8)) else (if q.val < 362 then (if q.val < 361 then 9 else 10) else (if q.val < 363
  then 12 else 11)))) else (if q.val < 371 then (if q.val < 367 then (if q.val < 365 then 12 else
  (if q.val < 366 then 11 else 9)) else (if q.val < 369 then (if q.val < 368 then 8 else 9) else (if
  q.val < 370 then 8 else 14))) else (if q.val < 374 then (if q.val < 372 then 13 else (if q.val <
  373 then 0 else 1)) else (if q.val < 376 then 0 else (if q.val < 377 then 1 else 0)))))) else (if
  q.val < 405 then (if q.val < 391 then (if q.val < 384 then (if q.val < 381 then (if q.val < 379
  then 0 else (if q.val < 380 then 1 else 0)) else (if q.val < 382 then 0 else (if q.val < 383 then
  2 else 1))) else (if q.val < 387 then (if q.val < 385 then 0 else (if q.val < 386 then 0 else 2))
  else (if q.val < 389 then 2 else (if q.val < 390 then 1 else 0)))) else (if q.val < 398 then (if
  q.val < 394 then (if q.val < 392 then 0 else 2) else (if q.val < 396 then (if q.val < 395 then 2
  else 0) else 2)) else (if q.val < 401 then (if q.val < 399 then 0 else (if q.val < 400 then 1 else
  0)) else (if q.val < 403 then (if q.val < 402 then 1 else 0) else (if q.val < 404 then 1 else
  0))))) else (if q.val < 418 then (if q.val < 411 then (if q.val < 408 then (if q.val < 406 then 1
  else (if q.val < 407 then 0 else 1)) else (if q.val < 409 then 0 else 1)) else (if q.val < 414
  then (if q.val < 412 then 1 else (if q.val < 413 then 2 else 1)) else (if q.val < 416 then 0 else
  (if q.val < 417 then 1 else 0)))) else (if q.val < 425 then (if q.val < 421 then (if q.val < 419
  then 1 else (if q.val < 420 then 1 else 0)) else (if q.val < 423 then (if q.val < 422 then 0 else
  2) else (if q.val < 424 then 1 else 0))) else (if q.val < 428 then (if q.val < 426 then 1 else (if
  q.val < 427 then 0 else 1)) else (if q.val < 430 then (if q.val < 429 then 1 else 10) else (if
  q.val < 431 then 9 else 10)))))))))

/-- DAG zero-height (max `0`-transitions in `96..431` from `q`). -/
def nodeMax0 (q : Fin 432) : ℕ :=
  (if q.val < 216 then (if q.val < 108 then (if q.val < 54 then 0 else (if q.val < 81 then 0 else
    (if q.val < 94 then 0 else (if q.val < 101 then (if q.val < 97 then (if q.val < 95 then 0 else
      (if q.val < 96 then 0 else 3)) else (if q.val < 99 then (if q.val < 98 then 3 else 4) else
        3)) else (if q.val < 104 then (if q.val < 102 then 1 else (if q.val < 103 then 1 else 0))
          else (if q.val < 106 then (if q.val < 105 then 3 else 2) else (if q.val < 107 then 5 else
            1))))))) else (if q.val < 162 then (if q.val < 135 then (if q.val < 121 then (if q.val
              < 114 then (if q.val < 111 then (if q.val < 109 then 5 else 1) else (if q.val < 112
                then 1 else (if q.val < 113 then 2 else 1))) else (if q.val < 117 then (if q.val <
                  115 then 1 else (if q.val < 116 then 0 else 1)) else (if q.val < 119 then 1 else
                    (if q.val < 120 then 3 else 2)))) else (if q.val < 128 then (if q.val < 124
                      then (if q.val < 122 then 3 else (if q.val < 123 then 2 else 0)) else (if
                        q.val < 126 then (if q.val < 125 then 2 else 1) else 11)) else 11)) else
                          (if q.val < 148 then (if q.val < 141 then 11 else (if q.val < 144 then 11
                            else (if q.val < 146 then 11 else (if q.val < 147 then 11 else 10))))
                              else (if q.val < 155 then (if q.val < 151 then (if q.val < 149 then
                                10 else (if q.val < 150 then 10 else 11)) else 10) else (if q.val <
                                  158 then 10 else (if q.val < 160 then 10 else (if q.val < 161
                                    then 10 else 11)))))) else (if q.val < 189 then (if q.val < 175
                                      then (if q.val < 168 then (if q.val < 165 then (if q.val <
                                        163 then 10 else (if q.val < 164 then 10 else 3)) else (if
                                          q.val < 166 then 2 else (if q.val < 167 then 2 else 1)))
                                            else (if q.val < 171 then (if q.val < 169 then 1 else
                                              (if q.val < 170 then 0 else 11)) else 11)) else 11)
                                                else 11))) else (if q.val < 324 then (if q.val <
                                                  270 then (if q.val < 243 then 11 else (if q.val <
                                                    256 then 11 else (if q.val < 263 then 11 else
                                                      (if q.val < 266 then (if q.val < 264 then 11
                                                        else 10) else 10)))) else (if q.val < 297
                                                          then (if q.val < 283 then (if q.val < 276
                                                            then (if q.val < 273 then (if q.val <
                                                              271 then 5 else (if q.val < 272 then
                                                                5 else 9)) else 9) else (if q.val <
                                                                  279 then 9 else (if q.val < 281
                                                                    then (if q.val < 280 then 9
                                                                      else 10) else (if q.val < 282
                                                                        then 10 else 4)))) else (if
                                                                          q.val < 290 then (if
                                                                            q.val < 286 then (if
                                                                              q.val < 284 then 6
                                                                                else 5) else (if
                                                                                  q.val < 288 then
                                                                                    9 else 7)) else
                                                                                      (if q.val <
                                                                                        293 then (if
                                                                                          q.val <
                                                                                            291 then
                                                                                              6 else
                                                                                                9)

  else (if q.val < 295 then (if q.val < 294 then 9 else 8) else 8)))) else (if q.val < 310 then (if
  q.val < 303 then (if q.val < 300 then (if q.val < 298 then 6 else 3) else (if q.val < 301 then 6
  else 5)) else (if q.val < 306 then (if q.val < 304 then 4 else (if q.val < 305 then 6 else 7))
  else (if q.val < 308 then (if q.val < 307 then 5 else 7) else 8))) else (if q.val < 317 then (if
  q.val < 313 then (if q.val < 311 then 2 else 6) else (if q.val < 315 then (if q.val < 314 then 9
  else 6) else (if q.val < 316 then 9 else 5))) else (if q.val < 320 then (if q.val < 318 then 7
  else (if q.val < 319 then 9 else 8)) else (if q.val < 322 then (if q.val < 321 then 7 else 5) else
  (if q.val < 323 then 6 else 5))))))) else (if q.val < 378 then (if q.val < 351 then (if q.val <
  337 then (if q.val < 330 then (if q.val < 327 then (if q.val < 325 then 5 else (if q.val < 326
  then 8 else 5)) else (if q.val < 328 then 5 else 2)) else (if q.val < 333 then (if q.val < 331
  then 1 else (if q.val < 332 then 1 else 0)) else (if q.val < 335 then (if q.val < 334 then 2 else
  1) else (if q.val < 336 then 1 else 0)))) else (if q.val < 344 then (if q.val < 340 then (if q.val
  < 338 then 4 else (if q.val < 339 then 2 else 4)) else (if q.val < 342 then (if q.val < 341 then 2
  else 4) else (if q.val < 343 then 2 else 3))) else (if q.val < 347 then 2 else (if q.val < 349
  then (if q.val < 348 then 2 else 0) else 1)))) else (if q.val < 364 then (if q.val < 357 then 1
  else (if q.val < 360 then (if q.val < 358 then 1 else (if q.val < 359 then 4 else 5)) else (if
  q.val < 362 then (if q.val < 361 then 6 else 7) else (if q.val < 363 then 8 else 7)))) else (if
  q.val < 371 then (if q.val < 367 then (if q.val < 365 then 8 else (if q.val < 366 then 8 else 5))
  else (if q.val < 369 then (if q.val < 368 then 5 else 4) else (if q.val < 370 then 4 else 9)))
  else (if q.val < 374 then (if q.val < 372 then 9 else (if q.val < 373 then 0 else 1)) else (if
  q.val < 376 then 0 else (if q.val < 377 then 1 else 0)))))) else (if q.val < 405 then (if q.val <
  391 then (if q.val < 384 then (if q.val < 381 then (if q.val < 379 then 0 else (if q.val < 380
  then 1 else 0)) else (if q.val < 382 then 0 else 1)) else (if q.val < 387 then (if q.val < 385
  then 0 else (if q.val < 386 then 0 else 1)) else (if q.val < 389 then 1 else (if q.val < 390 then
  1 else 0)))) else (if q.val < 398 then (if q.val < 394 then (if q.val < 392 then 0 else 1) else
  (if q.val < 396 then (if q.val < 395 then 1 else 0) else 1)) else 0)) else (if q.val < 418 then
  (if q.val < 411 then 0 else (if q.val < 414 then (if q.val < 412 then 0 else 1) else 0)) else (if
  q.val < 425 then (if q.val < 421 then 0 else (if q.val < 423 then (if q.val < 422 then 0 else 1)
  else (if q.val < 424 then 1 else 0))) else (if q.val < 428 then 0 else (if q.val < 430 then (if
  q.val < 429 then 0 else 6) else (if q.val < 431 then 6 else 7)))))))))

/-- Minimum number of `1`-transitions on any path in `96..431` from `126` (`main().0`) to `q`. -/
def nodeMin1 (q : Fin 432) : ℕ :=
  (if q.val < 216 then (if q.val < 108 then (if q.val < 54 then 0 else (if q.val < 81 then 0 else
    (if q.val < 94 then 0 else (if q.val < 101 then (if q.val < 97 then (if q.val < 95 then 0 else
      (if q.val < 96 then 0 else 18)) else (if q.val < 99 then (if q.val < 98 then 19 else 14) else
        (if q.val < 100 then 14 else 15))) else (if q.val < 104 then (if q.val < 102 then 15 else
          16) else (if q.val < 106 then 16 else (if q.val < 107 then 15 else 16))))))) else (if
            q.val < 162 then (if q.val < 135 then (if q.val < 121 then (if q.val < 114 then (if
              q.val < 111 then (if q.val < 109 then 14 else (if q.val < 110 then 15 else 25)) else
                (if q.val < 112 then 26 else 21)) else (if q.val < 117 then (if q.val < 115 then 22
                  else (if q.val < 116 then 22 else 23)) else (if q.val < 119 then (if q.val < 118
                    then 22 else 23) else (if q.val < 120 then 21 else 22)))) else (if q.val < 128
                      then (if q.val < 124 then (if q.val < 122 then 60 else 0) else (if q.val <
                        126 then (if q.val < 125 then 1 else 2) else (if q.val < 127 then 0 else
                          1))) else (if q.val < 131 then (if q.val < 129 then 10 else (if q.val <
                            130 then 100 else 101)) else (if q.val < 133 then (if q.val < 132 then
                              102 else 103) else (if q.val < 134 then 104 else 105))))) else (if
                                q.val < 148 then (if q.val < 141 then (if q.val < 138 then (if
                                  q.val < 136 then 106 else (if q.val < 137 then 107 else 108))
                                    else (if q.val < 139 then 109 else (if q.val < 140 then 11 else
                                      110))) else (if q.val < 144 then (if q.val < 142 then 111
                                        else (if q.val < 143 then 112 else 113)) else (if q.val <
                                          146 then (if q.val < 145 then 114 else 115) else (if
                                            q.val < 147 then 116 else 117)))) else (if q.val < 155
                                              then (if q.val < 151 then (if q.val < 149 then 118
                                                else (if q.val < 150 then 119 else 12)) else (if
                                                  q.val < 153 then (if q.val < 152 then 120 else
                                                    121) else (if q.val < 154 then 122 else 123)))
                                                      else (if q.val < 158 then (if q.val < 156
                                                        then 124 else (if q.val < 157 then 125 else
                                                          126)) else (if q.val < 160 then (if q.val
                                                            < 159 then 127 else 128) else (if q.val
                                                              < 161 then 129 else 13)))))) else (if
                                                                q.val < 189 then (if q.val < 175
                                                                  then (if q.val < 168 then (if
                                                                    q.val < 165 then (if q.val <
                                                                      163 then 130 else (if q.val <
                                                                        164 then 131 else 132))
                                                                          else (if q.val < 166 then
                                                                            133 else 134)) else (if
                                                                              q.val < 171 then (if
                                                                                q.val < 169 then
                                                                                  135 else (if
                                                                                    q.val < 170
                                                                                      then 135 else
                                                                                        14)) else
                                                                                          (if q.val
                                                                                            < 173
                                                                                              then
                                                                                                (if

  q.val < 172 then 15 else 16) else (if q.val < 174 then 17 else 18)))) else (if q.val < 182 then
  (if q.val < 178 then (if q.val < 176 then 19 else (if q.val < 177 then 2 else 20)) else (if q.val
  < 180 then (if q.val < 179 then 21 else 22) else (if q.val < 181 then 23 else 24))) else (if q.val
  < 185 then (if q.val < 183 then 25 else (if q.val < 184 then 26 else 27)) else (if q.val < 187
  then (if q.val < 186 then 28 else 29) else (if q.val < 188 then 3 else 30))))) else (if q.val <
  202 then (if q.val < 195 then (if q.val < 192 then (if q.val < 190 then 31 else (if q.val < 191
  then 32 else 33)) else (if q.val < 193 then 34 else (if q.val < 194 then 35 else 36))) else (if
  q.val < 198 then (if q.val < 196 then 37 else (if q.val < 197 then 38 else 39)) else (if q.val <
  200 then (if q.val < 199 then 4 else 40) else (if q.val < 201 then 41 else 42)))) else (if q.val <
  209 then (if q.val < 205 then (if q.val < 203 then 43 else (if q.val < 204 then 44 else 45)) else
  (if q.val < 207 then (if q.val < 206 then 46 else 47) else (if q.val < 208 then 48 else 49))) else
  (if q.val < 212 then (if q.val < 210 then 5 else (if q.val < 211 then 50 else 51)) else (if q.val
  < 214 then (if q.val < 213 then 52 else 53) else (if q.val < 215 then 54 else 55)))))))) else (if
  q.val < 324 then (if q.val < 270 then (if q.val < 243 then (if q.val < 229 then (if q.val < 222
  then (if q.val < 219 then (if q.val < 217 then 56 else (if q.val < 218 then 57 else 58)) else (if
  q.val < 220 then 59 else (if q.val < 221 then 6 else 60))) else (if q.val < 225 then (if q.val <
  223 then 61 else (if q.val < 224 then 62 else 63)) else (if q.val < 227 then (if q.val < 226 then
  64 else 65) else (if q.val < 228 then 66 else 67)))) else (if q.val < 236 then (if q.val < 232
  then (if q.val < 230 then 68 else (if q.val < 231 then 69 else 7)) else (if q.val < 234 then (if
  q.val < 233 then 70 else 71) else (if q.val < 235 then 72 else 73))) else (if q.val < 239 then (if
  q.val < 237 then 74 else (if q.val < 238 then 75 else 76)) else (if q.val < 241 then (if q.val <
  240 then 77 else 78) else (if q.val < 242 then 79 else 8))))) else (if q.val < 256 then (if q.val
  < 249 then (if q.val < 246 then (if q.val < 244 then 80 else (if q.val < 245 then 81 else 82))
  else (if q.val < 247 then 83 else (if q.val < 248 then 84 else 85))) else (if q.val < 252 then (if
  q.val < 250 then 86 else (if q.val < 251 then 87 else 88)) else (if q.val < 254 then (if q.val <
  253 then 89 else 9) else (if q.val < 255 then 90 else 91)))) else (if q.val < 263 then (if q.val <
  259 then (if q.val < 257 then 92 else (if q.val < 258 then 93 else 94)) else (if q.val < 261 then
  (if q.val < 260 then 95 else 96) else (if q.val < 262 then 97 else 98))) else (if q.val < 266 then
  (if q.val < 264 then 99 else (if q.val < 265 then 47 else 48)) else (if q.val < 268 then (if q.val
  < 267 then 49 else 50) else (if q.val < 269 then 51 else 52)))))) else (if q.val < 297 then (if
  q.val < 283 then (if q.val < 276 then (if q.val < 273 then (if q.val < 271 then 53 else (if q.val
  < 272 then 54 else 46)) else (if q.val < 274 then 47 else (if q.val < 275 then 48 else 49))) else
  (if q.val < 279 then (if q.val < 277 then 50 else (if q.val < 278 then 98 else 99)) else (if q.val
  < 281 then (if q.val < 280 then 100 else 110) else (if q.val < 282 then 111 else 112)))) else (if
  q.val < 290 then (if q.val < 286 then (if q.val < 284 then 48 else (if q.val < 285 then 49 else
  50)) else (if q.val < 288 then (if q.val < 287 then 63 else 38) else (if q.val < 289 then 82 else
  108))) else (if q.val < 293 then (if q.val < 291 then 97 else (if q.val < 292 then 85 else 86))
  else (if q.val < 295 then (if q.val < 294 then 87 else 35) else (if q.val < 296 then 31 else
  24))))) else (if q.val < 310 then (if q.val < 303 then (if q.val < 300 then (if q.val < 298 then
  51 else (if q.val < 299 then 58 else 59)) else (if q.val < 301 then 87 else (if q.val < 302 then
  117 else 124))) else (if q.val < 306 then (if q.val < 304 then 125 else (if q.val < 305 then 82
  else 31)) else (if q.val < 308 then (if q.val < 307 then 25 else 99) else (if q.val < 309 then 91
  else 92)))) else (if q.val < 317 then (if q.val < 313 then (if q.val < 311 then 5 else (if q.val <
  312 then 28 else 17)) else (if q.val < 315 then (if q.val < 314 then 50 else 80) else (if q.val <
  316 then 64 else 90))) else (if q.val < 320 then (if q.val < 318 then 107 else (if q.val < 319
  then 101 else 109)) else (if q.val < 322 then (if q.val < 321 then 32 else 26) else (if q.val <
  323 then 72 else 83))))))) else (if q.val < 378 then (if q.val < 351 then (if q.val < 337 then (if
  q.val < 330 then (if q.val < 327 then (if q.val < 325 then 50 else (if q.val < 326 then 25 else
  36)) else (if q.val < 328 then 100 else (if q.val < 329 then 17 else 13))) else (if q.val < 333
  then (if q.val < 331 then 14 else 15) else (if q.val < 335 then (if q.val < 334 then 19 else 20)
  else 21))) else (if q.val < 344 then (if q.val < 340 then (if q.val < 338 then 17 else (if q.val <
  339 then 18 else 27)) else (if q.val < 342 then (if q.val < 341 then 28 else 16) else (if q.val <
  343 then 17 else 13))) else (if q.val < 347 then (if q.val < 345 then 22 else (if q.val < 346 then
  23 else 24)) else (if q.val < 349 then (if q.val < 348 then 25 else 7) else (if q.val < 350 then 6
  else 7))))) else (if q.val < 364 then (if q.val < 357 then (if q.val < 354 then (if q.val < 352
  then 8 else (if q.val < 353 then 5 else 17)) else (if q.val < 355 then 23 else (if q.val < 356
  then 24 else 25))) else (if q.val < 360 then (if q.val < 358 then 26 else 19) else (if q.val < 362
  then 27 else (if q.val < 363 then 55 else 56)))) else (if q.val < 371 then (if q.val < 367 then
  (if q.val < 365 then 26 else (if q.val < 366 then 27 else 49)) else (if q.val < 369 then (if q.val
  < 368 then 50 else 49) else (if q.val < 370 then 50 else 65))) else (if q.val < 374 then (if q.val
  < 372 then 66 else (if q.val < 373 then 9 else 57)) else (if q.val < 376 then (if q.val < 375 then
  57 else 17) else 18))))) else (if q.val < 405 then (if q.val < 391 then (if q.val < 384 then (if
  q.val < 381 then (if q.val < 379 then 15 else 20) else (if q.val < 382 then 1 else (if q.val < 383
  then 1 else 2))) else (if q.val < 387 then (if q.val < 385 then 2 else (if q.val < 386 then 2 else
  56)) else (if q.val < 389 then (if q.val < 388 then 18 else 22) else 23))) else (if q.val < 398
  then (if q.val < 394 then (if q.val < 392 then 3 else (if q.val < 393 then 59 else 28)) else (if
  q.val < 396 then (if q.val < 395 then 19 else 4) else (if q.val < 397 then 17 else 58))) else (if
  q.val < 401 then (if q.val < 399 then 26 else (if q.val < 400 then 6 else 7)) else (if q.val < 403
  then (if q.val < 402 then 2 else 3) else (if q.val < 404 then 8 else 9))))) else (if q.val < 418
  then (if q.val < 411 then (if q.val < 408 then (if q.val < 406 then 10 else (if q.val < 407 then
  11 else 12)) else (if q.val < 409 then 13 else (if q.val < 410 then 8 else 27))) else (if q.val <
  414 then (if q.val < 412 then 14 else (if q.val < 413 then 19 else 20)) else (if q.val < 416 then
  (if q.val < 415 then 20 else 23) else (if q.val < 417 then 6 else 7)))) else (if q.val < 425 then
  (if q.val < 421 then (if q.val < 419 then 20 else (if q.val < 420 then 18 else 23)) else (if q.val
  < 423 then (if q.val < 422 then 26 else 13) else 14)) else (if q.val < 428 then (if q.val < 426
  then 22 else (if q.val < 427 then 23 else 18)) else (if q.val < 430 then (if q.val < 429 then 16
  else 18) else (if q.val < 431 then 19 else 32)))))))))

/-- Minimum number of `0`-transitions on any path in `96..431` from `126` (`main().0`) to `q`. -/
def nodeMin0 (q : Fin 432) : ℕ :=
  (if q.val < 216 then (if q.val < 108 then (if q.val < 54 then 0 else (if q.val < 81 then 0 else
    (if q.val < 94 then 0 else (if q.val < 101 then (if q.val < 97 then (if q.val < 95 then 0 else
      (if q.val < 96 then 0 else 1)) else (if q.val < 99 then (if q.val < 98 then 1 else 2) else
        3)) else (if q.val < 104 then (if q.val < 102 then 4 else (if q.val < 103 then 4 else 5))
          else (if q.val < 106 then (if q.val < 105 then 3 else 4) else 1)))))) else (if q.val <
            162 then (if q.val < 135 then (if q.val < 121 then (if q.val < 114 then (if q.val < 111
              then (if q.val < 109 then 1 else (if q.val < 110 then 1 else 2)) else (if q.val < 112
                then 2 else (if q.val < 113 then 2 else 3))) else (if q.val < 117 then (if q.val <
                  115 then 3 else (if q.val < 116 then 4 else 3)) else (if q.val < 119 then 2 else
                    1))) else (if q.val < 128 then (if q.val < 124 then (if q.val < 122 then 1 else
                      (if q.val < 123 then 1 else 2)) else (if q.val < 126 then 1 else 0)) else 0))
                        else 0) else (if q.val < 189 then (if q.val < 175 then (if q.val < 168 then
                          (if q.val < 165 then 0 else (if q.val < 166 then 0 else (if q.val < 167
                            then 0 else 1))) else (if q.val < 171 then (if q.val < 169 then 1 else
                              (if q.val < 170 then 2 else 0)) else 0)) else 0) else 0))) else (if
                                q.val < 324 then (if q.val < 270 then (if q.val < 243 then 0 else
                                  (if q.val < 256 then 0 else (if q.val < 263 then 0 else (if q.val
                                    < 266 then (if q.val < 264 then 0 else 1) else 1)))) else 1)
                                      else (if q.val < 378 then (if q.val < 351 then (if q.val <
                                        337 then (if q.val < 330 then (if q.val < 327 then 1 else
                                          (if q.val < 328 then 1 else 2)) else (if q.val < 333 then
                                            (if q.val < 331 then 2 else (if q.val < 332 then 2 else
                                              3)) else (if q.val < 335 then 2 else (if q.val < 336
                                                then 2 else 3)))) else (if q.val < 344 then 1 else
                                                  (if q.val < 347 then 1 else (if q.val < 349 then
                                                    (if q.val < 348 then 1 else 3) else 2)))) else
                                                      (if q.val < 364 then (if q.val < 357 then (if
                                                        q.val < 354 then (if q.val < 352 then 2
                                                          else (if q.val < 353 then 2 else 3)) else
                                                            2) else (if q.val < 360 then (if q.val
                                                              < 358 then 2 else 1) else (if q.val <
                                                                362 then (if q.val < 361 then 1
                                                                  else 2) else 1))) else (if q.val
                                                                    < 371 then 1 else (if q.val <
                                                                      374 then 1 else (if q.val <
                                                                        376 then (if q.val < 375
                                                                          then 2 else 1) else (if
                                                                            q.val < 377 then 2 else
                                                                              3)))))) else (if
                                                                                q.val < 405 then
                                                                                  (if q.val < 391
                                                                                    then (if q.val
                                                                                      < 384 then
                                                                                        (if q.val <
                                                                                          381 then
                                                                                            (if
                                                                                              q.val
                                                                                                <

  379 then 1 else (if q.val < 380 then 1 else 2)) else (if q.val < 382 then 1 else 2)) else (if
  q.val < 387 then (if q.val < 385 then 3 else 1) else (if q.val < 389 then 2 else (if q.val < 390
  then 2 else 3)))) else (if q.val < 398 then (if q.val < 394 then (if q.val < 392 then 1 else (if
  q.val < 393 then 1 else 2)) else (if q.val < 396 then 1 else 2)) else (if q.val < 401 then 1 else
  (if q.val < 403 then 2 else 1)))) else (if q.val < 418 then (if q.val < 411 then (if q.val < 408
  then 1 else (if q.val < 409 then 1 else (if q.val < 410 then 3 else 2))) else (if q.val < 414 then
  (if q.val < 412 then 1 else 3) else (if q.val < 416 then 4 else 1))) else (if q.val < 425 then (if
  q.val < 421 then (if q.val < 419 then 1 else (if q.val < 420 then 2 else 3)) else (if q.val < 423
  then (if q.val < 422 then 1 else 3) else (if q.val < 424 then 3 else 4))) else (if q.val < 428
  then (if q.val < 426 then 2 else (if q.val < 427 then 2 else 1)) else (if q.val < 430 then (if
  q.val < 429 then 3 else 1) else 1))))))))

/-- Number of `0`-steps (`1..10`) from tree state `q ∈ {96..431}` to reach a leaf in `49..70`. -/
def zeroDepth (q : Fin 432) : ℕ :=
  (if q.val < 216 then (if q.val < 108 then (if q.val < 54 then 0 else (if q.val < 81 then 0 else
    (if q.val < 94 then 0 else (if q.val < 101 then (if q.val < 97 then (if q.val < 95 then 0 else
      (if q.val < 96 then 0 else 3)) else (if q.val < 99 then (if q.val < 98 then 3 else 2) else
        (if q.val < 100 then 1 else 2))) else (if q.val < 104 then (if q.val < 102 then 1 else (if
          q.val < 103 then 2 else 1)) else (if q.val < 106 then (if q.val < 105 then 2 else 1) else
            (if q.val < 107 then 3 else 2))))))) else (if q.val < 162 then (if q.val < 135 then (if
              q.val < 121 then (if q.val < 114 then (if q.val < 111 then (if q.val < 109 then 3
                else (if q.val < 110 then 2 else 1)) else (if q.val < 112 then 2 else (if q.val <
                  113 then 2 else 1))) else (if q.val < 117 then (if q.val < 115 then 2 else (if
                    q.val < 116 then 1 else 2)) else (if q.val < 119 then (if q.val < 118 then 1
                      else 2) else (if q.val < 120 then 3 else 2)))) else (if q.val < 128 then (if
                        q.val < 124 then (if q.val < 122 then 3 else (if q.val < 123 then 2 else
                          1)) else (if q.val < 126 then 2 else (if q.val < 127 then 3 else 2)))
                            else (if q.val < 131 then (if q.val < 129 then 2 else 8) else (if q.val
                              < 133 then (if q.val < 132 then 9 else 6) else 6)))) else (if q.val <
                                148 then (if q.val < 141 then (if q.val < 138 then (if q.val < 136
                                  then 7 else (if q.val < 137 then 8 else 6)) else (if q.val < 139
                                    then 6 else (if q.val < 140 then 3 else 9))) else (if q.val <
                                      144 then (if q.val < 142 then 6 else (if q.val < 143 then 8
                                        else 7)) else (if q.val < 146 then (if q.val < 145 then 6
                                          else 10) else (if q.val < 147 then 9 else 5)))) else (if
                                            q.val < 155 then (if q.val < 151 then (if q.val < 149
                                              then 4 else (if q.val < 150 then 5 else 2)) else (if
                                                q.val < 153 then (if q.val < 152 then 7 else 5)
                                                  else (if q.val < 154 then 6 else 5))) else (if
                                                    q.val < 158 then (if q.val < 156 then 6 else
                                                      (if q.val < 157 then 5 else 6)) else (if
                                                        q.val < 160 then 6 else (if q.val < 161
                                                          then 10 else 4)))))) else (if q.val < 189
                                                            then (if q.val < 175 then (if q.val <
                                                              168 then (if q.val < 165 then (if
                                                                q.val < 163 then 6 else (if q.val <
                                                                  164 then 10 else 3)) else (if
                                                                    q.val < 166 then 1 else (if
                                                                      q.val < 167 then 2 else 1)))
                                                                        else (if q.val < 171 then
                                                                          (if q.val < 169 then 2
                                                                            else (if q.val < 170
                                                                              then 1 else 4)) else
                                                                                (if q.val < 173
                                                                                  then (if q.val <
                                                                                    172 then 4 else
                                                                                      5) else (if
                                                                                        q.val < 174
                                                                                          then 6
                                                                                            else
                                                                                              2))))
                                                                                                else

  (if q.val < 182 then (if q.val < 178 then 2 else (if q.val < 180 then (if q.val < 179 then 4 else
  3) else (if q.val < 181 then 4 else 6))) else (if q.val < 185 then (if q.val < 183 then 4 else 5)
  else (if q.val < 187 then (if q.val < 186 then 6 else 5) else (if q.val < 188 then 2 else 6)))))
  else (if q.val < 202 then (if q.val < 195 then (if q.val < 192 then (if q.val < 190 then 7 else
  (if q.val < 191 then 8 else 6)) else (if q.val < 193 then 5 else (if q.val < 194 then 7 else 8)))
  else (if q.val < 198 then (if q.val < 196 then 5 else (if q.val < 197 then 8 else 6)) else (if
  q.val < 200 then (if q.val < 199 then 2 else 5) else (if q.val < 201 then 6 else 5)))) else (if
  q.val < 209 then (if q.val < 205 then (if q.val < 203 then 6 else 5) else (if q.val < 207 then (if
  q.val < 206 then 5 else 6) else 5)) else (if q.val < 212 then (if q.val < 210 then 3 else (if
  q.val < 211 then 6 else 7)) else (if q.val < 214 then (if q.val < 213 then 5 else 7) else (if
  q.val < 215 then 6 else 9)))))))) else (if q.val < 324 then (if q.val < 270 then (if q.val < 243
  then (if q.val < 229 then (if q.val < 222 then (if q.val < 219 then (if q.val < 217 then 2 else
  (if q.val < 218 then 2 else 3)) else 2) else (if q.val < 225 then (if q.val < 223 then 3 else (if
  q.val < 224 then 5 else 8)) else (if q.val < 227 then (if q.val < 226 then 6 else 5) else (if
  q.val < 228 then 8 else 5)))) else (if q.val < 236 then (if q.val < 232 then (if q.val < 230 then
  9 else (if q.val < 231 then 5 else 3)) else (if q.val < 234 then (if q.val < 233 then 5 else 6)
  else 6)) else (if q.val < 239 then 5 else (if q.val < 241 then (if q.val < 240 then 5 else 6) else
  (if q.val < 242 then 6 else 2))))) else (if q.val < 256 then (if q.val < 249 then (if q.val < 246
  then (if q.val < 244 then 7 else (if q.val < 245 then 5 else 8)) else (if q.val < 247 then 7 else
  (if q.val < 248 then 7 else 6))) else (if q.val < 252 then (if q.val < 250 then 4 else (if q.val <
  251 then 6 else 3)) else (if q.val < 254 then (if q.val < 253 then 7 else 3) else 6))) else (if
  q.val < 263 then (if q.val < 259 then 6 else (if q.val < 261 then 5 else (if q.val < 262 then 7
  else 8))) else (if q.val < 266 then 5 else (if q.val < 268 then (if q.val < 267 then 5 else 6)
  else (if q.val < 269 then 5 else 8)))))) else (if q.val < 297 then (if q.val < 283 then (if q.val
  < 276 then (if q.val < 273 then (if q.val < 271 then 5 else (if q.val < 272 then 5 else 4)) else
  (if q.val < 274 then 6 else 5)) else (if q.val < 279 then (if q.val < 277 then 6 else (if q.val <
  278 then 7 else 8)) else (if q.val < 281 then (if q.val < 280 then 6 else 8) else (if q.val < 282
  then 6 else 3)))) else (if q.val < 290 then (if q.val < 286 then (if q.val < 284 then 4 else 5)
  else (if q.val < 288 then 7 else (if q.val < 289 then 7 else 5))) else (if q.val < 293 then (if
  q.val < 291 then 6 else 5) else (if q.val < 295 then (if q.val < 294 then 9 else 6) else (if q.val
  < 296 then 6 else 5))))) else (if q.val < 310 then (if q.val < 303 then (if q.val < 300 then (if
  q.val < 298 then 6 else 2) else (if q.val < 301 then 5 else (if q.val < 302 then 4 else 5))) else
  (if q.val < 306 then (if q.val < 304 then 4 else (if q.val < 305 then 6 else 5)) else (if q.val <
  308 then (if q.val < 307 then 3 else 7) else 5))) else (if q.val < 317 then (if q.val < 313 then
  (if q.val < 311 then 2 else 5) else (if q.val < 315 then (if q.val < 314 then 5 else 6) else 5))
  else (if q.val < 320 then (if q.val < 318 then 7 else (if q.val < 319 then 9 else 5)) else 5)))))
  else (if q.val < 378 then (if q.val < 351 then (if q.val < 337 then (if q.val < 330 then (if q.val
  < 327 then 5 else (if q.val < 328 then 4 else 2)) else (if q.val < 333 then (if q.val < 331 then 1
  else (if q.val < 332 then 2 else 1)) else (if q.val < 335 then (if q.val < 334 then 2 else 1) else
  (if q.val < 336 then 2 else 1)))) else (if q.val < 344 then (if q.val < 340 then (if q.val < 338
  then 4 else (if q.val < 339 then 2 else 4)) else (if q.val < 342 then (if q.val < 341 then 2 else
  4) else (if q.val < 343 then 2 else 3))) else (if q.val < 347 then 2 else (if q.val < 349 then (if
  q.val < 348 then 2 else 1) else (if q.val < 350 then 1 else 2))))) else (if q.val < 364 then (if
  q.val < 357 then (if q.val < 354 then (if q.val < 352 then 2 else 1) else (if q.val < 355 then 1
  else (if q.val < 356 then 1 else 2))) else (if q.val < 360 then (if q.val < 358 then 2 else (if
  q.val < 359 then 4 else 5)) else (if q.val < 362 then (if q.val < 361 then 6 else 7) else (if
  q.val < 363 then 8 else 5)))) else (if q.val < 371 then (if q.val < 367 then (if q.val < 365 then
  4 else (if q.val < 366 then 8 else 4)) else (if q.val < 369 then (if q.val < 368 then 5 else 4)
  else (if q.val < 370 then 4 else 8))) else (if q.val < 374 then (if q.val < 372 then 5 else (if
  q.val < 373 then 1 else 2)) else (if q.val < 376 then 1 else (if q.val < 377 then 2 else 1))))))
  else (if q.val < 405 then (if q.val < 391 then (if q.val < 384 then (if q.val < 381 then (if q.val
  < 379 then 1 else (if q.val < 380 then 2 else 1)) else (if q.val < 382 then 1 else (if q.val < 383
  then 1 else 2))) else (if q.val < 387 then 1 else (if q.val < 389 then 1 else (if q.val < 390 then
  2 else 1)))) else 1) else (if q.val < 418 then (if q.val < 411 then 1 else (if q.val < 414 then
  (if q.val < 412 then 1 else (if q.val < 413 then 1 else 2)) else 1)) else (if q.val < 425 then (if
  q.val < 421 then 1 else (if q.val < 423 then 1 else (if q.val < 424 then 2 else 1))) else (if
  q.val < 428 then 1 else (if q.val < 430 then (if q.val < 429 then 1 else 4) else (if q.val < 431
  then 6 else 7)))))))))

/-- The leaf state in `49..70` reached from `q ∈ {96..431}` after `zeroDepth q` zero-steps. -/
def zeroLeaf (q : Fin 432) : Fin 432 :=
  (if q.val < 216 then (if q.val < 108 then (if q.val < 54 then 49 else (if q.val < 81 then 49 else
    (if q.val < 94 then 49 else (if q.val < 101 then (if q.val < 97 then (if q.val < 95 then 49
      else (if q.val < 96 then 49 else 69)) else (if q.val < 99 then (if q.val < 98 then 61 else
        49) else 49)) else (if q.val < 104 then (if q.val < 102 then 49 else 50) else (if q.val <
          106 then 50 else (if q.val < 107 then 49 else 55))))))) else (if q.val < 162 then (if
            q.val < 135 then (if q.val < 121 then (if q.val < 114 then (if q.val < 111 then (if
              q.val < 109 then 49 else (if q.val < 110 then 57 else 49)) else (if q.val < 112 then
                67 else 63)) else (if q.val < 117 then (if q.val < 115 then 65 else (if q.val < 116
                  then 65 else 63)) else (if q.val < 119 then 65 else (if q.val < 120 then 63 else
                    53)))) else (if q.val < 128 then (if q.val < 124 then (if q.val < 122 then 63
                      else 59) else (if q.val < 126 then (if q.val < 125 then 51 else 61) else (if
                        q.val < 127 then 59 else 49))) else (if q.val < 131 then (if q.val < 129
                          then 61 else 67) else (if q.val < 133 then (if q.val < 132 then 67 else
                            69) else (if q.val < 134 then 69 else 67))))) else (if q.val < 148 then
                              (if q.val < 141 then (if q.val < 138 then (if q.val < 136 then 67
                                else (if q.val < 137 then 67 else 69)) else (if q.val < 139 then 69
                                  else (if q.val < 140 then 59 else 67))) else (if q.val < 144 then
                                    67 else (if q.val < 146 then (if q.val < 145 then 69 else 67)
                                      else 67))) else (if q.val < 155 then (if q.val < 151 then (if
                                        q.val < 149 then 67 else (if q.val < 150 then 67 else 61))
                                          else (if q.val < 153 then 67 else (if q.val < 154 then 67
                                            else 69))) else (if q.val < 158 then (if q.val < 156
                                              then 67 else (if q.val < 157 then 69 else 67)) else
                                                (if q.val < 160 then (if q.val < 159 then 67 else
                                                  69) else 67))))) else (if q.val < 189 then (if
                                                    q.val < 175 then (if q.val < 168 then (if q.val
                                                      < 165 then (if q.val < 163 then 69 else 67)
                                                        else 67) else (if q.val < 171 then (if
                                                          q.val < 169 then 68 else (if q.val < 170
                                                            then 68 else 49)) else (if q.val < 173
                                                              then (if q.val < 172 then 49 else 67)
                                                                else 67))) else (if q.val < 182
                                                                  then (if q.val < 178 then (if
                                                                    q.val < 176 then 55 else (if
                                                                      q.val < 177 then 53 else 61))
                                                                        else (if q.val < 180 then
                                                                          (if q.val < 179 then 63
                                                                            else 67) else (if q.val
                                                                              < 181 then 49 else
                                                                                67))) else (if
                                                                                  q.val < 185 then
                                                                                    (if q.val < 183
                                                                                      then 67 else
                                                                                        (if q.val <
                                                                                          184 then
                                                                                            69 else
                                                                                              67))
                                                                                                else

  (if q.val < 187 then 67 else (if q.val < 188 then 55 else 67))))) else (if q.val < 202 then (if
  q.val < 195 then (if q.val < 192 then (if q.val < 190 then 69 else 67) else (if q.val < 193 then
  67 else (if q.val < 194 then 69 else 67))) else (if q.val < 198 then (if q.val < 196 then 67 else
  (if q.val < 197 then 69 else 67)) else (if q.val < 200 then (if q.val < 199 then 57 else 69) else
  (if q.val < 201 then 67 else 69)))) else (if q.val < 209 then (if q.val < 205 then (if q.val < 203
  then 67 else 69) else (if q.val < 207 then (if q.val < 206 then 67 else 69) else (if q.val < 208
  then 67 else 69))) else (if q.val < 212 then (if q.val < 210 then 59 else (if q.val < 211 then 69
  else 67)) else (if q.val < 214 then 67 else (if q.val < 215 then 69 else 67)))))))) else (if q.val
  < 324 then (if q.val < 270 then (if q.val < 243 then (if q.val < 229 then (if q.val < 222 then (if
  q.val < 219 then (if q.val < 217 then 53 else (if q.val < 218 then 61 else 57)) else (if q.val <
  220 then 55 else 61)) else (if q.val < 225 then (if q.val < 223 then 57 else (if q.val < 224 then
  67 else 69)) else (if q.val < 227 then (if q.val < 226 then 69 else 67) else 69))) else (if q.val
  < 236 then (if q.val < 232 then (if q.val < 230 then 67 else (if q.val < 231 then 67 else 59))
  else (if q.val < 234 then (if q.val < 233 then 69 else 67) else 69)) else (if q.val < 239 then (if
  q.val < 237 then 69 else 67) else (if q.val < 241 then 69 else (if q.val < 242 then 67 else
  61))))) else (if q.val < 256 then (if q.val < 249 then (if q.val < 246 then (if q.val < 244 then
  67 else (if q.val < 245 then 69 else 67)) else (if q.val < 247 then 67 else (if q.val < 248 then
  67 else 69))) else (if q.val < 252 then 67 else (if q.val < 254 then (if q.val < 253 then 67 else
  59) else 67))) else (if q.val < 263 then (if q.val < 259 then (if q.val < 257 then 67 else (if
  q.val < 258 then 67 else 69)) else (if q.val < 261 then (if q.val < 260 then 69 else 67) else 67))
  else (if q.val < 266 then (if q.val < 264 then 69 else (if q.val < 265 then 69 else 67)) else (if
  q.val < 268 then (if q.val < 267 then 69 else 67) else 69))))) else (if q.val < 297 then (if q.val
  < 283 then (if q.val < 276 then (if q.val < 273 then (if q.val < 271 then 69 else 67) else (if
  q.val < 274 then 67 else (if q.val < 275 then 69 else 67))) else (if q.val < 279 then 67 else (if
  q.val < 281 then 67 else (if q.val < 282 then 69 else 67)))) else (if q.val < 290 then (if q.val <
  286 then (if q.val < 284 then 67 else (if q.val < 285 then 69 else 67)) else (if q.val < 288 then
  69 else (if q.val < 289 then 67 else 69))) else (if q.val < 293 then (if q.val < 291 then 67 else
  69) else (if q.val < 295 then (if q.val < 294 then 67 else 69) else (if q.val < 296 then 69 else
  67))))) else (if q.val < 310 then (if q.val < 303 then (if q.val < 300 then (if q.val < 298 then
  67 else (if q.val < 299 then 57 else 61)) else 67) else (if q.val < 306 then (if q.val < 304 then
  67 else (if q.val < 305 then 67 else 69)) else 67)) else (if q.val < 317 then (if q.val < 313 then
  (if q.val < 311 then 59 else 67) else (if q.val < 315 then (if q.val < 314 then 69 else 67) else
  (if q.val < 316 then 69 else 67))) else (if q.val < 320 then (if q.val < 318 then 67 else (if
  q.val < 319 then 67 else 69)) else (if q.val < 322 then (if q.val < 321 then 69 else 67) else (if
  q.val < 323 then 69 else 67))))))) else (if q.val < 378 then (if q.val < 351 then (if q.val < 337
  then (if q.val < 330 then (if q.val < 327 then 67 else (if q.val < 328 then 67 else (if q.val <
  329 then 69 else 67))) else (if q.val < 333 then (if q.val < 331 then 69 else 62) else (if q.val <
  335 then (if q.val < 334 then 61 else 67) else 64))) else (if q.val < 344 then (if q.val < 340
  then (if q.val < 338 then 67 else (if q.val < 339 then 53 else 67)) else (if q.val < 342 then (if
  q.val < 341 then 55 else 67) else (if q.val < 343 then 57 else 67))) else (if q.val < 347 then (if
  q.val < 345 then 67 else (if q.val < 346 then 69 else 63)) else (if q.val < 349 then (if q.val <
  348 then 49 else 63) else (if q.val < 350 then 62 else 63))))) else (if q.val < 364 then (if q.val
  < 357 then (if q.val < 354 then (if q.val < 352 then 61 else (if q.val < 353 then 59 else 69))
  else (if q.val < 355 then 69 else (if q.val < 356 then 68 else 63))) else (if q.val < 360 then 67
  else (if q.val < 362 then 67 else (if q.val < 363 then 67 else 69)))) else (if q.val < 371 then
  (if q.val < 367 then (if q.val < 365 then 69 else (if q.val < 366 then 67 else 69)) else (if q.val
  < 369 then (if q.val < 368 then 67 else 69) else 67)) else (if q.val < 374 then (if q.val < 372
  then 69 else (if q.val < 373 then 64 else 62)) else (if q.val < 376 then (if q.val < 375 then 62
  else 68) else 68))))) else (if q.val < 405 then (if q.val < 391 then (if q.val < 384 then (if
  q.val < 381 then (if q.val < 379 then 70 else 62) else (if q.val < 382 then 49 else (if q.val <
  383 then 51 else 62))) else (if q.val < 387 then (if q.val < 385 then 62 else 53) else (if q.val <
  389 then 53 else 62))) else (if q.val < 398 then (if q.val < 394 then 55 else (if q.val < 396 then
  (if q.val < 395 then 55 else 57) else 57)) else (if q.val < 401 then (if q.val < 399 then 61 else
  (if q.val < 400 then 61 else 50)) else (if q.val < 403 then (if q.val < 402 then 61 else 52) else
  (if q.val < 404 then 61 else 54))))) else (if q.val < 418 then (if q.val < 411 then (if q.val <
  408 then (if q.val < 406 then 61 else (if q.val < 407 then 56 else 61)) else (if q.val < 409 then
  58 else 61)) else (if q.val < 414 then (if q.val < 412 then 61 else (if q.val < 413 then 61 else
  68)) else (if q.val < 416 then (if q.val < 415 then 68 else 63) else (if q.val < 417 then 63 else
  60)))) else (if q.val < 425 then (if q.val < 421 then (if q.val < 419 then 63 else (if q.val < 420
  then 63 else 65)) else (if q.val < 423 then 67 else 70)) else (if q.val < 428 then (if q.val < 426
  then 67 else (if q.val < 427 then 62 else 67)) else (if q.val < 430 then 69 else 67))))))))

/-- Internal decision-tree walk: succeeds with `some q_end` (`96 ≤ q_end.val`) iff starting at
`q` (`96 ≤ q.val`), every bit `b` in `pref` takes a rightward transition `(b, .right, q')` into
another decision-tree state `q'` (`96 ≤ q'.val`). -/
def walkInternal (q : Fin 432) : List (Fin 2) → Option (Fin 432)
  | [] => if 96 ≤ q.val then some q else none
  | b :: bs =>
    if 96 ≤ q.val then
      match refTrans q b with
      | some (w, .right, q') =>
        if w == b && 96 ≤ q'.val then walkInternal q' bs else none
      | _ => none
    else none

theorem tree_root_bounds :
    nodeMaxLen 126 = 147 ∧ nodeMax0 126 = 11 ∧ nodeMin1 126 = 0 ∧ nodeMin0 126 = 0 := by
  decide

def stepBoundsBool (q : Fin 432) (b : Fin 2) : Bool :=
  match refTrans q b with
  | some (w, .right, q') =>
    if 96 ≤ q.val && 96 ≤ q'.val then
      (w == b) &&
      (nodeMaxLen q' + 1 ≤ nodeMaxLen q) &&
      (nodeMax0 q' + (if b == 0 then 1 else 0) ≤ nodeMax0 q) &&
      (nodeMin1 q' ≤ nodeMin1 q + (if b == 1 then 1 else 0)) &&
      (nodeMin0 q' ≤ nodeMin0 q + (if b == 0 then 1 else 0))
    else true
  | _ => true

set_option maxHeartbeats 0 in
-- kernel `decide` over all 432 × 2 (state, symbol) pairs of the DAG bound table
theorem stepBoundsBool_all (q : Fin 432) (b : Fin 2) : stepBoundsBool q b = true := by
  revert q b; decide

theorem tree_step_bounds {q q' : Fin 432} {b w : Fin 2}
    (hq : 96 ≤ q.val) (hq' : 96 ≤ q'.val) (htr : refTrans q b = some (w, .right, q')) :
    w = b ∧
    nodeMaxLen q' + 1 ≤ nodeMaxLen q ∧
    nodeMax0 q' + (if b == 0 then 1 else 0) ≤ nodeMax0 q ∧
    nodeMin1 q' ≤ nodeMin1 q + (if b == 1 then 1 else 0) ∧
    nodeMin0 q' ≤ nodeMin0 q + (if b == 0 then 1 else 0) := by
  have h := stepBoundsBool_all q b
  simp only [stepBoundsBool, htr, hq, hq', decide_true, Bool.and_self, ↓reduceIte,
    Bool.and_eq_true, decide_eq_true_eq, Bool.and_assoc] at h
  rw [beq_iff_eq] at h
  exact h

def zeroStepBool (q : Fin 432) : Bool :=
  if 96 ≤ q.val then
    (1 ≤ zeroDepth q) && (zeroDepth q ≤ 10) &&
    (zeroDepth q ≤ nodeMax0 q + 1) &&
    (49 ≤ (zeroLeaf q).val) && ((zeroLeaf q).val ≤ 70) &&
    match refTrans q 0 with
    | some (w, .right, q') =>
      (w == 0) &&
      ((zeroDepth q == 1 && q' == zeroLeaf q) ||
       (96 ≤ q'.val && zeroDepth q == zeroDepth q' + 1 && q' == q' && zeroLeaf q' == zeroLeaf q))
    | _ => false
  else true

set_option maxHeartbeats 0 in
-- kernel `decide` over all 432 states of the zero-depth leaf table
theorem zeroStepBool_all (q : Fin 432) : zeroStepBool q = true := by
  revert q; decide

def oneStepBool (q : Fin 432) : Bool :=
  if 96 ≤ q.val then
    match refTrans q 1 with
    | none => q == 166
    | some (w, .left, q') =>
      (w == 0) && (89 ≤ q'.val) && (q'.val ≤ 95) &&
      (if q'.val ≤ 91 then q'.val - 89 ≤ nodeMin0 q
       else q'.val - 92 + 1 ≤ nodeMin1 q)
    | some (w, .right, q') =>
      (w == 1) &&
      ((49 ≤ q'.val && q'.val ≤ 70 && (isLeafInc q' || 1 ≤ nodeMin0 q)) ||
       (96 ≤ q'.val))
  else true

set_option maxHeartbeats 0 in
-- kernel `decide` over all 432 states of the one-transition classification table
theorem oneStepBool_all (q : Fin 432) : oneStepBool q = true := by
  revert q; decide

theorem leaf_stage3_eq (q' : Fin 432) :
    49 ≤ q'.val → q'.val ≤ 70 →
    refTrans q' 0 = some (1, .right, 8) ∧
    (if isLeafInc q' then q' = regIncStage3 (leafReg q')
     else q' = regDecnzStage3 (leafReg q')) := by
  revert q'; decide

theorem walkInternal_ge_96 {q q_end : Fin 432} {pref : List (Fin 2)}
    (h : walkInternal q pref = some q_end) :
    96 ≤ q.val ∧ 96 ≤ q_end.val := by
  induction pref generalizing q with
  | nil =>
    unfold walkInternal at h
    split at h
    · injection h with h'; subst h'; exact ⟨‹_›, ‹_›⟩
    · cases h
  | cons b bs ih =>
    unfold walkInternal at h
    split at h
    · rcases htr : refTrans q b with _ | ⟨w, d, q'⟩
      · rw [htr] at h; cases h
      · cases d with
        | left => rw [htr] at h; cases h
        | right =>
          rw [htr] at h
          dsimp only at h
          split at h
          · exact ⟨‹_›, (ih h).2⟩
          · cases h
    · cases h

theorem walkInternal_append (q : Fin 432) (p₁ p₂ : List (Fin 2)) :
    walkInternal q (p₁ ++ p₂) = (walkInternal q p₁).bind (fun q' => walkInternal q' p₂) := by
  induction p₁ generalizing q with
  | nil =>
    simp only [List.nil_append]
    change walkInternal q p₂ =
      (if 96 ≤ q.val then some q else none).bind (fun q' => walkInternal q' p₂)
    split
    · rfl
    · rename_i hq
      cases p₂ <;> simp [walkInternal, hq]
  | cons b bs ih =>
    simp only [List.cons_append, walkInternal]
    split
    · rcases htr : refTrans q b with _ | ⟨w, d, q'⟩
      · rfl
      · cases d with
        | left => rfl
        | right =>
          dsimp only
          split
          · exact ih q'
          · rfl
    · rfl

theorem walkInternal_take {q : Fin 432} {pref : List (Fin 2)}
    (h : (walkInternal q pref).isSome = true) (n : ℕ) :
    (walkInternal q (pref.take n)).isSome = true := by
  have heq : pref = pref.take n ++ pref.drop n := (List.take_append_drop n pref).symm
  rw [heq, walkInternal_append] at h
  rcases htake : walkInternal q (pref.take n) with _ | q'
  · rw [htake] at h; cases h
  · rfl

theorem walkInternal_bounds {q q_end : Fin 432} {pref : List (Fin 2)}
    (h : walkInternal q pref = some q_end) :
    pref.length + nodeMaxLen q_end ≤ nodeMaxLen q ∧
    pref.count 0 + nodeMax0 q_end ≤ nodeMax0 q ∧
    nodeMin1 q_end ≤ nodeMin1 q + pref.count 1 ∧
    nodeMin0 q_end ≤ nodeMin0 q + pref.count 0 := by
  induction pref generalizing q with
  | nil =>
    unfold walkInternal at h
    split at h
    · injection h with h'; subst h'; simp
    · cases h
  | cons b bs ih =>
    unfold walkInternal at h
    split at h
    · rename_i hq
      rcases htr : refTrans q b with _ | ⟨w, d, q'⟩
      · rw [htr] at h; cases h
      · cases d with
        | left => rw [htr] at h; cases h
        | right =>
          rw [htr] at h
          dsimp only at h
          split at h
          · rename_i hcond
            rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            rcases hcond with ⟨rfl, hq'⟩
            obtain ⟨_, hlen, hmax0, hmin1, hmin0⟩ := tree_step_bounds hq hq' htr
            obtain ⟨ih1, ih2, ih3, ih4⟩ := ih h
            rcases fin2_cases w with rfl | rfl <;>
              (simp only [List.length_cons, List.count_cons, beq_self_eq_true,
                ↓reduceIte] at hmax0 hmin1 hmin0 ⊢;
               change _ at hmax0 hmin1 hmin0 ⊢; omega)
          · cases h
    · cases h

theorem walkInternal_root_bounds {q_end : Fin 432} {pref : List (Fin 2)}
    (h : walkInternal 126 pref = some q_end) :
    pref.length + nodeMaxLen q_end ≤ 147 ∧
    pref.count 0 + nodeMax0 q_end ≤ 11 ∧
    nodeMin1 q_end ≤ pref.count 1 ∧
    nodeMin0 q_end ≤ pref.count 0 := by
  have hb := walkInternal_bounds h
  have hr := tree_root_bounds
  omega

theorem walkTape_of_walkInternal {q q_end : Fin 432} {pref : List (Fin 2)}
    (h : walkInternal q pref = some q_end) (walked rem : List (Fin 2)) :
    walkTape q walked (pref ++ rem) = walkTape q_end (walked ++ pref) rem := by
  induction pref generalizing q walked with
  | nil =>
    unfold walkInternal at h
    split at h
    · injection h with h'; subst h'; simp
    · cases h
  | cons b bs ih =>
    unfold walkInternal at h
    split at h
    · rcases htr : refTrans q b with _ | ⟨w, d, q'⟩
      · rw [htr] at h; cases h
      · cases d with
        | left => rw [htr] at h; cases h
        | right =>
          rw [htr] at h
          dsimp only at h
          split at h
          · rename_i hcond
            rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            rcases hcond with ⟨rfl, hq'⟩
            have hleaf : (49 ≤ q'.val && q'.val ≤ 70) = false := by
              rw [Bool.and_eq_false_iff]; right; rw [decide_eq_false_iff_not]; omega
            simp only [List.cons_append, walkTape, htr, beq_self_eq_true, ↓reduceIte,
              hleaf, Bool.false_eq_true]
            rw [ih h (walked ++ [w]), List.append_assoc, List.singleton_append]
          · cases h
    · cases h

theorem walkTape_replicate_zero :
    ∀ (d : ℕ) {q : Fin 432}, 96 ≤ q.val → zeroDepth q = d + 1 →
      ∀ (walked : List (Fin 2)) {pad : ℕ}, d + 1 ≤ pad →
      walkTape q walked (List.replicate pad 0) =
        .regLeaf (zeroLeaf q) (walked ++ List.replicate (d + 1) 0)
          (List.replicate (pad - (d + 1)) 0) ∧
      walkTape q walked (List.replicate (d + 1) 0) =
        .regLeaf (zeroLeaf q) (walked ++ List.replicate (d + 1) 0) [] ∧
      (walkInternal q (List.replicate d 0)).isSome = true := by
  intro d
  induction d with
  | zero =>
    intro q hq hd walked pad hpad
    have hz := zeroStepBool_all q
    simp only [zeroStepBool, hq, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_assoc] at hz
    rcases hz with ⟨_, _, _, h49, h70, hstep⟩
    rcases htr : refTrans q 0 with _ | ⟨w, dir, q'⟩
    · rw [htr] at hstep; cases hstep
    · cases dir with
      | left => rw [htr] at hstep; cases hstep
      | right =>
        rw [htr] at hstep
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hstep
        rcases hstep with ⟨rfl, ⟨_, rfl⟩ | ⟨hq', hd', _, _⟩⟩
        · have hleaf : (49 ≤ (zeroLeaf q).val && (zeroLeaf q).val ≤ 70) = true := by
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨h49, h70⟩
          have hpad_eq : pad = (pad - 1) + 1 := by omega
          refine ⟨?_, ?_, ?_⟩
          · conv_lhs => rw [hpad_eq, List.replicate_succ]
            simp [walkTape, htr, hleaf]
          · simp [walkTape, htr, hleaf]
          · simp [walkInternal, hq]
        · have hz' := zeroStepBool_all q'
          simp only [zeroStepBool, hq', ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
            Bool.and_assoc] at hz'
          omega
  | succ d ih =>
    intro q hq hd walked pad hpad
    have hz := zeroStepBool_all q
    simp only [zeroStepBool, hq, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_assoc] at hz
    rcases hz with ⟨_, _, _, _, _, hstep⟩
    rcases htr : refTrans q 0 with _ | ⟨w, dir, q'⟩
    · rw [htr] at hstep; cases hstep
    · cases dir with
      | left => rw [htr] at hstep; cases hstep
      | right =>
        rw [htr] at hstep
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hstep
        rcases hstep with ⟨rfl, ⟨hd1, _⟩ | ⟨hq', hd', _, hleaf_eq⟩⟩
        · omega
        · have hd_q' : zeroDepth q' = d + 1 := by omega
          have hleaf : (49 ≤ q'.val && q'.val ≤ 70) = false := by
            rw [Bool.and_eq_false_iff]; right; rw [decide_eq_false_iff_not]; omega
          have hpad_eq : pad = (pad - 1) + 1 := by omega
          have hpad' : d + 1 ≤ pad - 1 := by omega
          obtain ⟨hw1, hw2, hwi⟩ := ih hq' hd_q' (walked ++ [0]) hpad'
          refine ⟨?_, ?_, ?_⟩
          · conv_lhs => rw [hpad_eq, List.replicate_succ]
            simp only [walkTape, htr, beq_self_eq_true, ↓reduceIte, hleaf, Bool.false_eq_true]
            rw [hw1, hleaf_eq, List.append_assoc]
            have hsub : pad - 1 - (d + 1) = pad - (d + 1 + 1) := by omega
            rw [hsub]
            rfl
          · conv_lhs => rw [List.replicate_succ]
            simp only [walkTape, htr, beq_self_eq_true, ↓reduceIte, hleaf, Bool.false_eq_true]
            rw [hw2, hleaf_eq, List.append_assoc]
            rfl
          · simp [List.replicate_succ, walkInternal, hq, htr, hq', hwi]

/-- Structural invariant on call-stack bit-lists `bits`:
either `bits = []`, or `bits = pref ++ [1]` where `walkInternal 126 pref` succeeds in `96..431`. -/
def validStack (bits : List (Fin 2)) : Bool :=
  match bits.reverse with
  | [] => true
  | b :: revPref => (b == 1) && (walkInternal 126 revPref.reverse).isSome

theorem validStack_nil : validStack [] = true := rfl

theorem trimZeros_of_validStack {bits : List (Fin 2)} (h : validStack bits = true) :
    trimZeros bits = bits := by
  unfold validStack at h
  unfold trimZeros
  rcases hrev : bits.reverse with _ | ⟨b, revPref⟩
  · exact List.reverse_eq_nil_iff.mp hrev |>.symm
  · rw [hrev, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, _⟩
    rw [dropLeadingZeros_one, ← hrev, List.reverse_reverse]

theorem validStack_bounds {bits : List (Fin 2)} (h : validStack bits = true) :
    bits.length ≤ 148 ∧ bits.count 0 ≤ 11 := by
  unfold validStack at h
  rcases hrev : bits.reverse with _ | ⟨b, revPref⟩
  · have hnil := List.reverse_eq_nil_iff.mp hrev
    subst hnil; simp
  · rw [hrev, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
    rcases h with ⟨rfl, q_end, hwi⟩
    have hb := walkInternal_root_bounds hwi
    have hbits : bits = revPref.reverse ++ [1] := by
      simpa using congrArg List.reverse hrev
    rw [hbits, List.length_append, List.count_append]
    change revPref.reverse.length + 1 ≤ 148 ∧ revPref.reverse.count 0 + 0 ≤ 11
    omega

theorem validStack_applyBreak {bits : List (Fin 2)} {pos n : ℕ} (k : ℕ)
    (hn : pos ≤ n + 1) (h : (walkInternal 126 ((padTo bits pos).take n)).isSome = true) :
    validStack (applyBreak bits pos k) = true := by
  unfold validStack applyBreak
  rw [List.reverse_reverse]
  rcases popBreakRev_suffix k (padTo bits pos).reverse with hnil | ⟨rest, h1, hlt, htake⟩
  · simp [hnil]
  · rw [h1]
    simp only [beq_self_eq_true, Bool.true_and]
    rw [List.length_reverse, padTo_length] at hlt
    rw [List.reverse_reverse] at htake
    have hle : rest.length ≤ n := by omega
    have htake2 : rest.reverse = ((padTo bits pos).take n).take rest.length := by
      rw [← htake, List.take_take, Nat.min_eq_left hle]
    rw [htake2]
    exact walkInternal_take h rest.length

theorem validStack_applyContinue {bits : List (Fin 2)} {pos n : ℕ} (k : ℕ)
    (hn : pos ≤ n + 1) (h : (walkInternal 126 ((padTo bits pos).take n)).isSome = true) :
    validStack (applyContinue bits pos k) = true := by
  unfold validStack applyContinue
  rw [List.reverse_reverse]
  rcases popContinueRev_suffix k (padTo bits pos).reverse with hnil | ⟨rest, h1, hlt, htake⟩
  · simp [hnil]
  · rw [h1]
    simp only [beq_self_eq_true, Bool.true_and]
    rw [List.length_reverse, padTo_length] at hlt
    rw [List.reverse_reverse] at htake
    have hle : rest.length ≤ n := by omega
    have htake2 : rest.reverse = ((padTo bits pos).take n).take rest.length := by
      rw [← htake, List.take_take, Nat.min_eq_left hle]
    rw [htake2]
    exact walkInternal_take h rest.length

/-- Complete classification of the tree walk from `main().0` (`126`) on any `bits` satisfying
`validStack bits = true`. -/
inductive ValidStackClass (bits : List (Fin 2)) : Prop where
  | halt (pref : List (Fin 2))
      (hbits : bits = pref ++ [1])
      (hwalk : walkTape 126 [] bits = .halt 166 pref [1])
      (hpad : ∀ {pad : ℕ}, walkTape 126 [] (bits ++ List.replicate pad 0) =
        .halt 166 pref (1 :: List.replicate pad 0))
  | jumpBreak (k : ℕ) (pref : List (Fin 2))
      (hk2 : k ≤ 2)
      (hbits : bits = pref ++ [1])
      (hwalk : walkTape 126 [] bits = .jumpLeft ⟨89 + k, by omega⟩ pref [])
      (hcnt0 : pref.count 0 ≤ 12)
      (hk0 : k ≤ pref.count 0)
      (hvalid : validStack (applyBreak bits pref.length k) = true)
      (hpad : ∀ {pad : ℕ}, walkTape 126 [] (bits ++ List.replicate pad 0) =
        .jumpLeft ⟨89 + k, by omega⟩ pref (List.replicate pad 0))
  | jumpContinue (k : ℕ) (pref : List (Fin 2))
      (hk3 : k ≤ 3)
      (hbits : bits = pref ++ [1])
      (hwalk : walkTape 126 [] bits = .jumpLeft ⟨92 + k, by omega⟩ pref [])
      (hcnt0 : pref.count 0 ≤ 12)
      (hk1 : k + 1 ≤ pref.count 1)
      (hvalid : validStack (applyContinue bits pref.length k) = true)
      (hpad : ∀ {pad : ℕ}, walkTape 126 [] (bits ++ List.replicate pad 0) =
        .jumpLeft ⟨92 + k, by omega⟩ pref (List.replicate pad 0))
  | regLeaf (q' : Fin 432) (m : ℕ)
      (hm10 : m ≤ 10)
      (hm_pos : 1 ≤ bits.length + m)
      (hwalk : walkTape 126 [] (bits ++ List.replicate m 0) =
        .regLeaf q' (bits ++ List.replicate m 0) [])
      (h49 : 49 ≤ q'.val)
      (h70 : q'.val ≤ 70)
      (hcnt0 : (bits ++ List.replicate m 0).count 0 ≤ 12)
      (hvalid0 : validStack (applyBreak bits (bits.length + m) 0) = true)
      (hvalid1 : validStack (applyBreak bits (bits.length + m) 1) = true)
      (hdec0 : isLeafInc q' = false → 1 ≤ (bits ++ List.replicate m 0).count 0)
      (hpad : ∀ {pad : ℕ}, 12 ≤ pad → walkTape 126 [] (bits ++ List.replicate pad 0) =
        .regLeaf q' (bits ++ List.replicate m 0) (List.replicate (pad - m) 0))

theorem walkTape_of_validStack {bits : List (Fin 2)} (hv : validStack bits = true) :
    ValidStackClass bits := by
  unfold validStack at hv
  rcases hrev : bits.reverse with _ | ⟨b, revPref⟩
  · have hnil : bits = [] := List.reverse_eq_nil_iff.mp hrev
    subst hnil
    have hq126 : 96 ≤ (126 : Fin 432).val := by decide
    have hz := zeroStepBool_all 126
    simp only [zeroStepBool, hq126, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_assoc] at hz
    rcases hz with ⟨hd1, hd10, hd_max0, h49, h70, _⟩
    set d := zeroDepth 126 - 1
    have hd : zeroDepth 126 = d + 1 := by omega
    obtain ⟨_, hw2, hwi⟩ := walkTape_replicate_zero d hq126 hd [] (le_refl (d + 1))
    have htake : (padTo ([] : List (Fin 2)) (([] : List (Fin 2)).length + (d + 1))).take d =
        List.replicate d 0 := by
      simp [padTo, List.take_replicate]
    have hwi_pad : (walkInternal 126
        ((padTo ([] : List (Fin 2)) (([] : List (Fin 2)).length + (d + 1))).take d)).isSome =
          true := by
      rw [htake]; exact hwi
    have hcnt : (([] : List (Fin 2)) ++ List.replicate (d + 1) 0).count 0 = d + 1 := by
      rw [List.nil_append, List.count_replicate]; simp
    refine ValidStackClass.regLeaf (zeroLeaf 126) (d + 1) (by omega) (by simp) hw2 h49 h70
      (by omega) (validStack_applyBreak 0 (by simp) hwi_pad)
      (validStack_applyBreak 1 (by simp) hwi_pad) (fun _ => by omega) ?_
    intro pad hpad
    exact (walkTape_replicate_zero d hq126 hd [] (by omega : d + 1 ≤ pad)).1
  · rw [hrev, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hv
    rcases hv with ⟨rfl, q, hwi⟩
    set pref := revPref.reverse
    have hbits : bits = pref ++ [1] := by
      simpa [pref] using congrArg List.reverse hrev
    have hq : 96 ≤ q.val := (walkInternal_ge_96 hwi).2
    have hb := walkInternal_root_bounds hwi
    have ho := oneStepBool_all q
    simp only [oneStepBool, hq, ↓reduceIte] at ho
    rcases htr : refTrans q 1 with _ | ⟨w, dir, q'⟩
    · rw [htr, beq_iff_eq] at ho
      subst ho
      refine ValidStackClass.halt pref hbits ?_ ?_
      · rw [hbits, walkTape_of_walkInternal hwi [] [1]]
        simp [walkTape, htr]
      · intro pad
        rw [hbits, List.append_assoc, List.singleton_append,
          walkTape_of_walkInternal hwi [] (1 :: List.replicate pad 0)]
        simp [walkTape, htr]
    · cases dir with
      | left =>
        rw [htr] at ho
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
        rcases ho with ⟨⟨⟨rfl, h89⟩, h95⟩, hmin⟩
        have hpad_pref : (padTo bits pref.length).take pref.length = pref := by
          rw [hbits, padTo_of_ge (by simp)]; simp
        have hwi_some : (walkInternal 126 ((padTo bits pref.length).take pref.length)).isSome =
            true := by
          rw [hpad_pref, hwi]; rfl
        by_cases h91 : q'.val ≤ 91
        · simp only [h91, ↓reduceIte, decide_eq_true_eq] at hmin
          set k := q'.val - 89
          have hk2 : k ≤ 2 := by omega
          have hq'_eq : q' = ⟨89 + k, by omega⟩ := by ext; dsimp [k]; omega
          refine ValidStackClass.jumpBreak k pref hk2 hbits ?_ (by omega) (by omega)
            (validStack_applyBreak k (by omega) hwi_some) ?_
          · rw [hbits, walkTape_of_walkInternal hwi [] [1]]
            simp [walkTape, htr, ← hq'_eq]
          · intro pad
            rw [hbits, List.append_assoc, List.singleton_append,
              walkTape_of_walkInternal hwi [] (1 :: List.replicate pad 0)]
            simp [walkTape, htr, ← hq'_eq]
        · simp only [h91, ↓reduceIte, decide_eq_true_eq] at hmin
          set k := q'.val - 92
          have hk3 : k ≤ 3 := by omega
          have hq'_eq : q' = ⟨92 + k, by omega⟩ := by ext; dsimp [k]; omega
          refine ValidStackClass.jumpContinue k pref hk3 hbits ?_ (by omega) (by omega)
            (validStack_applyContinue k (by omega) hwi_some) ?_
          · rw [hbits, walkTape_of_walkInternal hwi [] [1]]
            simp [walkTape, htr, ← hq'_eq]
          · intro pad
            rw [hbits, List.append_assoc, List.singleton_append,
              walkTape_of_walkInternal hwi [] (1 :: List.replicate pad 0)]
            simp [walkTape, htr, ← hq'_eq]
      | right =>
        rw [htr] at ho
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ho
        rcases ho with ⟨rfl, ⟨⟨h49, h70⟩, hinc_or⟩ | hq'96⟩
        · have hleaf : (49 ≤ q'.val && q'.val ≤ 70) = true := by
            rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨h49, h70⟩
          have hpad_bits : (padTo bits (bits.length + 0)).take pref.length = pref := by
            rw [Nat.add_zero, padTo_of_ge (le_refl _), List.take_length, hbits]; simp
          have hwi_some : (walkInternal 126 ((padTo bits (bits.length +
              0)).take pref.length)).isSome = true := by
            rw [hpad_bits, hwi]; rfl
          have hlen_le : bits.length + 0 ≤ pref.length + 1 := by
            rw [hbits, List.length_append]; simp
          have hcnt0_eq : (bits ++ List.replicate 0 (0 : Fin 2)).count 0 = pref.count 0 := by
            rw [List.replicate_zero, List.append_nil, hbits, List.count_append]
            change pref.count 0 + 0 = pref.count 0; omega
          refine ValidStackClass.regLeaf q' 0 (by omega) (by rw [hbits, List.length_append]; simp)
            ?_ h49 h70 (by omega)
            (validStack_applyBreak 0 hlen_le hwi_some)
            (validStack_applyBreak 1 hlen_le hwi_some) ?_ ?_
          · rw [List.replicate_zero, List.append_nil, hbits, walkTape_of_walkInternal hwi [] [1]]
            simp [walkTape, htr, hleaf]
          · intro hdec
            rcases hinc_or with hinc | hmin0
            · rw [hinc] at hdec; cases hdec
            · omega
          · intro pad _
            rw [List.replicate_zero, List.append_nil, Nat.sub_zero, hbits, List.append_assoc,
              List.singleton_append, walkTape_of_walkInternal hwi [] (1 :: List.replicate pad 0)]
            simp [walkTape, htr, hleaf]
        · have hwi_bits : walkInternal 126 bits = some q' := by
            rw [hbits, walkInternal_append, hwi, Option.bind_some]
            simp [walkInternal, hq, htr, hq'96]
          have hb_bits := walkInternal_root_bounds hwi_bits
          have hz := zeroStepBool_all q'
          simp only [zeroStepBool, hq'96, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
            Bool.and_assoc] at hz
          rcases hz with ⟨hd1, hd10, hd_max0, h49, h70, _⟩
          set d := zeroDepth q' - 1
          have hd : zeroDepth q' = d + 1 := by omega
          obtain ⟨_, hw2, hwi_d⟩ := walkTape_replicate_zero d hq'96 hd bits (le_refl (d + 1))
          have hwalk_d : walkTape 126 [] (bits ++ List.replicate (d + 1) 0) =
              .regLeaf (zeroLeaf q') (bits ++ List.replicate (d + 1) 0) [] := by
            rw [walkTape_of_walkInternal hwi_bits [] (List.replicate (d + 1) 0), List.nil_append,
              hw2]
          have htake_d : (padTo bits (bits.length + (d + 1))).take (bits.length + d) =
              bits ++ List.replicate d 0 := by
            rw [padTo_of_le (by omega), Nat.add_sub_cancel_left, List.take_append,
              List.take_of_length_le (by omega), List.take_replicate, Nat.add_sub_cancel_left,
              Nat.min_eq_left (by omega)]
          have hwi_bd : (walkInternal 126 ((padTo bits (bits.length + (d +
              1))).take (bits.length + d))).isSome = true := by
            rw [htake_d, walkInternal_append, hwi_bits, Option.bind_some]; exact hwi_d
          have hcnt0_eq : (bits ++ List.replicate (d + 1) (0 : Fin 2)).count 0 =
              bits.count 0 + (d + 1) := by
            rw [List.count_append, List.count_replicate]; simp
          refine ValidStackClass.regLeaf (zeroLeaf q') (d + 1) (by omega) (by omega)
            hwalk_d h49 h70 (by omega)
            (validStack_applyBreak 0 (by omega) hwi_bd)
            (validStack_applyBreak 1 (by omega) hwi_bd)
            (fun _ => by omega) ?_
          intro pad hpad
          rw [walkTape_of_walkInternal hwi_bits [] (List.replicate pad 0), List.nil_append]
          exact (walkTape_replicate_zero d hq'96 hd bits (by omega : d + 1 ≤ pad)).1

/-!
### 4C. Return, Break/Cleanup, and Pass-1 Prep Gadgets
-/

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

theorem zfDispatch_trans_zero (d : ℕ) (hd1 : 1 ≤ d) (hd15 : d ≤ 15) :
    refTrans (zfDispatchState d) 0 = some (0, .left, zfDispatchState (d - 1)) := by
  revert d hd1 hd15; decide

theorem zfDispatch_trans_one (d : ℕ) (hd1 : 1 ≤ d) (hd15 : d ≤ 15) :
    refTrans (zfDispatchState d) 1 = some (1, .left, zfDispatchState d) := by
  revert d hd1 hd15; decide

theorem step_zfDispatch (d : ℕ) (hd1 : 1 ≤ d) (hd15 : d ≤ 15) (a : Fin 2)
    (L R : ListBlank (Fin 2)) :
    step reference ⟨zfDispatchState d, Tape.mkL (L.cons a) R⟩ =
      some ⟨zfDispatchState (d - [a].count 0), Tape.mkL L (R.cons a)⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mkL_left (zfDispatch_trans_zero d hd1 hd15) L R
  · exact step_mkL_left (zfDispatch_trans_one d hd1 hd15) L R

theorem zfDispatch_scan_list (l : List (Fin 2)) (d : ℕ)
    (hcount : l.count 0 < d) (hd15 : d ≤ 15) (L R : ListBlank (Fin 2)) :
    nSteps reference l.length
      ⟨zfDispatchState d, Tape.mkL (ListBlank.append l.reverse L) R⟩ =
      some ⟨zfDispatchState (d - l.count 0), Tape.mkL L (ListBlank.append l R)⟩ := by
  induction l using List.reverseRecOn generalizing d R with
  | nil => simp
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

theorem zfDispatch_bounce_default (k : ℕ) (_hk1 : 1 ≤ k) (hk15 : k ≤ 15)
    (R : ListBlank (Fin 2)) :
    nSteps reference (2 * k + 1)
      ⟨zfDispatchState k, Tape.mkL default R⟩ =
      some ⟨86, Tape.mk' default R⟩ := by
  have hleft : ∀ m, m ≤ 15 → ∀ R',
      nSteps reference m ⟨zfDispatchState m, Tape.mkL default R'⟩ =
        some ⟨86, Tape.mkL default (ListBlank.append (List.replicate m 0) R')⟩ := by
    intro m hm R'
    induction m generalizing R' with
    | zero => rfl
    | succ m ihm =>
      have hm1 : 1 ≤ m + 1 := by omega
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      have h1 : step reference ⟨zfDispatchState (m + 1), Tape.mkL default R'⟩ =
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

theorem root_scan_to_main (a : Fin 2) (R : ListBlank (Fin 2)) :
    nSteps reference 3
      ⟨86, Tape.mk' default (ListBlank.append [1, 1, a] R)⟩ =
      some ⟨126, Tape.mk' rootLeft R⟩ := by
  simp only [ListBlank.append]
  have h1 : step reference ⟨86, Tape.mk' default (((R.cons a).cons 1).cons 1)⟩ =
      some ⟨87, Tape.mk' (ListBlank.cons 1 default) ((R.cons a).cons 1)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference ⟨87, Tape.mk' (ListBlank.cons 1 default) ((R.cons a).cons 1)⟩ =
      some ⟨88, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons a)⟩ :=
    step_mk'_right (by rfl) _ _
  have h3 : step reference ⟨88, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons a)⟩ =
      some ⟨126, Tape.mk' rootLeft R⟩ := by
    rcases fin2_cases a with rfl | rfl
    · exact step_mk'_right (by rfl) _ _
    · exact step_mk'_right (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

theorem dispatch_return_to_main (w : List (Fin 2)) (d : ℕ)
    (hcount : w.count 0 + 1 < d) (hd15 : d ≤ 15) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
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

theorem continue0_return (w : List (Fin 2)) (hcount : w.count 0 ≤ 13) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨92, Tape.mkL (stackLeft w) R⟩ =
      some ⟨126, Tape.mk' rootLeft (ListBlank.append w R)⟩ := by
  induction w using List.reverseRecOn generalizing R with
  | nil =>
    rw [stackLeft_nil]
    have h1 : step reference ⟨92, Tape.mkL rootLeft R⟩ =
        some ⟨92, Tape.mkL ((ListBlank.cons 1 default).cons 1) (R.cons 0)⟩ :=
      step_mkL_left (by rfl) _ _
    have h2 : step reference ⟨92, Tape.mkL ((ListBlank.cons 1 default).cons 1) (R.cons 0)⟩ =
        some ⟨77, Tape.mkL (ListBlank.cons 1 default) ((R.cons 0).cons 1)⟩ :=
      step_mkL_left (by rfl) _ _
    have h3 : step reference ⟨77, Tape.mkL (ListBlank.cons 1 default) ((R.cons 0).cons 1)⟩ =
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
      have hstep : step reference ⟨92, Tape.mkL ((stackLeft w).cons 0) R⟩ =
          some ⟨92, Tape.mkL (stackLeft w) (R.cons 0)⟩ :=
        step_mkL_left (by rfl) _ _
      obtain ⟨s, hs1, hrest⟩ := ih hw (R.cons 0)
      rw [append_cons_snoc] at hrest
      exact ⟨s + 1, by omega, step_nSteps hstep hrest⟩
    · have hw : w.count 0 + 1 < 15 := by
        rw [List.count_append] at hcount
        change w.count 0 + 0 ≤ 13 at hcount
        omega
      have hstep : step reference ⟨92, Tape.mkL ((stackLeft w).cons 1) R⟩ =
          some ⟨zfDispatchState 15, Tape.mkL (stackLeft w) (R.cons 1)⟩ :=
        step_mkL_left (by rfl) _ _
      obtain ⟨s, hs1, hrest⟩ := dispatch_return_to_main w 15 hw (by decide) (R.cons 1)
      rw [append_cons_snoc] at hrest
      exact ⟨s + 1, by omega, step_nSteps hstep hrest⟩

theorem continue_trans_zero (k : ℕ) (hk3 : k ≤ 3) :
    refTrans ⟨92 + k, by omega⟩ 0 = some (0, .left, ⟨92 + k, by omega⟩) := by
  revert k hk3; decide

theorem continue_trans_one (k : ℕ) (hk2 : k ≤ 2) :
    refTrans ⟨92 + (k + 1), by omega⟩ 1 = some (0, .left, ⟨92 + k, by omega⟩) := by
  revert k hk2; decide

theorem continue_scan_to_92 (k : ℕ) (hk3 : k ≤ 3) (rev : List (Fin 2))
    (h1 : k + 1 ≤ rev.count 1) (L R : ListBlank (Fin 2)) :
    let w' := (popContinueRev k rev).reverse
    ∃ s, nSteps reference s
      ⟨⟨92 + k, by omega⟩, Tape.mkL (ListBlank.append rev L) R⟩ =
      some ⟨92, Tape.mkL (ListBlank.append w'.reverse L)
        (ListBlank.append (List.replicate (rev.length - w'.length) 0) R)⟩ := by
  induction rev generalizing k R with
  | nil =>
    simp at h1
  | cons b xs ih =>
    intro w'
    rcases fin2_cases b with rfl | rfl
    · have hstep : step reference
          ⟨⟨92 + k, by omega⟩, Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
          some ⟨⟨92 + k, by omega⟩, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
        step_mkL_left (continue_trans_zero k hk3) _ _
      have h1' : k + 1 ≤ xs.count 1 := by simpa using h1
      obtain ⟨s, hs⟩ := ih k hk3 h1' (R.cons 0)
      have hw'_eq : (popContinueRev k xs).reverse = w' := by
        simp [w', popContinueRev_zero]
      have hlen_le : w'.length ≤ xs.length := by
        rw [← hw'_eq, List.length_reverse]
        exact popContinueRev_length_le k xs
      have hsub : (0 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
        simp; omega
      rw [hw'_eq, append_replicate_cons, ← hsub] at hs
      exact ⟨s + 1, step_nSteps hstep hs⟩
    · cases k with
      | zero =>
        have hw'_rev : w'.reverse = 1 :: xs := by
          simp [w']
        have hsub : (1 :: xs).length - w'.length = 0 := by
          have : w'.length = (1 :: xs).length := by
            rw [← List.length_reverse, hw'_rev]
          omega
        refine ⟨0, ?_⟩
        rw [hw'_rev, hsub, List.replicate_zero, ListBlank.append]
        rfl
      | succ k' =>
        have hk'2 : k' ≤ 2 := by omega
        have hk'3 : k' ≤ 3 := by omega
        have hstep : step reference
            ⟨⟨92 + (k' + 1), by omega⟩, Tape.mkL ((ListBlank.append xs L).cons 1) R⟩ =
            some ⟨⟨92 + k', by omega⟩, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
          step_mkL_left (continue_trans_one k' hk'2) _ _
        have h1' : k' + 1 ≤ xs.count 1 := by
          rw [List.count_cons_self] at h1; omega
        obtain ⟨s, hs⟩ := ih k' hk'3 h1' (R.cons 0)
        have hw'_eq : (popContinueRev k' xs).reverse = w' := by
          simp [w', popContinueRev_succ_one]
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]
          exact popContinueRev_length_le k' xs
        have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
          simp; omega
        rw [hw'_eq, append_replicate_cons, ← hsub] at hs
        exact ⟨s + 1, step_nSteps hstep hs⟩

theorem continue_return_eval (k : ℕ) (hk3 : k ≤ 3) (walked : List (Fin 2))
    (h1 : k + 1 ≤ walked.count 1) (h0 : walked.count 0 ≤ 12) (R : ListBlank (Fin 2)) :
    let w' := (popContinueRev k walked.reverse).reverse
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨⟨92 + k, by omega⟩, Tape.mkL (stackLeft walked) R⟩ =
      some ⟨126, Tape.mk' rootLeft
        (ListBlank.append w'
          (ListBlank.append (List.replicate (walked.length - w'.length) 0) R))⟩ := by
  intro w'
  have h1_rev : k + 1 ≤ walked.reverse.count 1 := by
    rw [List.count_reverse]; exact h1
  obtain ⟨s₁, hs₁⟩ := continue_scan_to_92 k hk3 walked.reverse h1_rev rootLeft R
  rw [List.length_reverse] at hs₁
  have hw'_cnt : w'.count 0 ≤ 13 := by
    have hle : w'.count 0 ≤ walked.count 0 := by
      simpa [w'] using popContinueRev_count_zero_le k walked.reverse
    omega
  obtain ⟨s₂, hs₂_pos, hs₂⟩ := continue0_return w' hw'_cnt
    (ListBlank.append (List.replicate (walked.length - w'.length) 0) R)
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem cleanup_47_to_92 (L : ListBlank (Fin 2)) (z m : ℕ) (R : ListBlank (Fin 2)) :
    nSteps reference (2 * z + 2 * m + 3)
      ⟨47, Tape.mk' L (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨92, Tape.mkL L
        (ListBlank.append (List.replicate (z + m) 0) (ListBlank.append [1, 0] R))⟩ := by
  have hscan_z := nSteps_mk'_right_scan (q := 47) (a := 0) (b := 0) (by rfl) z
    L (ListBlank.append (encodeReg m) R)
  conv at hscan_z => rhs; rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨47, Tape.mk' (ListBlank.append (List.replicate z 0) L)
        ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ =
      some ⟨48, Tape.mk' ((ListBlank.append (List.replicate z 0) L).cons 0)
        (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan_m := nSteps_mk'_right_scan (q := 48) (a := 1) (b := 0) (by rfl) m
    ((ListBlank.append (List.replicate z 0) L).cons 0) (R.cons 0)
  have hzeros : ListBlank.append (List.replicate m 0)
      ((ListBlank.append (List.replicate z 0) L).cons 0) =
      (ListBlank.append (List.replicate (z + m) 0) L).cons 0 := by
    rw [append_replicate_cons, ← ListBlank.append_assoc, ← List.replicate_add]
    have hadd : m + 1 + z = (z + m) + 1 := by omega
    rw [hadd, List.replicate_succ, ListBlank.append]
  rw [hzeros] at hscan_m
  have h2 : step reference
      ⟨48, Tape.mk' ((ListBlank.append (List.replicate (z + m) 0) L).cons 0) (R.cons 0)⟩ =
      some ⟨5, Tape.mkL ((ListBlank.append (List.replicate (z + m) 0) L).cons 0) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ R
  have h3 : step reference
      ⟨5, Tape.mkL ((ListBlank.append (List.replicate (z + m) 0) L).cons 0) (R.cons 0)⟩ =
      some ⟨92, Tape.mkL (ListBlank.append (List.replicate (z + m) 0) L)
        (ListBlank.append [1, 0] R)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan_back := nSteps_mkL_left_scan (q := 92) (a := 0) (b := 0) (by rfl) (z + m)
    L (ListBlank.append [1, 0] R)
  have hcomb := nSteps_bind_eq hscan_z (step_nSteps h1 (nSteps_bind_eq hscan_m
    (step_nSteps h2 (step_nSteps h3 hscan_back))))
  have hlen : z + (m + ((z + m) + 1 + 1) + 1) = 2 * z + 2 * m + 3 := by omega
  rw [hlen] at hcomb
  exact hcomb

theorem break_trans_one (k : ℕ) (hk2 : k ≤ 2) :
    refTrans ⟨89 + k, by omega⟩ 1 = some (0, .left, ⟨89 + k, by omega⟩) := by
  revert k hk2; decide

theorem break_trans_zero_succ (k : ℕ) (hk1 : k ≤ 1) :
    refTrans ⟨89 + (k + 1), by omega⟩ 0 = some (0, .left, ⟨89 + k, by omega⟩) := by
  revert k hk1; decide

theorem break_scan_to_47 (k : ℕ) (hk2 : k ≤ 2) (rev : List (Fin 2))
    (h0 : k + 1 ≤ rev.count 0) (L R : ListBlank (Fin 2)) :
    let w' := (popBreakRev k rev).reverse
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨⟨89 + k, by omega⟩, Tape.mkL (ListBlank.append rev L) R⟩ =
      some ⟨47, Tape.mk' (ListBlank.append w'.reverse L)
        (ListBlank.append (List.replicate (rev.length - w'.length) 0) R)⟩ := by
  induction rev generalizing k R with
  | nil =>
    simp at h0
  | cons b xs ih =>
    intro w'
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero =>
        have hstep : step reference
            ⟨⟨89 + 0, by omega⟩, Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
            some ⟨47, Tape.mk' ((ListBlank.append xs L).cons 1) R⟩ :=
          step_mkL_right (by rfl) _ _
        have hw'_rev : w'.reverse = 1 :: xs := by
          simp [w']
        have hsub : (0 :: xs).length - w'.length = 0 := by
          have : w'.length = (0 :: xs).length := by
            rw [← List.length_reverse, hw'_rev, List.length_cons, List.length_cons]
          omega
        refine ⟨1, by omega, ?_⟩
        rw [hw'_rev, hsub, List.replicate_zero, ListBlank.append, ListBlank.append]
        exact step_one hstep
      | succ k' =>
        have hk'1 : k' ≤ 1 := by omega
        have hk'2 : k' ≤ 2 := by omega
        have hstep : step reference
            ⟨⟨89 + (k' + 1), by omega⟩, Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
            some ⟨⟨89 + k', by omega⟩, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
          step_mkL_left (break_trans_zero_succ k' hk'1) _ _
        have h0' : k' + 1 ≤ xs.count 0 := by
          rw [List.count_cons_self] at h0; omega
        obtain ⟨s, hs1, hs⟩ := ih k' hk'2 h0' (R.cons 0)
        have hw'_eq : (popBreakRev k' xs).reverse = w' := by
          simp [w', popBreakRev_succ_zero]
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]
          exact popBreakRev_length_le k' xs
        have hsub : (0 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
          simp; omega
        rw [hw'_eq, append_replicate_cons, ← hsub] at hs
        exact ⟨s + 1, by omega, step_nSteps hstep hs⟩
    · have hstep : step reference
          ⟨⟨89 + k, by omega⟩, Tape.mkL ((ListBlank.append xs L).cons 1) R⟩ =
          some ⟨⟨89 + k, by omega⟩, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
        step_mkL_left (break_trans_one k hk2) _ _
      have h0' : k + 1 ≤ xs.count 0 := by simpa using h0
      obtain ⟨s, hs1, hs⟩ := ih k hk2 h0' (R.cons 0)
      have hw'_eq : (popBreakRev k xs).reverse = w' := by
        simp [w', popBreakRev_one]
      have hlen_le : w'.length ≤ xs.length := by
        rw [← hw'_eq, List.length_reverse]
        exact popBreakRev_length_le k xs
      have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
        simp; omega
      rw [hw'_eq, append_replicate_cons, ← hsub] at hs
      exact ⟨s + 1, by omega, step_nSteps hstep hs⟩

theorem popBreakRev_of_count_eq (k : ℕ) (rev : List (Fin 2)) (h : rev.count 0 = k) :
    popBreakRev k rev = [] ∧ popBreakRev k (rev ++ [0]) = [1] := by
  induction rev generalizing k with
  | nil =>
    simp only [List.count_nil] at h
    subst h
    exact ⟨rfl, rfl⟩
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · rw [List.count_cons_self] at h
      subst h
      simpa using ih (xs.count 0) rfl
    · have h' : xs.count 0 = k := by simpa using h
      simpa using ih k h'

theorem continue0_return_root111 (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨92, Tape.mkL (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1) R⟩ =
      some ⟨126, Tape.mk' rootLeft R⟩ := by
  have h1 : step reference ⟨92,
      Tape.mkL (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1) R⟩ =
      some ⟨77, Tape.mkL ((default : ListBlank (Fin 2)).cons 1 |>.cons 1) (R.cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference ⟨77,
      Tape.mkL ((default : ListBlank (Fin 2)).cons 1 |>.cons 1) (R.cons 1)⟩ =
      some ⟨77, Tape.mkL (ListBlank.cons 1 default) ((R.cons 1).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have h3 : step reference ⟨77, Tape.mkL (ListBlank.cons 1 default) ((R.cons 1).cons 1)⟩ =
      some ⟨77, Tape.mkL default (((R.cons 1).cons 1).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hbounce := zfDispatch_bounce_default 15 (by decide) (by decide)
    (((R.cons 1).cons 1).cons 1)
  have hroot := root_scan_to_main 1 R
  have htotal := step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hbounce hroot)))
  exact ⟨_, by omega, htotal⟩

theorem append_replicate_zeros_eq (d z : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate d (0 : Fin 2)) (ListBlank.append (List.replicate z 0) R) =
      ListBlank.append (List.replicate (d + z) 0) R := by
  rw [← ListBlank.append_assoc, ← List.replicate_add]

theorem break_cleanup_eval (k : ℕ) (hk2 : k ≤ 2) (walked : List (Fin 2))
    (hk0 : k ≤ walked.count 0) (h0 : walked.count 0 ≤ 12)
    (z m : ℕ) (R : ListBlank (Fin 2)) :
    let w' := (popBreakRev k walked.reverse).reverse
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨⟨89 + k, by omega⟩, Tape.mkL (stackLeft walked)
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨126, Tape.mk' rootLeft
        (ListBlank.append w'
          (ListBlank.append (List.replicate (walked.length - w'.length + z + m) 0)
            (ListBlank.append [1, 0] R)))⟩ := by
  intro w'
  by_cases hlt : k + 1 ≤ walked.count 0
  · have hlt_rev : k + 1 ≤ walked.reverse.count 0 := by
      rw [List.count_reverse]; exact hlt
    obtain ⟨s₁, hs₁_pos, hs₁⟩ := break_scan_to_47 k hk2 walked.reverse hlt_rev rootLeft
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))
    rw [List.length_reverse, append_replicate_zeros_eq] at hs₁
    have hcl := cleanup_47_to_92 (stackLeft w') (walked.length - w'.length + z) m R
    have hw'_cnt : w'.count 0 ≤ 13 := by
      have hle : w'.count 0 ≤ walked.count 0 := by
        simpa [w'] using popBreakRev_count_zero_le k walked.reverse
      omega
    obtain ⟨s₂, hs₂_pos, hret⟩ := continue0_return w' hw'_cnt
      (ListBlank.append (List.replicate (walked.length - w'.length + z + m) 0)
        (ListBlank.append [1, 0] R))
    exact ⟨_, by omega, nSteps_bind_eq hs₁ (nSteps_bind_eq hcl hret)⟩
  · have heq : walked.reverse.count 0 = k := by
      rw [List.count_reverse]; omega
    obtain ⟨hw'_nil, hpop_0⟩ := popBreakRev_of_count_eq k walked.reverse heq
    have hw' : w' = [] := by
      simp [w', hw'_nil]
    have hstack_eq : stackLeft walked =
        ListBlank.append (walked.reverse ++ [0])
          ((default : ListBlank (Fin 2)).cons 1 |>.cons 1) := by
      unfold stackLeft rootLeft
      rw [ListBlank.append_assoc]
      rfl
    have hcnt_0 : k + 1 ≤ (walked.reverse ++ [0]).count 0 := by
      rw [List.count_append, heq]
      change k + 1 ≤ k + 1; omega
    obtain ⟨s₁, hs₁_pos, hs₁⟩ := break_scan_to_47 k hk2 (walked.reverse ++ [0]) hcnt_0
      ((default : ListBlank (Fin 2)).cons 1 |>.cons 1)
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))
    rw [← hstack_eq] at hs₁
    have hrev_1 : (popBreakRev k (walked.reverse ++ [0])).reverse.reverse = [1] := by
      rw [List.reverse_reverse, hpop_0]
    have hsub_len : (walked.reverse ++ [0]).length -
        (popBreakRev k (walked.reverse ++ [0])).reverse.length = walked.length := by
      rw [List.length_reverse, hpop_0, List.length_append, List.length_reverse]
      simp
    rw [hrev_1, hsub_len, append_replicate_zeros_eq] at hs₁
    change nSteps reference s₁ _ =
      some ⟨47, Tape.mk' (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1)
        (ListBlank.append (List.replicate (walked.length +
          z) 0) (ListBlank.append (encodeReg m) R))⟩ at hs₁
    have hcl := cleanup_47_to_92 (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1)
      (walked.length + z) m R
    obtain ⟨s₂, hs₂_pos, hret⟩ := continue0_return_root111
      (ListBlank.append (List.replicate (walked.length + z + m) 0) (ListBlank.append [1, 0] R))
    have hcomb := nSteps_bind_eq hs₁ (nSteps_bind_eq hcl hret)
    rw [hw']
    simpa using ⟨_, by omega, hcomb⟩

theorem prep_pass1_eval (stack : List (Fin 2)) (hstack : stack.count 0 ≤ 12)
    (p : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨8, Tape.mk' ((stackLeft stack).cons 1)
        (ListBlank.append (List.replicate (p + 1) 0) (ListBlank.append [1, 0] R))⟩ =
      some ⟨126, Tape.mk' rootLeft
        (ListBlank.append (stack ++ [1, 0] ++ encodeReg p) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨8, Tape.mk' ((stackLeft stack).cons 1)
        ((ListBlank.append (List.replicate p 0) (ListBlank.append [1, 0] R)).cons 0)⟩ =
      some ⟨9, Tape.mk' (((stackLeft stack).cons 1).cons 0)
        (ListBlank.append (List.replicate p 0) (ListBlank.append [1, 0] R))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 9) (a := 0) (b := 1) (by rfl) p
    (((stackLeft stack).cons 1).cons 0) (ListBlank.append [1, 0] R)
  have h2 : step reference
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

/-!
## 5. Abstract Call-Stack + Register Machine & Simulation Theorems
-/

/-- Abstract configuration of the `zf_432_wade.tm` call-stack + register machine. -/
structure ZfRegCfg where
  stack : List (Fin 2)
  regs : List ℕ
  deriving DecidableEq, Repr

/-- Canonical initial configuration with empty stack and 11 zeroed registers (`0..10`). -/
def zfRegInit : ZfRegCfg := ⟨[], List.replicate 11 0⟩

/-- Single step of the abstract call-stack + register machine. -/
def zfRegStep (c : ZfRegCfg) : Option ZfRegCfg :=
  match evalStack c.stack with
  | .halt => none
  | .jump stack' => some ⟨stack', c.regs⟩
  | .inc r stack_succ =>
    some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 + 1)⟩
  | .decnz r stack_succ stack_fail =>
    if c.regs.getD r 0 == 0 then
      some ⟨stack_fail, c.regs⟩
    else
      some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 - 1) ++ [0]⟩

/-- `n`-step execution of the abstract call-stack + register machine. -/
def zfRegNSteps : ℕ → ZfRegCfg → Option ZfRegCfg
  | 0, c => some c
  | n + 1, c => (zfRegStep c).bind (zfRegNSteps n)

@[simp]
theorem zfRegNSteps_zero (c : ZfRegCfg) : zfRegNSteps 0 c = some c := rfl

@[simp]
theorem zfRegNSteps_succ (n : ℕ) (c : ZfRegCfg) :
    zfRegNSteps (n + 1) c = (zfRegStep c).bind (zfRegNSteps n) := rfl

/-- The abstract call-stack + register machine halts starting from `zfRegInit`. -/
def ZfRegHalts : Prop :=
  (eval zfRegStep zfRegInit).Dom

theorem mem_eval_zfRegStep_iff_zfRegNSteps {c₀ ch : ZfRegCfg} :
    ch ∈ eval zfRegStep c₀ ↔ ∃ n, zfRegNSteps n c₀ = some ch ∧ zfRegStep ch = none := by
  constructor
  · intro h
    refine StateTransition.evalInduction h fun a ha ih => ?_
    rcases hs : zfRegStep a with _ | a'
    · have hmem : a ∈ eval zfRegStep a :=
        StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hs⟩
      have heq : ch = a := Part.mem_unique ha hmem
      subst heq
      exact ⟨0, rfl, hs⟩
    · obtain ⟨n, hn, hnone⟩ := ih a' hs
      exact ⟨n + 1, by simp [zfRegNSteps, hs, hn], hnone⟩
  · rintro ⟨n, hn, hnone⟩
    have hreach : Reaches zfRegStep c₀ ch := by
      induction n generalizing c₀ with
      | zero =>
        injection hn with h'
        subst h'
        exact Relation.ReflTransGen.refl
      | succ n ih =>
        unfold zfRegNSteps at hn
        rcases hs : zfRegStep c₀ with _ | c'
        · rw [hs] at hn; cases hn
        · rw [hs, Option.bind_some] at hn
          exact Relation.ReflTransGen.head hs (ih hn)
    exact StateTransition.mem_eval.mpr ⟨hreach, hnone⟩

theorem zfRegHalts_iff_exists_zfRegNSteps :
    ZfRegHalts ↔ ∃ n c, zfRegNSteps n zfRegInit = some c ∧ zfRegStep c = none := by
  unfold ZfRegHalts
  rw [Part.dom_iff_mem]
  simp only [mem_eval_zfRegStep_iff_zfRegNSteps]
  exact ⟨fun ⟨c, n, h⟩ => ⟨n, c, h⟩, fun ⟨n, c, h⟩ => ⟨c, n, h⟩⟩

/-- Structural invariant of reachable `ZfRegCfg` states:
`validStack c.stack = true` and `11 ≤ c.regs.length`. -/
def ZfRegInv (c : ZfRegCfg) : Prop :=
  validStack c.stack = true ∧ 11 ≤ c.regs.length

theorem zfRegInv_init : ZfRegInv zfRegInit :=
  ⟨validStack_nil, by decide⟩

theorem evalStack_of_halt {bits pref : List (Fin 2)}
    (hpad : walkTape 126 [] (bits ++ List.replicate 12 0) =
      .halt 166 pref (1 :: List.replicate 12 0)) :
    evalStack bits = .halt := by
  unfold evalStack
  rw [hpad]
  rfl

theorem evalStack_of_jumpBreak {bits pref : List (Fin 2)} {k : ℕ} (hk2 : k ≤ 2)
    (hpad : walkTape 126 [] (bits ++ List.replicate 12 0) =
      .jumpLeft ⟨89 + k, by omega⟩ pref (List.replicate 12 0)) :
    evalStack bits = .jump (applyBreak bits pref.length k) := by
  unfold evalStack
  rw [hpad]
  unfold outcomeToInstr
  have hle : (⟨89 + k, by omega⟩ : Fin 432).val ≤ 91 := by dsimp; omega
  have hsub : (⟨89 + k, by omega⟩ : Fin 432).val - 89 = k := by dsimp; omega
  simp [hle, hsub]

theorem evalStack_of_jumpContinue {bits pref : List (Fin 2)} {k : ℕ} (hk3 : k ≤ 3)
    (hpad : walkTape 126 [] (bits ++ List.replicate 12 0) =
      .jumpLeft ⟨92 + k, by omega⟩ pref (List.replicate 12 0)) :
    evalStack bits = .jump (applyContinue bits pref.length k) := by
  unfold evalStack
  rw [hpad]
  unfold outcomeToInstr
  have hle : ¬ (⟨92 + k, by omega⟩ : Fin 432).val ≤ 91 := by dsimp; omega
  have hsub : (⟨92 + k, by omega⟩ : Fin 432).val - 92 = k := by dsimp; omega
  simp [hle, hsub]

theorem evalStack_of_regLeaf {bits : List (Fin 2)} {q' : Fin 432} {m : ℕ}
    (hpad : walkTape 126 [] (bits ++ List.replicate 12 0) =
      .regLeaf q' (bits ++ List.replicate m 0) (List.replicate (12 - m) 0)) :
    evalStack bits =
      if isLeafInc q' then
        .inc (leafReg q') (applyBreak bits (bits.length + m) 0)
      else
        .decnz (leafReg q') (applyBreak bits (bits.length + m) 0)
          (applyBreak bits (bits.length + m) 1) := by
  unfold evalStack
  rw [hpad]
  unfold outcomeToInstr
  simp

theorem zfRegStep_preserves_inv {c c' : ZfRegCfg} (hInv : ZfRegInv c)
    (hs : zfRegStep c = some c') : ZfRegInv c' := by
  rcases hInv with ⟨hv, hlen⟩
  unfold zfRegStep at hs
  rcases walkTape_of_validStack hv with
    ⟨pref, _, _, hpad⟩ |
    ⟨k, pref, hk2, _, _, _, _, hvalid, hpad⟩ |
    ⟨k, pref, hk3, _, _, _, _, hvalid, hpad⟩ |
    ⟨q', m, _, _, _, _, _, _, hvalid0, hvalid1, _, hpad⟩
  · rw [evalStack_of_halt hpad] at hs
    cases hs
  · rw [evalStack_of_jumpBreak hk2 hpad] at hs
    injection hs with hs'
    subst hs'
    exact ⟨hvalid, hlen⟩
  · rw [evalStack_of_jumpContinue hk3 hpad] at hs
    injection hs with hs'
    subst hs'
    exact ⟨hvalid, hlen⟩
  · rw [evalStack_of_regLeaf (hpad (by omega))] at hs
    by_cases hinc : isLeafInc q' = true
    · simp only [hinc, ↓reduceIte] at hs
      injection hs with hs'
      subst hs'
      exact ⟨hvalid0, by simp [hlen]⟩
    · simp only [hinc, Bool.false_eq_true, ↓reduceIte] at hs
      split at hs
      · injection hs with hs'
        subst hs'
        exact ⟨hvalid1, hlen⟩
      · injection hs with hs'
        subst hs'
        refine ⟨hvalid0, ?_⟩
        simp; omega

theorem zfRootCfg_eq_treeWalkCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    zfRootCfg padTotal stack regs =
      treeWalkCfg 126 [] (stack ++ List.replicate (padTotal - stack.length) 0)
        rootLeft (regsTape (0 :: regs)) := by
  unfold zfRootCfg treeWalkCfg
  simp only [List.reverse_nil, ListBlank.append, regsTape, encodeRegs_cons, encodeReg,
    List.replicate_succ, List.replicate_zero, List.append_assoc,
    ListBlank.append_assoc]

theorem regLeaf_pass1_and_pass2_tree {q' : Fin 432} {bits : List (Fin 2)} {m padTotal : ℕ}
    (hm10 : m ≤ 10)
    (h49 : 49 ≤ q'.val) (h70 : q'.val ≤ 70)
    (hcnt0 : (bits ++ List.replicate m 0).count 0 ≤ 12)
    (hwalk : walkTape 126 [] (bits ++ List.replicate m 0) =
      .regLeaf q' (bits ++ List.replicate m 0) [])
    (hpad_walk : walkTape 126 [] (bits ++ List.replicate (padTotal - bits.length) 0) =
      .regLeaf q' (bits ++ List.replicate m 0) (List.replicate (padTotal - bits.length - m) 0))
    (hpad12 : 12 ≤ padTotal - bits.length)
    (regs : List ℕ) :
    let walked_l := bits ++ List.replicate m 0
    let p := padTotal - bits.length - m - 2
    ∃ s, 1 ≤ s ∧ nSteps reference s (zfRootCfg padTotal bits regs) =
      some ⟨q', Tape.mk' (stackLeft walked_l) ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ := by
  intro walked_l p
  have hw1 := walkTape_sound 126 [] (bits ++ List.replicate (padTotal - bits.length) 0)
    rootLeft (regsTape (0 :: regs))
  rw [hpad_walk, ← zfRootCfg_eq_treeWalkCfg] at hw1
  rcases hw1 with ⟨_, _, _, s₁, hs₁_pos, hw1⟩
  unfold treeWalkCfg at hw1
  change nSteps reference s₁ (zfRootCfg padTotal bits regs) =
    some ⟨q', Tape.mk' (stackLeft walked_l)
      (ListBlank.append (List.replicate (padTotal - bits.length -
        m) 0) (regsTape (0 :: regs)))⟩ at hw1
  have hsub_p : padTotal - bits.length - m = (p + 1) + 1 := by omega
  have hregs0 : regsTape (0 :: regs) = ListBlank.append [1, 0] (regsTape regs) := by
    rw [regsTape_cons]; rfl
  rw [hsub_p, hregs0, List.replicate_succ, ListBlank.append] at hw1
  have hq'0 := (leaf_stage3_eq q' h49 h70).1
  have hstep_q' : step reference
      ⟨q', Tape.mk' (stackLeft walked_l)
        ((ListBlank.append (List.replicate (p + 1) 0) (ListBlank.append [1,
          0] (regsTape regs))).cons 0)⟩ =
      some ⟨8, Tape.mk' ((stackLeft walked_l).cons 1)
        (ListBlank.append (List.replicate (p + 1) 0) (ListBlank.append [1, 0] (regsTape regs)))⟩ :=
    step_mk'_right hq'0 _ _
  obtain ⟨s_prep, hs_prep_pos, hprep⟩ := prep_pass1_eval walked_l hcnt0 p (regsTape regs)
  have hprep_eq : ListBlank.append (walked_l ++ [1, 0] ++ encodeReg p) (regsTape regs) =
      ListBlank.append walked_l ((regsTape (p :: regs)).cons 0 |>.cons 1) := by
    rw [regsTape_cons]
    simp only [List.append_assoc, ListBlank.append_assoc, ListBlank.append]
  rw [hprep_eq] at hprep
  have hw2 := walkTape_sound 126 [] walked_l rootLeft ((regsTape (p :: regs)).cons 0 |>.cons 1)
  rw [hwalk] at hw2
  rcases hw2 with ⟨_, _, _, s₂, hs₂_pos, hw2⟩
  unfold treeWalkCfg at hw2
  simp only [List.reverse_nil, ListBlank.append] at hw2
  change nSteps reference s₂
    ⟨126, Tape.mk' rootLeft (ListBlank.append walked_l ((regsTape (p :: regs)).cons 0 |>.cons 1))⟩ =
    some ⟨q', Tape.mk' (stackLeft walked_l) ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ at hw2
  have hcomb := nSteps_bind_eq hw1 (step_nSteps hstep_q' (nSteps_bind_eq hprep hw2))
  exact ⟨_, by omega, hcomb⟩

theorem regLeaf_break_to_root (k : ℕ) (hk2 : k ≤ 2) {bits : List (Fin 2)} {m padTotal : ℕ}
    (hm10 : m ≤ 10) (hpad12 : 12 ≤ padTotal - bits.length)
    (hk0 : k ≤ (bits ++ List.replicate m 0).count 0)
    (hcnt0 : (bits ++ List.replicate m 0).count 0 ≤ 12)
    (regs' : List ℕ) :
    let walked_l := bits ++ List.replicate m 0
    let p := padTotal - bits.length - m - 2
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨⟨89 + k, by omega⟩, Tape.mkL (stackLeft walked_l)
        ((regsTape (p :: regs')).cons 0 |>.cons 0)⟩ =
      some (zfRootCfg padTotal (applyBreak bits (bits.length + m) k) regs') := by
  intro walked_l p
  have hR_eq : ((regsTape (p :: regs')).cons 0 |>.cons 0) =
      ListBlank.append (List.replicate 2 0) (ListBlank.append (encodeReg p) (regsTape regs')) := by
    rw [regsTape_cons]; rfl
  rw [hR_eq]
  obtain ⟨s, hs_pos, hcl⟩ := break_cleanup_eval k hk2 walked_l hk0 hcnt0 2 p (regsTape regs')
  have hw'_eq : (popBreakRev k walked_l.reverse).reverse =
      applyBreak bits (bits.length + m) k := by
    unfold applyBreak
    rw [padTo_of_le (by omega), Nat.add_sub_cancel_left]
  have hlen_le : (applyBreak bits (bits.length + m) k).length ≤ walked_l.length := by
    rw [← hw'_eq, List.length_reverse]
    exact le_trans (popBreakRev_length_le k walked_l.reverse) (by simp)
  have hlen_w : walked_l.length = bits.length + m := by simp [walked_l]
  have hpad_eq : walked_l.length - (applyBreak bits (bits.length + m) k).length + 2 + p =
      padTotal - (applyBreak bits (bits.length + m) k).length := by
    omega
  rw [hw'_eq, hpad_eq] at hcl
  have hroot_eq : ⟨126, Tape.mk' rootLeft
      (ListBlank.append (applyBreak bits (bits.length + m) k)
        (ListBlank.append (List.replicate (padTotal - (applyBreak bits (bits.length +
          m) k).length) 0)
          (ListBlank.append [1, 0] (regsTape regs'))))⟩ =
      zfRootCfg padTotal (applyBreak bits (bits.length + m) k) regs' := by
    unfold zfRootCfg regsTape
    simp only [List.append_assoc, ListBlank.append_assoc]
  rw [hroot_eq] at hcl
  exact ⟨s, hs_pos, hcl⟩

/-- Single-step simulation of `zfRegStep` by `reference`:
given the three Layer 1 Pass-2 register theorems (`hInc`, `hDecZero`, `hDecPos`),
for any `padTotal ≥ 160` and any `c : ZfRegCfg` satisfying `ZfRegInv c`:
- if `zfRegStep c = some c'`, then `reference` steps from `zfRootCfg padTotal c.stack c.regs`
  to `zfRootCfg padTotal c'.stack c'.regs` in `s ≥ 1` steps;
- if `zfRegStep c = none`, then `reference` reaches a halting configuration from
  `zfRootCfg padTotal c.stack c.regs`. -/
theorem tm_simulates_zfRegStep
    (hInc : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩)
    (hDecZero : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      regs[k] = 0 → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨90, Tape.mkL L_stack ((regsTape (p :: regs)).cons 0 |>.cons 0)⟩)
    (hDecPos : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      0 < regs[k] → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0)⟩)
    {padTotal : ℕ} (hpad : 160 ≤ padTotal)
    {c : ZfRegCfg} (hInv : ZfRegInv c) :
    match zfRegStep c with
    | some c' =>
      ∃ s, 1 ≤ s ∧ nSteps reference s (zfRootCfg padTotal c.stack c.regs) =
        some (zfRootCfg padTotal c'.stack c'.regs)
    | none =>
      ∃ s ch, nSteps reference s (zfRootCfg padTotal c.stack c.regs) = some ch ∧
        step reference ch = none := by
  rcases hInv with ⟨hv, hregs_len⟩
  have hbits_len : c.stack.length ≤ 148 := (validStack_bounds hv).1
  have hpad12 : 12 ≤ padTotal - c.stack.length := by omega
  unfold zfRegStep
  rcases walkTape_of_validStack hv with
    ⟨pref, hbits, _, hpad_walk⟩ |
    ⟨k, pref, hk2, hbits, _, hcnt0, hk0, _, hpad_walk⟩ |
    ⟨k, pref, hk3, hbits, _, hcnt0, hk1, _, hpad_walk⟩ |
    ⟨q', m, hm10, _, hwalk, h49, h70, hcnt0, _, _, hdec0, hpad_walk⟩
  · rw [evalStack_of_halt hpad_walk]
    have hw := walkTape_sound 126 [] (c.stack ++ List.replicate (padTotal - c.stack.length) 0)
      rootLeft (regsTape (0 :: c.regs))
    rw [hpad_walk, ← zfRootCfg_eq_treeWalkCfg] at hw
    rcases hw with ⟨_, s, ch, _, hsteps, hnone⟩
    exact ⟨s, ch, hsteps, hnone⟩
  · rw [evalStack_of_jumpBreak hk2 hpad_walk]
    dsimp only
    have hw := walkTape_sound 126 [] (c.stack ++ List.replicate (padTotal - c.stack.length) 0)
      rootLeft (regsTape (0 :: c.regs))
    rw [hpad_walk, ← zfRootCfg_eq_treeWalkCfg] at hw
    rcases hw with ⟨_, s₁, hs₁_pos, hw⟩
    have hR_eq : ListBlank.append (0 :: List.replicate (padTotal -
        c.stack.length) 0) (regsTape (0 :: c.regs)) =
        ListBlank.append (List.replicate (padTotal - c.stack.length + 1) 0)
          (ListBlank.append (encodeReg 0) (regsTape c.regs)) := by
      rw [← List.replicate_succ, regsTape_cons]
    change nSteps reference s₁ (zfRootCfg padTotal c.stack c.regs) =
      some ⟨⟨89 + k, by omega⟩, Tape.mkL (stackLeft pref)
        (ListBlank.append (0 :: List.replicate (padTotal -
          c.stack.length) 0) (regsTape (0 :: c.regs)))⟩ at hw
    rw [hR_eq] at hw
    obtain ⟨s₂, hs₂_pos, hcl⟩ := break_cleanup_eval k hk2 pref hk0 hcnt0
      (padTotal - c.stack.length + 1) 0 (regsTape c.regs)
    have hw'_eq : (popBreakRev k pref.reverse).reverse = applyBreak c.stack pref.length k := by
      unfold applyBreak
      rw [hbits, padTo_of_ge (by simp)]; simp
    have hlen_le : (applyBreak c.stack pref.length k).length ≤ pref.length := by
      rw [← hw'_eq, List.length_reverse]
      exact le_trans (popBreakRev_length_le k pref.reverse) (by simp)
    have hlen_bits : c.stack.length = pref.length + 1 := by rw [hbits, List.length_append]; simp
    have hpad_eq : pref.length - (applyBreak c.stack pref.length k).length +
        (padTotal - c.stack.length + 1) + 0 =
        padTotal - (applyBreak c.stack pref.length k).length := by omega
    rw [hw'_eq, hpad_eq] at hcl
    have hroot_eq : ⟨126, Tape.mk' rootLeft
        (ListBlank.append (applyBreak c.stack pref.length k)
          (ListBlank.append (List.replicate (padTotal -
            (applyBreak c.stack pref.length k).length) 0)
            (ListBlank.append [1, 0] (regsTape c.regs))))⟩ =
        zfRootCfg padTotal (applyBreak c.stack pref.length k) c.regs := by
      unfold zfRootCfg regsTape
      simp only [List.append_assoc, ListBlank.append_assoc]
    rw [hroot_eq] at hcl
    exact ⟨_, by omega, nSteps_bind_eq hw hcl⟩
  · rw [evalStack_of_jumpContinue hk3 hpad_walk]
    dsimp only
    have hw := walkTape_sound 126 [] (c.stack ++ List.replicate (padTotal - c.stack.length) 0)
      rootLeft (regsTape (0 :: c.regs))
    rw [hpad_walk, ← zfRootCfg_eq_treeWalkCfg] at hw
    rcases hw with ⟨_, s₁, hs₁_pos, hw⟩
    have hR_eq : ListBlank.append (0 :: List.replicate (padTotal -
        c.stack.length) 0) (regsTape (0 :: c.regs)) =
        ListBlank.append (List.replicate (padTotal - c.stack.length +
          1) 0) (regsTape (0 :: c.regs)) := by
      rw [← List.replicate_succ]
    change nSteps reference s₁ (zfRootCfg padTotal c.stack c.regs) =
      some ⟨⟨92 + k, by omega⟩, Tape.mkL (stackLeft pref)
        (ListBlank.append (0 :: List.replicate (padTotal -
          c.stack.length) 0) (regsTape (0 :: c.regs)))⟩ at hw
    rw [hR_eq] at hw
    obtain ⟨s₂, hs₂_pos, hret⟩ := continue_return_eval k hk3 pref hk1 hcnt0
      (ListBlank.append (List.replicate (padTotal - c.stack.length + 1) 0) (regsTape (0 :: c.regs)))
    have hw'_eq : (popContinueRev k pref.reverse).reverse =
        applyContinue c.stack pref.length k := by
      unfold applyContinue
      rw [hbits, padTo_of_ge (by simp)]; simp
    have hlen_le : (applyContinue c.stack pref.length k).length ≤ pref.length := by
      rw [← hw'_eq, List.length_reverse]
      exact le_trans (popContinueRev_length_le k pref.reverse) (by simp)
    have hlen_bits : c.stack.length = pref.length + 1 := by rw [hbits, List.length_append]; simp
    have hpad_eq : pref.length - (applyContinue c.stack pref.length k).length +
        (padTotal - c.stack.length + 1) =
        padTotal - (applyContinue c.stack pref.length k).length := by omega
    rw [hw'_eq, append_replicate_zeros_eq, hpad_eq] at hret
    have hregs0 : regsTape (0 :: c.regs) = ListBlank.append [1, 0] (regsTape c.regs) := by
      rw [regsTape_cons]; rfl
    have hroot_eq : ⟨126, Tape.mk' rootLeft
        (ListBlank.append (applyContinue c.stack pref.length k)
          (ListBlank.append (List.replicate (padTotal -
            (applyContinue c.stack pref.length k).length) 0)
            (regsTape (0 :: c.regs))))⟩ =
        zfRootCfg padTotal (applyContinue c.stack pref.length k) c.regs := by
      rw [hregs0]
      unfold zfRootCfg regsTape
      simp only [List.append_assoc, ListBlank.append_assoc]
    rw [hroot_eq] at hret
    exact ⟨_, by omega, nSteps_bind_eq hw hret⟩
  · rw [evalStack_of_regLeaf (hpad_walk (by omega))]
    set r := leafReg q'
    have hr11 : r < 11 := leafReg_lt_11 q'
    have hr : r < c.regs.length := by omega
    have hgetD : c.regs.getD r 0 = c.regs[r] := by
      simp [List.getD_eq_getElem?_getD, hr]
    obtain ⟨s₁, hs₁_pos, htree⟩ := regLeaf_pass1_and_pass2_tree hm10 h49 h70 hcnt0
      hwalk (hpad_walk hpad12) hpad12 c.regs
    have hleaf_eq := (leaf_stage3_eq q' h49 h70).2
    by_cases hinc : isLeafInc q' = true
    · simp only [hinc, ↓reduceIte] at hleaf_eq ⊢
      rw [hleaf_eq] at htree
      rw [hgetD]
      obtain ⟨s₂, hs₂_pos, hinc_step⟩ := hInc r hr11 (padTotal - c.stack.length - m - 2)
        c.regs hr (stackLeft (c.stack ++ List.replicate m 0))
      obtain ⟨s₃, hs₃_pos, hbrk⟩ := regLeaf_break_to_root 0 (by decide) hm10 hpad12
        (by omega) hcnt0 (c.regs.set r (c.regs[r] + 1))
      exact ⟨_, by omega, nSteps_bind_eq htree (nSteps_bind_eq hinc_step hbrk)⟩
    · have hinc_false : isLeafInc q' = false := Bool.eq_false_iff.mpr hinc
      simp only [hinc_false, Bool.false_eq_true, ↓reduceIte] at hleaf_eq ⊢
      rw [hleaf_eq] at htree
      rw [hgetD]
      by_cases hz : c.regs[r] = 0
      · have hbeq : (c.regs[r] == 0) = true := beq_iff_eq.mpr hz
        simp only [hbeq, ↓reduceIte]
        obtain ⟨s₂, hs₂_pos, hdec_step⟩ := hDecZero r hr11 (padTotal - c.stack.length - m - 2)
          c.regs hr hz (stackLeft (c.stack ++ List.replicate m 0))
        obtain ⟨s₃, hs₃_pos, hbrk⟩ := regLeaf_break_to_root 1 (by decide) hm10 hpad12
          (hdec0 hinc_false) hcnt0 c.regs
        exact ⟨_, by omega, nSteps_bind_eq htree (nSteps_bind_eq hdec_step hbrk)⟩
      · have hpos : 0 < c.regs[r] := by omega
        have hbeq : (c.regs[r] == 0) = false := beq_eq_false_iff_ne.mpr hz
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨s₂, hs₂_pos, hdec_step⟩ := hDecPos r hr11 (padTotal - c.stack.length - m - 2)
          c.regs hr hpos (stackLeft (c.stack ++ List.replicate m 0))
        obtain ⟨s₃, hs₃_pos, hbrk⟩ := regLeaf_break_to_root 0 (by decide) hm10 hpad12
          (by omega) hcnt0 (c.regs.set r (c.regs[r] - 1) ++ [0])
        exact ⟨_, by omega, nSteps_bind_eq htree (nSteps_bind_eq hdec_step hbrk)⟩

/-- Forward simulation: if the abstract machine halts from `c` (`ZfRegInv c`),
then `reference` halts from `zfRootCfg padTotal c.stack c.regs` (`160 ≤ padTotal`). -/
theorem tm_eval_dom_of_zfReg_eval_dom
    (hInc : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩)
    (hDecZero : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      regs[k] = 0 → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨90, Tape.mkL L_stack ((regsTape (p :: regs)).cons 0 |>.cons 0)⟩)
    (hDecPos : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      0 < regs[k] → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0)⟩)
    {padTotal : ℕ} (hpad : 160 ≤ padTotal)
    {c : ZfRegCfg} (hInv : ZfRegInv c) (hDom : (eval zfRegStep c).Dom) :
    (eval (step reference) (zfRootCfg padTotal c.stack c.regs)).Dom := by
  rw [Part.dom_iff_mem] at hDom
  rcases hDom with ⟨ch_reg, hmem⟩
  revert hInv
  refine StateTransition.evalInduction hmem fun a _ ih hInv => ?_
  have hsim := tm_simulates_zfRegStep hInc hDecZero hDecPos hpad hInv
  rcases hs : zfRegStep a with _ | a'
  · rw [hs] at hsim
    obtain ⟨s, ch, hs_steps, hnone⟩ := hsim
    rw [Part.dom_iff_mem]
    exact ⟨ch, mem_eval_iff_nSteps.mpr ⟨s, hs_steps, hnone⟩⟩
  · rw [hs] at hsim
    obtain ⟨s, _, hsteps⟩ := hsim
    have hInv' := zfRegStep_preserves_inv hInv hs
    exact (nSteps_eval_dom hsteps).mpr (ih a' hs hInv')

/-- Backward simulation: if `reference` halts in `N` steps from `zfRootCfg padTotal c.stack c.regs`
(`160 ≤ padTotal`, `ZfRegInv c`), then the abstract machine halts from `c`. -/
theorem zfReg_eval_dom_of_tm_nSteps_halt
    (hInc : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩)
    (hDecZero : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      regs[k] = 0 → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨90, Tape.mkL L_stack ((regsTape (p :: regs)).cons 0 |>.cons 0)⟩)
    (hDecPos : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      0 < regs[k] → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0)⟩)
    {padTotal : ℕ} (hpad : 160 ≤ padTotal) :
    ∀ N {c : ZfRegCfg} {ch : Cfg 432 2},
      ZfRegInv c →
      nSteps reference N (zfRootCfg padTotal c.stack c.regs) = some ch →
      step reference ch = none →
      (eval zfRegStep c).Dom := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro c ch hInv hN hnone
    have hsim := tm_simulates_zfRegStep hInc hDecZero hDecPos hpad hInv
    rcases hs : zfRegStep c with _ | c'
    · rw [Part.dom_iff_mem]
      exact ⟨c, StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hs⟩⟩
    · rw [hs] at hsim
      obtain ⟨s, hs_pos, hsteps⟩ := hsim
      have hle : s ≤ N := by
        by_contra hlt
        have hgt : 1 ≤ s - N := by omega
        have hsplit : s = N + (s - N) := by omega
        rw [hsplit, nSteps_add, hN, Option.bind_some, nSteps_of_halt hnone hgt] at hsteps
        cases hsteps
      have hsplit : N = s + (N - s) := by omega
      rw [hsplit, nSteps_add, hsteps, Option.bind_some] at hN
      have hInv' := zfRegStep_preserves_inv hInv hs
      have hDom' := ih (N - s) (by omega) hInv' hN hnone
      have hreach : Reaches zfRegStep c c' :=
        Relation.ReflTransGen.head hs Relation.ReflTransGen.refl
      rwa [StateTransition.reaches_eval hreach]

/-- Bisimulation relation on `ZfRegCfg` agreeing on `stack` and the first 11 registers. -/
def ZfRegSim (c₁ c₂ : ZfRegCfg) : Prop :=
  c₁.stack = c₂.stack ∧ 11 ≤ c₁.regs.length ∧ 11 ≤ c₂.regs.length ∧
    c₁.regs.take 11 = c₂.regs.take 11

theorem evalStack_reg_lt_11 (bits : List (Fin 2)) :
    match evalStack bits with
    | .inc r _ => r < 11
    | .decnz r _ _ => r < 11
    | _ => True := by
  unfold evalStack outcomeToInstr
  rcases walkTape 126 [] (bits ++ List.replicate 12 0) with _ | ⟨q', _, _⟩ | ⟨q', _, _⟩ | _
  · trivial
  · by_cases h : q'.val ≤ 91 <;> simp [h]
  · by_cases h : isLeafInc q' = true <;> simp [h, leafReg_lt_11 q']
  · trivial

theorem getD_eq_of_take_11 {r₁ r₂ : List ℕ} {k : ℕ} (hk : k < 11)
    (h : r₁.take 11 = r₂.take 11) :
    r₁.getD k 0 = r₂.getD k 0 := by
  have h1 : r₁.getD k 0 = (r₁.take 11).getD k 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  have h2 : r₂.getD k 0 = (r₂.take 11).getD k 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  rw [h1, h2, h]

theorem zfRegStep_sim {c₁ c₂ : ZfRegCfg} (hsim : ZfRegSim c₁ c₂) :
    match zfRegStep c₁, zfRegStep c₂ with
    | none, none => True
    | some c₁', some c₂' => ZfRegSim c₁' c₂'
    | _, _ => False := by
  rcases hsim with ⟨hstack, hlen₁, hlen₂, htake⟩
  have hr_lt := evalStack_reg_lt_11 c₁.stack
  unfold zfRegStep
  rw [← hstack]
  rcases hev : evalStack c₁.stack with _ | stack' | ⟨r, stack_succ⟩ | ⟨r, stack_succ, stack_fail⟩
  · trivial
  · exact ⟨rfl, hlen₁, hlen₂, htake⟩
  · rw [hev] at hr_lt
    have hget := getD_eq_of_take_11 hr_lt htake
    refine ⟨rfl, by simp [hlen₁], by simp [hlen₂], ?_⟩
    rw [List.take_set, List.take_set, hget, htake]
  · rw [hev] at hr_lt
    have hget := getD_eq_of_take_11 hr_lt htake
    dsimp only
    rw [hget]
    by_cases hz : (c₂.regs.getD r 0 == 0) = true
    · simp only [hz, ↓reduceIte]
      exact ⟨rfl, hlen₁, hlen₂, htake⟩
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      refine ⟨rfl, by simp; omega, by simp; omega, ?_⟩
      dsimp only
      have hle₁ : 11 ≤ (c₁.regs.set r (c₂.regs.getD r 0 - 1)).length := by simp [hlen₁]
      have hle₂ : 11 ≤ (c₂.regs.set r (c₂.regs.getD r 0 - 1)).length := by simp [hlen₂]
      rw [List.take_append_of_le_length hle₁, List.take_append_of_le_length hle₂,
        List.take_set, List.take_set, htake]

theorem eval_zfRegStep_dom_of_sim {c₁ c₂ : ZfRegCfg} (hsim : ZfRegSim c₁ c₂)
    (hDom : (eval zfRegStep c₁).Dom) : (eval zfRegStep c₂).Dom := by
  rw [Part.dom_iff_mem] at hDom ⊢
  rcases hDom with ⟨ch₁, hmem⟩
  obtain ⟨n, hn, hnone⟩ := mem_eval_zfRegStep_iff_zfRegNSteps.mp hmem
  have hstep_n : ∀ m {a₁ a₂ : ZfRegCfg}, ZfRegSim a₁ a₂ →
      zfRegNSteps m a₁ = some ch₁ →
      ∃ ch₂, zfRegNSteps m a₂ = some ch₂ ∧ ZfRegSim ch₁ ch₂ := by
    intro m
    induction m with
    | zero =>
      intro a₁ a₂ hsim_a hm
      injection hm with hm'
      subst hm'
      exact ⟨a₂, rfl, hsim_a⟩
    | succ m ih =>
      intro a₁ a₂ hsim_a hm
      unfold zfRegNSteps at hm ⊢
      have hstep := zfRegStep_sim hsim_a
      rcases hs₁ : zfRegStep a₁ with _ | a₁' <;> rcases hs₂ : zfRegStep a₂ with _ | a₂'
      · rw [hs₁] at hm; cases hm
      · rw [hs₁, hs₂] at hstep; cases hstep
      · rw [hs₁, hs₂] at hstep; cases hstep
      · rw [hs₁, hs₂] at hstep
        rw [hs₁, Option.bind_some] at hm
        exact ih hstep hm
  obtain ⟨ch₂, hn₂, hsim_ch⟩ := hstep_n n hsim hn
  have hstep_ch := zfRegStep_sim hsim_ch
  rw [hnone] at hstep_ch
  rcases hs₂ : zfRegStep ch₂ with _ | ch₂'
  · exact ⟨ch₂, mem_eval_zfRegStep_iff_zfRegNSteps.mpr ⟨n, hn₂, hs₂⟩⟩
  · rw [hs₂] at hstep_ch; cases hstep_ch

theorem eval_zfRegStep_dom_iff_sim {c₁ c₂ : ZfRegCfg} (hsim : ZfRegSim c₁ c₂) :
    (eval zfRegStep c₁).Dom ↔ (eval zfRegStep c₂).Dom := by
  have hsymm : ZfRegSim c₂ c₁ := ⟨hsim.1.symm, hsim.2.2.1, hsim.2.1, hsim.2.2.2.symm⟩
  exact ⟨eval_zfRegStep_dom_of_sim hsim, eval_zfRegStep_dom_of_sim hsymm⟩

/-- Halting equivalence between `zfRootCfg padTotal [] initRegs` and `ZfRegHalts`
for any `padTotal ≥ 160` and any `initRegs` starting with 11 zeros. -/
theorem halts_zfRootCfg_iff_zfRegHalts
    (hInc : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩)
    (hDecZero : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      regs[k] = 0 → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨90, Tape.mkL L_stack ((regsTape (p :: regs)).cons 0 |>.cons 0)⟩)
    (hDecPos : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      0 < regs[k] → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0)⟩)
    {padTotal : ℕ} (hpad : 160 ≤ padTotal)
    {initRegs : List ℕ} (hlen : 11 ≤ initRegs.length)
    (htake : initRegs.take 11 = List.replicate 11 0) :
    (eval (step reference) (zfRootCfg padTotal [] initRegs)).Dom ↔ ZfRegHalts := by
  have hInv : ZfRegInv ⟨[], initRegs⟩ := ⟨validStack_nil, hlen⟩
  have hsim : ZfRegSim ⟨[], initRegs⟩ zfRegInit := by
    refine ⟨rfl, hlen, by decide, ?_⟩
    simpa [zfRegInit] using htake
  unfold ZfRegHalts
  rw [← eval_zfRegStep_dom_iff_sim hsim]
  constructor
  · intro hDom
    rw [Part.dom_iff_mem] at hDom
    rcases hDom with ⟨ch, hmem⟩
    obtain ⟨N, hN, hnone⟩ := mem_eval_iff_nSteps.mp hmem
    exact zfReg_eval_dom_of_tm_nSteps_halt hInc hDecZero hDecPos hpad N hInv hN hnone
  · intro hDom
    exact tm_eval_dom_of_zfReg_eval_dom hInc hDecZero hDecPos hpad hInv hDom

/-- Complete equivalence between `Halts reference` and `ZfRegHalts`, given the Layer 1
boot and Pass-2 register evaluation theorems. -/
theorem halts_reference_iff_zfRegHalts
    (hBoot : ∃ s padTotal initRegs, 160 ≤ padTotal ∧ 11 ≤ initRegs.length ∧
      initRegs.take 11 = List.replicate 11 0 ∧
      nSteps reference s init = some (zfRootCfg padTotal [] initRegs))
    (hInc : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩)
    (hDecZero : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      regs[k] = 0 → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨90, Tape.mkL L_stack ((regsTape (p :: regs)).cons 0 |>.cons 0)⟩)
    (hDecPos : ∀ (k : ℕ), k < 11 → ∀ (p : ℕ) (regs : List ℕ) (hk : k < regs.length),
      0 < regs[k] → ∀ (L_stack : ListBlank (Fin 2)),
      ∃ s, 1 ≤ s ∧ nSteps reference s
        ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨89, Tape.mkL L_stack
          ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0)⟩) :
    Halts reference ↔ ZfRegHalts := by
  obtain ⟨s, padTotal, initRegs, hpad, hlen, htake, hboot_steps⟩ := hBoot
  unfold Halts
  rw [nSteps_eval_dom hboot_steps]
  exact halts_zfRootCfg_iff_zfRegHalts hInc hDecZero hDecPos hpad hlen htake

end ConjectureMachines.Zf429.Layer2
