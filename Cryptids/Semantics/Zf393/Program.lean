/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Zf.RegisterMachine

/-!
# Layer 2 & Layer 3 for `zf393` (`zf2.tm` / `zf2.py` post-`10fcf152b3`)

This standalone module proves:
1. Equivalence between the Layer 1 call-stack machine `Zf393RegHalts` (`Zf393RegCfg` with
   left-to-right tape registers `[scratch3, ..., prooflist]`) and the logical 11-register call-stack
   machine `ZfLog11Halts` (`[prooflist, ..., scratch3]`).
2. Complete evaluation of all 324 decision-tree nodes (`69..392`), the 13-step `unpair` header
   (`k = 0..13`), the 20 reordered axiom/rule clauses (`k = 13..123`, including the bugfixed
   `B6a` check at states `255..256` preserving `param3`), and the halt check (`k = 123, 124`),
   yielding `zf393RegHalts_iff_zf393MainHalts : Zf393RegHalts ↔ Zf393MainHalts`.
3. Full soundness and completeness of `zf393MainStep` against O'Rear's Hilbert system `ZFProvable`
   (`zf393MainHalts_iff_zfInconsistent : Zf393MainHalts ↔ ZFInconsistent`), giving
   `zf393RegHalts_iff_zfInconsistent : Zf393RegHalts ↔ ZFInconsistent` and unconditional
   non-halting `not_zf393RegHalts : ¬ Zf393RegHalts` via Mathlib's `ZFSet.{0}` model.
-/

@[expose] public section

namespace ConjectureMachines.Zf393.Layer2

open Turing StateTransition ConjectureMachines ConjectureMachines.Semantics.Zf

set_option maxRecDepth 200000

def zf393Trans (q : Fin 393) (s : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 196 then
    if q.val < 98 then
      if q.val < 49 then
        if q.val < 24 then
          if q.val < 12 then
            if q.val < 6 then
              if q.val < 3 then
                if q.val < 1 then
                  if s.val = 0 then some (1, .right, 1) else some (0, .left, 2)
                else
                  if q.val < 2 then
                    if s.val = 0 then some (0, .right, 2) else some (0, .right, 1)
                  else
                    if s.val = 0 then some (1, .left, 3) else some (0, .right, 4)
              else
                if q.val < 4 then
                  if s.val = 0 then some (0, .left, 4) else some (0, .left, 68)
                else
                  if q.val < 5 then
                    if s.val = 0 then some (1, .left, 0) else some (0, .left, 1)
                  else
                    if s.val = 0 then some (1, .right, 6) else some (1, .left, 10)
            else
              if q.val < 9 then
                if q.val < 7 then
                  if s.val = 0 then some (0, .right, 6) else some (0, .right, 7)
                else
                  if q.val < 8 then
                    if s.val = 0 then some (1, .right, 8) else some (1, .right, 7)
                  else
                    if s.val = 0 then some (0, .right, 9) else some (0, .right, 7)
              else
                if q.val < 10 then
                  if s.val = 0 then some (0, .left, 5) else some (1, .right, 9)
                else
                  if q.val < 11 then
                    if s.val = 0 then some (0, .left, 26) else some (1, .right, 11)
                  else
                    if s.val = 0 then some (1, .right, 12) else some (0, .right, 11)
          else
            if q.val < 18 then
              if q.val < 15 then
                if q.val < 13 then
                  if s.val = 0 then some (0, .left, 17) else some (1, .right, 9)
                else
                  if q.val < 14 then
                    if s.val = 0 then some (1, .right, 14) else none
                  else
                    if s.val = 0 then some (0, .right, 14) else some (1, .right, 15)
              else
                if q.val < 16 then
                  if s.val = 0 then some (0, .right, 16) else some (1, .right, 15)
                else
                  if q.val < 17 then
                    if s.val = 0 then some (1, .left, 23) else some (1, .right, 15)
                  else
                    if s.val = 0 then some (1, .right, 18) else some (0, .left, 23)
            else
              if q.val < 21 then
                if q.val < 19 then
                  if s.val = 0 then some (0, .right, 18) else some (1, .right, 19)
                else
                  if q.val < 20 then
                    if s.val = 0 then some (0, .right, 20) else some (1, .right, 19)
                  else
                    if s.val = 0 then some (0, .left, 21) else some (1, .right, 19)
              else
                if q.val < 22 then
                  if s.val = 0 then some (1, .left, 22) else some (0, .left, 23)
                else
                  if q.val < 23 then
                    if s.val = 0 then some (0, .right, 21) else some (1, .left, 22)
                  else
                    if s.val = 0 then some (0, .left, 24) else some (1, .left, 23)
        else
          if q.val < 36 then
            if q.val < 30 then
              if q.val < 27 then
                if q.val < 25 then
                  if s.val = 0 then some (0, .left, 25) else some (1, .left, 23)
                else
                  if q.val < 26 then
                    if s.val = 0 then some (0, .left, 25) else some (0, .left, 61)
                  else
                    if s.val = 0 then some (0, .left, 27) else some (1, .left, 26)
              else
                if q.val < 28 then
                  if s.val = 0 then some (0, .left, 28) else some (1, .left, 26)
                else
                  if q.val < 29 then
                    if s.val = 0 then some (0, .left, 28) else some (0, .left, 62)
                  else
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 49)
            else
              if q.val < 33 then
                if q.val < 31 then
                  if s.val = 0 then some (0, .right, 17) else some (1, .right, 50)
                else
                  if q.val < 32 then
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 39)
                  else
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 40)
              else
                if q.val < 34 then
                  if s.val = 0 then some (0, .right, 17) else some (1, .right, 29)
                else
                  if q.val < 35 then
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 30)
                  else
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 33)
          else
            if q.val < 42 then
              if q.val < 39 then
                if q.val < 37 then
                  if s.val = 0 then some (0, .right, 17) else some (1, .right, 34)
                else
                  if q.val < 38 then
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 35)
                  else
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 36)
              else
                if q.val < 40 then
                  if s.val = 0 then some (0, .right, 17) else some (1, .right, 5)
                else
                  if q.val < 41 then
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 13)
                  else
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 37)
            else
              if q.val < 45 then
                if q.val < 43 then
                  if s.val = 0 then some (0, .right, 17) else some (1, .right, 38)
                else
                  if q.val < 44 then
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 41)
                  else
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 42)
              else
                if q.val < 47 then
                  if q.val < 46 then
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 43)
                  else
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 44)
                else
                  if q.val < 48 then
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 31)
                  else
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 32)
      else
        if q.val < 73 then
          if q.val < 61 then
            if q.val < 55 then
              if q.val < 52 then
                if q.val < 50 then
                  if s.val = 0 then some (0, .right, 17) else some (1, .right, 47)
                else
                  if q.val < 51 then
                    if s.val = 0 then some (0, .right, 17) else some (1, .right, 48)
                  else
                    if s.val = 0 then some (0, .left, 52) else some (1, .left, 64)
              else
                if q.val < 53 then
                  if s.val = 0 then some (0, .left, 53) else some (1, .left, 64)
                else
                  if q.val < 54 then
                    if s.val = 0 then some (0, .left, 54) else some (1, .left, 64)
                  else
                    if s.val = 0 then some (0, .left, 55) else some (1, .left, 64)
            else
              if q.val < 58 then
                if q.val < 56 then
                  if s.val = 0 then some (0, .left, 56) else some (1, .left, 64)
                else
                  if q.val < 57 then
                    if s.val = 0 then some (0, .left, 57) else some (1, .left, 64)
                  else
                    if s.val = 0 then some (0, .left, 58) else some (1, .left, 64)
              else
                if q.val < 59 then
                  if s.val = 0 then some (0, .left, 59) else some (1, .left, 64)
                else
                  if q.val < 60 then
                    if s.val = 0 then some (0, .right, 60) else some (1, .left, 64)
                  else
                    if s.val = 0 then some (0, .right, 60) else some (1, .right, 99)
          else
            if q.val < 67 then
              if q.val < 64 then
                if q.val < 62 then
                  if s.val = 0 then some (1, .left, 64) else some (0, .left, 61)
                else
                  if q.val < 63 then
                    if s.val = 0 then some (0, .left, 61) else some (0, .left, 62)
                  else
                    if s.val = 0 then some (0, .left, 62) else some (0, .left, 63)
              else
                if q.val < 65 then
                  if s.val = 0 then some (0, .left, 51) else some (1, .left, 64)
                else
                  if q.val < 66 then
                    if s.val = 0 then some (0, .left, 65) else some (0, .left, 64)
                  else
                    if s.val = 0 then some (0, .left, 66) else some (0, .left, 65)
            else
              if q.val < 70 then
                if q.val < 68 then
                  if s.val = 0 then some (0, .left, 67) else some (0, .left, 66)
                else
                  if q.val < 69 then
                    if s.val = 0 then some (0, .left, 68) else some (0, .left, 67)
                  else
                    if s.val = 0 then some (0, .right, 289) else some (1, .right, 70)
              else
                if q.val < 71 then
                  if s.val = 0 then some (0, .right, 294) else some (1, .right, 379)
                else
                  if q.val < 72 then
                    if s.val = 0 then some (0, .right, 72) else some (0, .left, 62)
                  else
                    if s.val = 0 then some (0, .right, 29) else some (1, .right, 73)
        else
          if q.val < 85 then
            if q.val < 79 then
              if q.val < 76 then
                if q.val < 74 then
                  if s.val = 0 then some (0, .right, 74) else some (1, .right, 77)
                else
                  if q.val < 75 then
                    if s.val = 0 then some (0, .right, 29) else some (1, .right, 75)
                  else
                    if s.val = 0 then some (0, .right, 76) else some (0, .left, 62)
              else
                if q.val < 77 then
                  if s.val = 0 then some (0, .right, 30) else some (1, .right, 30)
                else
                  if q.val < 78 then
                    if s.val = 0 then some (0, .right, 78) else some (0, .left, 62)
                  else
                    if s.val = 0 then some (0, .right, 30) else some (1, .right, 289)
            else
              if q.val < 82 then
                if q.val < 80 then
                  if s.val = 0 then some (0, .right, 71) else some (1, .right, 80)
                else
                  if q.val < 81 then
                    if s.val = 0 then some (0, .right, 352) else some (1, .right, 366)
                  else
                    if s.val = 0 then some (0, .right, 71) else some (1, .right, 82)
              else
                if q.val < 83 then
                  if s.val = 0 then some (0, .right, 356) else some (1, .right, 368)
                else
                  if q.val < 84 then
                    if s.val = 0 then some (0, .right, 29) else some (1, .right, 84)
                  else
                    if s.val = 0 then some (0, .right, 382) else some (1, .right, 371)
          else
            if q.val < 91 then
              if q.val < 88 then
                if q.val < 86 then
                  if s.val = 0 then some (0, .right, 86) else some (1, .right, 90)
                else
                  if q.val < 87 then
                    if s.val = 0 then some (0, .right, 43) else some (1, .right, 87)
                  else
                    if s.val = 0 then some (0, .right, 88) else some (1, .right, 89)
              else
                if q.val < 89 then
                  if s.val = 0 then some (0, .right, 45) else some (0, .left, 65)
                else
                  if q.val < 90 then
                    if s.val = 0 then some (0, .right, 376) else some (0, .left, 63)
                  else
                    if s.val = 0 then some (0, .right, 45) else some (1, .right, 91)
            else
              if q.val < 94 then
                if q.val < 92 then
                  if s.val = 0 then some (0, .right, 381) else some (0, .left, 62)
                else
                  if q.val < 93 then
                    if s.val = 0 then some (0, .right, 85) else some (1, .right, 382)
                  else
                    if s.val = 0 then some (0, .right, 85) else some (1, .right, 94)
              else
                if q.val < 96 then
                  if q.val < 95 then
                    if s.val = 0 then some (0, .right, 348) else some (1, .right, 364)
                  else
                    if s.val = 0 then some (0, .right, 96) else some (1, .right, 97)
                else
                  if q.val < 97 then
                    if s.val = 0 then some (0, .right, 39) else some (0, .left, 62)
                  else
                    if s.val = 0 then some (0, .right, 343) else some (1, .right, 98)
    else
      if q.val < 147 then
        if q.val < 122 then
          if q.val < 110 then
            if q.val < 104 then
              if q.val < 101 then
                if q.val < 99 then
                  if s.val = 0 then some (0, .right, 362) else some (1, .right, 32)
                else
                  if q.val < 100 then
                    if s.val = 0 then some (0, .right, 95) else some (1, .right, 100)
                  else
                    if s.val = 0 then some (0, .right, 342) else some (1, .right, 101)
              else
                if q.val < 102 then
                  if s.val = 0 then some (0, .right, 346) else some (1, .right, 102)
                else
                  if q.val < 103 then
                    if s.val = 0 then some (0, .right, 352) else some (1, .right, 103)
                  else
                    if s.val = 0 then some (0, .right, 356) else some (1, .right, 104)
            else
              if q.val < 107 then
                if q.val < 105 then
                  if s.val = 0 then some (0, .right, 269) else some (1, .right, 105)
                else
                  if q.val < 106 then
                    if s.val = 0 then some (0, .right, 360) else some (1, .right, 106)
                  else
                    if s.val = 0 then some (0, .right, 269) else some (1, .right, 107)
              else
                if q.val < 108 then
                  if s.val = 0 then some (0, .right, 364) else some (1, .right, 108)
                else
                  if q.val < 109 then
                    if s.val = 0 then some (0, .right, 269) else some (1, .right, 109)
                  else
                    if s.val = 0 then some (0, .right, 366) else some (1, .right, 110)
          else
            if q.val < 116 then
              if q.val < 113 then
                if q.val < 111 then
                  if s.val = 0 then some (0, .right, 269) else some (1, .right, 111)
                else
                  if q.val < 112 then
                    if s.val = 0 then some (0, .right, 368) else some (1, .right, 112)
                  else
                    if s.val = 0 then some (0, .right, 304) else some (1, .right, 113)
              else
                if q.val < 114 then
                  if s.val = 0 then some (0, .right, 321) else some (1, .right, 114)
                else
                  if q.val < 115 then
                    if s.val = 0 then some (0, .right, 277) else some (1, .right, 115)
                  else
                    if s.val = 0 then some (0, .right, 265) else some (1, .right, 116)
            else
              if q.val < 119 then
                if q.val < 117 then
                  if s.val = 0 then some (0, .right, 320) else some (1, .right, 117)
                else
                  if q.val < 118 then
                    if s.val = 0 then some (0, .right, 257) else some (1, .right, 118)
                  else
                    if s.val = 0 then some (0, .right, 270) else some (1, .right, 119)
              else
                if q.val < 120 then
                  if s.val = 0 then some (0, .right, 325) else some (1, .right, 120)
                else
                  if q.val < 121 then
                    if s.val = 0 then some (0, .right, 319) else some (1, .right, 121)
                  else
                    if s.val = 0 then some (0, .right, 249) else some (1, .right, 122)
        else
          if q.val < 134 then
            if q.val < 128 then
              if q.val < 125 then
                if q.val < 123 then
                  if s.val = 0 then some (0, .right, 238) else some (1, .right, 123)
                else
                  if q.val < 124 then
                    if s.val = 0 then some (0, .right, 390) else some (1, .right, 124)
                  else
                    if s.val = 0 then some (0, .right, 238) else some (1, .right, 125)
              else
                if q.val < 126 then
                  if s.val = 0 then some (0, .right, 248) else some (1, .right, 126)
                else
                  if q.val < 127 then
                    if s.val = 0 then some (0, .right, 323) else some (1, .right, 127)
                  else
                    if s.val = 0 then some (0, .right, 270) else some (1, .right, 128)
            else
              if q.val < 131 then
                if q.val < 129 then
                  if s.val = 0 then some (0, .right, 245) else some (1, .right, 129)
                else
                  if q.val < 130 then
                    if s.val = 0 then some (0, .right, 321) else some (1, .right, 130)
                  else
                    if s.val = 0 then some (0, .right, 320) else some (1, .right, 131)
              else
                if q.val < 132 then
                  if s.val = 0 then some (0, .right, 247) else some (1, .right, 132)
                else
                  if q.val < 133 then
                    if s.val = 0 then some (0, .right, 272) else some (1, .right, 133)
                  else
                    if s.val = 0 then some (0, .right, 241) else some (1, .right, 134)
          else
            if q.val < 140 then
              if q.val < 137 then
                if q.val < 135 then
                  if s.val = 0 then some (0, .right, 392) else some (1, .right, 135)
                else
                  if q.val < 136 then
                    if s.val = 0 then some (0, .right, 298) else some (1, .right, 136)
                  else
                    if s.val = 0 then some (0, .right, 274) else some (1, .right, 137)
              else
                if q.val < 138 then
                  if s.val = 0 then some (0, .right, 245) else some (1, .right, 138)
                else
                  if q.val < 139 then
                    if s.val = 0 then some (0, .right, 285) else some (1, .right, 139)
                  else
                    if s.val = 0 then some (0, .right, 247) else some (1, .right, 140)
            else
              if q.val < 143 then
                if q.val < 141 then
                  if s.val = 0 then some (0, .right, 278) else some (1, .right, 141)
                else
                  if q.val < 142 then
                    if s.val = 0 then some (0, .right, 241) else some (1, .right, 142)
                  else
                    if s.val = 0 then some (0, .right, 298) else some (1, .right, 143)
              else
                if q.val < 145 then
                  if q.val < 144 then
                    if s.val = 0 then some (0, .right, 392) else some (1, .right, 144)
                  else
                    if s.val = 0 then some (0, .right, 300) else some (1, .right, 145)
                else
                  if q.val < 146 then
                    if s.val = 0 then some (0, .right, 226) else some (1, .right, 146)
                  else
                    if s.val = 0 then some (0, .right, 300) else some (1, .right, 147)
      else
        if q.val < 171 then
          if q.val < 159 then
            if q.val < 153 then
              if q.val < 150 then
                if q.val < 148 then
                  if s.val = 0 then some (0, .right, 329) else some (1, .right, 148)
                else
                  if q.val < 149 then
                    if s.val = 0 then some (0, .right, 271) else some (1, .right, 149)
                  else
                    if s.val = 0 then some (0, .right, 254) else some (1, .right, 150)
              else
                if q.val < 151 then
                  if s.val = 0 then some (0, .right, 302) else some (1, .right, 151)
                else
                  if q.val < 152 then
                    if s.val = 0 then some (0, .right, 254) else some (1, .right, 152)
                  else
                    if s.val = 0 then some (0, .right, 271) else some (1, .right, 153)
            else
              if q.val < 156 then
                if q.val < 154 then
                  if s.val = 0 then some (0, .right, 323) else some (1, .right, 154)
                else
                  if q.val < 155 then
                    if s.val = 0 then some (0, .right, 351) else some (1, .right, 155)
                  else
                    if s.val = 0 then some (0, .right, 364) else some (1, .right, 156)
              else
                if q.val < 157 then
                  if s.val = 0 then some (0, .right, 255) else some (1, .right, 157)
                else
                  if q.val < 158 then
                    if s.val = 0 then some (0, .right, 355) else some (1, .right, 158)
                  else
                    if s.val = 0 then some (0, .right, 366) else some (1, .right, 159)
          else
            if q.val < 165 then
              if q.val < 162 then
                if q.val < 160 then
                  if s.val = 0 then some (0, .right, 255) else some (1, .right, 160)
                else
                  if q.val < 161 then
                    if s.val = 0 then some (0, .right, 231) else some (1, .right, 161)
                  else
                    if s.val = 0 then some (0, .right, 329) else some (1, .right, 162)
              else
                if q.val < 163 then
                  if s.val = 0 then some (0, .right, 331) else some (1, .right, 163)
                else
                  if q.val < 164 then
                    if s.val = 0 then some (0, .right, 253) else some (1, .right, 164)
                  else
                    if s.val = 0 then some (0, .right, 272) else some (1, .right, 165)
            else
              if q.val < 168 then
                if q.val < 166 then
                  if s.val = 0 then some (0, .right, 279) else some (1, .right, 166)
                else
                  if q.val < 167 then
                    if s.val = 0 then some (0, .right, 325) else some (1, .right, 167)
                  else
                    if s.val = 0 then some (0, .right, 259) else some (1, .right, 168)
              else
                if q.val < 169 then
                  if s.val = 0 then some (0, .right, 243) else some (1, .right, 169)
                else
                  if q.val < 170 then
                    if s.val = 0 then some (0, .right, 329) else some (1, .right, 170)
                  else
                    if s.val = 0 then some (0, .right, 273) else some (1, .right, 171)
        else
          if q.val < 183 then
            if q.val < 177 then
              if q.val < 174 then
                if q.val < 172 then
                  if s.val = 0 then some (0, .right, 329) else some (1, .right, 172)
                else
                  if q.val < 173 then
                    if s.val = 0 then some (0, .right, 226) else some (1, .right, 173)
                  else
                    if s.val = 0 then some (0, .right, 327) else some (1, .right, 174)
              else
                if q.val < 175 then
                  if s.val = 0 then some (0, .right, 302) else some (1, .right, 175)
                else
                  if q.val < 176 then
                    if s.val = 0 then some (0, .right, 300) else some (1, .right, 176)
                  else
                    if s.val = 0 then some (0, .right, 244) else some (1, .right, 177)
            else
              if q.val < 180 then
                if q.val < 178 then
                  if s.val = 0 then some (0, .right, 390) else some (1, .right, 178)
                else
                  if q.val < 179 then
                    if s.val = 0 then some (0, .right, 273) else some (1, .right, 179)
                  else
                    if s.val = 0 then some (0, .right, 274) else some (1, .right, 180)
              else
                if q.val < 181 then
                  if s.val = 0 then some (0, .right, 302) else some (1, .right, 181)
                else
                  if q.val < 182 then
                    if s.val = 0 then some (0, .right, 390) else some (1, .right, 182)
                  else
                    if s.val = 0 then some (0, .right, 268) else some (1, .right, 183)
          else
            if q.val < 189 then
              if q.val < 186 then
                if q.val < 184 then
                  if s.val = 0 then some (0, .right, 320) else some (1, .right, 184)
                else
                  if q.val < 185 then
                    if s.val = 0 then some (0, .right, 275) else some (1, .right, 185)
                  else
                    if s.val = 0 then some (0, .right, 327) else some (1, .right, 186)
              else
                if q.val < 187 then
                  if s.val = 0 then some (0, .right, 248) else some (1, .right, 187)
                else
                  if q.val < 188 then
                    if s.val = 0 then some (0, .right, 263) else some (1, .right, 188)
                  else
                    if s.val = 0 then some (0, .right, 275) else some (1, .right, 189)
            else
              if q.val < 192 then
                if q.val < 190 then
                  if s.val = 0 then some (0, .right, 250) else some (1, .right, 190)
                else
                  if q.val < 191 then
                    if s.val = 0 then some (0, .right, 304) else some (1, .right, 191)
                  else
                    if s.val = 0 then some (0, .right, 257) else some (1, .right, 192)
              else
                if q.val < 194 then
                  if q.val < 193 then
                    if s.val = 0 then some (0, .right, 276) else some (1, .right, 193)
                  else
                    if s.val = 0 then some (0, .right, 79) else some (1, .right, 194)
                else
                  if q.val < 195 then
                    if s.val = 0 then some (0, .right, 282) else some (1, .right, 195)
                  else
                    if s.val = 0 then some (0, .right, 390) else some (1, .right, 196)
  else
    if q.val < 294 then
      if q.val < 245 then
        if q.val < 220 then
          if q.val < 208 then
            if q.val < 202 then
              if q.val < 199 then
                if q.val < 197 then
                  if s.val = 0 then some (0, .right, 388) else some (1, .right, 197)
                else
                  if q.val < 198 then
                    if s.val = 0 then some (0, .right, 354) else some (1, .right, 198)
                  else
                    if s.val = 0 then some (0, .right, 366) else some (1, .right, 199)
              else
                if q.val < 200 then
                  if s.val = 0 then some (0, .right, 93) else some (1, .right, 200)
                else
                  if q.val < 201 then
                    if s.val = 0 then some (0, .right, 276) else some (1, .right, 201)
                  else
                    if s.val = 0 then some (0, .right, 259) else some (1, .right, 202)
            else
              if q.val < 205 then
                if q.val < 203 then
                  if s.val = 0 then some (0, .right, 231) else some (1, .right, 203)
                else
                  if q.val < 204 then
                    if s.val = 0 then some (0, .right, 270) else some (1, .right, 204)
                  else
                    if s.val = 0 then some (0, .right, 300) else some (1, .right, 205)
              else
                if q.val < 206 then
                  if s.val = 0 then some (0, .right, 267) else some (1, .right, 206)
                else
                  if q.val < 207 then
                    if s.val = 0 then some (0, .right, 260) else some (1, .right, 207)
                  else
                    if s.val = 0 then some (0, .right, 304) else some (1, .right, 208)
          else
            if q.val < 214 then
              if q.val < 211 then
                if q.val < 209 then
                  if s.val = 0 then some (0, .right, 260) else some (1, .right, 209)
                else
                  if q.val < 210 then
                    if s.val = 0 then some (0, .right, 249) else some (1, .right, 210)
                  else
                    if s.val = 0 then some (0, .right, 319) else some (1, .right, 211)
              else
                if q.val < 212 then
                  if s.val = 0 then some (0, .right, 277) else some (1, .right, 212)
                else
                  if q.val < 213 then
                    if s.val = 0 then some (0, .right, 327) else some (1, .right, 213)
                  else
                    if s.val = 0 then some (0, .right, 261) else some (1, .right, 214)
            else
              if q.val < 217 then
                if q.val < 215 then
                  if s.val = 0 then some (0, .right, 390) else some (1, .right, 215)
                else
                  if q.val < 216 then
                    if s.val = 0 then some (0, .right, 261) else some (1, .right, 216)
                  else
                    if s.val = 0 then some (0, .right, 277) else some (1, .right, 217)
              else
                if q.val < 218 then
                  if s.val = 0 then some (0, .right, 250) else some (1, .right, 218)
                else
                  if q.val < 219 then
                    if s.val = 0 then some (0, .right, 278) else some (1, .right, 219)
                  else
                    if s.val = 0 then some (0, .right, 272) else some (1, .right, 220)
        else
          if q.val < 232 then
            if q.val < 226 then
              if q.val < 223 then
                if q.val < 221 then
                  if s.val = 0 then some (0, .right, 278) else some (1, .right, 221)
                else
                  if q.val < 222 then
                    if s.val = 0 then some (0, .right, 305) else some (1, .right, 222)
                  else
                    if s.val = 0 then some (0, .right, 47) else some (1, .right, 223)
              else
                if q.val < 224 then
                  if s.val = 0 then some (0, .right, 224) else none
                else
                  if q.val < 225 then
                    if s.val = 0 then some (0, .right, 47) else some (1, .right, 225)
                  else
                    if s.val = 0 then some (0, .right, 288) else some (0, .left, 62)
            else
              if q.val < 229 then
                if q.val < 227 then
                  if s.val = 0 then some (0, .right, 243) else some (1, .right, 227)
                else
                  if q.val < 228 then
                    if s.val = 0 then some (0, .right, 327) else some (1, .right, 228)
                  else
                    if s.val = 0 then some (0, .right, 273) else some (1, .right, 229)
              else
                if q.val < 230 then
                  if s.val = 0 then some (0, .right, 244) else some (1, .right, 230)
                else
                  if q.val < 231 then
                    if s.val = 0 then some (0, .right, 329) else some (1, .right, 282)
                  else
                    if s.val = 0 then some (0, .right, 253) else some (1, .right, 232)
          else
            if q.val < 238 then
              if q.val < 235 then
                if q.val < 233 then
                  if s.val = 0 then some (0, .right, 325) else some (1, .right, 233)
                else
                  if q.val < 234 then
                    if s.val = 0 then some (0, .right, 325) else some (1, .right, 234)
                  else
                    if s.val = 0 then some (0, .right, 300) else some (1, .right, 235)
              else
                if q.val < 236 then
                  if s.val = 0 then some (0, .right, 259) else some (1, .right, 236)
                else
                  if q.val < 237 then
                    if s.val = 0 then some (0, .right, 271) else some (1, .right, 237)
                  else
                    if s.val = 0 then some (0, .right, 283) else some (1, .right, 279)
            else
              if q.val < 241 then
                if q.val < 239 then
                  if s.val = 0 then some (0, .right, 321) else some (1, .right, 239)
                else
                  if q.val < 240 then
                    if s.val = 0 then some (0, .right, 264) else some (1, .right, 240)
                  else
                    if s.val = 0 then some (0, .right, 265) else some (1, .right, 278)
              else
                if q.val < 243 then
                  if q.val < 242 then
                    if s.val = 0 then some (0, .right, 248) else some (1, .right, 242)
                  else
                    if s.val = 0 then some (0, .right, 270) else some (1, .right, 283)
                else
                  if q.val < 244 then
                    if s.val = 0 then some (0, .right, 246) else some (1, .right, 286)
                  else
                    if s.val = 0 then some (0, .right, 327) else some (1, .right, 246)
      else
        if q.val < 269 then
          if q.val < 257 then
            if q.val < 251 then
              if q.val < 248 then
                if q.val < 246 then
                  if s.val = 0 then some (0, .right, 267) else some (1, .right, 285)
                else
                  if q.val < 247 then
                    if s.val = 0 then some (0, .right, 268) else some (1, .right, 279)
                  else
                    if s.val = 0 then some (0, .right, 327) else some (1, .right, 264)
              else
                if q.val < 249 then
                  if s.val = 0 then some (0, .right, 263) else some (1, .right, 390)
                else
                  if q.val < 250 then
                    if s.val = 0 then some (0, .right, 320) else some (1, .right, 263)
                  else
                    if s.val = 0 then some (0, .right, 327) else some (1, .right, 251)
            else
              if q.val < 254 then
                if q.val < 252 then
                  if s.val = 0 then some (0, .right, 390) else some (1, .right, 252)
                else
                  if q.val < 253 then
                    if s.val = 0 then some (0, .right, 323) else some (1, .right, 325)
                  else
                    if s.val = 0 then some (0, .right, 283) else some (1, .right, 273)
              else
                if q.val < 255 then
                  if s.val = 0 then some (0, .right, 279) else some (1, .right, 327)
                else
                  if q.val < 256 then
                    if s.val = 0 then some (0, .right, 358) else some (1, .right, 256)
                  else
                    if s.val = 0 then some (0, .right, 368) else some (1, .right, 92)
          else
            if q.val < 263 then
              if q.val < 260 then
                if q.val < 258 then
                  if s.val = 0 then some (0, .right, 319) else some (1, .right, 258)
                else
                  if q.val < 259 then
                    if s.val = 0 then some (0, .right, 329) else some (1, .right, 390)
                  else
                    if s.val = 0 then some (0, .right, 284) else some (1, .right, 325)
              else
                if q.val < 261 then
                  if s.val = 0 then some (0, .right, 304) else some (1, .right, 280)
                else
                  if q.val < 262 then
                    if s.val = 0 then some (0, .right, 319) else some (1, .right, 262)
                  else
                    if s.val = 0 then some (0, .right, 304) else some (1, .right, 329)
            else
              if q.val < 266 then
                if q.val < 264 then
                  if s.val = 0 then some (0, .right, 320) else some (1, .right, 280)
                else
                  if q.val < 265 then
                    if s.val = 0 then some (0, .right, 321) else some (1, .right, 287)
                  else
                    if s.val = 0 then some (0, .right, 319) else some (1, .right, 266)
              else
                if q.val < 267 then
                  if s.val = 0 then some (0, .right, 298) else some (1, .right, 325)
                else
                  if q.val < 268 then
                    if s.val = 0 then some (0, .right, 281) else some (1, .right, 319)
                  else
                    if s.val = 0 then some (0, .right, 390) else some (1, .right, 281)
        else
          if q.val < 281 then
            if q.val < 275 then
              if q.val < 272 then
                if q.val < 270 then
                  if s.val = 0 then some (0, .right, 313) else some (1, .right, 377)
                else
                  if q.val < 271 then
                    if s.val = 0 then some (0, .right, 325) else some (1, .right, 331)
                  else
                    if s.val = 0 then some (0, .right, 325) else some (1, .right, 390)
              else
                if q.val < 273 then
                  if s.val = 0 then some (0, .right, 390) else some (1, .right, 325)
                else
                  if q.val < 274 then
                    if s.val = 0 then some (0, .right, 300) else some (1, .right, 302)
                  else
                    if s.val = 0 then some (0, .right, 390) else some (1, .right, 298)
            else
              if q.val < 278 then
                if q.val < 276 then
                  if s.val = 0 then some (0, .right, 320) else some (1, .right, 304)
                else
                  if q.val < 277 then
                    if s.val = 0 then some (0, .right, 305) else some (1, .right, 81)
                  else
                    if s.val = 0 then some (0, .right, 319) else some (1, .right, 320)
              else
                if q.val < 279 then
                  if s.val = 0 then some (0, .right, 323) else some (1, .right, 331)
                else
                  if q.val < 280 then
                    if s.val = 0 then some (0, .right, 298) else some (1, .right, 300)
                  else
                    if s.val = 0 then some (0, .right, 319) else some (1, .right, 327)
          else
            if q.val < 287 then
              if q.val < 284 then
                if q.val < 282 then
                  if s.val = 0 then some (0, .right, 390) else some (1, .right, 305)
                else
                  if q.val < 283 then
                    if s.val = 0 then some (0, .right, 302) else some (1, .right, 298)
                  else
                    if s.val = 0 then some (0, .right, 305) else some (1, .right, 298)
              else
                if q.val < 285 then
                  if s.val = 0 then some (0, .right, 298) else some (1, .right, 302)
                else
                  if q.val < 286 then
                    if s.val = 0 then some (0, .right, 320) else some (1, .right, 321)
                  else
                    if s.val = 0 then some (0, .right, 329) else some (1, .right, 284)
            else
              if q.val < 290 then
                if q.val < 288 then
                  if s.val = 0 then some (0, .right, 304) else some (1, .right, 327)
                else
                  if q.val < 289 then
                    if s.val = 0 then some (0, .right, 48) else some (1, .right, 48)
                  else
                    if s.val = 0 then some (0, .right, 314) else some (1, .right, 380)
              else
                if q.val < 292 then
                  if q.val < 291 then
                    if s.val = 0 then some (0, .right, 383) else some (1, .right, 291)
                  else
                    if s.val = 0 then some (0, .right, 49) else some (1, .right, 292)
                else
                  if q.val < 293 then
                    if s.val = 0 then some (0, .right, 293) else some (0, .left, 66)
                  else
                    if s.val = 0 then some (0, .right, 42) else some (1, .right, 389)
    else
      if q.val < 343 then
        if q.val < 318 then
          if q.val < 306 then
            if q.val < 300 then
              if q.val < 297 then
                if q.val < 295 then
                  if s.val = 0 then some (0, .right, 373) else some (1, .right, 295)
                else
                  if q.val < 296 then
                    if s.val = 0 then some (0, .right, 47) else some (1, .right, 296)
                  else
                    if s.val = 0 then some (0, .right, 297) else some (0, .left, 66)
              else
                if q.val < 298 then
                  if s.val = 0 then some (0, .right, 44) else some (1, .right, 386)
                else
                  if q.val < 299 then
                    if s.val = 0 then some (0, .right, 304) else some (1, .right, 299)
                  else
                    if s.val = 0 then some (0, .right, 347) else some (1, .right, 364)
            else
              if q.val < 303 then
                if q.val < 301 then
                  if s.val = 0 then some (0, .right, 304) else some (1, .right, 301)
                else
                  if q.val < 302 then
                    if s.val = 0 then some (0, .right, 353) else some (1, .right, 366)
                  else
                    if s.val = 0 then some (0, .right, 304) else some (1, .right, 303)
              else
                if q.val < 304 then
                  if s.val = 0 then some (0, .right, 357) else some (1, .right, 368)
                else
                  if q.val < 305 then
                    if s.val = 0 then some (0, .right, 290) else some (1, .right, 372)
                  else
                    if s.val = 0 then some (0, .right, 386) else some (1, .right, 306)
          else
            if q.val < 312 then
              if q.val < 309 then
                if q.val < 307 then
                  if s.val = 0 then some (0, .right, 315) else some (1, .right, 307)
                else
                  if q.val < 308 then
                    if s.val = 0 then some (0, .right, 380) else some (1, .right, 308)
                  else
                    if s.val = 0 then some (0, .right, 83) else some (1, .right, 359)
              else
                if q.val < 310 then
                  if s.val = 0 then some (0, .right, 43) else some (0, .left, 66)
                else
                  if q.val < 311 then
                    if s.val = 0 then some (0, .right, 42) else some (1, .right, 311)
                  else
                    if s.val = 0 then some (0, .right, 309) else some (1, .right, 312)
            else
              if q.val < 315 then
                if q.val < 313 then
                  if s.val = 0 then some (0, .right, 370) else some (0, .left, 67)
                else
                  if q.val < 314 then
                    if s.val = 0 then some (0, .right, 39) else some (1, .right, 310)
                  else
                    if s.val = 0 then some (0, .right, 49) else some (1, .right, 310)
              else
                if q.val < 316 then
                  if s.val = 0 then some (0, .right, 49) else some (1, .right, 316)
                else
                  if q.val < 317 then
                    if s.val = 0 then some (0, .right, 48) else some (1, .right, 317)
                  else
                    if s.val = 0 then some (0, .right, 309) else some (1, .right, 318)
        else
          if q.val < 330 then
            if q.val < 324 then
              if q.val < 321 then
                if q.val < 319 then
                  if s.val = 0 then some (0, .right, 388) else some (0, .left, 67)
                else
                  if q.val < 320 then
                    if s.val = 0 then some (0, .right, 304) else some (1, .right, 48)
                  else
                    if s.val = 0 then some (0, .right, 304) else some (1, .right, 288)
              else
                if q.val < 322 then
                  if s.val = 0 then some (0, .right, 319) else some (1, .right, 288)
                else
                  if q.val < 323 then
                    if s.val = 0 then some (0, .right, 320) else some (1, .right, 288)
                  else
                    if s.val = 0 then some (0, .right, 392) else some (1, .right, 324)
            else
              if q.val < 327 then
                if q.val < 325 then
                  if s.val = 0 then some (0, .right, 390) else some (1, .right, 392)
                else
                  if q.val < 326 then
                    if s.val = 0 then some (0, .right, 69) else some (1, .right, 326)
                  else
                    if s.val = 0 then some (0, .right, 322) else some (1, .right, 69)
              else
                if q.val < 328 then
                  if s.val = 0 then some (0, .right, 69) else some (1, .right, 328)
                else
                  if q.val < 329 then
                    if s.val = 0 then some (0, .right, 319) else some (1, .right, 69)
                  else
                    if s.val = 0 then some (0, .right, 69) else some (1, .right, 330)
          else
            if q.val < 336 then
              if q.val < 333 then
                if q.val < 331 then
                  if s.val = 0 then some (0, .right, 304) else some (1, .right, 69)
                else
                  if q.val < 332 then
                    if s.val = 0 then some (0, .right, 392) else some (1, .right, 332)
                  else
                    if s.val = 0 then some (0, .right, 325) else some (1, .right, 392)
              else
                if q.val < 334 then
                  if s.val = 0 then some (0, .right, 44) else some (0, .left, 65)
                else
                  if q.val < 335 then
                    if s.val = 0 then some (0, .right, 50) else some (0, .left, 65)
                  else
                    if s.val = 0 then some (0, .right, 48) else some (0, .left, 65)
            else
              if q.val < 339 then
                if q.val < 337 then
                  if s.val = 0 then some (0, .right, 337) else some (0, .left, 65)
                else
                  if q.val < 338 then
                    if s.val = 0 then some (0, .right, 48) else some (1, .right, 42)
                  else
                    if s.val = 0 then some (0, .right, 339) else some (0, .left, 65)
              else
                if q.val < 341 then
                  if q.val < 340 then
                    if s.val = 0 then some (0, .right, 42) else some (1, .right, 46)
                  else
                    if s.val = 0 then some (0, .right, 341) else some (0, .left, 65)
                else
                  if q.val < 342 then
                    if s.val = 0 then some (0, .right, 42) else some (1, .right, 44)
                  else
                    if s.val = 0 then some (0, .right, 29) else some (0, .left, 64)
      else
        if q.val < 368 then
          if q.val < 355 then
            if q.val < 349 then
              if q.val < 346 then
                if q.val < 344 then
                  if s.val = 0 then some (0, .right, 31) else some (1, .right, 344)
                else
                  if q.val < 345 then
                    if s.val = 0 then some (0, .right, 345) else some (0, .left, 65)
                  else
                    if s.val = 0 then some (0, .right, 42) else some (1, .right, 40)
              else
                if q.val < 347 then
                  if s.val = 0 then some (0, .right, 33) else some (0, .left, 64)
                else
                  if q.val < 348 then
                    if s.val = 0 then some (0, .right, 33) else some (1, .right, 336)
                  else
                    if s.val = 0 then some (0, .right, 33) else some (1, .right, 349)
            else
              if q.val < 352 then
                if q.val < 350 then
                  if s.val = 0 then some (0, .right, 350) else some (0, .left, 65)
                else
                  if q.val < 351 then
                    if s.val = 0 then some (0, .right, 42) else some (1, .right, 48)
                  else
                    if s.val = 0 then some (0, .right, 33) else some (1, .right, 340)
              else
                if q.val < 353 then
                  if s.val = 0 then some (0, .right, 35) else some (0, .left, 64)
                else
                  if q.val < 354 then
                    if s.val = 0 then some (0, .right, 35) else some (1, .right, 336)
                  else
                    if s.val = 0 then some (0, .right, 35) else some (1, .right, 338)
          else
            if q.val < 361 then
              if q.val < 358 then
                if q.val < 356 then
                  if s.val = 0 then some (0, .right, 35) else some (1, .right, 340)
                else
                  if q.val < 357 then
                    if s.val = 0 then some (0, .right, 37) else some (0, .left, 64)
                  else
                    if s.val = 0 then some (0, .right, 37) else some (1, .right, 336)
              else
                if q.val < 359 then
                  if s.val = 0 then some (0, .right, 37) else some (1, .right, 338)
                else
                  if q.val < 360 then
                    if s.val = 0 then some (0, .right, 41) else some (0, .left, 64)
                  else
                    if s.val = 0 then some (0, .right, 41) else some (1, .right, 361)
            else
              if q.val < 364 then
                if q.val < 362 then
                  if s.val = 0 then some (0, .right, 30) else some (0, .left, 65)
                else
                  if q.val < 363 then
                    if s.val = 0 then some (0, .right, 41) else some (1, .right, 363)
                  else
                    if s.val = 0 then some (0, .right, 32) else some (0, .left, 65)
              else
                if q.val < 366 then
                  if q.val < 365 then
                    if s.val = 0 then some (0, .right, 41) else some (1, .right, 365)
                  else
                    if s.val = 0 then some (0, .right, 34) else some (0, .left, 65)
                else
                  if q.val < 367 then
                    if s.val = 0 then some (0, .right, 41) else some (1, .right, 367)
                  else
                    if s.val = 0 then some (0, .right, 36) else some (0, .left, 65)
        else
          if q.val < 380 then
            if q.val < 374 then
              if q.val < 371 then
                if q.val < 369 then
                  if s.val = 0 then some (0, .right, 41) else some (1, .right, 369)
                else
                  if q.val < 370 then
                    if s.val = 0 then some (0, .right, 38) else some (0, .left, 65)
                  else
                    if s.val = 0 then some (0, .right, 41) else some (1, .right, 333)
              else
                if q.val < 372 then
                  if s.val = 0 then some (0, .right, 41) else some (1, .right, 335)
                else
                  if q.val < 373 then
                    if s.val = 0 then some (0, .right, 41) else some (1, .right, 334)
                  else
                    if s.val = 0 then some (0, .right, 41) else some (1, .right, 374)
            else
              if q.val < 377 then
                if q.val < 375 then
                  if s.val = 0 then some (0, .right, 375) else some (0, .left, 65)
                else
                  if q.val < 376 then
                    if s.val = 0 then some (0, .right, 48) else some (1, .right, 44)
                  else
                    if s.val = 0 then some (0, .right, 43) else some (0, .left, 64)
              else
                if q.val < 378 then
                  if s.val = 0 then some (0, .right, 43) else some (1, .right, 378)
                else
                  if q.val < 379 then
                    if s.val = 0 then some (0, .right, 40) else some (0, .left, 65)
                  else
                    if s.val = 0 then some (0, .right, 43) else some (1, .right, 335)
          else
            if q.val < 386 then
              if q.val < 383 then
                if q.val < 381 then
                  if s.val = 0 then some (0, .right, 43) else some (1, .right, 334)
                else
                  if q.val < 382 then
                    if s.val = 0 then some (0, .right, 45) else some (0, .left, 64)
                  else
                    if s.val = 0 then some (0, .right, 47) else some (0, .left, 64)
              else
                if q.val < 384 then
                  if s.val = 0 then some (0, .right, 47) else some (1, .right, 384)
                else
                  if q.val < 385 then
                    if s.val = 0 then some (0, .right, 385) else some (0, .left, 65)
                  else
                    if s.val = 0 then some (0, .right, 50) else some (1, .right, 42)
            else
              if q.val < 389 then
                if q.val < 387 then
                  if s.val = 0 then some (0, .right, 47) else some (1, .right, 387)
                else
                  if q.val < 388 then
                    if s.val = 0 then some (0, .right, 42) else some (0, .left, 65)
                  else
                    if s.val = 0 then some (0, .right, 47) else some (1, .right, 333)
              else
                if q.val < 391 then
                  if q.val < 390 then
                    if s.val = 0 then some (0, .right, 49) else some (1, .right, 335)
                  else
                    if s.val = 0 then some (0, .right, 69) else some (1, .right, 391)
                else
                  if q.val < 392 then
                    if s.val = 0 then some (0, .right, 320) else some (1, .right, 69)
                  else
                    if s.val = 0 then some (0, .right, 321) else some (1, .right, 69)

def popBreakRev : ℕ → List (Fin 2) → List (Fin 2)
  | _, [] => []
  | k, 1 :: rest => popBreakRev k rest
  | 0, 0 :: rest => 1 :: rest
  | k + 1, 0 :: rest => popBreakRev k rest

@[simp] theorem popBreakRev_nil (k : ℕ) : popBreakRev k [] = [] := rfl
@[simp] theorem popBreakRev_one (k : ℕ) (rest : List (Fin 2)) :
    popBreakRev k (1 :: rest) = popBreakRev k rest := rfl
@[simp] theorem popBreakRev_zero (rest : List (Fin 2)) :
    popBreakRev 0 (0 :: rest) = 1 :: rest := rfl
@[simp] theorem popBreakRev_succ (k : ℕ) (rest : List (Fin 2)) :
    popBreakRev (k + 1) (0 :: rest) = popBreakRev k rest := rfl

def popContinueRev : ℕ → List (Fin 2) → List (Fin 2)
  | _, [] => []
  | k, 0 :: rest => popContinueRev k rest
  | 0, 1 :: rest => 1 :: rest
  | k + 1, 1 :: rest => popContinueRev k rest

@[simp] theorem popContinueRev_nil (k : ℕ) : popContinueRev k [] = [] := rfl
@[simp] theorem popContinueRev_zero (k : ℕ) (rest : List (Fin 2)) :
    popContinueRev k (0 :: rest) = popContinueRev k rest := rfl
@[simp] theorem popContinueRev_zero_one (rest : List (Fin 2)) :
    popContinueRev 0 (1 :: rest) = 1 :: rest := rfl
@[simp] theorem popContinueRev_succ_one (k : ℕ) (rest : List (Fin 2)) :
    popContinueRev (k + 1) (1 :: rest) = popContinueRev k rest := rfl

def retStack (P : List (Fin 2)) : List (Fin 2) :=
  (popBreakRev 0 P.reverse).reverse

def dropLeadingZeros : List (Fin 2) → List (Fin 2)
  | 0 :: rest => dropLeadingZeros rest
  | xs => xs

def trimZeros (P : List (Fin 2)) : List (Fin 2) :=
  (dropLeadingZeros P.reverse).reverse

def isLeafState (q : Fin 393) : Bool :=
  (29 ≤ q.val) && (q.val ≤ 50)

def isLeafInc (q : Fin 393) : Bool :=
  (q.val % 2) == 0

/-- Physical left-to-right tape register index (`0..10`), matching `Zf393Layer1.leafReg`. -/
def leafReg (q : Fin 393) : Fin 11 :=
  match q.val with
  | 46 | 45 => 0
  | 44 | 43 => 1
  | 42 | 41 => 2
  | 38 | 37 => 3
  | 36 | 35 => 4
  | 34 | 33 => 5
  | 30 | 29 => 6
  | 50 | 49 => 7
  | 48 | 47 => 8
  | 32 | 31 => 9
  | _ => 10

/-- Logical register index (`0 = prooflist .. 10 = scratch3`), equal to `10 - (leafReg q).val`. -/
def logLeafReg (q : Fin 393) : ℕ :=
  match q.val with
  | 46 | 45 => 10
  | 44 | 43 => 9
  | 42 | 41 => 8
  | 38 | 37 => 7
  | 36 | 35 => 6
  | 34 | 33 => 5
  | 30 | 29 => 4
  | 50 | 49 => 3
  | 48 | 47 => 2
  | 32 | 31 => 1
  | _ => 0

theorem ten_sub_leafReg_eq_logLeafReg (q : Fin 393) :
    10 - (leafReg q).val = logLeafReg q := by
  revert q; decide

inductive TreeOutcome
  | halt (q : Fin 393) (walked rem : List (Fin 2))
  | jumpLeft (q : Fin 393) (walked rem : List (Fin 2))
  | regLeaf (q : Fin 393) (walked rem : List (Fin 2))
  | outOfFuel
  deriving DecidableEq, Repr

def walkTape (q : Fin 393) (walked : List (Fin 2)) : List (Fin 2) → TreeOutcome
  | [] => .outOfFuel
  | b :: rem =>
    match zf393Trans q b with
    | none => .halt q walked (b :: rem)
    | some (w, .left, q') =>
      if w == 0 then .jumpLeft q' walked rem else .outOfFuel
    | some (w, .right, q') =>
      if w == b then
        if isLeafState q' then .regLeaf q' (walked ++ [w]) rem
        else walkTape q' (walked ++ [w]) rem
      else .outOfFuel

/-- Layer 1 abstract call-stack configuration (`regs` in tape order `[scratch3, ..., prooflist]`).
-/
structure Zf393RegCfg where
  ip : List (Fin 2)
  regs : List ℕ
  deriving DecidableEq, Repr

def zf393RegInit : Zf393RegCfg :=
  ⟨[], List.replicate 11 0⟩

def zf393RegStep (c : Zf393RegCfg) : Option Zf393RegCfg :=
  match walkTape 99 [] (c.ip ++ List.replicate 10 0) with
  | .halt _ _ _ => none
  | .outOfFuel => none
  | .jumpLeft q' walked _ =>
    match q'.val with
    | 61 => some ⟨(popBreakRev 0 walked.reverse).reverse, c.regs⟩
    | 62 => some ⟨(popBreakRev 1 walked.reverse).reverse, c.regs⟩
    | 63 => some ⟨(popBreakRev 2 walked.reverse).reverse, c.regs⟩
    | 64 => some ⟨(popContinueRev 0 walked.reverse).reverse, c.regs⟩
    | 65 => some ⟨(popContinueRev 1 walked.reverse).reverse, c.regs⟩
    | 66 => some ⟨(popContinueRev 2 walked.reverse).reverse, c.regs⟩
    | 67 => some ⟨(popContinueRev 3 walked.reverse).reverse, c.regs⟩
    | 68 => some ⟨(popContinueRev 4 walked.reverse).reverse, c.regs⟩
    | _ => none
  | .regLeaf q' walked _ =>
    let r := leafReg q'
    if isLeafInc q' then
      some ⟨retStack walked, c.regs.set r.val (c.regs.getD r.val 0 + 1)⟩
    else if c.regs.getD r.val 0 == 0 then
      some ⟨(popBreakRev 1 walked.reverse).reverse, c.regs⟩
    else
      some ⟨retStack walked, c.regs.set r.val (c.regs.getD r.val 0 - 1)⟩

def zf393RegNSteps : ℕ → Zf393RegCfg → Option Zf393RegCfg
  | 0, c => some c
  | n + 1, c =>
    match zf393RegStep c with
    | none => none
    | some c' => zf393RegNSteps n c'

def Zf393RegHalts : Prop :=
  ∃ n c, zf393RegNSteps n zf393RegInit = some c ∧ zf393RegStep c = none

/-- Logical instruction decoded at stack `ip` with registers in logical order `0..10`. -/
inductive StackInstr where
  | halt
  | jump (ip' : List (Fin 2))
  | inc (r : ℕ) (ip_succ : List (Fin 2))
  | decnz (r : ℕ) (ip_succ ip_fail : List (Fin 2))
  deriving DecidableEq, Repr

def evalStack (ip : List (Fin 2)) : StackInstr :=
  match walkTape 99 [] (ip ++ List.replicate 10 0) with
  | .halt _ _ _ => .halt
  | .outOfFuel => .halt
  | .jumpLeft q' walked _ =>
    match q'.val with
    | 61 => .jump (popBreakRev 0 walked.reverse).reverse
    | 62 => .jump (popBreakRev 1 walked.reverse).reverse
    | 63 => .jump (popBreakRev 2 walked.reverse).reverse
    | 64 => .jump (popContinueRev 0 walked.reverse).reverse
    | 65 => .jump (popContinueRev 1 walked.reverse).reverse
    | 66 => .jump (popContinueRev 2 walked.reverse).reverse
    | 67 => .jump (popContinueRev 3 walked.reverse).reverse
    | 68 => .jump (popContinueRev 4 walked.reverse).reverse
    | _ => .halt
  | .regLeaf q' walked _ =>
    let lr := logLeafReg q'
    if isLeafInc q' then
      .inc lr (retStack walked)
    else
      .decnz lr (retStack walked) (popBreakRev 1 walked.reverse).reverse

structure ZfLogCfg where
  stack : List (Fin 2)
  regs : List ℕ
  deriving DecidableEq, Repr

def zfLogInit : ZfLogCfg :=
  ⟨[], List.replicate 11 0⟩

def zfReg11Step (c : ZfLogCfg) : Option ZfLogCfg :=
  match evalStack c.stack with
  | .halt => none
  | .jump s' => some ⟨s', c.regs⟩
  | .inc r s_succ =>
    some ⟨s_succ, c.regs.set r (c.regs.getD r 0 + 1)⟩
  | .decnz r s_succ s_fail =>
    if c.regs.getD r 0 == 0 then
      some ⟨s_fail, c.regs⟩
    else
      some ⟨s_succ, c.regs.set r (c.regs.getD r 0 - 1)⟩

def zfReg11NSteps : ℕ → ZfLogCfg → Option ZfLogCfg
  | 0, c => some c
  | n + 1, c => (zfReg11Step c).bind (zfReg11NSteps n)

def ZfLog11Halts : Prop :=
  ∃ n c, zfReg11NSteps n zfLogInit = some c ∧ zfReg11Step c = none

@[simp]
theorem zfReg11NSteps_zero (c : ZfLogCfg) : zfReg11NSteps 0 c = some c := rfl

@[simp]
theorem zfReg11NSteps_succ (n : ℕ) (c : ZfLogCfg) :
    zfReg11NSteps (n + 1) c = (zfReg11Step c).bind (zfReg11NSteps n) := rfl

theorem zfReg11Step_one {c c' : ZfLogCfg} (h : zfReg11Step c = some c') :
    zfReg11NSteps 1 c = some c' := by
  simp [zfReg11NSteps, h]

theorem step_zfReg11NSteps {n : ℕ} {c₁ c₂ c₃ : ZfLogCfg}
    (h1 : zfReg11Step c₁ = some c₂) (h2 : zfReg11NSteps n c₂ = some c₃) :
    zfReg11NSteps (n + 1) c₁ = some c₃ := by
  simp [zfReg11NSteps, h1, h2]

theorem zfReg11NSteps_add (m n : ℕ) (c : ZfLogCfg) :
    zfReg11NSteps (m + n) c = (zfReg11NSteps m c).bind (zfReg11NSteps n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    simp only [Nat.succ_add, zfReg11NSteps_succ]
    cases zfReg11Step c <;> simp [ih]

theorem zfReg11NSteps_bind_eq {m n : ℕ} {c₁ c₂ c₃ : ZfLogCfg}
    (h1 : zfReg11NSteps m c₁ = some c₂) (h2 : zfReg11NSteps n c₂ = some c₃) :
    zfReg11NSteps (m + n) c₁ = some c₃ := by
  rw [zfReg11NSteps_add, h1, Option.bind_some, h2]

theorem rev11_getD_set {regs : List ℕ} (hlen : regs.length = 11) (k : Fin 11) :
    regs.reverse.getD k.val 0 = regs.getD (10 - k.val) 0 ∧
    ∀ v, regs.reverse.set k.val v = (regs.set (10 - k.val) v).reverse := by
  rcases regs with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, _ | ⟨r4, _ | ⟨r5, _ |
    ⟨r6, _ | ⟨r7, _ | ⟨r8, _ | ⟨r9, _ | ⟨r10, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen; done)
  rcases k with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hn⟩ <;> try omega
  all_goals exact ⟨rfl, fun _ => rfl⟩

theorem zf393RegStep_eq_zfReg11Step (ip : List (Fin 2)) {regs : List ℕ}
    (hlen : regs.length = 11) :
    zf393RegStep ⟨ip, regs.reverse⟩ =
      (zfReg11Step ⟨ip, regs⟩).map (fun c' => ⟨c'.stack, c'.regs.reverse⟩) := by
  unfold zf393RegStep zfReg11Step evalStack
  generalize walkTape 99 [] (ip ++ List.replicate 10 0) = out
  cases out with
  | halt _ _ _ => rfl
  | outOfFuel => rfl
  | jumpLeft q' walked _ =>
    dsimp only
    split <;> rfl
  | regLeaf q' walked _ =>
    dsimp only
    obtain ⟨hget, hset⟩ := rev11_getD_set hlen (leafReg q')
    rw [ten_sub_leafReg_eq_logLeafReg q'] at hget hset
    rcases isLeafInc q' with _ | _
    · rw [hget]
      split <;> simp only [Option.map, hset]; split <;> rfl
    · simp only [↓reduceIte, Option.map, hget, hset]

theorem zfReg11Step_length {c c' : ZfLogCfg} (hlen : c.regs.length = 11)
    (hs : zfReg11Step c = some c') : c'.regs.length = 11 := by
  unfold zfReg11Step at hs
  rcases h : evalStack c.stack with _ | s' | ⟨r, s_succ⟩ | ⟨r, s_succ, s_fail⟩
  · rw [h] at hs; cases hs
  · rw [h] at hs; injection hs with h'; rw [← h']; exact hlen
  · rw [h] at hs; injection hs with h'; rw [← h']; simp [hlen]
  · rw [h] at hs
    dsimp only at hs
    rcases hz : (c.regs.getD r 0 == 0) with _ | _
    · rw [hz] at hs; injection hs with h'; rw [← h']; simp [hlen]
    · rw [hz] at hs; injection hs with h'; rw [← h']; exact hlen

theorem zf393RegHalts_iff_zfLog11Halts :
    Zf393RegHalts ↔ ZfLog11Halts := by
  have hinit : zf393RegInit = ⟨zfLogInit.stack, zfLogInit.regs.reverse⟩ := rfl
  constructor
  · rintro ⟨n, ch, hn, hnone⟩
    have aux : ∀ m (cL : ZfLogCfg), cL.regs.length = 11 →
        zf393RegNSteps m ⟨cL.stack, cL.regs.reverse⟩ = some ch →
        ∃ chL, zfReg11NSteps m cL = some chL ∧ chL.regs.length = 11 ∧
          ch = ⟨chL.stack, chL.regs.reverse⟩ := by
      intro m
      induction m with
      | zero =>
        intro cL hlen hm
        injection hm with hm'
        exact ⟨cL, rfl, hlen, hm'.symm⟩
      | succ m ih =>
        intro cL hlen hm
        simp only [zf393RegNSteps, zf393RegStep_eq_zfReg11Step cL.stack hlen] at hm
        rcases hs : zfReg11Step cL with _ | cL'
        · rw [hs] at hm; cases hm
        · rw [hs] at hm
          rw [zfReg11NSteps_succ, hs, Option.bind_some]
          exact ih cL' (zfReg11Step_length hlen hs) hm
    obtain ⟨chL, hnL, hlenL, rfl⟩ := aux n zfLogInit rfl (by rwa [← hinit])
    rw [zf393RegStep_eq_zfReg11Step chL.stack hlenL] at hnone
    rcases hs : zfReg11Step chL with _ | _
    · exact ⟨n, chL, hnL, hs⟩
    · rw [hs] at hnone; cases hnone
  · rintro ⟨n, chL, hnL, hnone⟩
    have aux : ∀ m (cL : ZfLogCfg), cL.regs.length = 11 →
        zfReg11NSteps m cL = some chL →
        chL.regs.length = 11 ∧
          zf393RegNSteps m ⟨cL.stack, cL.regs.reverse⟩ = some ⟨chL.stack, chL.regs.reverse⟩ := by
      intro m
      induction m with
      | zero =>
        intro cL hlen hm
        injection hm with hm'; subst hm'
        exact ⟨hlen, rfl⟩
      | succ m ih =>
        intro cL hlen hm
        simp only [zfReg11NSteps] at hm
        rcases hs : zfReg11Step cL with _ | cL'
        · rw [hs] at hm; cases hm
        · rw [hs, Option.bind_some] at hm
          simp only [zf393RegNSteps, zf393RegStep_eq_zfReg11Step cL.stack hlen, hs]
          exact ih cL' (zfReg11Step_length hlen hs) hm
    obtain ⟨hlenL, hn⟩ := aux n zfLogInit rfl hnL
    refine ⟨n, ⟨chL.stack, chL.regs.reverse⟩, by rwa [hinit], ?_⟩
    rw [zf393RegStep_eq_zfReg11Step chL.stack hlenL, hnone]
    rfl

def walkInternal (q : Fin 393) : List (Fin 2) → Option (Fin 393)
  | [] => if 69 ≤ q.val then some q else none
  | b :: bs =>
    if 69 ≤ q.val then
      match zf393Trans q b with
      | some (w, .right, q') =>
        if w == b && 69 ≤ q'.val then walkInternal q' bs else none
      | _ => none
    else none

theorem walkInternal_ge_69 {q q' : Fin 393} {P : List (Fin 2)}
    (h : walkInternal q P = some q') : 69 ≤ q.val ∧ 69 ≤ q'.val := by
  induction P generalizing q with
  | nil =>
    simp only [walkInternal] at h
    split at h
    · rename_i hq; injection h with h'; subst h'; exact ⟨hq, hq⟩
    · cases h
  | cons b bs ih =>
    simp only [walkInternal] at h
    split at h
    · rename_i hq
      rcases htr : zf393Trans q b with _ | ⟨w, d, q1⟩
      · rw [htr] at h; cases h
      · rw [htr] at h
        cases d with
        | left => cases h
        | right =>
          dsimp only at h
          split at h
          · exact ⟨hq, (ih h).2⟩
          · cases h
    · cases h

theorem walkInternal_append (q : Fin 393) (P Q : List (Fin 2)) :
    walkInternal q (P ++ Q) = (walkInternal q P).bind (fun q' => walkInternal q' Q) := by
  induction P generalizing q with
  | nil =>
    simp only [List.nil_append, walkInternal]
    split
    · rfl
    · rename_i hlt
      cases Q with
      | nil => simp [walkInternal, hlt]
      | cons _ _ => simp [walkInternal, hlt]
  | cons b bs ih =>
    simp only [List.cons_append, walkInternal]
    split
    · rcases htr : zf393Trans q b with _ | ⟨w, d, q1⟩
      · rfl
      · cases d with
        | left => rfl
        | right =>
          dsimp only
          split
          · exact ih q1
          · rfl
    · rfl

theorem walkInternal_snoc {q q_mid q_end : Fin 393} {P : List (Fin 2)} {b : Fin 2}
    (hP : walkInternal q P = some q_mid)
    (htr : zf393Trans q_mid b = some (b, .right, q_end))
    (hq_end : 69 ≤ q_end.val) :
    walkInternal q (P ++ [b]) = some q_end := by
  have hge := (walkInternal_ge_69 hP).2
  rw [walkInternal_append, hP, Option.bind_some]
  simp [walkInternal, hge, htr, hq_end]

theorem walkTape_of_walkInternal {q q' : Fin 393} {P : List (Fin 2)}
    (h : walkInternal q P = some q') (walked rest : List (Fin 2)) :
    walkTape q walked (P ++ rest) = walkTape q' (walked ++ P) rest := by
  induction P generalizing q walked with
  | nil =>
    simp only [walkInternal] at h
    split at h
    · injection h with h'; subst h'; simp
    · cases h
  | cons b bs ih =>
    simp only [walkInternal] at h
    split at h
    · rcases htr : zf393Trans q b with _ | ⟨w, d, q1⟩
      · rw [htr] at h; cases h
      · rw [htr] at h
        cases d with
        | left => cases h
        | right =>
          dsimp only at h
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            have hwb : w = b := beq_iff_eq.mp hcond.1
            subst hwb
            have hleaf : isLeafState q1 = false := by
              unfold isLeafState; simp; omega
            simp only [List.cons_append, walkTape, htr, beq_self_eq_true, hleaf,
              Bool.false_eq_true, ↓reduceIte]
            rw [ih h (walked ++ [w])]
            simp [List.append_assoc]
          · cases h
    · cases h

theorem dropLeadingZeros_spec (rev : List (Fin 2)) :
    rev = List.replicate (rev.length - (dropLeadingZeros rev).length) 0 ++
      dropLeadingZeros rev := by
  induction rev with
  | nil => rfl
  | cons b rest ih =>
    rcases b with ⟨_ | _ | n, hn⟩
    · have hlen : (dropLeadingZeros rest).length ≤ rest.length := by
        have := congrArg List.length ih
        simp at this; omega
      have hsub : (rest.length + 1) - (dropLeadingZeros rest).length =
          (rest.length - (dropLeadingZeros rest).length) + 1 := by omega
      change (0 : Fin 2) :: rest =
        List.replicate ((rest.length + 1) - (dropLeadingZeros rest).length) 0 ++
          dropLeadingZeros rest
      rw [hsub, List.replicate_succ, List.cons_append, ← ih]
    · have hb : (⟨1, hn⟩ : Fin 2) = 1 := rfl
      rw [hb]
      simp [dropLeadingZeros]
    · omega

theorem eq_trimZeros_append_replicate (P : List (Fin 2)) :
    P = trimZeros P ++ List.replicate (P.length - (trimZeros P).length) 0 := by
  have h := congrArg List.reverse (dropLeadingZeros_spec P.reverse)
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate,
    List.length_reverse] at h
  unfold trimZeros at *
  rwa [List.length_reverse]

theorem walkTape_extend_zeros (q : Fin 393) (walked rem : List (Fin 2)) (n : ℕ) :
    match walkTape q walked rem with
    | .outOfFuel => True
    | .halt q_h w_h r_h =>
      walkTape q walked (rem ++ List.replicate n 0) =
        .halt q_h w_h (r_h ++ List.replicate n 0)
    | .jumpLeft q' w_j r_j =>
      walkTape q walked (rem ++ List.replicate n 0) =
        .jumpLeft q' w_j (r_j ++ List.replicate n 0)
    | .regLeaf q' w_l r_l =>
      walkTape q walked (rem ++ List.replicate n 0) =
        .regLeaf q' w_l (r_l ++ List.replicate n 0) := by
  induction rem generalizing q walked with
  | nil => trivial
  | cons b rem' ih =>
    simp only [List.cons_append, walkTape]
    rcases htr : zf393Trans q b with _ | ⟨w, d, q'⟩
    · rfl
    · cases d with
      | left =>
        dsimp only
        rcases hw0 : (w == 0) with _ | _
        · trivial
        · rfl
      | right =>
        dsimp only
        rcases hwb : (w == b) with _ | _
        · trivial
        · rcases hl : isLeafState q' with _ | _
          · exact ih q' (walked ++ [w])
          · rfl

theorem walkTape_outOfFuel_indep (q : Fin 393) (w1 w2 rem : List (Fin 2)) :
    (walkTape q w1 rem == .outOfFuel) = (walkTape q w2 rem == .outOfFuel) := by
  induction rem generalizing q w1 w2 with
  | nil => rfl
  | cons b rem' ih =>
    simp only [walkTape]
    rcases htr : zf393Trans q b with _ | ⟨w, d, q'⟩
    · rfl
    · cases d with
      | left =>
        dsimp only
        rcases hw0 : (w == 0) with _ | _ <;> rfl
      | right =>
        dsimp only
        rcases hwb : (w == b) with _ | _
        · rfl
        · rcases hl : isLeafState q' with _ | _
          · exact ih q' (w1 ++ [w]) (w2 ++ [w])
          · rfl

set_option maxHeartbeats 0 in
-- Finite `decide` check over all 324 DAG states `69..392`.
theorem walkTape_ten_zeros_nil (q : Fin 393) (hq : 69 ≤ q.val) :
    (walkTape q [] (List.replicate 10 0) == .outOfFuel) = false := by
  revert q hq; decide

@[simp]
theorem retStack_append_zero (P : List (Fin 2)) :
    retStack (P ++ [0]) = P ++ [1] := by
  simp [retStack]

@[simp]
theorem retStack_append_one (P : List (Fin 2)) :
    retStack (P ++ [1]) = retStack P := by
  simp [retStack]

@[simp]
theorem retStack_replicate_one (k : ℕ) :
    retStack (List.replicate k 1) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ', retStack_append_one, ih]

@[simp]
theorem trimZeros_append_zero (P : List (Fin 2)) :
    trimZeros (P ++ [0]) = trimZeros P := by
  simp [trimZeros, dropLeadingZeros]

@[simp]
theorem trimZeros_append_one (P : List (Fin 2)) :
    trimZeros (P ++ [1]) = P ++ [1] := by
  simp [trimZeros, dropLeadingZeros]

@[simp]
theorem trimZeros_replicate_zero (k : ℕ) :
    trimZeros (List.replicate k 0) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ', trimZeros_append_zero, ih]

@[simp]
theorem trimZeros_replicate_one (k : ℕ) :
    trimZeros (List.replicate k 1) = List.replicate k 1 := by
  cases k with
  | zero => rfl
  | succ k => rw [List.replicate_succ', trimZeros_append_one]

theorem popContinueRev_zero_eq_dropLeadingZeros (rev : List (Fin 2)) :
    popContinueRev 0 rev = dropLeadingZeros rev := by
  induction rev with
  | nil => rfl
  | cons b rest ih =>
    rcases b with ⟨_ | _ | n, hn⟩
    · simp [popContinueRev, dropLeadingZeros, ih]
    · rfl
    · omega

theorem evalStack_trimZeros_of_walkInternal {P : List (Fin 2)} {q : Fin 393}
    (h : walkInternal 99 P = some q) :
    evalStack (trimZeros P) = evalStack P := by
  let m := P.length - (trimZeros P).length
  have hP_split : P = trimZeros P ++ List.replicate m 0 := eq_trimZeros_append_replicate P
  have hw_app := walkInternal_append 99 (trimZeros P) (List.replicate m 0)
  rw [← hP_split, h] at hw_app
  rcases hqt : walkInternal 99 (trimZeros P) with _ | qt
  · rw [hqt] at hw_app; cases hw_app
  · have hq69 : 69 ≤ qt.val := (walkInternal_ge_69 hqt).2
    have hnot : (walkTape 99 [] (trimZeros P ++ List.replicate 10 0) == .outOfFuel) = false := by
      rw [walkTape_of_walkInternal hqt [] (List.replicate 10 0),
        walkTape_outOfFuel_indep qt ([] ++ trimZeros P) [] (List.replicate 10 0)]
      exact walkTape_ten_zeros_nil qt hq69
    have hext := walkTape_extend_zeros 99 [] (trimZeros P ++ List.replicate 10 0) m
    have heq_list :
        (trimZeros P ++ List.replicate 10 0) ++ List.replicate m 0 =
        P ++ List.replicate 10 0 := by
      rw [List.append_assoc, ← List.replicate_add, Nat.add_comm 10 m, List.replicate_add,
        ← List.append_assoc, ← hP_split]
    rw [heq_list] at hext
    unfold evalStack
    rcases hw : walkTape 99 [] (trimZeros P ++ List.replicate 10 0) with
      ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | _
    · rw [hw] at hext; rw [hext]
    · rw [hw] at hext; rw [hext]
    · rw [hw] at hext; rw [hext]
    · rw [hw] at hnot; cases hnot

theorem evalStack_leaf0_of_walkInternal {P : List (Fin 2)} {q q' : Fin 393}
    (h : walkInternal 99 P = some q)
    (htr : zf393Trans q 0 = some (0, .right, q'))
    (h29 : 29 ≤ q'.val) (h50 : q'.val ≤ 50) :
    evalStack P =
      if isLeafInc q' then
        .inc (logLeafReg q') (P ++ [1])
      else
        .decnz (logLeafReg q') (P ++ [1]) (retStack P) := by
  have hleaf : isLeafState q' = true := by
    unfold isLeafState; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h29, h50⟩
  have hwalk : walkTape 99 [] (P ++ List.replicate 10 0) =
      .regLeaf q' (P ++ [0]) (List.replicate 9 0) := by
    rw [walkTape_of_walkInternal h [] (List.replicate 10 0), List.nil_append]
    change walkTape q P (0 :: List.replicate 9 0) = _
    simp [walkTape, htr, hleaf]
  unfold evalStack
  rw [hwalk]
  simp [retStack]

theorem evalStack_leaf1_inc_of_walkInternal {P : List (Fin 2)} {q q' : Fin 393}
    (h : walkInternal 99 P = some q)
    (htr : zf393Trans q 1 = some (1, .right, q'))
    (h29 : 29 ≤ q'.val) (h50 : q'.val ≤ 50) (hinc : isLeafInc q' = true) :
    evalStack (P ++ [1]) = .inc (logLeafReg q') (retStack P) := by
  have hleaf : isLeafState q' = true := by
    unfold isLeafState; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h29, h50⟩
  have hwalk : walkTape 99 [] ((P ++ [1]) ++ List.replicate 10 0) =
      .regLeaf q' (P ++ [1]) (List.replicate 10 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 10 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 10 0) = _
    simp [walkTape, htr, hleaf]
  unfold evalStack
  rw [hwalk]
  simp [hinc]

theorem evalStack_break1_of_walkInternal {P : List (Fin 2)} {q : Fin 393} {k : ℕ}
    (hk2 : k ≤ 2) (h : walkInternal 99 P = some q)
    (htr : zf393Trans q 1 = some (0, .left, ⟨61 + k, by omega⟩)) :
    evalStack (P ++ [1]) = .jump (popBreakRev k P.reverse).reverse := by
  have hwalk : walkTape 99 [] ((P ++ [1]) ++ List.replicate 10 0) =
      .jumpLeft ⟨61 + k, by omega⟩ P (List.replicate 10 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 10 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 10 0) = _
    simp [walkTape, htr]
  unfold evalStack
  rw [hwalk]
  match k, hk2 with
  | 0, _ | 1, _ | 2, _ => rfl

theorem evalStack_continue1_of_walkInternal {P : List (Fin 2)} {q : Fin 393} {k : ℕ}
    (hk3 : k ≤ 3) (h : walkInternal 99 P = some q)
    (htr : zf393Trans q 1 = some (0, .left, ⟨64 + k, by omega⟩)) :
    evalStack (P ++ [1]) = .jump (popContinueRev k P.reverse).reverse := by
  have hwalk : walkTape 99 [] ((P ++ [1]) ++ List.replicate 10 0) =
      .jumpLeft ⟨64 + k, by omega⟩ P (List.replicate 10 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 10 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 10 0) = _
    simp [walkTape, htr]
  unfold evalStack
  rw [hwalk]
  match k, hk3 with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

def SubEval (q : Fin 393) (f : List ℕ → List ℕ) : Prop :=
  ∀ (P : List (Fin 2)),
    walkInternal 99 P = some q →
    ∀ (regs : List ℕ), regs.length = 11 →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ = some ⟨retStack P, f regs⟩ ∧
        (f regs).length = 11

theorem SubEval.congr {q : Fin 393} {f g : List ℕ → List ℕ}
    (h : SubEval q f) (heq : ∀ regs, regs.length = 11 → f regs = g regs) :
    SubEval q g := by
  intro P hP regs hlen
  obtain ⟨s, hs, hsteps, hflen⟩ := h P hP regs hlen
  rw [heq regs hlen] at hsteps hflen
  exact ⟨s, hs, hsteps, hflen⟩

/-- Sequential composition combinator: if `q` transitions on `0` to `q₀` (`69 ≤ q₀.val`) and on
`1` to `q₁` (`69 ≤ q₁.val`), then `SubEval q₀ f₀` and `SubEval q₁ f₁` compose to
`SubEval q (fun regs => f₁ (f₀ regs))`. -/
theorem subEval_seq {q q₀ q₁ : Fin 393} {f₀ f₁ : List ℕ → List ℕ}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀)) (hq₀ : 69 ≤ q₀.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (h0 : SubEval q₀ f₀) (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs => f₁ (f₀ regs)) := by
  intro P hP regs hlen
  have hP0 : walkInternal 99 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := h0 (P ++ [0]) hP0 regs hlen
  rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
  obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 (f₀ regs) hlen₀
  rw [trimZeros_append_one, retStack_append_one] at hsteps₁
  exact ⟨s₀ + s₁, by omega, zfReg11NSteps_bind_eq hsteps₀ hsteps₁, hlen₁⟩

theorem zfReg11Step_of_jump {s s' : List (Fin 2)} {regs : List ℕ}
    (h : evalStack s = .jump s') :
    zfReg11Step ⟨s, regs⟩ = some ⟨s', regs⟩ := by
  unfold zfReg11Step; dsimp only; rw [h]

theorem zfReg11Step_of_inc {s s' : List (Fin 2)} {r : ℕ} {regs : List ℕ}
    (h : evalStack s = .inc r s') :
    zfReg11Step ⟨s, regs⟩ = some ⟨s', regs.set r (regs.getD r 0 + 1)⟩ := by
  unfold zfReg11Step; dsimp only; rw [h]

theorem zfReg11Step_of_decnz_zero {s s_succ s_fail : List (Fin 2)} {r : ℕ} {regs : List ℕ}
    (h : evalStack s = .decnz r s_succ s_fail) (hz : regs.getD r 0 = 0) :
    zfReg11Step ⟨s, regs⟩ = some ⟨s_fail, regs⟩ := by
  unfold zfReg11Step; dsimp only; rw [h]; dsimp only; rw [hz]; rfl

theorem zfReg11Step_of_decnz_succ {s s_succ s_fail : List (Fin 2)} {r v : ℕ} {regs : List ℕ}
    (h : evalStack s = .decnz r s_succ s_fail) (hv : regs.getD r 0 = v + 1) :
    zfReg11Step ⟨s, regs⟩ = some ⟨s_succ, regs.set r v⟩ := by
  unfold zfReg11Step; dsimp only; rw [h]; dsimp only; rw [hv]; rfl

/-- Sequential + increment leaf combinator: if `q` transitions on `0` to `q₀` (`69 ≤ q₀.val`) and
on `1` to an increment leaf `q₁ ∈ {29..50}`, then `SubEval q₀ f₀` composes with the increment of
`logLeafReg q₁`. -/
theorem subEval_seq_inc {q q₀ q₁ : Fin 393} {f₀ : List ℕ → List ℕ}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀)) (hq₀ : 69 ≤ q₀.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁))
    (h49 : 29 ≤ q₁.val) (h70 : q₁.val ≤ 50) (hinc : isLeafInc q₁ = true)
    (h0 : SubEval q₀ f₀) :
    SubEval q (fun regs =>
      let r := f₀ regs
      r.set (logLeafReg q₁) (r.getD (logLeafReg q₁) 0 + 1)) := by
  intro P hP regs hlen
  have hP0 : walkInternal 99 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := h0 (P ++ [0]) hP0 regs hlen
  rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
  have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 h49 h70 hinc
  have hstep1 := zfReg11Step_of_inc (regs := f₀ regs) hev1
  refine ⟨s₀ + 1, by omega, zfReg11NSteps_bind_eq hsteps₀ (zfReg11Step_one hstep1), ?_⟩
  simp [hlen₀]

/-- Two-increment leaf node combinator: if `q` transitions on `0` to increment leaf `q₀` and on
`1` to increment leaf `q₁`, then `q` increments `logLeafReg q₀` followed by `logLeafReg q₁`. -/
theorem subEval_inc_inc {q q₀ q₁ : Fin 393}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀))
    (h0_49 : 29 ≤ q₀.val) (h0_70 : q₀.val ≤ 50) (hinc0 : isLeafInc q₀ = true)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁))
    (h1_49 : 29 ≤ q₁.val) (h1_70 : q₁.val ≤ 50) (hinc1 : isLeafInc q₁ = true) :
    SubEval q (fun regs =>
      let r₁ := regs.set (logLeafReg q₀) (regs.getD (logLeafReg q₀) 0 + 1)
      r₁.set (logLeafReg q₁) (r₁.getD (logLeafReg q₁) 0 + 1)) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .inc (logLeafReg q₀) (P ++ [1]) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 h0_49 h0_70]
    simp [hinc0]
  have hstep0 := zfReg11Step_of_inc (regs := regs) hev0
  have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 h1_49 h1_70 hinc1
  let r₁ := regs.set (logLeafReg q₀) (regs.getD (logLeafReg q₀) 0 + 1)
  have hstep1 := zfReg11Step_of_inc (regs := r₁) hev1
  refine ⟨2, by omega, step_zfReg11NSteps hstep0 (zfReg11Step_one hstep1), ?_⟩
  simp [hlen]

/-- Increment leaf + sequential combinator: if `q` transitions on `0` to an increment leaf
`q₀ ∈ {29..50}` and on `1` to `q₁` (`69 ≤ q₁.val`), then `q` increments `logLeafReg q₀` followed by
`f₁`. -/
theorem subEval_inc_seq {q q₀ q₁ : Fin 393} {f₁ : List ℕ → List ℕ}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀))
    (h49 : 29 ≤ q₀.val) (h70 : q₀.val ≤ 50) (hinc : isLeafInc q₀ = true)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs =>
      f₁ (regs.set (logLeafReg q₀) (regs.getD (logLeafReg q₀) 0 + 1))) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .inc (logLeafReg q₀) (P ++ [1]) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 h49 h70]
    simp [hinc]
  let r₀ := regs.set (logLeafReg q₀) (regs.getD (logLeafReg q₀) 0 + 1)
  have hstep0 : zfReg11Step ⟨trimZeros P, regs⟩ = some ⟨P ++ [1], r₀⟩ :=
    zfReg11Step_of_inc hev0
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 r₀ (by simp [r₀, hlen])
  rw [trimZeros_append_one, retStack_append_one] at hsteps₁
  exact ⟨s₁ + 1, by omega, step_zfReg11NSteps hstep0 hsteps₁, hlen₁⟩

/-! ## Section 4: Register Bank Arithmetic Helpers & Parametric Loop Lemmas -/

theorem getD_set_self (regs : List ℕ) (r v : ℕ) (hr : r < regs.length) :
    (regs.set r v).getD r 0 = v := by
  simp [List.getD_eq_getElem?_getD, hr]

theorem getD_set_ne (regs : List ℕ) {r₁ r₂ : ℕ} (v : ℕ) (hne : r₁ ≠ r₂) :
    (regs.set r₁ v).getD r₂ 0 = regs.getD r₂ 0 := by
  simp [List.getD_eq_getElem?_getD, hne]

theorem set_getD_self (regs : List ℕ) (r : ℕ) :
    regs.set r (regs.getD r 0) = regs := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    rw [List.getElem_set]
    split_ifs with heq
    · subst heq
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    · rfl

theorem set_eq_self_of_getD_eq {regs : List ℕ} {r v : ℕ} (h : regs.getD r 0 = v) :
    regs.set r v = regs := by
  rw [← h, set_getD_self]

theorem set_comm_of_ne (regs : List ℕ) {r₁ r₂ : ℕ} (v₁ v₂ : ℕ) (hne : r₁ ≠ r₂) :
    (regs.set r₁ v₁).set r₂ v₂ = (regs.set r₂ v₂).set r₁ v₁ :=
  List.set_comm v₁ v₂ hne

/-- Parametric `while_decnz(r, ())` loop: clears register `r` to `0`.
Covers states `342, 346, 352, 356, 359, 376, 381, 382`. -/
theorem subEval_while_clear {q q_dec : Fin 393} (r : ℕ) (hr : r < 11)
    (htr0 : zf393Trans q 0 = some (0, .right, q_dec))
    (h49 : 29 ≤ q_dec.val) (h70 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr : logLeafReg q_dec = r)
    (htr1 : zf393Trans q 1 = some (0, .left, 64)) :
    SubEval q (fun regs => regs.set r 0) := by
  intro P hP
  have hev0 : evalStack (trimZeros P) = .decnz r (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 h49 h70]
    simp [hdec, hlr]
  have hev1 : evalStack (P ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (k := 0) (by omega) hP htr1
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD r 0 = v →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ = some ⟨retStack P, regs.set r 0⟩ ∧
        (regs.set r 0).length = 11 := by
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      have hstep := zfReg11Step_of_decnz_zero hev0 hv
      rw [set_eq_self_of_getD_eq hv]
      exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
    | succ v ih =>
      intro regs hlen hv
      have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
      have hstep2 := zfReg11Step_of_jump (regs := regs.set r v) hev1
      have hlen' : (regs.set r v).length = 11 := by simp [hlen]
      have hv' : (regs.set r v).getD r 0 = v := getD_set_self regs r v (by omega)
      obtain ⟨s, hs, hsteps, _⟩ := ih (regs.set r v) hlen' hv'
      rw [List.set_set] at hsteps
      exact ⟨s + 2, by omega,
        step_zfReg11NSteps hstep1 (step_zfReg11NSteps hstep2 hsteps), by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD r 0) regs hlen rfl

/-- Parametric `while_decnz(r₁, 3.<r₂>.inc)` loop: adds `r₁` into `r₂` and zeroes `r₁`.
Covers states `360, 362, 364, 366, 368, 370, 371, 372, 377, 379, 380, 386, 388, 389`. -/
theorem subEval_while_move1 {q q_dec q₁ q_inc : Fin 393} (r₁ r₂ : ℕ)
    (hr₁ : r₁ < 11) (_hr₂ : r₂ < 11) (hne : r₁ ≠ r₂)
    (htr0 : zf393Trans q 0 = some (0, .right, q_dec))
    (hdec49 : 29 ≤ q_dec.val) (hdec70 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr1 : logLeafReg q_dec = r₁)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (htr10 : zf393Trans q₁ 0 = some (0, .right, q_inc))
    (hinc49 : 29 ≤ q_inc.val) (hinc70 : q_inc.val ≤ 50) (hinc : isLeafInc q_inc = true)
    (hlr2 : logLeafReg q_inc = r₂)
    (htr11 : zf393Trans q₁ 1 = some (0, .left, 65)) :
    SubEval q (fun regs => (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + regs.getD r₁ 0)) := by
  intro P hP
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hev0 : evalStack (trimZeros P) = .decnz r₁ (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec49 hdec70]
    simp [hdec, hlr1]
  have hev10 : evalStack (P ++ [1]) = .inc r₂ (P ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hinc49 hinc70
    simpa [hinc, hlr2] using h
  have hev11 : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) (by omega) hP1 htr11
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD r₁ 0 = v →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P, (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)⟩ ∧
        ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)).length = 11 := by
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      have hstep := zfReg11Step_of_decnz_zero hev0 hv
      have hset : (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + 0) = regs := by
        rw [Nat.add_zero, set_eq_self_of_getD_eq hv, set_getD_self]
      rw [hset]
      exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
    | succ v ih =>
      intro regs hlen hv
      let regs₁ := (regs.set r₁ v).set r₂ (regs.getD r₂ 0 + 1)
      have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
      have hstep2 : zfReg11Step ⟨P ++ [1], regs.set r₁ v⟩ = some ⟨P ++ [1] ++ [1], regs₁⟩ := by
        rw [zfReg11Step_of_inc hev10, getD_set_ne _ _ hne]
      have hstep3 := zfReg11Step_of_jump (regs := regs₁) hev11
      have hlen₁ : regs₁.length = 11 := by simp [regs₁, hlen]
      have hv₁ : regs₁.getD r₁ 0 = v := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne.symm, getD_set_self regs r₁ v (by omega)]
      obtain ⟨s, hs, hsteps, _⟩ := ih regs₁ hlen₁ hv₁
      have hregs_eq : (regs₁.set r₁ 0).set r₂ (regs₁.getD r₂ 0 + v) =
          (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + (v + 1)) := by
        have hr₂_get : regs₁.getD r₂ 0 = regs.getD r₂ 0 + 1 :=
          getD_set_self (regs.set r₁ v) r₂ (regs.getD r₂ 0 + 1) (by simp; omega)
        rw [hr₂_get]
        dsimp only [regs₁]
        rw [set_comm_of_ne (regs.set r₁ v) (regs.getD r₂ 0 + 1) 0 hne.symm,
          List.set_set, List.set_set]
        congr 1
        omega
      rw [hregs_eq] at hsteps
      exact ⟨s + 3, by omega,
        step_zfReg11NSteps hstep1 (step_zfReg11NSteps hstep2 (step_zfReg11NSteps hstep3 hsteps)),
        by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD r₁ 0) regs hlen rfl

/-- Parametric `while_decnz(r₁, { inc r₂; inc r₃ })` loop: adds `r₁` into both `r₂` and `r₃`
and zeroes `r₁`. Covers states `343, 351, 347, 348, 355, 353, 354, 357, 358, 373, 383`. -/
theorem subEval_while_move2 {q q_dec q₁ q₂ q_inc1 q_inc2 : Fin 393} (r₁ r₂ r₃ : ℕ)
    (hr₁ : r₁ < 11) (hr₂ : r₂ < 11) (hr₃ : r₃ < 11)
    (hne12 : r₁ ≠ r₂) (hne13 : r₁ ≠ r₃) (hne23 : r₂ ≠ r₃)
    (htr0 : zf393Trans q 0 = some (0, .right, q_dec))
    (hdec49 : 29 ≤ q_dec.val) (hdec70 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr1 : logLeafReg q_dec = r₁)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (htr10 : zf393Trans q₁ 0 = some (0, .right, q₂)) (hq₂ : 69 ≤ q₂.val)
    (htr11 : zf393Trans q₁ 1 = some (0, .left, 65))
    (htr20 : zf393Trans q₂ 0 = some (0, .right, q_inc1))
    (hinc1_49 : 29 ≤ q_inc1.val) (hinc1_70 : q_inc1.val ≤ 50) (hinc1 : isLeafInc q_inc1 = true)
    (hlr2 : logLeafReg q_inc1 = r₂)
    (htr21 : zf393Trans q₂ 1 = some (1, .right, q_inc2))
    (hinc2_49 : 29 ≤ q_inc2.val) (hinc2_70 : q_inc2.val ≤ 50) (hinc2 : isLeafInc q_inc2 = true)
    (hlr3 : logLeafReg q_inc2 = r₃) :
    SubEval q (fun regs =>
      ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + regs.getD r₁ 0)).set
        r₃ (regs.getD r₃ 0 + regs.getD r₁ 0)) := by
  intro P hP
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hP10 : walkInternal 99 (P ++ [1] ++ [0]) = some q₂ := walkInternal_snoc hP1 htr10 hq₂
  have hbody := subEval_inc_inc htr20 hinc1_49 hinc1_70 hinc1 htr21 hinc2_49 hinc2_70 hinc2
  have hev0 : evalStack (trimZeros P) = .decnz r₁ (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec49 hdec70]
    simp [hdec, hlr1]
  have hev11 : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) (by omega) hP1 htr11
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD r₁ 0 = v →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P,
          ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)).set r₃ (regs.getD r₃ 0 + v)⟩ ∧
        (((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)).set
          r₃ (regs.getD r₃ 0 + v)).length = 11 := by
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      have hstep := zfReg11Step_of_decnz_zero hev0 hv
      have hset :
          ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + 0)).set r₃ (regs.getD r₃ 0 + 0) = regs := by
        rw [Nat.add_zero, Nat.add_zero, set_eq_self_of_getD_eq hv, set_getD_self, set_getD_self]
      rw [hset]
      exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
    | succ v ih =>
      intro regs hlen hv
      have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
      obtain ⟨sb, hsb, hsteps_b, hlen_b⟩ :=
        hbody (P ++ [1] ++ [0]) hP10 (regs.set r₁ v) (by simp [hlen])
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero, hlr2, hlr3] at hsteps_b
      let regs₁ := ((regs.set r₁ v).set r₂ (regs.getD r₂ 0 + 1)).set r₃ (regs.getD r₃ 0 + 1)
      have hb_eq : ((regs.set r₁ v).set r₂ ((regs.set r₁ v).getD r₂ 0 + 1)).set
          r₃ (((regs.set r₁ v).set r₂ ((regs.set r₁ v).getD r₂ 0 + 1)).getD r₃ 0 + 1) = regs₁ := by
        dsimp only [regs₁]
        rw [getD_set_ne _ _ hne12, getD_set_ne _ _ hne23, getD_set_ne _ _ hne13]
      dsimp only at hsteps_b
      rw [hb_eq] at hsteps_b
      have hstep3 := zfReg11Step_of_jump (regs := regs₁) hev11
      have hlen₁ : regs₁.length = 11 := by simp [regs₁, hlen]
      have hv₁ : regs₁.getD r₁ 0 = v := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne13.symm, getD_set_ne _ _ hne12.symm,
          getD_set_self regs r₁ v (by omega)]
      obtain ⟨s, hs, hsteps, _⟩ := ih regs₁ hlen₁ hv₁
      have hregs_eq :
          ((regs₁.set r₁ 0).set r₂ (regs₁.getD r₂ 0 + v)).set r₃ (regs₁.getD r₃ 0 + v) =
          ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + (v + 1))).set
            r₃ (regs.getD r₃ 0 + (v + 1)) := by
        have hr₂_get : regs₁.getD r₂ 0 = regs.getD r₂ 0 + 1 := by
          dsimp [regs₁]
          rw [getD_set_ne _ _ hne23.symm,
            getD_set_self (regs.set r₁ v) r₂ (regs.getD r₂ 0 + 1) (by simp; omega)]
        have hr₃_get : regs₁.getD r₃ 0 = regs.getD r₃ 0 + 1 := by
          dsimp [regs₁]
          exact getD_set_self _ r₃ (regs.getD r₃ 0 + 1) (by simp; omega)
        rw [hr₂_get, hr₃_get]
        dsimp only [regs₁]
        rw [set_comm_of_ne _ (regs.getD r₃ 0 + 1) 0 hne13.symm,
          set_comm_of_ne (regs.set r₁ v) (regs.getD r₂ 0 + 1) 0 hne12.symm,
          List.set_set,
          set_comm_of_ne _ (regs.getD r₃ 0 + 1) (regs.getD r₂ 0 + 1 + v) hne23.symm,
          List.set_set, List.set_set]
        have hadd1 : regs.getD r₂ 0 + 1 + v = regs.getD r₂ 0 + (v + 1) := by omega
        have hadd2 : regs.getD r₃ 0 + 1 + v = regs.getD r₃ 0 + (v + 1) := by omega
        rw [hadd1, hadd2]
      rw [hregs_eq] at hsteps
      have hchain1 := step_zfReg11NSteps hstep1 hsteps_b
      have hchain2 := zfReg11NSteps_bind_eq hchain1 (step_zfReg11NSteps hstep3 hsteps)
      exact ⟨(sb + 1) + (s + 1), by omega, hchain2, by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD r₁ 0) regs hlen rfl

/-! ## Section 5: Concrete `while_decnz` Subroutine Instantiations -/

/-- `while_decnz(axiomcode,()).0` (State `342`): clears register `4`. -/
theorem subEval_342 : SubEval 342 (fun regs => regs.set 4 0) :=
  subEval_while_clear 4 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(param1,()).0` (State `346`): clears register `5`. -/
theorem subEval_346 : SubEval 346 (fun regs => regs.set 5 0) :=
  subEval_while_clear 5 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(param2,()).0` (State `352`): clears register `6`. -/
theorem subEval_352 : SubEval 352 (fun regs => regs.set 6 0) :=
  subEval_while_clear 6 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(param3,()).0` (State `356`): clears register `7`. -/
theorem subEval_356 : SubEval 356 (fun regs => regs.set 7 0) :=
  subEval_while_clear 7 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,()).0` (State `359`): clears register `8`. -/
theorem subEval_359 : SubEval 359 (fun regs => regs.set 8 0) :=
  subEval_while_clear 8 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch2,()).0` (State `376`): clears register `9`. -/
theorem subEval_376 : SubEval 376 (fun regs => regs.set 9 0) :=
  subEval_while_clear 9 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch3,()).0` (State `381`): clears register `10`. -/
theorem subEval_381 : SubEval 381 (fun regs => regs.set 10 0) :=
  subEval_while_clear 10 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(topwff,()).0` (State `382`): clears register `2`. -/
theorem subEval_382 : SubEval 382 (fun regs => regs.set 2 0) :=
  subEval_while_clear 2 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.axiomcode.inc).0` (State `360`):
adds register `8` into `4` and zeroes `8`. -/
theorem subEval_360 :
    SubEval 360 (fun regs => (regs.set 8 0).set 4 (regs.getD 4 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 4 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.nextproof.inc).0` (State `362`):
adds register `8` into `1` and zeroes `8`. -/
theorem subEval_362 :
    SubEval 362 (fun regs => (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 1 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.param1.inc).0` (State `364`):
adds register `8` into `5` and zeroes `8`. -/
theorem subEval_364 :
    SubEval 364 (fun regs => (regs.set 8 0).set 5 (regs.getD 5 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 5 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.param2.inc).0` (State `366`):
adds register `8` into `6` and zeroes `8`. -/
theorem subEval_366 :
    SubEval 366 (fun regs => (regs.set 8 0).set 6 (regs.getD 6 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 6 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.param3.inc).0` (State `368`):
adds register `8` into `7` and zeroes `8`. -/
theorem subEval_368 :
    SubEval 368 (fun regs => (regs.set 8 0).set 7 (regs.getD 7 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 7 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.scratch2.inc).0` (State `370`):
adds register `8` into `9` and zeroes `8`. -/
theorem subEval_370 :
    SubEval 370 (fun regs => (regs.set 8 0).set 9 (regs.getD 9 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 9 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.topwff.inc).0` (State `371`):
adds register `8` into `2` and zeroes `8`. -/
theorem subEval_371 :
    SubEval 371 (fun regs => (regs.set 8 0).set 2 (regs.getD 2 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.wffstack.inc).0` (State `372`):
adds register `8` into `3` and zeroes `8`. -/
theorem subEval_372 :
    SubEval 372 (fun regs => (regs.set 8 0).set 3 (regs.getD 3 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 3 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch2,3.prooflist.inc).0` (State `377`):
adds register `9` into `0` and zeroes `9`. -/
theorem subEval_377 :
    SubEval 377 (fun regs => (regs.set 9 0).set 0 (regs.getD 0 0 + regs.getD 9 0)) :=
  subEval_while_move1 9 0 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch2,3.topwff.inc).0` (State `379`):
adds register `9` into `2` and zeroes `9`. -/
theorem subEval_379 :
    SubEval 379 (fun regs => (regs.set 9 0).set 2 (regs.getD 2 0 + regs.getD 9 0)) :=
  subEval_while_move1 9 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch2,3.wffstack.inc).0` (State `380`):
adds register `9` into `3` and zeroes `9`. -/
theorem subEval_380 :
    SubEval 380 (fun regs => (regs.set 9 0).set 3 (regs.getD 3 0 + regs.getD 9 0)) :=
  subEval_while_move1 9 3 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(topwff,3.scratch1.inc).0` (State `386`):
adds register `2` into `8` and zeroes `2`. -/
theorem subEval_386 :
    SubEval 386 (fun regs => (regs.set 2 0).set 8 (regs.getD 8 0 + regs.getD 2 0)) :=
  subEval_while_move1 2 8 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(topwff,3.scratch2.inc).0` (State `388`):
adds register `2` into `9` and zeroes `2`. -/
theorem subEval_388 :
    SubEval 388 (fun regs => (regs.set 2 0).set 9 (regs.getD 9 0 + regs.getD 2 0)) :=
  subEval_while_move1 2 9 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(wffstack,3.topwff.inc).0` (State `389`):
adds register `3` into `2` and zeroes `3`. -/
theorem subEval_389 :
    SubEval 389 (fun regs => (regs.set 3 0).set 2 (regs.getD 2 0 + regs.getD 3 0)) :=
  subEval_while_move1 3 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(nextproof,47).0` (State `343`):
adds register `1` into `8` and `0` and zeroes `1`. -/
theorem subEval_343 :
    SubEval 343 (fun regs =>
      ((regs.set 1 0).set 8 (regs.getD 8 0 + regs.getD 1 0)).set
        0 (regs.getD 0 0 + regs.getD 1 0)) :=
  subEval_while_move2 1 8 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param1,86).0` (State `351`): adds register `5` into `8` and `9` and zeroes `5`. -/
theorem subEval_351 :
    SubEval 351 (fun regs =>
      ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set
        9 (regs.getD 9 0 + regs.getD 5 0)) :=
  subEval_while_move2 5 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param1,42).0` (State `347`): adds register `5` into `2` and `8` and zeroes `5`. -/
theorem subEval_347 :
    SubEval 347 (fun regs =>
      ((regs.set 5 0).set 2 (regs.getD 2 0 + regs.getD 5 0)).set
        8 (regs.getD 8 0 + regs.getD 5 0)) :=
  subEval_while_move2 5 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param1,72).0` (State `348`): adds register `5` into `8` and `2` and zeroes `5`. -/
theorem subEval_348 :
    SubEval 348 (fun regs =>
      ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set
        2 (regs.getD 2 0 + regs.getD 5 0)) :=
  subEval_while_move2 5 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param2,86).0` (State `355`): adds register `6` into `8` and `9` and zeroes `6`. -/
theorem subEval_355 :
    SubEval 355 (fun regs =>
      ((regs.set 6 0).set 8 (regs.getD 8 0 + regs.getD 6 0)).set
        9 (regs.getD 9 0 + regs.getD 6 0)) :=
  subEval_while_move2 6 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param2,42).0` (State `353`): adds register `6` into `2` and `8` and zeroes `6`. -/
theorem subEval_353 :
    SubEval 353 (fun regs =>
      ((regs.set 6 0).set 2 (regs.getD 2 0 + regs.getD 6 0)).set
        8 (regs.getD 8 0 + regs.getD 6 0)) :=
  subEval_while_move2 6 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param2,69).0` (State `354`): adds register `6` into `8` and `10` and zeroes `6`. -/
theorem subEval_354 :
    SubEval 354 (fun regs =>
      ((regs.set 6 0).set 8 (regs.getD 8 0 + regs.getD 6 0)).set
        10 (regs.getD 10 0 + regs.getD 6 0)) :=
  subEval_while_move2 6 8 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param3,42).0` (State `357`): adds register `7` into `2` and `8` and zeroes `7`. -/
theorem subEval_357 :
    SubEval 357 (fun regs =>
      ((regs.set 7 0).set 2 (regs.getD 2 0 + regs.getD 7 0)).set
        8 (regs.getD 8 0 + regs.getD 7 0)) :=
  subEval_while_move2 7 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param3,69).0` (State `358`): adds register `7` into `8` and `10` and zeroes `7`. -/
theorem subEval_358 :
    SubEval 358 (fun regs =>
      ((regs.set 7 0).set 8 (regs.getD 8 0 + regs.getD 7 0)).set
        10 (regs.getD 10 0 + regs.getD 7 0)) :=
  subEval_while_move2 7 8 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(scratch1,9).0` (State `373`):
adds register `8` into `2` and `9` and zeroes `8`. -/
theorem subEval_373 :
    SubEval 373 (fun regs =>
      ((regs.set 8 0).set 2 (regs.getD 2 0 + regs.getD 8 0)).set
        9 (regs.getD 9 0 + regs.getD 8 0)) :=
  subEval_while_move2 8 2 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(topwff,21).0` (State `383`):
adds register `2` into `3` and `8` and zeroes `2`. -/
theorem subEval_383 :
    SubEval 383 (fun regs =>
      ((regs.set 2 0).set 3 (regs.getD 3 0 + regs.getD 2 0)).set
        8 (regs.getD 8 0 + regs.getD 2 0)) :=
  subEval_while_move2 2 3 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-! ## Section 1: Cantor Pairing Subroutines (`290..297`) -/

/-- Inner body `293` of `pair(scratch1, topwff, wffstack)`:
increments `scratch1` (`8`) and moves `wffstack` (`3`) into `topwff` (`2`). -/
theorem subEval_293 :
    SubEval 293 (fun regs =>
      let r₀ := regs.set 8 (regs.getD 8 0 + 1)
      (r₀.set 3 0).set 2 (r₀.getD 2 0 + r₀.getD 3 0)) :=
  subEval_inc_seq (q₀ := 42) rfl (by decide) (by decide) rfl rfl (by decide) subEval_389

/-- Inner body `297` of `pair(scratch2, scratch1, topwff)`:
increments `scratch2` (`9`) and moves `topwff` (`2`) into `scratch1` (`8`). -/
theorem subEval_297 :
    SubEval 297 (fun regs =>
      let r₀ := regs.set 9 (regs.getD 9 0 + 1)
      (r₀.set 2 0).set 8 (r₀.getD 8 0 + r₀.getD 2 0)) :=
  subEval_inc_seq (q₀ := 44) rfl (by decide) (by decide) rfl rfl (by decide) subEval_386

/-- Parametric Cantor pairing subroutine `pair(out, r1, r2)` covering states `290` and `294`. -/
theorem subEval_pair {q q_move2 q1 q_dec q2 q3 : Fin 393} (out r1 r2 : ℕ)
    (hout : out < 11) (hr1 : r1 < 11) (hr2 : r2 < 11)
    (hne12 : r1 ≠ r2) (hne1o : r1 ≠ out) (hne2o : r2 ≠ out)
    (htr0 : zf393Trans q 0 = some (0, .right, q_move2)) (hq_move2 : 69 ≤ q_move2.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q1)) (hq1 : 69 ≤ q1.val)
    (htr10 : zf393Trans q1 0 = some (0, .right, q_dec))
    (hdec49 : 29 ≤ q_dec.val) (hdec70 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr_dec : logLeafReg q_dec = r2)
    (htr11 : zf393Trans q1 1 = some (1, .right, q2)) (hq2 : 69 ≤ q2.val)
    (htr20 : zf393Trans q2 0 = some (0, .right, q3)) (hq3 : 69 ≤ q3.val)
    (htr21 : zf393Trans q2 1 = some (0, .left, 66))
    (hmove2 : SubEval q_move2 (fun regs =>
      ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)))
    (hbody : SubEval q3 (fun regs =>
      let r₀ := regs.set out (regs.getD out 0 + 1)
      (r₀.set r2 0).set r1 (r₀.getD r1 0 + r₀.getD r2 0))) :
    SubEval q (regPairOp out r1 r2) := by
  intro P hP
  have hP0 : walkInternal 99 (P ++ [0]) = some q_move2 := walkInternal_snoc hP htr0 hq_move2
  have hP1 : walkInternal 99 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  have hP11 : walkInternal 99 (P ++ [1] ++ [1]) = some q2 := walkInternal_snoc hP1 htr11 hq2
  have hP110 : walkInternal 99 (P ++ [1] ++ [1] ++ [0]) = some q3 :=
    walkInternal_snoc hP11 htr20 hq3
  have hev10 : evalStack (P ++ [1]) = .decnz r2 (P ++ [1] ++ [1]) (retStack P) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hdec49 hdec70
    simpa [hdec, hlr_dec] using h
  have hev21 : evalStack (P ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h :=
      evalStack_continue1_of_walkInternal (P := P ++ [1] ++ [1]) (k := 2) (by omega) hP11 htr21
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (n : ℕ) (regs : List ℕ), regs.length = 11 →
      regs.getD r1 0 + regs.getD r2 0 = n →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P,
          ((regs.set r1 0).set r2 0).set out (triLoop n (regs.getD out 0 + regs.getD r1 0))⟩ ∧
        (((regs.set r1 0).set r2 0).set
          out (triLoop n (regs.getD out 0 + regs.getD r1 0))).length = 11 := by
    intro n
    induction n with
    | zero =>
      intro regs hlen hn
      obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := hmove2 (P ++ [0]) hP0 regs hlen
      rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
      dsimp only at hsteps₀
      let regs₁ := ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)
      change zfReg11NSteps s₀ ⟨trimZeros P, regs⟩ = some ⟨P ++ [1], regs₁⟩ at hsteps₀
      have hr2_zero : regs₁.getD r2 0 = 0 := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne2o.symm,
          getD_set_self _ r2 (regs.getD r2 0 + regs.getD r1 0) (by simp; omega)]
        omega
      have hstep1 := zfReg11Step_of_decnz_zero (regs := regs₁) hev10 hr2_zero
      have hregs_eq : regs₁ =
          ((regs.set r1 0).set r2 0).set out (triLoop 0 (regs.getD out 0 + regs.getD r1 0)) := by
        dsimp [regs₁, triLoop]
        have hsum : regs.getD r2 0 + regs.getD r1 0 = 0 := by omega
        rw [hsum]
      rw [hregs_eq] at hsteps₀ hstep1
      exact ⟨s₀ + 1, by omega, zfReg11NSteps_bind_eq hsteps₀ (zfReg11Step_one hstep1),
        by simp [hlen]⟩
    | succ m ih =>
      intro regs hlen hn
      obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := hmove2 (P ++ [0]) hP0 regs hlen
      rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
      dsimp only at hsteps₀
      let regs₁ := ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)
      change zfReg11NSteps s₀ ⟨trimZeros P, regs⟩ = some ⟨P ++ [1], regs₁⟩ at hsteps₀
      have hr2_succ : regs₁.getD r2 0 = m + 1 := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne2o.symm,
          getD_set_self _ r2 (regs.getD r2 0 + regs.getD r1 0) (by simp; omega)]
        omega
      have hstep1 := zfReg11Step_of_decnz_succ (regs := regs₁) hev10 hr2_succ
      obtain ⟨s₃, hs₃, hsteps₃, hlen₃⟩ :=
        hbody (P ++ [1] ++ [1] ++ [0]) hP110 (regs₁.set r2 m) (by simp [regs₁, hlen])
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps₃
      dsimp only at hsteps₃
      let regs₂ := ((regs.set r1 m).set r2 0).set out (regs.getD out 0 + regs.getD r1 0 + 1)
      have hbody_eq :
          (let r₀ := (regs₁.set r2 m).set out ((regs₁.set r2 m).getD out 0 + 1)
           (r₀.set r2 0).set r1 (r₀.getD r1 0 + r₀.getD r2 0)) = regs₂ := by
        dsimp only [regs₁, regs₂]
        have hout_get :
            ((((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
              out (regs.getD out 0 + regs.getD r1 0)).set r2 m).getD out 0 =
            regs.getD out 0 + regs.getD r1 0 := by
          rw [getD_set_ne _ _ hne2o,
            getD_set_self _ out (regs.getD out 0 + regs.getD r1 0) (by simp; omega)]
        rw [hout_get]
        have hr0_eq :
            ((((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
              out (regs.getD out 0 + regs.getD r1 0)).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1) =
            ((regs.set r1 0).set r2 m).set out (regs.getD out 0 + regs.getD r1 0 + 1) := by
          rw [set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0) m hne2o.symm,
            List.set_set, List.set_set]
        rw [hr0_eq]
        have hr1_get :
            (((regs.set r1 0).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1)).getD r1 0 = 0 := by
          rw [getD_set_ne _ _ hne1o.symm, getD_set_ne _ _ hne12.symm,
            getD_set_self regs r1 0 (by omega)]
        have hr2_get :
            (((regs.set r1 0).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1)).getD r2 0 = m := by
          rw [getD_set_ne _ _ hne2o.symm, getD_set_self _ r2 m (by simp; omega)]
        rw [hr1_get, hr2_get, Nat.zero_add]
        rw [set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne2o.symm,
          List.set_set,
          set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) m hne1o.symm,
          set_comm_of_ne (regs.set r1 0) 0 m hne12.symm,
          List.set_set]
      rw [hbody_eq] at hsteps₃
      have hstep_jmp := zfReg11Step_of_jump (regs := regs₂) hev21
      have hlen₂ : regs₂.length = 11 := by simp [regs₂, hlen]
      have hr1_₂ : regs₂.getD r1 0 = m := by
        dsimp [regs₂]
        rw [getD_set_ne _ _ hne1o.symm, getD_set_ne _ _ hne12.symm,
          getD_set_self regs r1 m (by omega)]
      have hr2_₂ : regs₂.getD r2 0 = 0 := by
        dsimp [regs₂]
        rw [getD_set_ne _ _ hne2o.symm, getD_set_self _ r2 0 (by simp; omega)]
      have hout_₂ : regs₂.getD out 0 = regs.getD out 0 + regs.getD r1 0 + 1 := by
        dsimp [regs₂]
        exact getD_set_self _ out (regs.getD out 0 + regs.getD r1 0 + 1) (by simp; omega)
      obtain ⟨s_ih, hs_ih, hsteps_ih, _⟩ := ih regs₂ hlen₂ (by omega)
      have hfinal_eq :
          ((regs₂.set r1 0).set r2 0).set out (triLoop m (regs₂.getD out 0 + regs₂.getD r1 0)) =
          ((regs.set r1 0).set r2 0).set
            out (triLoop (m + 1) (regs.getD out 0 + regs.getD r1 0)) := by
        rw [hout_₂, hr1_₂]
        have htri : triLoop m (regs.getD out 0 + regs.getD r1 0 + 1 + m) =
            triLoop (m + 1) (regs.getD out 0 + regs.getD r1 0) := by
          simp only [triLoop]
          congr 1
          omega
        rw [htri]
        dsimp only [regs₂]
        rw [set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne1o.symm,
          set_comm_of_ne (regs.set r1 m) 0 0 hne12.symm,
          List.set_set,
          set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne2o.symm,
          List.set_set, List.set_set]
      rw [hfinal_eq] at hsteps_ih
      have hchain1 := zfReg11NSteps_bind_eq hsteps₀ (step_zfReg11NSteps hstep1 hsteps₃)
      have hchain2 := zfReg11NSteps_bind_eq hchain1 (step_zfReg11NSteps hstep_jmp hsteps_ih)
      exact ⟨(s₀ + (s₃ + 1)) + (s_ih + 1), by omega, hchain2, by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD r1 0 + regs.getD r2 0) regs hlen rfl

/-- `pair(scratch1, topwff, wffstack).0` (State `290`): Cantor-pairs `2` and `3` into `8`. -/
theorem subEval_290 : SubEval 290 (regPairOp 8 2 3) :=
  subEval_pair 8 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl subEval_383 subEval_293

/-- `pair(scratch2, scratch1, topwff).0` (State `294`): Cantor-pairs `8` and `2` into `9`. -/
theorem subEval_294 : SubEval 294 (regPairOp 9 8 2) :=
  subEval_pair 9 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl subEval_373 subEval_297

/-! ## Section 2: Cantor Unpairing Subroutines (`309..318`) -/

/-- General functional specification of `unpair(out1, out2, rin)` on an 11-register bank `regs`
for arbitrary initial values of `out1` and `out2`. -/
def regUnpairGen (out1 out2 rin : ℕ) (regs : List ℕ) : List ℕ :=
  let p := unpairLoop (regs.getD rin 0) (regs.getD out1 0, regs.getD out2 0)
  ((regs.set rin 0).set out1 p.1).set out2 p.2

theorem regUnpairGen_eq_regUnpairOp {out1 out2 rin : ℕ} {regs : List ℕ}
    (h1 : regs.getD out1 0 = 0) (h2 : regs.getD out2 0 = 0) :
    regUnpairGen out1 out2 rin regs = regUnpairOp out1 out2 rin regs := by
  unfold regUnpairGen regUnpairOp
  rw [h1, h2]

/-- Parametric Cantor unpairing subroutine `unpair(out1, 9, rin)` covering states
`313, 314, 315`. -/
theorem subEval_unpair {q q_dec q1 q_inc1 q2 q3 q_move : Fin 393} (out1 rin : ℕ)
    (hout1 : out1 < 11) (hrin : rin < 11)
    (hne_in_1 : rin ≠ out1) (hne_in_9 : rin ≠ 9) (hne_1_9 : out1 ≠ 9)
    (htr0 : zf393Trans q 0 = some (0, .right, q_dec))
    (hdec49 : 29 ≤ q_dec.val) (hdec70 : q_dec.val ≤ 50) (hdec : isLeafInc q_dec = false)
    (hlr_dec : logLeafReg q_dec = rin)
    (htr1 : zf393Trans q 1 = some (1, .right, q1)) (hq1 : 69 ≤ q1.val)
    (htr10 : zf393Trans q1 0 = some (0, .right, q_inc1))
    (hinc49 : 29 ≤ q_inc1.val) (hinc70 : q_inc1.val ≤ 50) (hinc : isLeafInc q_inc1 = true)
    (hlr_inc : logLeafReg q_inc1 = out1)
    (htr11 : zf393Trans q1 1 = some (1, .right, q2)) (hq2 : 69 ≤ q2.val)
    (htr20 : zf393Trans q2 0 = some (0, .right, 309))
    (htr21 : zf393Trans q2 1 = some (1, .right, q3)) (hq3 : 69 ≤ q3.val)
    (htr30 : zf393Trans q3 0 = some (0, .right, q_move)) (hq_move : 69 ≤ q_move.val)
    (htr31 : zf393Trans q3 1 = some (0, .left, 67))
    (hmove : SubEval q_move (fun regs =>
      (regs.set out1 0).set 9 (regs.getD 9 0 + regs.getD out1 0))) :
    SubEval q (regUnpairGen out1 9 rin) := by
  intro P hP
  have hP1 : walkInternal 99 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  have hP11 : walkInternal 99 (P ++ [1] ++ [1]) = some q2 := walkInternal_snoc hP1 htr11 hq2
  have hP110 : walkInternal 99 (P ++ [1] ++ [1] ++ [0]) = some 309 :=
    walkInternal_snoc hP11 htr20 (by decide)
  have hP111 : walkInternal 99 (P ++ [1] ++ [1] ++ [1]) = some q3 :=
    walkInternal_snoc hP11 htr21 hq3
  have hP1110 : walkInternal 99 (P ++ [1] ++ [1] ++ [1] ++ [0]) = some q_move :=
    walkInternal_snoc hP111 htr30 hq_move
  have hev0 : evalStack (trimZeros P) = .decnz rin (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec49 hdec70]
    simp [hdec, hlr_dec]
  have hev10 : evalStack (P ++ [1]) = .inc out1 (P ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hinc49 hinc70
    simpa [hinc, hlr_inc] using h
  have hev11 : evalStack (P ++ [1] ++ [1]) =
      .decnz 9 (P ++ [1] ++ [1] ++ [0] ++ [1]) (P ++ [1] ++ [1] ++ [1]) := by
    have htrim := evalStack_trimZeros_of_walkInternal hP110
    rw [trimZeros_append_zero, trimZeros_append_one] at htrim
    have hleaf := evalStack_leaf0_of_walkInternal (q' := 43) hP110 rfl (by decide) (by decide)
    rw [htrim, hleaf, retStack_append_zero]
    rfl
  have hev1101 : evalStack (P ++ [1] ++ [1] ++ [0] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal
      (P := P ++ [1] ++ [1] ++ [0]) (k := 2) (by omega) hP110 rfl
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hev1111 : evalStack (P ++ [1] ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal
      (P := P ++ [1] ++ [1] ++ [1]) (k := 3) (by omega) hP111 htr31
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (z : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD rin 0 = z →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P, regUnpairGen out1 9 rin regs⟩ ∧
        (regUnpairGen out1 9 rin regs).length = 11 := by
    intro z
    induction z with
    | zero =>
      intro regs hlen hz
      have hstep := zfReg11Step_of_decnz_zero hev0 hz
      have hset : regUnpairGen out1 9 rin regs = regs := by
        unfold regUnpairGen
        rw [hz]
        dsimp [unpairLoop]
        rw [set_eq_self_of_getD_eq hz, set_getD_self, set_getD_self]
      rw [hset]
      exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
    | succ z ih =>
      intro regs hlen hz
      have hstep1 := zfReg11Step_of_decnz_succ hev0 hz
      let regs₁ := (regs.set rin z).set out1 (regs.getD out1 0 + 1)
      have hstep2 : zfReg11Step ⟨P ++ [1], regs.set rin z⟩ = some ⟨P ++ [1] ++ [1], regs₁⟩ := by
        rw [zfReg11Step_of_inc hev10, getD_set_ne _ _ hne_in_1]
      have hr9_₁ : regs₁.getD 9 0 = regs.getD 9 0 := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne_1_9, getD_set_ne _ _ hne_in_9]
      rcases hy : regs.getD 9 0 with _ | y
      · -- Case `regs.getD 9 0 = 0`
        have hstep3 := zfReg11Step_of_decnz_zero (regs := regs₁) hev11 (by rw [hr9_₁, hy])
        obtain ⟨sm, hsm, hsteps_m, _⟩ :=
          hmove (P ++ [1] ++ [1] ++ [1] ++ [0]) hP1110 regs₁ (by simp [regs₁, hlen])
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_m
        dsimp only at hsteps_m
        let regs₂ := ((regs.set rin z).set out1 0).set 9 (regs.getD out1 0 + 1)
        have hm_eq :
            (regs₁.set out1 0).set 9 (regs₁.getD 9 0 + regs₁.getD out1 0) = regs₂ := by
          rw [hr9_₁, hy, Nat.zero_add]
          dsimp [regs₁, regs₂]
          have hout1_get : ((regs.set rin z).set out1 (regs.getD out1 0 + 1)).getD out1 0 =
              regs.getD out1 0 + 1 :=
            getD_set_self _ out1 (regs.getD out1 0 + 1) (by simp; omega)
          rw [hout1_get, List.set_set]
        rw [hm_eq] at hsteps_m
        have hstep_jmp := zfReg11Step_of_jump (regs := regs₂) hev1111
        have hlen₂ : regs₂.length = 11 := by simp [regs₂, hlen]
        have hrin_₂ : regs₂.getD rin 0 = z := by
          dsimp [regs₂]
          rw [getD_set_ne _ _ hne_in_9.symm, getD_set_ne _ _ hne_in_1.symm,
            getD_set_self regs rin z (by omega)]
        obtain ⟨s_ih, hs_ih, hsteps_ih, _⟩ := ih regs₂ hlen₂ hrin_₂
        have hgen_eq : regUnpairGen out1 9 rin regs₂ = regUnpairGen out1 9 rin regs := by
          unfold regUnpairGen
          have hout1_₂ : regs₂.getD out1 0 = 0 := by
            dsimp [regs₂]
            rw [getD_set_ne _ _ hne_1_9.symm, getD_set_self _ out1 0 (by simp; omega)]
          have hr9_₂ : regs₂.getD 9 0 = regs.getD out1 0 + 1 := by
            dsimp [regs₂]
            exact getD_set_self _ 9 (regs.getD out1 0 + 1) (by simp; omega)
          have hloop_step :
              unpairLoop (z + 1) (regs.getD out1 0, 0) = unpairLoop z (0, regs.getD out1 0 + 1) :=
            rfl
          rw [hrin_₂, hout1_₂, hr9_₂, hz, hy, hloop_step]
          dsimp only [regs₂]
          rw [set_comm_of_ne _ (regs.getD out1 0 + 1) 0 hne_in_9.symm,
            set_comm_of_ne (regs.set rin z) 0 0 hne_in_1.symm,
            List.set_set,
            set_comm_of_ne _ (regs.getD out1 0 + 1) _ hne_1_9.symm,
            List.set_set, List.set_set]
        rw [hgen_eq] at hsteps_ih
        have hchain1 := step_zfReg11NSteps hstep1 (step_zfReg11NSteps hstep2
          (step_zfReg11NSteps hstep3 hsteps_m))
        have hchain2 := zfReg11NSteps_bind_eq hchain1 (step_zfReg11NSteps hstep_jmp hsteps_ih)
        exact ⟨(sm + 3) + (s_ih + 1), by omega, hchain2, by simp [regUnpairGen, hlen]⟩
      · -- Case `regs.getD 9 0 = y + 1`
        have hstep3 := zfReg11Step_of_decnz_succ (regs := regs₁) hev11 (by rw [hr9_₁, hy])
        let regs₂ := regs₁.set 9 y
        have hstep_jmp := zfReg11Step_of_jump (regs := regs₂) hev1101
        have hlen₂ : regs₂.length = 11 := by simp [regs₂, regs₁, hlen]
        have hrin_₂ : regs₂.getD rin 0 = z := by
          dsimp [regs₂, regs₁]
          rw [getD_set_ne _ _ hne_in_9.symm, getD_set_ne _ _ hne_in_1.symm,
            getD_set_self regs rin z (by omega)]
        obtain ⟨s_ih, hs_ih, hsteps_ih, _⟩ := ih regs₂ hlen₂ hrin_₂
        have hgen_eq : regUnpairGen out1 9 rin regs₂ = regUnpairGen out1 9 rin regs := by
          unfold regUnpairGen
          have hout1_₂ : regs₂.getD out1 0 = regs.getD out1 0 + 1 := by
            dsimp [regs₂, regs₁]
            rw [getD_set_ne _ _ hne_1_9.symm,
              getD_set_self _ out1 (regs.getD out1 0 + 1) (by simp; omega)]
          have hr9_₂ : regs₂.getD 9 0 = y := by
            dsimp [regs₂, regs₁]
            exact getD_set_self _ 9 y (by simp; omega)
          have hloop_step :
              unpairLoop (z + 1) (regs.getD out1 0, y + 1) =
              unpairLoop z (regs.getD out1 0 + 1, y) := rfl
          rw [hrin_₂, hout1_₂, hr9_₂, hz, hy, hloop_step]
          dsimp only [regs₂, regs₁]
          rw [set_comm_of_ne _ y 0 hne_in_9.symm,
            set_comm_of_ne (regs.set rin z) (regs.getD out1 0 + 1) 0 hne_in_1.symm,
            List.set_set,
            set_comm_of_ne _ y _ hne_1_9.symm,
            List.set_set, List.set_set]
        rw [hgen_eq] at hsteps_ih
        have hchain := step_zfReg11NSteps hstep1 (step_zfReg11NSteps hstep2
          (step_zfReg11NSteps hstep3 (step_zfReg11NSteps hstep_jmp hsteps_ih)))
        exact ⟨s_ih + 4, by omega, hchain, by simp [regUnpairGen, hlen]⟩
  intro regs hlen
  exact hloop (regs.getD rin 0) regs hlen rfl

/-- `unpair(scratch1, scratch2, prooflist).0` (State `313`): unpairs `0` into `8` and `9`. -/
theorem subEval_313 : SubEval 313 (regUnpairGen 8 9 0) :=
  subEval_unpair 8 0 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl subEval_370

/-- `unpair(scratch1, scratch2, wffstack).0` (State `314`): unpairs `3` into `8` and `9`. -/
theorem subEval_314 : SubEval 314 (regUnpairGen 8 9 3) :=
  subEval_unpair 8 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl subEval_370

/-- `unpair(topwff, scratch2, wffstack).0` (State `315`): unpairs `3` into `2` and `9`. -/
theorem subEval_315 : SubEval 315 (regUnpairGen 2 9 3) :=
  subEval_unpair 2 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl subEval_388

/-! ## Section 3: Composite RPN Formula Subroutines -/

/-- Register-bank operation of `main().n_149.0` (State `269`). -/
def reg269Op (regs : List ℕ) : List ℕ :=
  let r := regUnpairGen 8 9 0 regs
  (r.set 9 0).set 0 (r.getD 0 0 + r.getD 9 0)

/-- `main().n_149.0` (State `269`): unpairs `prooflist` (`0`) into `scratch1` (`8`) and
`prooflist` (`0`) via `scratch2` (`9`). -/
theorem subEval_269 : SubEval 269 reg269Op := by
  unfold reg269Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_313 subEval_377

/-- Register-bank operation of `n_165.0` (State `289`). -/
def reg289Op (regs : List ℕ) : List ℕ :=
  let r := regUnpairGen 8 9 3 regs
  (r.set 9 0).set 3 (r.getD 3 0 + r.getD 9 0)

/-- `n_165.0` (State `289`): unpairs `wffstack` (`3`) into `scratch1` (`8`) and
`wffstack` (`3`) via `scratch2` (`9`). -/
theorem subEval_289 : SubEval 289 reg289Op := by
  unfold reg289Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_314 subEval_380

/-- Register-bank operation of `cons().1` (State `70`). -/
def reg70Op (regs : List ℕ) : List ℕ :=
  let r := regPairOp 9 8 2 regs
  (r.set 9 0).set 2 (r.getD 2 0 + r.getD 9 0)

/-- `cons().1` (State `70`): pairs `scratch1` (`8`) and `topwff` (`2`) into `topwff` (`2`)
via `scratch2` (`9`). -/
theorem subEval_70 : SubEval 70 reg70Op := by
  unfold reg70Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_294 subEval_379

/-- Register-bank operation of `cons()` (State `69`). -/
def regConsOp (regs : List ℕ) : List ℕ :=
  reg70Op (reg289Op regs)

/-- `cons().0` (State `69`): pops from `wffstack` (`3`) into `scratch1` (`8`) and pairs with
`topwff` (`2`). -/
theorem subEval_69 : SubEval 69 regConsOp := by
  unfold regConsOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_289 subEval_70

/-- Register-bank operation of `pushwff()` (State `304`). -/
def regPushwffOp (regs : List ℕ) : List ℕ :=
  let r := regPairOp 8 2 3 regs
  (r.set 8 0).set 3 (r.getD 3 0 + r.getD 8 0)

/-- `pushwff().0` (State `304`): pairs `topwff` (`2`) and `wffstack` (`3`) into `wffstack` (`3`)
and zeroes `topwff` (`2`). -/
theorem subEval_304 : SubEval 304 regPushwffOp := by
  unfold regPushwffOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_290 subEval_372

/-- Register-bank operation of `v_1_()` (State `319`). -/
def regV1Op (regs : List ℕ) : List ℕ :=
  let r := regPushwffOp regs
  r.set 2 (r.getD 2 0 + 1)

/-- `v_1_().0` (State `319`): `pushwff(); inc topwff`. -/
theorem subEval_319 : SubEval 319 regV1Op := by
  unfold regV1Op
  exact subEval_seq_inc (q₁ := 48) rfl (by decide) rfl (by decide) (by decide) rfl subEval_304

theorem subEval_288 :
    SubEval 288 (fun regs => regs.set 2 (regs.getD 2 0 + 2)) := by
  refine (subEval_inc_inc rfl (by decide) (by decide) rfl
    rfl (by decide) (by decide) rfl).congr ?_
  intro regs hlen
  change (regs.set 2 (regs.getD 2 0 + 1)).set 2
    ((regs.set 2 (regs.getD 2 0 + 1)).getD 2 0 + 1) = regs.set 2 (regs.getD 2 0 + 2)
  rw [getD_set_self regs 2 (regs.getD 2 0 + 1) (by omega), List.set_set]

def regV2Op (regs : List ℕ) : List ℕ :=
  let r := regV1Op regs
  r.set 2 (r.getD 2 0 + 1)

theorem subEval_320 : SubEval 320 regV2Op := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_304 subEval_288).congr ?_
  intro regs hlen
  dsimp only [regV2Op, regV1Op]
  have hlen0 : 2 < (regPushwffOp regs).length := by simp [regPushwffOp, regPairOp, hlen]
  rw [getD_set_self (regPushwffOp regs) 2 ((regPushwffOp regs).getD 2 0 + 1) hlen0, List.set_set]

def regV3Op (regs : List ℕ) : List ℕ :=
  let r := regV2Op regs
  r.set 2 (r.getD 2 0 + 1)

theorem subEval_321 : SubEval 321 regV3Op := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_319 subEval_288).congr ?_
  intro regs hlen
  dsimp only [regV3Op, regV2Op]
  have hlen1 : 2 < (regV1Op regs).length := by simp [regV1Op, regPushwffOp, regPairOp, hlen]
  rw [getD_set_self (regV1Op regs) 2 ((regV1Op regs).getD 2 0 + 1) hlen1, List.set_set]

def regV4Op (regs : List ℕ) : List ℕ :=
  let r := regV3Op regs
  r.set 2 (r.getD 2 0 + 1)

theorem subEval_322 : SubEval 322 regV4Op := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_320 subEval_288).congr ?_
  intro regs hlen
  dsimp only [regV4Op, regV3Op]
  have hlen2 : 2 < (regV2Op regs).length := by
    simp [regV2Op, regV1Op, regPushwffOp, regPairOp, hlen]
  rw [getD_set_self (regV2Op regs) 2 ((regV2Op regs).getD 2 0 + 1) hlen2, List.set_set]

/-- Register-bank operation of `weq().1` (State `330`). -/
def reg330Op (regs : List ℕ) : List ℕ :=
  regConsOp (regPushwffOp regs)

/-- `weq().1` (State `330`): `pushwff(); cons()`. -/
theorem subEval_330 : SubEval 330 reg330Op := by
  unfold reg330Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_304 subEval_69

/-- Register-bank operation of `weq()` (State `329`). -/
def regWeqOp (regs : List ℕ) : List ℕ :=
  reg330Op (regConsOp regs)

/-- `weq().0` (State `329`): `cons(); pushwff(); cons()`. -/
theorem subEval_329 : SubEval 329 regWeqOp := by
  unfold regWeqOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_69 subEval_330

/-- Register-bank operation of `wel().1` (State `328`). -/
def reg328Op (regs : List ℕ) : List ℕ :=
  regConsOp (regV1Op regs)

/-- `wel().1` (State `328`): `v_1_(); cons()`. -/
theorem subEval_328 : SubEval 328 reg328Op := by
  unfold reg328Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_319 subEval_69

/-- Register-bank operation of `wel()` (State `327`). -/
def regWelOp (regs : List ℕ) : List ℕ :=
  reg328Op (regConsOp regs)

/-- `wel().0` (State `327`): `cons(); v_1_(); cons()`. -/
theorem subEval_327 : SubEval 327 regWelOp := by
  unfold regWelOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_69 subEval_328

/-- Register-bank operation of `wim().1` (State `391`). -/
def reg391Op (regs : List ℕ) : List ℕ :=
  regConsOp (regV2Op regs)

/-- `wim().1` (State `391`): `v_2_(); cons()`. -/
theorem subEval_391 : SubEval 391 reg391Op := by
  unfold reg391Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_320 subEval_69

/-- Register-bank operation of `wim()` (State `390`). -/
def regWimOp (regs : List ℕ) : List ℕ :=
  reg391Op (regConsOp regs)

/-- `wim().0` (State `390`): `cons(); v_2_(); cons()`. -/
theorem subEval_390 : SubEval 390 regWimOp := by
  unfold regWimOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_69 subEval_391

/-- Register-bank operation of `wn()` (State `392`). -/
def regWnOp (regs : List ℕ) : List ℕ :=
  regConsOp (regV3Op regs)

/-- `wn().0` (State `392`): `v_3_(); cons()`. -/
theorem subEval_392 : SubEval 392 regWnOp := by
  unfold regWnOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_321 subEval_69

/-- Register-bank operation of `wal().1` (State `326`). -/
def reg326Op (regs : List ℕ) : List ℕ :=
  regConsOp (regV4Op regs)

/-- `wal().1` (State `326`): `v_4_(); cons()`. -/
theorem subEval_326 : SubEval 326 reg326Op := by
  unfold reg326Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_322 subEval_69

/-- Register-bank operation of `wal()` (State `325`). -/
def regWalOp (regs : List ℕ) : List ℕ :=
  reg326Op (regConsOp regs)

/-- `wal().0` (State `325`): `cons(); v_4_(); cons()`. -/
theorem subEval_325 : SubEval 325 regWalOp := by
  unfold regWalOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_69 subEval_326

/-- Register-bank operation of `wex().1` (State `332`). -/
def reg332Op (regs : List ℕ) : List ℕ :=
  regWnOp (regWalOp regs)

/-- `wex().1` (State `332`): `wal(); wn()`. -/
theorem subEval_332 : SubEval 332 reg332Op := by
  unfold reg332Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_325 subEval_392

/-- Register-bank operation of `wex()` (State `331`). -/
def regWexOp (regs : List ℕ) : List ℕ :=
  reg332Op (regWnOp regs)

/-- `wex().0` (State `331`): `wn(); wal(); wn()`. -/
theorem subEval_331 : SubEval 331 regWexOp := by
  unfold regWexOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_392 subEval_332

/-- Register-bank operation of `wa().1` (State `324`). -/
def reg324Op (regs : List ℕ) : List ℕ :=
  regWnOp (regWimOp regs)

/-- `wa().1` (State `324`): `wim(); wn()`. -/
theorem subEval_324 : SubEval 324 reg324Op := by
  unfold reg324Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_390 subEval_392

/-- Register-bank operation of `wa()` (State `323`). -/
def regWaOp (regs : List ℕ) : List ℕ :=
  reg324Op (regWnOp regs)

/-- `wa().0` (State `323`): `wn(); wim(); wn()`. -/
theorem subEval_323 : SubEval 323 regWaOp := by
  unfold regWaOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_392 subEval_324

/-- Register-bank operation of `par1().1` (State `299`). -/
def reg299Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 5 0).set 2 (regs.getD 2 0 + regs.getD 5 0)).set
    8 (regs.getD 8 0 + regs.getD 5 0)
  (r.set 8 0).set 5 (r.getD 5 0 + r.getD 8 0)

/-- `par1().1` (State `299`): copies `param1` (`5`) into `topwff` (`2`) via `scratch1` (`8`). -/
theorem subEval_299 : SubEval 299 reg299Op := by
  unfold reg299Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_347 subEval_364

/-- Register-bank operation of `par1()` (State `298`). -/
def regPar1Op (regs : List ℕ) : List ℕ :=
  reg299Op (regPushwffOp regs)

/-- `par1().0` (State `298`): `pushwff(); topwff = param1`. -/
theorem subEval_298 : SubEval 298 regPar1Op := by
  unfold regPar1Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_304 subEval_299

/-- Register-bank operation of `par2().1` (State `301`). -/
def reg301Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 6 0).set 2 (regs.getD 2 0 + regs.getD 6 0)).set
    8 (regs.getD 8 0 + regs.getD 6 0)
  (r.set 8 0).set 6 (r.getD 6 0 + r.getD 8 0)

/-- `par2().1` (State `301`): copies `param2` (`6`) into `topwff` (`2`) via `scratch1` (`8`). -/
theorem subEval_301 : SubEval 301 reg301Op := by
  unfold reg301Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_353 subEval_366

/-- Register-bank operation of `par2()` (State `300`). -/
def regPar2Op (regs : List ℕ) : List ℕ :=
  reg301Op (regPushwffOp regs)

/-- `par2().0` (State `300`): `pushwff(); topwff = param2`. -/
theorem subEval_300 : SubEval 300 regPar2Op := by
  unfold regPar2Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_304 subEval_301

/-- Register-bank operation of `par3().1` (State `303`). -/
def reg303Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 7 0).set 2 (regs.getD 2 0 + regs.getD 7 0)).set
    8 (regs.getD 8 0 + regs.getD 7 0)
  (r.set 8 0).set 7 (r.getD 7 0 + r.getD 8 0)

/-- `par3().1` (State `303`): copies `param3` (`7`) into `topwff` (`2`) via `scratch1` (`8`). -/
theorem subEval_303 : SubEval 303 reg303Op := by
  unfold reg303Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_357 subEval_368

/-- Register-bank operation of `par3()` (State `302`). -/
def regPar3Op (regs : List ℕ) : List ℕ :=
  reg303Op (regPushwffOp regs)

/-- `par3().0` (State `302`): `pushwff(); topwff = param3`. -/
theorem subEval_302 : SubEval 302 regPar3Op := by
  unfold regPar3Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_304 subEval_303

/-! ## Section 4: `WffState` Register-Bank Embedding & Simp Lemmas -/

/-- Embed `WffState` along with `(prooflist, nextproof)` into the 11-register bank with
zeroed scratch registers `8, 9, 10`. -/
def wffStateToRegs (pl np : ℕ) (s : WffState) : List ℕ :=
  [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]

@[simp]
theorem wffStateToRegs_length (pl np : ℕ) (s : WffState) :
    (wffStateToRegs pl np s).length = 11 := rfl

@[simp]
theorem regPushwffOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regPushwffOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 0 s) := by
  simp [regPushwffOp, regPairOp, wffStateToRegs, rpnVk, pairLoop_eq_cantorPair]

@[simp]
theorem regV1Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regV1Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 1 s) := by
  unfold regV1Op
  rw [regPushwffOp_wffStateToRegs]
  rfl

@[simp]
theorem regV2Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regV2Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 2 s) := by
  unfold regV2Op
  rw [regV1Op_wffStateToRegs]
  rfl

@[simp]
theorem regV3Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regV3Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 3 s) := by
  unfold regV3Op
  rw [regV2Op_wffStateToRegs]
  rfl

@[simp]
theorem regV4Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regV4Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 4 s) := by
  unfold regV4Op
  rw [regV3Op_wffStateToRegs]
  rfl

@[simp]
theorem regConsOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regConsOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons s) := by
  simp [regConsOp, reg70Op, reg289Op, regUnpairGen, regPairOp, wffStateToRegs, rpnCons,
    unpairLoop_zero_zero, pairLoop_eq_cantorPair]

@[simp]
theorem reg330Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg330Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons (rpnVk 0 s)) := by
  simp [reg330Op]

@[simp]
theorem regWeqOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWeqOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWeq s) := by
  simp [regWeqOp, rpnWeq]

@[simp]
theorem reg328Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg328Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons (rpnVk 1 s)) := by
  simp [reg328Op]

@[simp]
theorem regWelOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWelOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWel s) := by
  simp [regWelOp, rpnWel]

@[simp]
theorem reg391Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg391Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons (rpnVk 2 s)) := by
  simp [reg391Op]

@[simp]
theorem regWimOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWimOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWim s) := by
  simp [regWimOp, rpnWim]

@[simp]
theorem regWnOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWnOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWn s) := by
  simp [regWnOp, rpnWn]

@[simp]
theorem reg326Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg326Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons (rpnVk 4 s)) := by
  simp [reg326Op]

@[simp]
theorem regWalOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWalOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWal s) := by
  simp [regWalOp, rpnWal]

@[simp]
theorem reg332Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg332Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWn (rpnWal s)) := by
  simp [reg332Op]

@[simp]
theorem regWexOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWexOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWex s) := by
  simp [regWexOp, rpnWex]

@[simp]
theorem reg324Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg324Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWn (rpnWim s)) := by
  simp [reg324Op]

@[simp]
theorem regWaOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWaOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWa s) := by
  simp [regWaOp, rpnWa]

@[simp]
theorem regPar1Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regPar1Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnPar1 s) := by
  unfold regPar1Op
  rw [regPushwffOp_wffStateToRegs]
  simp [reg299Op, wffStateToRegs, rpnVk, rpnPar1]

@[simp]
theorem regPar2Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regPar2Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnPar2 s) := by
  unfold regPar2Op
  rw [regPushwffOp_wffStateToRegs]
  simp [reg301Op, wffStateToRegs, rpnVk, rpnPar2]

@[simp]
theorem regPar3Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regPar3Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnPar3 s) := by
  unfold regPar3Op
  rw [regPushwffOp_wffStateToRegs]
  simp [reg303Op, wffStateToRegs, rpnVk, rpnPar3]

@[simp]
theorem reg269Op_eval (pl np top stk ac p1 p2 p3 s3 : ℕ) :
    reg269Op [pl, np, top, stk, ac, p1, p2, p3, 0, 0, s3] =
      [(cantorUnpair pl).2, np, top, stk, ac, p1, p2, p3, (cantorUnpair pl).1, 0, s3] := by
  simp [reg269Op, regUnpairGen, unpairLoop_zero_zero]

@[simp]
theorem reg289Op_eval (pl np top stk ac p1 p2 p3 s3 : ℕ) :
    reg289Op [pl, np, top, stk, ac, p1, p2, p3, 0, 0, s3] =
      [pl, np, top, (cantorUnpair stk).2, ac, p1, p2, p3, (cantorUnpair stk).1, 0, s3] := by
  simp [reg289Op, regUnpairGen, unpairLoop_zero_zero]

/-! ## Section 1: Generic Conditional Subroutine Combinator (`subEval_cond`) -/

/-- Generic conditional subroutine combinator: if `q` transitions on `0` to a condition-checker
node `q₀` (`69 ≤ q₀.val`) and on `1` to a `then`-branch `q₁` (`69 ≤ q₁.val`) with `SubEval q₁ f₁`,
and `q₀` at `P ++ [0]` either exits normally to `retStack (P ++ [0]) = P ++ [1]` when `cond regs`
holds or breaks 1 level to `(popBreakRev 1 (P ++ [0]).reverse).reverse = retStack P` when
`cond regs` is false, then `q` satisfies
`SubEval q (fun regs => if cond regs then f₁ (f₀ regs) else f₀ regs)`. -/
theorem subEval_cond {q q₀ q₁ : Fin 393} {cond : List ℕ → Prop} [DecidablePred cond]
    {f₀ f₁ : List ℕ → List ℕ}
    (htr0 : zf393Trans q 0 = some (0, .right, q₀)) (hq₀ : 69 ≤ q₀.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q₁)) (hq₁ : 69 ≤ q₁.val)
    (h0 : ∀ (Q : List (Fin 2)), walkInternal 99 Q = some q₀ →
      ∀ (regs : List ℕ), regs.length = 11 →
        ∃ s ≥ 1,
          zfReg11NSteps s ⟨trimZeros Q, regs⟩ =
            some ⟨if cond regs then retStack Q else (popBreakRev 1 Q.reverse).reverse,
                  f₀ regs⟩ ∧
          (f₀ regs).length = 11)
    (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs => if cond regs then f₁ (f₀ regs) else f₀ regs) := by
  intro P hP regs hlen
  have hP0 : walkInternal 99 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  have hP1 : walkInternal 99 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := h0 (P ++ [0]) hP0 regs hlen
  have hbrk : (popBreakRev 1 (P ++ [0]).reverse).reverse = retStack P := by
    simp [retStack]
  rw [trimZeros_append_zero, retStack_append_zero, hbrk] at hsteps₀
  by_cases hc : cond regs
  · simp only [hc, ↓reduceIte] at hsteps₀ ⊢
    obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 (f₀ regs) hlen₀
    rw [trimZeros_append_one, retStack_append_one] at hsteps₁
    exact ⟨s₀ + s₁, by omega, zfReg11NSteps_bind_eq hsteps₀ hsteps₁, hlen₁⟩
  · simp only [hc, ↓reduceIte] at hsteps₀ ⊢
    exact ⟨s₀, hs₀, hsteps₀, hlen₀⟩

/-! ## Section 2: `if_not_decnz(prooflist, 72).0` (States `95..98`) -/

/-- `if_not_decnz(prooflist, 72).2` (State `98`): adds `scratch1` (`8`) into `nextproof` (`1`),
zeroes `8`, and increments `nextproof` (`1`). -/
theorem subEval_98 :
    SubEval 98 (fun regs =>
      (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0 + 1)) := by
  refine (subEval_seq_inc rfl (by decide) rfl (by decide) (by decide) rfl subEval_362).congr ?_
  intro regs hlen
  change ((regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)).set 1
    (((regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)).getD 1 0 + 1) =
    (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0 + 1)
  rw [getD_set_self _ 1 _ (by simp [hlen]), List.set_set]

/-- `if_not_decnz(prooflist, 72).1` (State `97`): copies `nextproof` (`1`) to `prooflist` (`0`)
and increments `nextproof` (`1`) via `scratch1` (`8`). -/
def reg97Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 1 0).set 8 (regs.getD 8 0 + regs.getD 1 0)).set 0
    (regs.getD 0 0 + regs.getD 1 0)
  (r.set 8 0).set 1 (r.getD 1 0 + r.getD 8 0 + 1)

theorem subEval_97 : SubEval 97 reg97Op := by
  unfold reg97Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_343 subEval_98

/-- `if_not_decnz(prooflist, 72).0` (State `95`): if `prooflist` (`0`) is `0`, reloads `prooflist`
from `nextproof` (`1`) and increments `nextproof` (`1`); otherwise decrements `prooflist` (`0`). -/
def reg95Op (regs : List ℕ) : List ℕ :=
  if regs.getD 0 0 = 0 then
    reg97Op regs
  else
    regs.set 0 (regs.getD 0 0 - 1)

theorem subEval_95 : SubEval 95 reg95Op := by
  intro P hP regs hlen
  unfold reg95Op
  have hP0 : walkInternal 99 (P ++ [0]) = some 96 :=
    walkInternal_snoc hP rfl (by decide)
  have hP1 : walkInternal 99 (P ++ [1]) = some 97 :=
    walkInternal_snoc hP rfl (by decide)
  have hev0 : evalStack (trimZeros P) = .decnz 0 (P ++ [0] ++ [1]) (P ++ [1]) := by
    rw [← trimZeros_append_zero P, evalStack_trimZeros_of_walkInternal hP0,
      evalStack_leaf0_of_walkInternal hP0 rfl (by decide) (by decide)]
    simp [isLeafInc, logLeafReg]
  rcases hv : regs.getD 0 0 with _ | v
  · -- Case `regs.getD 0 0 = 0`
    have hstep1 := zfReg11Step_of_decnz_zero hev0 hv
    obtain ⟨s, hs, hsteps, hlen'⟩ := subEval_97 (P ++ [1]) hP1 regs hlen
    rw [trimZeros_append_one, retStack_append_one] at hsteps
    exact ⟨s + 1, by omega, step_zfReg11NSteps hstep1 hsteps, hlen'⟩
  · -- Case `regs.getD 0 0 = v + 1`
    have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
    have hev_brk : evalStack (P ++ [0] ++ [1]) = .jump (retStack P) := by
      have h := evalStack_break1_of_walkInternal (P := P ++ [0]) (k := 1) (by decide) hP0 rfl
      simpa [retStack] using h
    have hstep2 := zfReg11Step_of_jump (regs := regs.set 0 v) hev_brk
    exact ⟨2, by omega, step_zfReg11NSteps hstep1 (zfReg11Step_one hstep2), by simp [hlen]⟩

/-! ## Section 3: `if_decnz(axiomcode, 43).0` (`83..84`) & `select().0` (`305..308`) -/

/-- `if_decnz(axiomcode, 43).1` (State `84`): clears `topwff` (`2`) and moves `scratch1` (`8`)
into `topwff` (`2`). -/
theorem subEval_84 :
    SubEval 84 (fun regs => (regs.set 8 0).set 2 (regs.getD 8 0)) := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_382 subEval_371).congr ?_
  intro regs hlen
  have hget2 : (regs.set 2 0).getD 2 0 = 0 := getD_set_self regs 2 0 (by omega)
  have hget8 : (regs.set 2 0).getD 8 0 = regs.getD 8 0 := getD_set_ne regs 0 (by decide)
  rw [hget2, hget8, Nat.zero_add,
    set_comm_of_ne regs 0 0 (by decide), List.set_set]

/-- `if_decnz(axiomcode, 43).0` (State `83`): if `axiomcode` (`4`) is `0`, does nothing;
otherwise decrements `axiomcode` (`4`) and moves `scratch1` (`8`) into `topwff` (`2`). -/
def reg83Op (regs : List ℕ) : List ℕ :=
  if regs.getD 4 0 = 0 then
    regs
  else
    ((regs.set 4 (regs.getD 4 0 - 1)).set 8 0).set 2 (regs.getD 8 0)

theorem subEval_83 : SubEval 83 reg83Op := by
  intro P hP regs hlen
  unfold reg83Op
  have hP1 : walkInternal 99 (P ++ [1]) = some 84 :=
    walkInternal_snoc hP rfl (by decide)
  have hev0 : evalStack (trimZeros P) = .decnz 4 (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP rfl (by decide) (by decide)]
    simp [isLeafInc, logLeafReg]
  rcases hv : regs.getD 4 0 with _ | v
  · -- Case `regs.getD 4 0 = 0`
    have hstep := zfReg11Step_of_decnz_zero hev0 hv
    exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
  · -- Case `regs.getD 4 0 = v + 1`
    have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
    obtain ⟨s, hs, hsteps, hlen'⟩ :=
      subEval_84 (P ++ [1]) hP1 (regs.set 4 v) (by simp [hlen])
    rw [trimZeros_append_one, retStack_append_one] at hsteps
    dsimp only at hsteps hlen'
    have hget8 : (regs.set 4 v).getD 8 0 = regs.getD 8 0 := getD_set_ne regs v (by decide)
    rw [hget8] at hsteps hlen'
    exact ⟨s + 1, by omega, step_zfReg11NSteps hstep1 hsteps, hlen'⟩

/-- `select().3` (State `308`): runs `if_decnz(axiomcode, 43)` (`83`) followed by clearing
`scratch1` (`8`). -/
def reg308Op (regs : List ℕ) : List ℕ :=
  (reg83Op regs).set 8 0

theorem subEval_308 : SubEval 308 reg308Op := by
  unfold reg308Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_83 subEval_359

/-- `select().2` (State `307`): moves `scratch2` (`9`) into `wffstack` (`3`) and runs `308`. -/
def reg307Op (regs : List ℕ) : List ℕ :=
  reg308Op ((regs.set 9 0).set 3 (regs.getD 3 0 + regs.getD 9 0))

theorem subEval_307 : SubEval 307 reg307Op := by
  unfold reg307Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_380 subEval_308

/-- `select().1` (State `306`): unpairs `wffstack` (`3`) into `(topwff, scratch2)` via `315`
and runs `307`. -/
def reg306Op (f354 : List ℕ → List ℕ) (regs : List ℕ) : List ℕ :=
  reg307Op (f354 regs)

theorem subEval_306 {f354 : List ℕ → List ℕ} (h354 : SubEval 315 f354) :
    SubEval 306 (reg306Op f354) := by
  unfold reg306Op
  exact subEval_seq rfl (by decide) rfl (by decide) h354 subEval_307

/-- `select().0` (State `305`): moves `topwff` (`2`) into `scratch1` (`8`) and runs `306`. -/
def regSelectGenOp (f354 : List ℕ → List ℕ) (regs : List ℕ) : List ℕ :=
  reg306Op f354 ((regs.set 2 0).set 8 (regs.getD 8 0 + regs.getD 2 0))

theorem subEval_305 {f354 : List ℕ → List ℕ} (h354 : SubEval 315 f354) :
    SubEval 305 (regSelectGenOp f354) := by
  unfold regSelectGenOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_386 (subEval_306 h354)

/-! ## Section 4: `cparam().n_91.0` (`71..78`) and `cparam` (`79, 81`) -/

/-- `cparam().n_91.5` (State `76`): increments `axiomcode` (`4`) twice. -/
theorem subEval_76 :
    SubEval 76 (fun regs => regs.set 4 (regs.getD 4 0 + 2)) := by
  refine (subEval_inc_inc (q₀ := 30) (q₁ := 30)
    rfl (by decide) (by decide) rfl rfl (by decide) (by decide) rfl).congr ?_
  intro regs hlen
  change (regs.set 4 (regs.getD 4 0 + 1)).set 4
    ((regs.set 4 (regs.getD 4 0 + 1)).getD 4 0 + 1) = regs.set 4 (regs.getD 4 0 + 2)
  rw [getD_set_self regs 4 _ (by omega), List.set_set]

/-- `cparam().n_91.7` (State `78`): increments `axiomcode` (`4`) and then runs `289`
(`pop_to_scratch1`). -/
theorem subEval_78 {f328 : List ℕ → List ℕ} (h328 : SubEval 289 f328) :
    SubEval 78 (fun regs => f328 (regs.set 4 (regs.getD 4 0 + 1))) :=
  subEval_inc_seq (q₀ := 30) (q₁ := 289) rfl (by decide) (by decide) rfl rfl (by decide) h328

/-- `cparam().n_91.0` (State `71`): condition-checker for `axiomcode == 1`.
At call-stack prefix `Q` (`walkInternal 99 Q = some 71`):
- If `regs.getD 4 0 = 1`: restores `axiomcode = 1`, executes `289` (`f328 regs`), and exits
  normally to `retStack Q` (`= P ++ [1]` when `Q = P ++ [0]`).
- If `regs.getD 4 0 ≠ 1`: leaves `regs` unchanged and breaks 1 level to
  `(popBreakRev 1 Q.reverse).reverse` (`= retStack P` when `Q = P ++ [0]`). -/
theorem subEval_71 {f328 : List ℕ → List ℕ} (h328 : SubEval 289 f328)
    (Q : List (Fin 2)) (hQ : walkInternal 99 Q = some 71)
    (regs : List ℕ) (hlen : regs.length = 11) :
    ∃ s ≥ 1,
      zfReg11NSteps s ⟨trimZeros Q, regs⟩ =
        some ⟨if regs.getD 4 0 = 1 then retStack Q else (popBreakRev 1 Q.reverse).reverse,
              if regs.getD 4 0 = 1 then f328 regs else regs⟩ ∧
      (if regs.getD 4 0 = 1 then f328 regs else regs).length = 11 := by
  have hQ0 : walkInternal 99 (Q ++ [0]) = some 72 :=
    walkInternal_snoc hQ rfl (by decide)
  have hQ01 : walkInternal 99 (Q ++ [0] ++ [1]) = some 73 :=
    walkInternal_snoc hQ0 rfl (by decide)
  have hQ010 : walkInternal 99 (Q ++ [0] ++ [1] ++ [0]) = some 74 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0101 : walkInternal 99 (Q ++ [0] ++ [1] ++ [0] ++ [1]) = some 75 :=
    walkInternal_snoc hQ010 rfl (by decide)
  have hQ01010 : walkInternal 99 (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [0]) = some 76 :=
    walkInternal_snoc hQ0101 rfl (by decide)
  have hQ011 : walkInternal 99 (Q ++ [0] ++ [1] ++ [1]) = some 77 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0110 : walkInternal 99 (Q ++ [0] ++ [1] ++ [1] ++ [0]) = some 78 :=
    walkInternal_snoc hQ011 rfl (by decide)
  have hev99 : evalStack (trimZeros Q) = .decnz 4 (Q ++ [0] ++ [1]) (Q ++ [1]) := by
    rw [← trimZeros_append_zero Q, evalStack_trimZeros_of_walkInternal hQ0,
      evalStack_leaf0_of_walkInternal hQ0 rfl (by decide) (by decide)]
    simp [isLeafInc, logLeafReg]
  have hev98_brk : evalStack (Q ++ [1]) = .jump (popBreakRev 1 Q.reverse).reverse :=
    evalStack_break1_of_walkInternal (k := 1) (by decide) hQ rfl
  have hev101 : evalStack (Q ++ [0] ++ [1]) =
      .decnz 4 (Q ++ [0] ++ [1] ++ [0] ++ [1]) (Q ++ [0] ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hQ010 rfl (by decide) (by decide)
    rw [← evalStack_trimZeros_of_walkInternal hQ010, trimZeros_append_zero,
      trimZeros_append_one, retStack_append_zero] at h
    exact h
  rcases hv : regs.getD 4 0 with _ | _ | v
  · -- Case `regs.getD 4 0 = 0`
    simp only [Nat.zero_ne_one, ↓reduceIte]
    have hstep1 := zfReg11Step_of_decnz_zero hev99 hv
    have hstep2 := zfReg11Step_of_jump (regs := regs) hev98_brk
    exact ⟨2, by omega, step_zfReg11NSteps hstep1 (zfReg11Step_one hstep2), hlen⟩
  · -- Case `regs.getD 4 0 = 1`
    simp only [↓reduceIte]
    have hstep1 := zfReg11Step_of_decnz_succ hev99 hv
    have hv0 : (regs.set 4 0).getD 4 0 = 0 := getD_set_self regs 4 0 (by omega)
    have hstep2 := zfReg11Step_of_decnz_zero hev101 hv0
    obtain ⟨s, hs, hsteps_105, hlen_105⟩ :=
      subEval_78 h328 (Q ++ [0] ++ [1] ++ [1] ++ [0]) hQ0110 (regs.set 4 0) (by simp [hlen])
    rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_105
    dsimp only [logLeafReg] at hsteps_105 hlen_105
    have hrestore : (regs.set 4 0).set 4 ((regs.set 4 0).getD 4 0 + 1) = regs := by
      rw [hv0, List.set_set, set_eq_self_of_getD_eq hv]
    rw [hrestore] at hsteps_105 hlen_105
    have hev104_brk : evalStack (Q ++ [0] ++ [1] ++ [1] ++ [1]) = .jump (retStack Q) := by
      have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [1])
        (k := 1) (by decide) hQ011 rfl
      simpa [retStack] using h
    have hstep4 := zfReg11Step_of_jump (regs := f328 regs) hev104_brk
    have hchain := step_zfReg11NSteps hstep1
      (step_zfReg11NSteps hstep2 (zfReg11NSteps_bind_eq hsteps_105 (zfReg11Step_one hstep4)))
    exact ⟨s + 1 + 2, by omega, hchain, hlen_105⟩
  · -- Case `regs.getD 4 0 = v + 2`
    have hne : v + 1 + 1 ≠ 1 := by omega
    simp only [hne, ↓reduceIte]
    have hstep1 := zfReg11Step_of_decnz_succ hev99 hv
    have hv1 : (regs.set 4 (v + 1)).getD 4 0 = v + 1 := getD_set_self regs 4 (v + 1) (by omega)
    have hstep2 := zfReg11Step_of_decnz_succ hev101 hv1
    rw [List.set_set] at hstep2
    obtain ⟨s, hs, hsteps_103, _⟩ :=
      subEval_76 (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [0]) hQ01010 (regs.set 4 v) (by simp [hlen])
    rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_103
    dsimp only at hsteps_103
    have hrestore : (regs.set 4 v).set 4 ((regs.set 4 v).getD 4 0 + 2) = regs := by
      rw [getD_set_self regs 4 v (by omega), List.set_set, set_eq_self_of_getD_eq hv]
    rw [hrestore] at hsteps_103
    have hev102_brk : evalStack (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [1]) = .jump (Q ++ [1]) := by
      have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [0] ++ [1])
        (k := 1) (by decide) hQ0101 rfl
      simpa using h
    have hstep4 := zfReg11Step_of_jump (regs := regs) hev102_brk
    have hstep5 := zfReg11Step_of_jump (regs := regs) hev98_brk
    have hchain := step_zfReg11NSteps hstep1
      (step_zfReg11NSteps hstep2
        (zfReg11NSteps_bind_eq hsteps_103 (step_zfReg11NSteps hstep4 (zfReg11Step_one hstep5))))
    exact ⟨s + 2 + 2, by omega, hchain, hlen⟩

/-- `cparam(param2).1` (State `80`): clears `param2` (`6`) and moves `scratch1` (`8`) into
`param2` (`6`). -/
theorem subEval_80 :
    SubEval 80 (fun regs => (regs.set 8 0).set 6 (regs.getD 8 0)) := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_352 subEval_366).congr ?_
  intro regs hlen
  have hget6 : (regs.set 6 0).getD 6 0 = 0 := getD_set_self regs 6 0 (by omega)
  have hget8 : (regs.set 6 0).getD 8 0 = regs.getD 8 0 := getD_set_ne regs 0 (by decide)
  rw [hget6, hget8, Nat.zero_add,
    set_comm_of_ne regs 0 0 (by decide), List.set_set]

/-- `cparam(param2).0` (State `79`): if `axiomcode == 1`, runs `289` (`pop_to_scratch1`) and
moves `scratch1` (`8`) into `param2` (`6`); otherwise leaves `regs` unchanged. -/
theorem subEval_79 {f328 : List ℕ → List ℕ} (h328 : SubEval 289 f328) :
    SubEval 79 (fun regs =>
      if regs.getD 4 0 = 1 then
        let r := f328 regs
        (r.set 8 0).set 6 (r.getD 8 0)
      else
        regs) := by
  refine (subEval_cond (cond := fun regs => regs.getD 4 0 = 1)
    rfl (by decide) rfl (by decide) (subEval_71 h328) subEval_80).congr ?_
  intro regs _hlen
  split_ifs <;> rfl

/-- `cparam(param3).1` (State `82`): clears `param3` (`7`) and moves `scratch1` (`8`) into
`param3` (`7`). -/
theorem subEval_82 :
    SubEval 82 (fun regs => (regs.set 8 0).set 7 (regs.getD 8 0)) := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_356 subEval_368).congr ?_
  intro regs hlen
  have hget7 : (regs.set 7 0).getD 7 0 = 0 := getD_set_self regs 7 0 (by omega)
  have hget8 : (regs.set 7 0).getD 8 0 = regs.getD 8 0 := getD_set_ne regs 0 (by decide)
  rw [hget7, hget8, Nat.zero_add,
    set_comm_of_ne regs 0 0 (by decide), List.set_set]

/-- `cparam(param3).0` (State `81`): if `axiomcode == 1`, runs `289` (`pop_to_scratch1`) and
moves `scratch1` (`8`) into `param3` (`7`); otherwise leaves `regs` unchanged. -/
theorem subEval_81 {f328 : List ℕ → List ℕ} (h328 : SubEval 289 f328) :
    SubEval 81 (fun regs =>
      if regs.getD 4 0 = 1 then
        let r := f328 regs
        (r.set 8 0).set 7 (r.getD 8 0)
      else
        regs) := by
  refine (subEval_cond (cond := fun regs => regs.getD 4 0 = 1)
    rfl (by decide) rfl (by decide) (subEval_71 h328) subEval_82).congr ?_
  intro regs _hlen
  split_ifs <;> rfl

/-! ## Section 5: `if_eq().n_111.0` (States `85..91`), `93`, `92`, and `298` -/

/-- `if_eq().n_111.0` (State `85`): equality comparison loop on `scratch2` (`9`) and
`scratch3` (`10`).
At call-stack prefix `Q` (`walkInternal 99 Q = some 85`):
- Always zeroes both `scratch2` (`9`) and `scratch3` (`10`).
- If `regs.getD 9 0 = regs.getD 10 0`: exits normally to `retStack Q`
  (`= P ++ [1]` when `Q = P ++ [0]`).
- If `regs.getD 9 0 ≠ regs.getD 10 0`: breaks 1 level out of `Q` to
  `(popBreakRev 1 Q.reverse).reverse` (`= retStack P` when `Q = P ++ [0]`). -/
theorem subEval_85 (Q : List (Fin 2)) (hQ : walkInternal 99 Q = some 85) :
    ∀ (regs : List ℕ), regs.length = 11 →
      ∃ s ≥ 1,
        zfReg11NSteps s ⟨trimZeros Q, regs⟩ =
          some ⟨if regs.getD 9 0 = regs.getD 10 0 then retStack Q
                else (popBreakRev 1 Q.reverse).reverse,
                (regs.set 9 0).set 10 0⟩ ∧
        ((regs.set 9 0).set 10 0).length = 11 := by
  have hQ0 : walkInternal 99 (Q ++ [0]) = some 86 :=
    walkInternal_snoc hQ rfl (by decide)
  have hQ01 : walkInternal 99 (Q ++ [0] ++ [1]) = some 87 :=
    walkInternal_snoc hQ0 rfl (by decide)
  have hQ010 : walkInternal 99 (Q ++ [0] ++ [1] ++ [0]) = some 88 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ011 : walkInternal 99 (Q ++ [0] ++ [1] ++ [1]) = some 89 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0110 : walkInternal 99 (Q ++ [0] ++ [1] ++ [1] ++ [0]) = some 376 :=
    walkInternal_snoc hQ011 rfl (by decide)
  have hQ1 : walkInternal 99 (Q ++ [1]) = some 90 :=
    walkInternal_snoc hQ rfl (by decide)
  have hQ11 : walkInternal 99 (Q ++ [1] ++ [1]) = some 91 :=
    walkInternal_snoc hQ1 rfl (by decide)
  have hQ110 : walkInternal 99 (Q ++ [1] ++ [1] ++ [0]) = some 381 :=
    walkInternal_snoc hQ11 rfl (by decide)
  have hev113 : evalStack (trimZeros Q) = .decnz 9 (Q ++ [0] ++ [1]) (Q ++ [1]) := by
    rw [← trimZeros_append_zero Q, evalStack_trimZeros_of_walkInternal hQ0,
      evalStack_leaf0_of_walkInternal hQ0 rfl (by decide) (by decide)]
    simp [isLeafInc, logLeafReg]
  have hev115 : evalStack (Q ++ [0] ++ [1]) =
      .decnz 10 (Q ++ [0] ++ [1] ++ [0] ++ [1]) (Q ++ [0] ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hQ010 rfl (by decide) (by decide)
    rw [← evalStack_trimZeros_of_walkInternal hQ010, trimZeros_append_zero,
      trimZeros_append_one, retStack_append_zero] at h
    exact h
  have hev115_cont : evalStack (Q ++ [0] ++ [1] ++ [0] ++ [1]) = .jump (trimZeros Q) := by
    have h := evalStack_continue1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [0])
      (k := 1) (by decide) hQ010 rfl
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hev116_brk : evalStack (Q ++ [0] ++ [1] ++ [1] ++ [1]) =
      .jump (popBreakRev 1 Q.reverse).reverse := by
    have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [1])
      (k := 2) (by decide) hQ011 rfl
    simpa using h
  have hev117 : evalStack (Q ++ [1]) = .decnz 10 (Q ++ [1] ++ [1]) (retStack Q) := by
    have h := evalStack_leaf0_of_walkInternal hQ1 rfl (by decide) (by decide)
    simpa [isLeafInc, logLeafReg] using h
  have hev118_brk : evalStack (Q ++ [1] ++ [1] ++ [1]) =
      .jump (popBreakRev 1 Q.reverse).reverse := by
    have h := evalStack_break1_of_walkInternal (P := Q ++ [1] ++ [1])
      (k := 1) (by decide) hQ11 rfl
    simpa using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD 9 0 = v →
      ∃ s ≥ 1,
        zfReg11NSteps s ⟨trimZeros Q, regs⟩ =
          some ⟨if v = regs.getD 10 0 then retStack Q
                else (popBreakRev 1 Q.reverse).reverse,
                (regs.set 9 0).set 10 0⟩ ∧
        ((regs.set 9 0).set 10 0).length = 11 := by
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      have hstep1 := zfReg11Step_of_decnz_zero hev113 hv
      rcases hw : regs.getD 10 0 with _ | w
      · -- `v = 0` and `regs.getD 10 0 = 0`
        simp only [↓reduceIte]
        have hstep2 := zfReg11Step_of_decnz_zero hev117 hw
        have hset : (regs.set 9 0).set 10 0 = regs := by
          rw [set_eq_self_of_getD_eq hv, set_eq_self_of_getD_eq hw]
        rw [hset]
        exact ⟨2, by omega, step_zfReg11NSteps hstep1 (zfReg11Step_one hstep2), hlen⟩
      · -- `v = 0` and `regs.getD 10 0 = w + 1`
        have hne : 0 ≠ w + 1 := by omega
        simp only [hne, ↓reduceIte]
        have hstep2 := zfReg11Step_of_decnz_succ hev117 hw
        obtain ⟨s, hs, hsteps_420, _⟩ :=
          subEval_381 (Q ++ [1] ++ [1] ++ [0]) hQ110 (regs.set 10 w) (by simp [hlen])
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_420
        dsimp only at hsteps_420
        rw [List.set_set] at hsteps_420
        have hstep4 := zfReg11Step_of_jump (regs := regs.set 10 0) hev118_brk
        have hset9 : (regs.set 9 0).set 10 0 = regs.set 10 0 := by
          rw [set_eq_self_of_getD_eq hv]
        rw [hset9]
        have hchain := step_zfReg11NSteps hstep1
          (step_zfReg11NSteps hstep2 (zfReg11NSteps_bind_eq hsteps_420 (zfReg11Step_one hstep4)))
        exact ⟨s + 1 + 2, by omega, hchain, by simp [hlen]⟩
    | succ v ih =>
      intro regs hlen hv
      have hstep1 := zfReg11Step_of_decnz_succ hev113 hv
      rcases hw : regs.getD 10 0 with _ | w
      · -- `regs.getD 9 0 = v + 1` and `regs.getD 10 0 = 0`
        have hne : v + 1 ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
        have hw' : (regs.set 9 v).getD 10 0 = 0 := by
          rw [getD_set_ne _ _ (by decide), hw]
        have hstep2 := zfReg11Step_of_decnz_zero hev115 hw'
        obtain ⟨s, hs, hsteps_415, _⟩ :=
          subEval_376 (Q ++ [0] ++ [1] ++ [1] ++ [0]) hQ0110 (regs.set 9 v) (by simp [hlen])
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_415
        dsimp only at hsteps_415
        rw [List.set_set] at hsteps_415
        have hstep4 := zfReg11Step_of_jump (regs := regs.set 9 0) hev116_brk
        have hset10 : (regs.set 9 0).set 10 0 = regs.set 9 0 := by
          have hw0 : (regs.set 9 0).getD 10 0 = 0 := by
            rw [getD_set_ne _ _ (by decide), hw]
          exact set_eq_self_of_getD_eq hw0
        rw [hset10]
        have hchain := step_zfReg11NSteps hstep1
          (step_zfReg11NSteps hstep2 (zfReg11NSteps_bind_eq hsteps_415 (zfReg11Step_one hstep4)))
        exact ⟨s + 1 + 2, by omega, hchain, by simp [hlen]⟩
      · -- `regs.getD 9 0 = v + 1` and `regs.getD 10 0 = w + 1`
        have hw' : (regs.set 9 v).getD 10 0 = w + 1 := by
          rw [getD_set_ne _ _ (by decide), hw]
        have hstep2 := zfReg11Step_of_decnz_succ hev115 hw'
        let regs₁ := (regs.set 9 v).set 10 w
        have hstep3 := zfReg11Step_of_jump (regs := regs₁) hev115_cont
        have hlen₁ : regs₁.length = 11 := by simp [regs₁, hlen]
        have hv₁ : regs₁.getD 9 0 = v := by
          dsimp only [regs₁]
          rw [getD_set_ne _ _ (by decide), getD_set_self regs 9 v (by omega)]
        have hw₁ : regs₁.getD 10 0 = w := by
          dsimp only [regs₁]
          exact getD_set_self (regs.set 9 v) 10 w (by simp [hlen])
        obtain ⟨s, hs, hsteps_ih, _⟩ := ih regs₁ hlen₁ hv₁
        have hset_eq : (regs₁.set 9 0).set 10 0 = (regs.set 9 0).set 10 0 := by
          dsimp only [regs₁]
          rw [set_comm_of_ne (regs.set 9 v) w 0 (by decide), List.set_set, List.set_set]
        have heq_iff : (v = w) ↔ (v + 1 = w + 1) := by omega
        rw [hw₁, hset_eq] at hsteps_ih
        have hcond_eq : (if v = w then retStack Q else (popBreakRev 1 Q.reverse).reverse) =
            (if v + 1 = w + 1 then retStack Q else (popBreakRev 1 Q.reverse).reverse) := by
          simp only [heq_iff]
        rw [hcond_eq] at hsteps_ih
        have hchain := step_zfReg11NSteps hstep1
          (step_zfReg11NSteps hstep2 (step_zfReg11NSteps hstep3 hsteps_ih))
        exact ⟨s + 3, by omega, hchain, by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD 9 0) regs hlen rfl

/-- `if_eq(scratch2, scratch3, 75).1` (State `94`): adds `param1` (`5`) into `topwff` (`2`)
while preserving `param1` (`5`) via `scratch1` (`8`). -/
def reg94Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set 2
    (regs.getD 2 0 + regs.getD 5 0)
  (r.set 8 0).set 5 (r.getD 5 0 + r.getD 8 0)

theorem subEval_94 : SubEval 94 reg94Op := by
  unfold reg94Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_348 subEval_364

/-- `if_eq(scratch2, scratch3, 75).0` (State `93`): compares `scratch2` (`9`) and
`scratch3` (`10`),
zeroing both; if equal, adds `param1` (`5`) into `topwff` (`2`) via `94`. -/
def reg93Op (regs : List ℕ) : List ℕ :=
  if regs.getD 9 0 = regs.getD 10 0 then
    reg94Op ((regs.set 9 0).set 10 0)
  else
    (regs.set 9 0).set 10 0

theorem subEval_93 : SubEval 93 reg93Op :=
  subEval_cond (cond := fun regs => regs.getD 9 0 = regs.getD 10 0)
    rfl (by decide) rfl (by decide) subEval_85 subEval_94

/-- `if_eq(scratch2, scratch3, 41).0` (State `92`): compares `scratch2` (`9`) and
`scratch3` (`10`),
zeroing both; if equal, clears `topwff` (`2`) to `0`. -/
def reg92Op (regs : List ℕ) : List ℕ :=
  if regs.getD 9 0 = regs.getD 10 0 then
    ((regs.set 9 0).set 10 0).set 2 0
  else
    (regs.set 9 0).set 10 0

theorem subEval_92 : SubEval 92 reg92Op :=
  subEval_cond (cond := fun regs => regs.getD 9 0 = regs.getD 10 0)
    rfl (by decide) rfl (by decide) subEval_85 subEval_382
/-- `main().n_140.1` (State `256`): restores `scratch1` (`8`) into `param3` (`7`) and runs `92`. -/
def reg256Op (regs : List ℕ) : List ℕ :=
  reg92Op ((regs.set 8 0).set 7 (regs.getD 7 0 + regs.getD 8 0))

theorem subEval_256 : SubEval 256 reg256Op := by
  unfold reg256Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_368 subEval_92

/-- `main().n_140.0` (State `255`): copies `param3` (`7`) into `scratch1` (`8`) and `scratch3`
(`10`), restores `scratch1` (`8`) into `param3` (`7`), and compares `scratch2` (`9`) with `scratch3`
(`10`), clearing `topwff` (`2`) if equal while leaving `param3` intact. -/
def reg255Op (regs : List ℕ) : List ℕ :=
  reg256Op (((regs.set 7 0).set 8 (regs.getD 8 0 + regs.getD 7 0)).set 10
    (regs.getD 10 0 + regs.getD 7 0))

theorem subEval_255 : SubEval 255 reg255Op := by
  unfold reg255Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_358 subEval_256
def regSelectOp (regs : List ℕ) : List ℕ :=
  regSelectGenOp (regUnpairGen 2 9 3) regs

theorem subEval_305_inst : SubEval 305 regSelectOp :=
  subEval_305 subEval_315

/-- Concrete `cparam(param2)` operation on the 11-register bank. -/
def regCparam2Op (regs : List ℕ) : List ℕ :=
  if regs.getD 4 0 = 1 then
    let r := reg289Op regs
    (r.set 8 0).set 6 (r.getD 8 0)
  else
    regs

theorem subEval_79_inst : SubEval 79 regCparam2Op :=
  subEval_79 subEval_289

/-- Concrete `cparam(param3)` operation on the 11-register bank. -/
def regCparam3Op (regs : List ℕ) : List ℕ :=
  if regs.getD 4 0 = 1 then
    let r := reg289Op regs
    (r.set 8 0).set 7 (r.getD 8 0)
  else
    regs

theorem subEval_81_inst : SubEval 81 regCparam3Op :=
  subEval_81 subEval_289

@[simp]
theorem regSelectOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regSelectOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnSelect s) := by
  unfold regSelectOp regSelectGenOp reg306Op reg307Op reg308Op reg83Op regUnpairGen
    wffStateToRegs rpnSelect
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, Nat.zero_add, unpairLoop_zero_zero]
  rcases s.axiomcode with _ | ac <;> rfl

@[simp]
theorem regCparam2Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regCparam2Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCparam2 s) := by
  unfold regCparam2Op wffStateToRegs rpnCparam2
  change (if s.axiomcode = 1 then
    let r := reg289Op
      [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]
    (r.set 8 0).set 6 (r.getD 8 0)
  else [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]) = _
  rw [reg289Op_eval]
  split_ifs <;> rfl

@[simp]
theorem regCparam3Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regCparam3Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCparam3 s) := by
  unfold regCparam3Op wffStateToRegs rpnCparam3
  change (if s.axiomcode = 1 then
    let r := reg289Op
      [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]
    (r.set 8 0).set 7 (r.getD 8 0)
  else [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]) = _
  rw [reg289Op_eval]
  split_ifs <;> rfl


set_option maxRecDepth 200000

/-! ## 1. Generic Spine-Step Combinators & Spine Walk Lemmas (`k = 0..134`) -/

/-- Generic spine-step lemma: if `main().k` (`walkInternal 99 (List.replicate k 1) = some q_k`)
transitions on `0` to subroutine node `q_sub` (`69 ≤ q_sub.val`) with `SubEval q_sub f`, then
starting from `⟨List.replicate k 1, regs⟩` reaches `⟨List.replicate (k + 1) 1, f regs⟩` in
`s ≥ 1` steps of `zfReg11Step`. -/
theorem spine_step_of_subEval {k : ℕ} {q_k q_sub : Fin 393} {f : List ℕ → List ℕ}
    (hwalk : walkInternal 99 (List.replicate k 1) = some q_k)
    (htr0 : zf393Trans q_k 0 = some (0, .right, q_sub))
    (hq_sub : 69 ≤ q_sub.val)
    (hsub : SubEval q_sub f)
    (regs : List ℕ) (hlen : regs.length = 11) :
    ∃ s ≥ 1, zfReg11NSteps s ⟨List.replicate k 1, regs⟩ =
      some ⟨List.replicate (k + 1) 1, f regs⟩ ∧ (f regs).length = 11 := by
  have hwalk0 : walkInternal 99 (List.replicate k 1 ++ [0]) = some q_sub :=
    walkInternal_snoc hwalk htr0 hq_sub
  obtain ⟨s, hs, hsteps, hflen⟩ := hsub (List.replicate k 1 ++ [0]) hwalk0 regs hlen
  rw [trimZeros_append_zero, trimZeros_replicate_one, retStack_append_zero,
    ← List.replicate_succ'] at hsteps
  exact ⟨s, hs, hsteps, hflen⟩

/-- Register-level spine segment evaluation from `List.replicate k₁ 1` to `List.replicate k₂ 1`. -/
def RegSpineEval (k₁ k₂ : ℕ) (f : List ℕ → List ℕ) : Prop :=
  ∀ (regs : List ℕ), regs.length = 11 →
    ∃ s ≥ 1, zfReg11NSteps s ⟨List.replicate k₁ 1, regs⟩ =
      some ⟨List.replicate k₂ 1, f regs⟩ ∧ (f regs).length = 11

theorem regSpineEval_step {k k' : ℕ} {q_k q_sub : Fin 393} {f : List ℕ → List ℕ}
    (hwalk : walkInternal 99 (List.replicate k 1) = some q_k)
    (htr0 : zf393Trans q_k 0 = some (0, .right, q_sub))
    (hq_sub : 69 ≤ q_sub.val)
    (hsub : SubEval q_sub f)
    (hk : k + 1 = k' := by rfl) :
    RegSpineEval k k' f := by
  subst hk
  exact spine_step_of_subEval hwalk htr0 hq_sub hsub

theorem regSpineEval_trans {k₁ k₂ k₃ : ℕ} {f₁ f₂ f : List ℕ → List ℕ}
    (h1 : RegSpineEval k₁ k₂ f₁) (h2 : RegSpineEval k₂ k₃ f₂)
    (heq : (fun regs => f₂ (f₁ regs)) = f := by rfl) :
    RegSpineEval k₁ k₃ f := by
  subst heq
  intro regs hlen
  obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 regs hlen
  obtain ⟨s₂, hs₂, hsteps₂, hlen₂⟩ := h2 (f₁ regs) hlen₁
  exact ⟨s₁ + s₂, by omega, zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hlen₂⟩

theorem walkInternal_spine_succ {k : ℕ} {q_k q_next : Fin 393}
    (hk : walkInternal 99 (List.replicate k 1) = some q_k)
    (htr1 : zf393Trans q_k 1 = some (1, .right, q_next))
    (hq_next : 69 ≤ q_next.val) :
    walkInternal 99 (List.replicate (k + 1) 1) = some q_next := by
  rw [List.replicate_succ']
  exact walkInternal_snoc hk htr1 hq_next

theorem walkInternal_spine_0 : walkInternal 99 (List.replicate 0 1) = some 99 := rfl
theorem walkInternal_spine_1 : walkInternal 99 (List.replicate 1 1) = some 100 :=
  walkInternal_spine_succ walkInternal_spine_0 rfl (by decide)
theorem walkInternal_spine_2 : walkInternal 99 (List.replicate 2 1) = some 101 :=
  walkInternal_spine_succ walkInternal_spine_1 rfl (by decide)
theorem walkInternal_spine_3 : walkInternal 99 (List.replicate 3 1) = some 102 :=
  walkInternal_spine_succ walkInternal_spine_2 rfl (by decide)
theorem walkInternal_spine_4 : walkInternal 99 (List.replicate 4 1) = some 103 :=
  walkInternal_spine_succ walkInternal_spine_3 rfl (by decide)
theorem walkInternal_spine_5 : walkInternal 99 (List.replicate 5 1) = some 104 :=
  walkInternal_spine_succ walkInternal_spine_4 rfl (by decide)
theorem walkInternal_spine_6 : walkInternal 99 (List.replicate 6 1) = some 105 :=
  walkInternal_spine_succ walkInternal_spine_5 rfl (by decide)
theorem walkInternal_spine_7 : walkInternal 99 (List.replicate 7 1) = some 106 :=
  walkInternal_spine_succ walkInternal_spine_6 rfl (by decide)
theorem walkInternal_spine_8 : walkInternal 99 (List.replicate 8 1) = some 107 :=
  walkInternal_spine_succ walkInternal_spine_7 rfl (by decide)
theorem walkInternal_spine_9 : walkInternal 99 (List.replicate 9 1) = some 108 :=
  walkInternal_spine_succ walkInternal_spine_8 rfl (by decide)
theorem walkInternal_spine_10 : walkInternal 99 (List.replicate 10 1) = some 109 :=
  walkInternal_spine_succ walkInternal_spine_9 rfl (by decide)
theorem walkInternal_spine_11 : walkInternal 99 (List.replicate 11 1) = some 110 :=
  walkInternal_spine_succ walkInternal_spine_10 rfl (by decide)
theorem walkInternal_spine_12 : walkInternal 99 (List.replicate 12 1) = some 111 :=
  walkInternal_spine_succ walkInternal_spine_11 rfl (by decide)
theorem walkInternal_spine_13 : walkInternal 99 (List.replicate 13 1) = some 112 :=
  walkInternal_spine_succ walkInternal_spine_12 rfl (by decide)
theorem walkInternal_spine_14 : walkInternal 99 (List.replicate 14 1) = some 113 :=
  walkInternal_spine_succ walkInternal_spine_13 rfl (by decide)
theorem walkInternal_spine_15 : walkInternal 99 (List.replicate 15 1) = some 114 :=
  walkInternal_spine_succ walkInternal_spine_14 rfl (by decide)
theorem walkInternal_spine_16 : walkInternal 99 (List.replicate 16 1) = some 115 :=
  walkInternal_spine_succ walkInternal_spine_15 rfl (by decide)
theorem walkInternal_spine_17 : walkInternal 99 (List.replicate 17 1) = some 116 :=
  walkInternal_spine_succ walkInternal_spine_16 rfl (by decide)
theorem walkInternal_spine_18 : walkInternal 99 (List.replicate 18 1) = some 117 :=
  walkInternal_spine_succ walkInternal_spine_17 rfl (by decide)
theorem walkInternal_spine_19 : walkInternal 99 (List.replicate 19 1) = some 118 :=
  walkInternal_spine_succ walkInternal_spine_18 rfl (by decide)
theorem walkInternal_spine_20 : walkInternal 99 (List.replicate 20 1) = some 119 :=
  walkInternal_spine_succ walkInternal_spine_19 rfl (by decide)
theorem walkInternal_spine_21 : walkInternal 99 (List.replicate 21 1) = some 120 :=
  walkInternal_spine_succ walkInternal_spine_20 rfl (by decide)
theorem walkInternal_spine_22 : walkInternal 99 (List.replicate 22 1) = some 121 :=
  walkInternal_spine_succ walkInternal_spine_21 rfl (by decide)
theorem walkInternal_spine_23 : walkInternal 99 (List.replicate 23 1) = some 122 :=
  walkInternal_spine_succ walkInternal_spine_22 rfl (by decide)
theorem walkInternal_spine_24 : walkInternal 99 (List.replicate 24 1) = some 123 :=
  walkInternal_spine_succ walkInternal_spine_23 rfl (by decide)
theorem walkInternal_spine_25 : walkInternal 99 (List.replicate 25 1) = some 124 :=
  walkInternal_spine_succ walkInternal_spine_24 rfl (by decide)
theorem walkInternal_spine_26 : walkInternal 99 (List.replicate 26 1) = some 125 :=
  walkInternal_spine_succ walkInternal_spine_25 rfl (by decide)
theorem walkInternal_spine_27 : walkInternal 99 (List.replicate 27 1) = some 126 :=
  walkInternal_spine_succ walkInternal_spine_26 rfl (by decide)
theorem walkInternal_spine_28 : walkInternal 99 (List.replicate 28 1) = some 127 :=
  walkInternal_spine_succ walkInternal_spine_27 rfl (by decide)
theorem walkInternal_spine_29 : walkInternal 99 (List.replicate 29 1) = some 128 :=
  walkInternal_spine_succ walkInternal_spine_28 rfl (by decide)
theorem walkInternal_spine_30 : walkInternal 99 (List.replicate 30 1) = some 129 :=
  walkInternal_spine_succ walkInternal_spine_29 rfl (by decide)
theorem walkInternal_spine_31 : walkInternal 99 (List.replicate 31 1) = some 130 :=
  walkInternal_spine_succ walkInternal_spine_30 rfl (by decide)
theorem walkInternal_spine_32 : walkInternal 99 (List.replicate 32 1) = some 131 :=
  walkInternal_spine_succ walkInternal_spine_31 rfl (by decide)
theorem walkInternal_spine_33 : walkInternal 99 (List.replicate 33 1) = some 132 :=
  walkInternal_spine_succ walkInternal_spine_32 rfl (by decide)
theorem walkInternal_spine_34 : walkInternal 99 (List.replicate 34 1) = some 133 :=
  walkInternal_spine_succ walkInternal_spine_33 rfl (by decide)
theorem walkInternal_spine_35 : walkInternal 99 (List.replicate 35 1) = some 134 :=
  walkInternal_spine_succ walkInternal_spine_34 rfl (by decide)
theorem walkInternal_spine_36 : walkInternal 99 (List.replicate 36 1) = some 135 :=
  walkInternal_spine_succ walkInternal_spine_35 rfl (by decide)
theorem walkInternal_spine_37 : walkInternal 99 (List.replicate 37 1) = some 136 :=
  walkInternal_spine_succ walkInternal_spine_36 rfl (by decide)
theorem walkInternal_spine_38 : walkInternal 99 (List.replicate 38 1) = some 137 :=
  walkInternal_spine_succ walkInternal_spine_37 rfl (by decide)
theorem walkInternal_spine_39 : walkInternal 99 (List.replicate 39 1) = some 138 :=
  walkInternal_spine_succ walkInternal_spine_38 rfl (by decide)
theorem walkInternal_spine_40 : walkInternal 99 (List.replicate 40 1) = some 139 :=
  walkInternal_spine_succ walkInternal_spine_39 rfl (by decide)
theorem walkInternal_spine_41 : walkInternal 99 (List.replicate 41 1) = some 140 :=
  walkInternal_spine_succ walkInternal_spine_40 rfl (by decide)
theorem walkInternal_spine_42 : walkInternal 99 (List.replicate 42 1) = some 141 :=
  walkInternal_spine_succ walkInternal_spine_41 rfl (by decide)
theorem walkInternal_spine_43 : walkInternal 99 (List.replicate 43 1) = some 142 :=
  walkInternal_spine_succ walkInternal_spine_42 rfl (by decide)
theorem walkInternal_spine_44 : walkInternal 99 (List.replicate 44 1) = some 143 :=
  walkInternal_spine_succ walkInternal_spine_43 rfl (by decide)
theorem walkInternal_spine_45 : walkInternal 99 (List.replicate 45 1) = some 144 :=
  walkInternal_spine_succ walkInternal_spine_44 rfl (by decide)
theorem walkInternal_spine_46 : walkInternal 99 (List.replicate 46 1) = some 145 :=
  walkInternal_spine_succ walkInternal_spine_45 rfl (by decide)
theorem walkInternal_spine_47 : walkInternal 99 (List.replicate 47 1) = some 146 :=
  walkInternal_spine_succ walkInternal_spine_46 rfl (by decide)
theorem walkInternal_spine_48 : walkInternal 99 (List.replicate 48 1) = some 147 :=
  walkInternal_spine_succ walkInternal_spine_47 rfl (by decide)
theorem walkInternal_spine_49 : walkInternal 99 (List.replicate 49 1) = some 148 :=
  walkInternal_spine_succ walkInternal_spine_48 rfl (by decide)
theorem walkInternal_spine_50 : walkInternal 99 (List.replicate 50 1) = some 149 :=
  walkInternal_spine_succ walkInternal_spine_49 rfl (by decide)
theorem walkInternal_spine_51 : walkInternal 99 (List.replicate 51 1) = some 150 :=
  walkInternal_spine_succ walkInternal_spine_50 rfl (by decide)
theorem walkInternal_spine_52 : walkInternal 99 (List.replicate 52 1) = some 151 :=
  walkInternal_spine_succ walkInternal_spine_51 rfl (by decide)
theorem walkInternal_spine_53 : walkInternal 99 (List.replicate 53 1) = some 152 :=
  walkInternal_spine_succ walkInternal_spine_52 rfl (by decide)
theorem walkInternal_spine_54 : walkInternal 99 (List.replicate 54 1) = some 153 :=
  walkInternal_spine_succ walkInternal_spine_53 rfl (by decide)
theorem walkInternal_spine_55 : walkInternal 99 (List.replicate 55 1) = some 154 :=
  walkInternal_spine_succ walkInternal_spine_54 rfl (by decide)
theorem walkInternal_spine_56 : walkInternal 99 (List.replicate 56 1) = some 155 :=
  walkInternal_spine_succ walkInternal_spine_55 rfl (by decide)
theorem walkInternal_spine_57 : walkInternal 99 (List.replicate 57 1) = some 156 :=
  walkInternal_spine_succ walkInternal_spine_56 rfl (by decide)
theorem walkInternal_spine_58 : walkInternal 99 (List.replicate 58 1) = some 157 :=
  walkInternal_spine_succ walkInternal_spine_57 rfl (by decide)
theorem walkInternal_spine_59 : walkInternal 99 (List.replicate 59 1) = some 158 :=
  walkInternal_spine_succ walkInternal_spine_58 rfl (by decide)
theorem walkInternal_spine_60 : walkInternal 99 (List.replicate 60 1) = some 159 :=
  walkInternal_spine_succ walkInternal_spine_59 rfl (by decide)
theorem walkInternal_spine_61 : walkInternal 99 (List.replicate 61 1) = some 160 :=
  walkInternal_spine_succ walkInternal_spine_60 rfl (by decide)
theorem walkInternal_spine_62 : walkInternal 99 (List.replicate 62 1) = some 161 :=
  walkInternal_spine_succ walkInternal_spine_61 rfl (by decide)
theorem walkInternal_spine_63 : walkInternal 99 (List.replicate 63 1) = some 162 :=
  walkInternal_spine_succ walkInternal_spine_62 rfl (by decide)
theorem walkInternal_spine_64 : walkInternal 99 (List.replicate 64 1) = some 163 :=
  walkInternal_spine_succ walkInternal_spine_63 rfl (by decide)
theorem walkInternal_spine_65 : walkInternal 99 (List.replicate 65 1) = some 164 :=
  walkInternal_spine_succ walkInternal_spine_64 rfl (by decide)
theorem walkInternal_spine_66 : walkInternal 99 (List.replicate 66 1) = some 165 :=
  walkInternal_spine_succ walkInternal_spine_65 rfl (by decide)
theorem walkInternal_spine_67 : walkInternal 99 (List.replicate 67 1) = some 166 :=
  walkInternal_spine_succ walkInternal_spine_66 rfl (by decide)
theorem walkInternal_spine_68 : walkInternal 99 (List.replicate 68 1) = some 167 :=
  walkInternal_spine_succ walkInternal_spine_67 rfl (by decide)
theorem walkInternal_spine_69 : walkInternal 99 (List.replicate 69 1) = some 168 :=
  walkInternal_spine_succ walkInternal_spine_68 rfl (by decide)
theorem walkInternal_spine_70 : walkInternal 99 (List.replicate 70 1) = some 169 :=
  walkInternal_spine_succ walkInternal_spine_69 rfl (by decide)
theorem walkInternal_spine_71 : walkInternal 99 (List.replicate 71 1) = some 170 :=
  walkInternal_spine_succ walkInternal_spine_70 rfl (by decide)
theorem walkInternal_spine_72 : walkInternal 99 (List.replicate 72 1) = some 171 :=
  walkInternal_spine_succ walkInternal_spine_71 rfl (by decide)
theorem walkInternal_spine_73 : walkInternal 99 (List.replicate 73 1) = some 172 :=
  walkInternal_spine_succ walkInternal_spine_72 rfl (by decide)
theorem walkInternal_spine_74 : walkInternal 99 (List.replicate 74 1) = some 173 :=
  walkInternal_spine_succ walkInternal_spine_73 rfl (by decide)
theorem walkInternal_spine_75 : walkInternal 99 (List.replicate 75 1) = some 174 :=
  walkInternal_spine_succ walkInternal_spine_74 rfl (by decide)
theorem walkInternal_spine_76 : walkInternal 99 (List.replicate 76 1) = some 175 :=
  walkInternal_spine_succ walkInternal_spine_75 rfl (by decide)
theorem walkInternal_spine_77 : walkInternal 99 (List.replicate 77 1) = some 176 :=
  walkInternal_spine_succ walkInternal_spine_76 rfl (by decide)
theorem walkInternal_spine_78 : walkInternal 99 (List.replicate 78 1) = some 177 :=
  walkInternal_spine_succ walkInternal_spine_77 rfl (by decide)
theorem walkInternal_spine_79 : walkInternal 99 (List.replicate 79 1) = some 178 :=
  walkInternal_spine_succ walkInternal_spine_78 rfl (by decide)
theorem walkInternal_spine_80 : walkInternal 99 (List.replicate 80 1) = some 179 :=
  walkInternal_spine_succ walkInternal_spine_79 rfl (by decide)
theorem walkInternal_spine_81 : walkInternal 99 (List.replicate 81 1) = some 180 :=
  walkInternal_spine_succ walkInternal_spine_80 rfl (by decide)
theorem walkInternal_spine_82 : walkInternal 99 (List.replicate 82 1) = some 181 :=
  walkInternal_spine_succ walkInternal_spine_81 rfl (by decide)
theorem walkInternal_spine_83 : walkInternal 99 (List.replicate 83 1) = some 182 :=
  walkInternal_spine_succ walkInternal_spine_82 rfl (by decide)
theorem walkInternal_spine_84 : walkInternal 99 (List.replicate 84 1) = some 183 :=
  walkInternal_spine_succ walkInternal_spine_83 rfl (by decide)
theorem walkInternal_spine_85 : walkInternal 99 (List.replicate 85 1) = some 184 :=
  walkInternal_spine_succ walkInternal_spine_84 rfl (by decide)
theorem walkInternal_spine_86 : walkInternal 99 (List.replicate 86 1) = some 185 :=
  walkInternal_spine_succ walkInternal_spine_85 rfl (by decide)
theorem walkInternal_spine_87 : walkInternal 99 (List.replicate 87 1) = some 186 :=
  walkInternal_spine_succ walkInternal_spine_86 rfl (by decide)
theorem walkInternal_spine_88 : walkInternal 99 (List.replicate 88 1) = some 187 :=
  walkInternal_spine_succ walkInternal_spine_87 rfl (by decide)
theorem walkInternal_spine_89 : walkInternal 99 (List.replicate 89 1) = some 188 :=
  walkInternal_spine_succ walkInternal_spine_88 rfl (by decide)
theorem walkInternal_spine_90 : walkInternal 99 (List.replicate 90 1) = some 189 :=
  walkInternal_spine_succ walkInternal_spine_89 rfl (by decide)
theorem walkInternal_spine_91 : walkInternal 99 (List.replicate 91 1) = some 190 :=
  walkInternal_spine_succ walkInternal_spine_90 rfl (by decide)
theorem walkInternal_spine_92 : walkInternal 99 (List.replicate 92 1) = some 191 :=
  walkInternal_spine_succ walkInternal_spine_91 rfl (by decide)
theorem walkInternal_spine_93 : walkInternal 99 (List.replicate 93 1) = some 192 :=
  walkInternal_spine_succ walkInternal_spine_92 rfl (by decide)
theorem walkInternal_spine_94 : walkInternal 99 (List.replicate 94 1) = some 193 :=
  walkInternal_spine_succ walkInternal_spine_93 rfl (by decide)
theorem walkInternal_spine_95 : walkInternal 99 (List.replicate 95 1) = some 194 :=
  walkInternal_spine_succ walkInternal_spine_94 rfl (by decide)
theorem walkInternal_spine_96 : walkInternal 99 (List.replicate 96 1) = some 195 :=
  walkInternal_spine_succ walkInternal_spine_95 rfl (by decide)
theorem walkInternal_spine_97 : walkInternal 99 (List.replicate 97 1) = some 196 :=
  walkInternal_spine_succ walkInternal_spine_96 rfl (by decide)
theorem walkInternal_spine_98 : walkInternal 99 (List.replicate 98 1) = some 197 :=
  walkInternal_spine_succ walkInternal_spine_97 rfl (by decide)
theorem walkInternal_spine_99 : walkInternal 99 (List.replicate 99 1) = some 198 :=
  walkInternal_spine_succ walkInternal_spine_98 rfl (by decide)
theorem walkInternal_spine_100 : walkInternal 99 (List.replicate 100 1) = some 199 :=
  walkInternal_spine_succ walkInternal_spine_99 rfl (by decide)
theorem walkInternal_spine_101 : walkInternal 99 (List.replicate 101 1) = some 200 :=
  walkInternal_spine_succ walkInternal_spine_100 rfl (by decide)
theorem walkInternal_spine_102 : walkInternal 99 (List.replicate 102 1) = some 201 :=
  walkInternal_spine_succ walkInternal_spine_101 rfl (by decide)
theorem walkInternal_spine_103 : walkInternal 99 (List.replicate 103 1) = some 202 :=
  walkInternal_spine_succ walkInternal_spine_102 rfl (by decide)
theorem walkInternal_spine_104 : walkInternal 99 (List.replicate 104 1) = some 203 :=
  walkInternal_spine_succ walkInternal_spine_103 rfl (by decide)
theorem walkInternal_spine_105 : walkInternal 99 (List.replicate 105 1) = some 204 :=
  walkInternal_spine_succ walkInternal_spine_104 rfl (by decide)
theorem walkInternal_spine_106 : walkInternal 99 (List.replicate 106 1) = some 205 :=
  walkInternal_spine_succ walkInternal_spine_105 rfl (by decide)
theorem walkInternal_spine_107 : walkInternal 99 (List.replicate 107 1) = some 206 :=
  walkInternal_spine_succ walkInternal_spine_106 rfl (by decide)
theorem walkInternal_spine_108 : walkInternal 99 (List.replicate 108 1) = some 207 :=
  walkInternal_spine_succ walkInternal_spine_107 rfl (by decide)
theorem walkInternal_spine_109 : walkInternal 99 (List.replicate 109 1) = some 208 :=
  walkInternal_spine_succ walkInternal_spine_108 rfl (by decide)
theorem walkInternal_spine_110 : walkInternal 99 (List.replicate 110 1) = some 209 :=
  walkInternal_spine_succ walkInternal_spine_109 rfl (by decide)
theorem walkInternal_spine_111 : walkInternal 99 (List.replicate 111 1) = some 210 :=
  walkInternal_spine_succ walkInternal_spine_110 rfl (by decide)
theorem walkInternal_spine_112 : walkInternal 99 (List.replicate 112 1) = some 211 :=
  walkInternal_spine_succ walkInternal_spine_111 rfl (by decide)
theorem walkInternal_spine_113 : walkInternal 99 (List.replicate 113 1) = some 212 :=
  walkInternal_spine_succ walkInternal_spine_112 rfl (by decide)
theorem walkInternal_spine_114 : walkInternal 99 (List.replicate 114 1) = some 213 :=
  walkInternal_spine_succ walkInternal_spine_113 rfl (by decide)
theorem walkInternal_spine_115 : walkInternal 99 (List.replicate 115 1) = some 214 :=
  walkInternal_spine_succ walkInternal_spine_114 rfl (by decide)
theorem walkInternal_spine_116 : walkInternal 99 (List.replicate 116 1) = some 215 :=
  walkInternal_spine_succ walkInternal_spine_115 rfl (by decide)
theorem walkInternal_spine_117 : walkInternal 99 (List.replicate 117 1) = some 216 :=
  walkInternal_spine_succ walkInternal_spine_116 rfl (by decide)
theorem walkInternal_spine_118 : walkInternal 99 (List.replicate 118 1) = some 217 :=
  walkInternal_spine_succ walkInternal_spine_117 rfl (by decide)
theorem walkInternal_spine_119 : walkInternal 99 (List.replicate 119 1) = some 218 :=
  walkInternal_spine_succ walkInternal_spine_118 rfl (by decide)
theorem walkInternal_spine_120 : walkInternal 99 (List.replicate 120 1) = some 219 :=
  walkInternal_spine_succ walkInternal_spine_119 rfl (by decide)
theorem walkInternal_spine_121 : walkInternal 99 (List.replicate 121 1) = some 220 :=
  walkInternal_spine_succ walkInternal_spine_120 rfl (by decide)
theorem walkInternal_spine_122 : walkInternal 99 (List.replicate 122 1) = some 221 :=
  walkInternal_spine_succ walkInternal_spine_121 rfl (by decide)
theorem walkInternal_spine_123 : walkInternal 99 (List.replicate 123 1) = some 222 :=
  walkInternal_spine_succ walkInternal_spine_122 rfl (by decide)
theorem walkInternal_spine_124 : walkInternal 99 (List.replicate 124 1) = some 223 :=
  walkInternal_spine_succ walkInternal_spine_123 rfl (by decide)

def WffSubEval (q : Fin 393) (op : WffState → WffState) : Prop :=
  ∀ (P : List (Fin 2)),
    walkInternal 99 P = some q →
    ∀ (pl np : ℕ) (s : WffState),
      ∃ steps ≥ 1, zfReg11NSteps steps ⟨trimZeros P, wffStateToRegs pl np s⟩ =
        some ⟨retStack P, wffStateToRegs pl np (op s)⟩

theorem wffSubEval_of_subEval {q : Fin 393} {f : List ℕ → List ℕ}
    {op : WffState → WffState} (hsub : SubEval q f)
    (heq : ∀ pl np s, f (wffStateToRegs pl np s) = wffStateToRegs pl np (op s)) :
    WffSubEval q op := by
  intro P hP pl np s
  obtain ⟨steps, hsteps, heval, _⟩ := hsub P hP (wffStateToRegs pl np s) rfl
  rw [heq pl np s] at heval
  exact ⟨steps, hsteps, heval⟩

theorem wffSubEval_seq {q q0 q1 : Fin 393} {op0 op1 op : WffState → WffState}
    (htr0 : zf393Trans q 0 = some (0, .right, q0)) (hq0 : 69 ≤ q0.val)
    (htr1 : zf393Trans q 1 = some (1, .right, q1)) (hq1 : 69 ≤ q1.val)
    (h0 : WffSubEval q0 op0) (h1 : WffSubEval q1 op1)
    (heq : (fun s => op1 (op0 s)) = op := by rfl) :
    WffSubEval q op := by
  subst heq
  intro P hP pl np s
  have hP0 : walkInternal 99 (P ++ [0]) = some q0 := walkInternal_snoc hP htr0 hq0
  have hP1 : walkInternal 99 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  obtain ⟨s0, hs0, hsteps0⟩ := h0 (P ++ [0]) hP0 pl np s
  rw [trimZeros_append_zero, retStack_append_zero] at hsteps0
  obtain ⟨s1, hs1, hsteps1⟩ := h1 (P ++ [1]) hP1 pl np (op0 s)
  rw [trimZeros_append_one, retStack_append_one] at hsteps1
  exact ⟨s0 + s1, by omega, zfReg11NSteps_bind_eq hsteps0 hsteps1⟩

theorem wffSubEval_79 : WffSubEval 79 rpnCparam2 :=
  wffSubEval_of_subEval subEval_79_inst regCparam2Op_wffStateToRegs
theorem wffSubEval_81 : WffSubEval 81 rpnCparam3 :=
  wffSubEval_of_subEval subEval_81_inst regCparam3Op_wffStateToRegs
theorem wffSubEval_298 : WffSubEval 298 rpnPar1 :=
  wffSubEval_of_subEval subEval_298 regPar1Op_wffStateToRegs
theorem wffSubEval_300 : WffSubEval 300 rpnPar2 :=
  wffSubEval_of_subEval subEval_300 regPar2Op_wffStateToRegs
theorem wffSubEval_302 : WffSubEval 302 rpnPar3 :=
  wffSubEval_of_subEval subEval_302 regPar3Op_wffStateToRegs
theorem wffSubEval_304 : WffSubEval 304 (rpnVk 0) :=
  wffSubEval_of_subEval subEval_304 regPushwffOp_wffStateToRegs
theorem wffSubEval_305 : WffSubEval 305 rpnSelect :=
  wffSubEval_of_subEval subEval_305_inst regSelectOp_wffStateToRegs
theorem wffSubEval_319 : WffSubEval 319 (rpnVk 1) :=
  wffSubEval_of_subEval subEval_319 regV1Op_wffStateToRegs
theorem wffSubEval_320 : WffSubEval 320 (rpnVk 2) :=
  wffSubEval_of_subEval subEval_320 regV2Op_wffStateToRegs
theorem wffSubEval_321 : WffSubEval 321 (rpnVk 3) :=
  wffSubEval_of_subEval subEval_321 regV3Op_wffStateToRegs
theorem wffSubEval_323 : WffSubEval 323 rpnWa :=
  wffSubEval_of_subEval subEval_323 regWaOp_wffStateToRegs
theorem wffSubEval_325 : WffSubEval 325 rpnWal :=
  wffSubEval_of_subEval subEval_325 regWalOp_wffStateToRegs
theorem wffSubEval_327 : WffSubEval 327 rpnWel :=
  wffSubEval_of_subEval subEval_327 regWelOp_wffStateToRegs
theorem wffSubEval_329 : WffSubEval 329 rpnWeq :=
  wffSubEval_of_subEval subEval_329 regWeqOp_wffStateToRegs
theorem wffSubEval_331 : WffSubEval 331 rpnWex :=
  wffSubEval_of_subEval subEval_331 regWexOp_wffStateToRegs
theorem wffSubEval_390 : WffSubEval 390 rpnWim :=
  wffSubEval_of_subEval subEval_390 regWimOp_wffStateToRegs
theorem wffSubEval_392 : WffSubEval 392 rpnWn :=
  wffSubEval_of_subEval subEval_392 regWnOp_wffStateToRegs

abbrev wffOp_277 (s : WffState) : WffState := (rpnVk 2) ((rpnVk 1) s)
theorem wffSubEval_277 : WffSubEval 277 wffOp_277 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_319 wffSubEval_320
abbrev wffOp_266 (s : WffState) : WffState := rpnWal (rpnPar1 s)
theorem wffSubEval_266 : WffSubEval 266 wffOp_266 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_298 wffSubEval_325
abbrev wffOp_265 (s : WffState) : WffState := wffOp_266 ((rpnVk 1) s)
theorem wffSubEval_265 : WffSubEval 265 wffOp_265 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_319 wffSubEval_266
abbrev wffOp_258 (s : WffState) : WffState := rpnWim (rpnWeq s)
theorem wffSubEval_258 : WffSubEval 258 wffOp_258 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_329 wffSubEval_390
abbrev wffOp_257 (s : WffState) : WffState := wffOp_258 ((rpnVk 1) s)
theorem wffSubEval_257 : WffSubEval 257 wffOp_257 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_319 wffSubEval_258
abbrev wffOp_270 (s : WffState) : WffState := rpnWex (rpnWal s)
theorem wffSubEval_270 : WffSubEval 270 wffOp_270 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_325 wffSubEval_331
abbrev wffOp_280 (s : WffState) : WffState := rpnWel ((rpnVk 1) s)
theorem wffSubEval_280 : WffSubEval 280 wffOp_280 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_319 wffSubEval_327
abbrev wffOp_263 (s : WffState) : WffState := wffOp_280 ((rpnVk 2) s)
theorem wffSubEval_263 : WffSubEval 263 wffOp_263 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_320 wffSubEval_280
abbrev wffOp_249 (s : WffState) : WffState := wffOp_263 ((rpnVk 2) s)
theorem wffSubEval_249 : WffSubEval 249 wffOp_249 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_320 wffSubEval_263
abbrev wffOp_287 (s : WffState) : WffState := rpnWel ((rpnVk 0) s)
theorem wffSubEval_287 : WffSubEval 287 wffOp_287 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_304 wffSubEval_327
abbrev wffOp_264 (s : WffState) : WffState := wffOp_287 ((rpnVk 3) s)
theorem wffSubEval_264 : WffSubEval 264 wffOp_264 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_321 wffSubEval_287
abbrev wffOp_278 (s : WffState) : WffState := rpnWex (rpnWa s)
theorem wffSubEval_278 : WffSubEval 278 wffOp_278 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_323 wffSubEval_331
abbrev wffOp_240 (s : WffState) : WffState := wffOp_278 (wffOp_265 s)
theorem wffSubEval_240 : WffSubEval 240 wffOp_240 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_265 wffSubEval_278
abbrev wffOp_239 (s : WffState) : WffState := wffOp_240 (wffOp_264 s)
theorem wffSubEval_239 : WffSubEval 239 wffOp_239 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_264 wffSubEval_240
abbrev wffOp_238 (s : WffState) : WffState := wffOp_239 ((rpnVk 3) s)
theorem wffSubEval_238 : WffSubEval 238 wffOp_238 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_321 wffSubEval_239
abbrev wffOp_248 (s : WffState) : WffState := rpnWim (wffOp_263 s)
theorem wffSubEval_248 : WffSubEval 248 wffOp_248 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_263 wffSubEval_390
abbrev wffOp_281 (s : WffState) : WffState := rpnSelect (rpnWim s)
theorem wffSubEval_281 : WffSubEval 281 wffOp_281 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_390 wffSubEval_305
abbrev wffOp_267 (s : WffState) : WffState := (rpnVk 1) (wffOp_281 s)
theorem wffSubEval_267 : WffSubEval 267 wffOp_267 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_281 wffSubEval_319
abbrev wffOp_285 (s : WffState) : WffState := (rpnVk 3) ((rpnVk 2) s)
theorem wffSubEval_285 : WffSubEval 285 wffOp_285 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_320 wffSubEval_321
abbrev wffOp_245 (s : WffState) : WffState := wffOp_285 (wffOp_267 s)
theorem wffSubEval_245 : WffSubEval 245 wffOp_245 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_267 wffSubEval_285
abbrev wffOp_247 (s : WffState) : WffState := wffOp_264 (rpnWel s)
theorem wffSubEval_247 : WffSubEval 247 wffOp_247 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_327 wffSubEval_264
abbrev wffOp_272 (s : WffState) : WffState := rpnWal (rpnWim s)
theorem wffSubEval_272 : WffSubEval 272 wffOp_272 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_390 wffSubEval_325
abbrev wffOp_283 (s : WffState) : WffState := rpnPar1 (rpnSelect s)
theorem wffSubEval_283 : WffSubEval 283 wffOp_283 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_305 wffSubEval_298
abbrev wffOp_242 (s : WffState) : WffState := wffOp_283 (wffOp_270 s)
theorem wffSubEval_242 : WffSubEval 242 wffOp_242 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_270 wffSubEval_283
abbrev wffOp_241 (s : WffState) : WffState := wffOp_242 (wffOp_248 s)
theorem wffSubEval_241 : WffSubEval 241 wffOp_241 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_248 wffSubEval_242
abbrev wffOp_274 (s : WffState) : WffState := rpnPar1 (rpnWim s)
theorem wffSubEval_274 : WffSubEval 274 wffOp_274 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_390 wffSubEval_298
abbrev wffOp_268 (s : WffState) : WffState := wffOp_281 (rpnWim s)
theorem wffSubEval_268 : WffSubEval 268 wffOp_268 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_390 wffSubEval_281
abbrev wffOp_279 (s : WffState) : WffState := rpnPar2 (rpnPar1 s)
theorem wffSubEval_279 : WffSubEval 279 wffOp_279 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_298 wffSubEval_300
abbrev wffOp_246 (s : WffState) : WffState := wffOp_279 (wffOp_268 s)
theorem wffSubEval_246 : WffSubEval 246 wffOp_246 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_268 wffSubEval_279
abbrev wffOp_284 (s : WffState) : WffState := rpnPar3 (rpnPar1 s)
theorem wffSubEval_284 : WffSubEval 284 wffOp_284 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_298 wffSubEval_302
abbrev wffOp_286 (s : WffState) : WffState := wffOp_284 (rpnWeq s)
theorem wffSubEval_286 : WffSubEval 286 wffOp_286 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_329 wffSubEval_284
abbrev wffOp_243 (s : WffState) : WffState := wffOp_286 (wffOp_246 s)
theorem wffSubEval_243 : WffSubEval 243 wffOp_243 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_246 wffSubEval_286
abbrev wffOp_273 (s : WffState) : WffState := rpnPar3 (rpnPar2 s)
theorem wffSubEval_273 : WffSubEval 273 wffOp_273 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_300 wffSubEval_302
abbrev wffOp_244 (s : WffState) : WffState := wffOp_246 (rpnWel s)
theorem wffSubEval_244 : WffSubEval 244 wffOp_244 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_327 wffSubEval_246
abbrev wffOp_282 (s : WffState) : WffState := rpnPar1 (rpnPar3 s)
theorem wffSubEval_282 : WffSubEval 282 wffOp_282 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_302 wffSubEval_298
abbrev wffOp_230 (s : WffState) : WffState := wffOp_282 (rpnWeq s)
theorem wffSubEval_230 : WffSubEval 230 wffOp_230 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_329 wffSubEval_282
abbrev wffOp_229 (s : WffState) : WffState := wffOp_230 (wffOp_244 s)
theorem wffSubEval_229 : WffSubEval 229 wffOp_229 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_244 wffSubEval_230
abbrev wffOp_228 (s : WffState) : WffState := wffOp_229 (wffOp_273 s)
theorem wffSubEval_228 : WffSubEval 228 wffOp_228 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_273 wffSubEval_229
abbrev wffOp_227 (s : WffState) : WffState := wffOp_228 (rpnWel s)
theorem wffSubEval_227 : WffSubEval 227 wffOp_227 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_327 wffSubEval_228
abbrev wffOp_226 (s : WffState) : WffState := wffOp_227 (wffOp_243 s)
theorem wffSubEval_226 : WffSubEval 226 wffOp_226 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_243 wffSubEval_227
abbrev wffOp_271 (s : WffState) : WffState := rpnWim (rpnWal s)
theorem wffSubEval_271 : WffSubEval 271 wffOp_271 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_325 wffSubEval_390
abbrev wffOp_254 (s : WffState) : WffState := rpnWel (wffOp_279 s)
theorem wffSubEval_254 : WffSubEval 254 wffOp_254 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_279 wffSubEval_327
abbrev wffOp_253 (s : WffState) : WffState := wffOp_273 (wffOp_283 s)
theorem wffSubEval_253 : WffSubEval 253 wffOp_253 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_283 wffSubEval_273
abbrev wffOp_259 (s : WffState) : WffState := rpnWal (wffOp_284 s)
theorem wffSubEval_259 : WffSubEval 259 wffOp_259 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_284 wffSubEval_325
abbrev wffOp_237 (s : WffState) : WffState := wffOp_279 (wffOp_283 s)
theorem wffSubEval_237 : WffSubEval 237 wffOp_237 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_283 wffSubEval_279
abbrev wffOp_236 (s : WffState) : WffState := wffOp_237 (wffOp_271 s)
theorem wffSubEval_236 : WffSubEval 236 wffOp_236 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_271 wffSubEval_237
abbrev wffOp_235 (s : WffState) : WffState := wffOp_236 (wffOp_259 s)
theorem wffSubEval_235 : WffSubEval 235 wffOp_235 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_259 wffSubEval_236
abbrev wffOp_234 (s : WffState) : WffState := wffOp_235 (rpnPar2 s)
theorem wffSubEval_234 : WffSubEval 234 wffOp_234 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_300 wffSubEval_235
abbrev wffOp_233 (s : WffState) : WffState := wffOp_234 (rpnWal s)
theorem wffSubEval_233 : WffSubEval 233 wffOp_233 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_325 wffSubEval_234
abbrev wffOp_232 (s : WffState) : WffState := wffOp_233 (rpnWal s)
theorem wffSubEval_232 : WffSubEval 232 wffOp_232 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_325 wffSubEval_233
abbrev wffOp_231 (s : WffState) : WffState := wffOp_232 (wffOp_253 s)
theorem wffSubEval_231 : WffSubEval 231 wffOp_231 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_253 wffSubEval_232
abbrev wffOp_275 (s : WffState) : WffState := (rpnVk 0) ((rpnVk 2) s)
theorem wffSubEval_275 : WffSubEval 275 wffOp_275 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_320 wffSubEval_304
abbrev wffOp_252 (s : WffState) : WffState := rpnWal (rpnWa s)
theorem wffSubEval_252 : WffSubEval 252 wffOp_252 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_323 wffSubEval_325
abbrev wffOp_251 (s : WffState) : WffState := wffOp_252 (rpnWim s)
theorem wffSubEval_251 : WffSubEval 251 wffOp_251 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_390 wffSubEval_252
abbrev wffOp_250 (s : WffState) : WffState := wffOp_251 (rpnWel s)
theorem wffSubEval_250 : WffSubEval 250 wffOp_250 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_327 wffSubEval_251
abbrev wffOp_276 (s : WffState) : WffState := rpnCparam3 (rpnSelect s)
theorem wffSubEval_276 : WffSubEval 276 wffOp_276 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_305 wffSubEval_81
abbrev wffOp_260 (s : WffState) : WffState := wffOp_280 ((rpnVk 0) s)
theorem wffSubEval_260 : WffSubEval 260 wffOp_260 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_304 wffSubEval_280
abbrev wffOp_262 (s : WffState) : WffState := rpnWeq ((rpnVk 0) s)
theorem wffSubEval_262 : WffSubEval 262 wffOp_262 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_304 wffSubEval_329
abbrev wffOp_261 (s : WffState) : WffState := wffOp_262 ((rpnVk 1) s)
theorem wffSubEval_261 : WffSubEval 261 wffOp_261 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_319 wffSubEval_262

def WffSpineEval (k₁ k₂ : ℕ) (op : WffState → WffState) : Prop :=
  ∀ (pl np : ℕ) (s : WffState),
    ∃ steps ≥ 1, zfReg11NSteps steps ⟨List.replicate k₁ 1, wffStateToRegs pl np s⟩ =
      some ⟨List.replicate k₂ 1, wffStateToRegs pl np (op s)⟩

theorem wffSpineEval_step {k k' : ℕ} {q_k q_sub : Fin 393} {op : WffState → WffState}
    (hwalk : walkInternal 99 (List.replicate k 1) = some q_k)
    (htr0 : zf393Trans q_k 0 = some (0, .right, q_sub))
    (hq_sub : 69 ≤ q_sub.val)
    (hsub : WffSubEval q_sub op)
    (hk : k + 1 = k' := by rfl) :
    WffSpineEval k k' op := by
  subst hk
  intro pl np s
  have hwalk0 : walkInternal 99 (List.replicate k 1 ++ [0]) = some q_sub :=
    walkInternal_snoc hwalk htr0 hq_sub
  obtain ⟨steps, hsteps, heval⟩ := hsub (List.replicate k 1 ++ [0]) hwalk0 pl np s
  rw [trimZeros_append_zero, trimZeros_replicate_one, retStack_append_zero,
    ← List.replicate_succ'] at heval
  exact ⟨steps, hsteps, heval⟩

theorem wffSpineEval_trans {k₁ k₂ k₃ : ℕ} {op₁ op₂ op : WffState → WffState}
    (h1 : WffSpineEval k₁ k₂ op₁) (h2 : WffSpineEval k₂ k₃ op₂)
    (heq : (fun s => op₂ (op₁ s)) = op := by rfl) :
    WffSpineEval k₁ k₃ op := by
  subst heq
  intro pl np s
  obtain ⟨s₁, hs₁, heval₁⟩ := h1 pl np s
  obtain ⟨s₂, hs₂, heval₂⟩ := h2 pl np (op₁ s)
  exact ⟨s₁ + s₂, by omega, zfReg11NSteps_bind_eq heval₁ heval₂⟩

theorem wffSpineEval_of_regSpineEval {k₁ k₂ : ℕ} {f : List ℕ → List ℕ}
    {op : WffState → WffState} (h : RegSpineEval k₁ k₂ f)
    (heq : ∀ pl np s, f (wffStateToRegs pl np s) = wffStateToRegs pl np (op s)) :
    WffSpineEval k₁ k₂ op := by
  intro pl np s
  obtain ⟨steps, hsteps, heval, _⟩ := h (wffStateToRegs pl np s) rfl
  rw [heq pl np s] at heval
  exact ⟨steps, hsteps, heval⟩

/-- Bugfixed first variable-distinctness check in `B6a` (`zf393`, `k = 55..58`):
checks `s.param1 = s.param3` and restores BOTH `param1` and `param3`. -/
def rpnZf393B6aCheck1 (s : WffState) : WffState :=
  { s with topwff := if s.param1 = s.param3 then 0 else s.topwff }

/-- Bugfixed second variable-distinctness check in `B6a` (`zf393`, `k = 58..61`):
checks `s.param2 = s.param3` and restores BOTH `param2` and `param3`. -/
def rpnZf393B6aCheck2 (s : WffState) : WffState :=
  { s with topwff := if s.param2 = s.param3 then 0 else s.topwff }

theorem wffSpineEval_55_58 : WffSpineEval 55 58 rpnZf393B6aCheck1 := by
  refine wffSpineEval_of_regSpineEval
    (regSpineEval_trans (regSpineEval_step walkInternal_spine_55 rfl (by decide) subEval_351) <|
     regSpineEval_trans (regSpineEval_step walkInternal_spine_56 rfl (by decide) subEval_364) <|
     regSpineEval_step walkInternal_spine_57 rfl (by decide) subEval_255) ?_
  intro pl np s
  simp only [wffStateToRegs, reg255Op, reg256Op, reg92Op, rpnZf393B6aCheck1, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, Nat.zero_add]
  split_ifs <;> rfl

theorem wffSpineEval_58_61 : WffSpineEval 58 61 rpnZf393B6aCheck2 := by
  refine wffSpineEval_of_regSpineEval
    (regSpineEval_trans (regSpineEval_step walkInternal_spine_58 rfl (by decide) subEval_355) <|
     regSpineEval_trans (regSpineEval_step walkInternal_spine_59 rfl (by decide) subEval_366) <|
     regSpineEval_step walkInternal_spine_60 rfl (by decide) subEval_255) ?_
  intro pl np s
  simp only [wffStateToRegs, reg255Op, reg256Op, reg92Op, rpnZf393B6aCheck2, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, Nat.zero_add]
  split_ifs <;> rfl

theorem wffSpineEval_97_101 : WffSpineEval 97 101 rpnDetCheck := by
  refine wffSpineEval_of_regSpineEval
    (regSpineEval_trans (regSpineEval_step walkInternal_spine_97 rfl (by decide) subEval_388) <|
     regSpineEval_trans (regSpineEval_step walkInternal_spine_98 rfl (by decide) subEval_354) <|
     regSpineEval_trans (regSpineEval_step walkInternal_spine_99 rfl (by decide) subEval_366) <|
     regSpineEval_step walkInternal_spine_100 rfl (by decide) subEval_93) ?_
  intro pl np s
  simp only [wffStateToRegs, reg93Op, reg94Op, rpnDetCheck, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, Nat.zero_add]
  split_ifs <;> rfl

abbrev wffSpineOp_13_21 (s : WffState) : WffState :=
  rpnWal (wffOp_270 (wffOp_257 ((rpnVk 2) (wffOp_265 (wffOp_277 ((rpnVk 3) ((rpnVk 0) (s))))))))
theorem wffSpineEval_13_21 : WffSpineEval 13 21 wffSpineOp_13_21 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_13 rfl (by decide) wffSubEval_304) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_14 rfl (by decide) wffSubEval_321) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_15 rfl (by decide) wffSubEval_277) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_16 rfl (by decide) wffSubEval_265) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_17 rfl (by decide) wffSubEval_320) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_18 rfl (by decide) wffSubEval_257) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_19 rfl (by decide) wffSubEval_270) <|
  (wffSpineEval_step walkInternal_spine_20 rfl (by decide) wffSubEval_325)
abbrev wffSpineOp_21_29 (s : WffState) : WffState :=
  wffOp_270 (rpnWa (wffOp_248 (wffOp_238 (rpnWim (wffOp_238 (wffOp_249 ((rpnVk 1) (s))))))))
theorem wffSpineEval_21_29 : WffSpineEval 21 29 wffSpineOp_21_29 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_21 rfl (by decide) wffSubEval_319) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_22 rfl (by decide) wffSubEval_249) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_23 rfl (by decide) wffSubEval_238) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_24 rfl (by decide) wffSubEval_390) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_25 rfl (by decide) wffSubEval_238) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_26 rfl (by decide) wffSubEval_248) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_27 rfl (by decide) wffSubEval_323) <|
  (wffSpineEval_step walkInternal_spine_28 rfl (by decide) wffSubEval_270)
abbrev wffSpineOp_29_37 (s : WffState) : WffState :=
  rpnPar1 (rpnWn (wffOp_241 (wffOp_272 (wffOp_247 ((rpnVk 2) ((rpnVk 3) (wffOp_245 (s))))))))
theorem wffSpineEval_29_37 : WffSpineEval 29 37 wffSpineOp_29_37 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_29 rfl (by decide) wffSubEval_245) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_30 rfl (by decide) wffSubEval_321) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_31 rfl (by decide) wffSubEval_320) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_32 rfl (by decide) wffSubEval_247) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_33 rfl (by decide) wffSubEval_272) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_34 rfl (by decide) wffSubEval_241) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_35 rfl (by decide) wffSubEval_392) <|
  (wffSpineEval_step walkInternal_spine_36 rfl (by decide) wffSubEval_298)
abbrev wffSpineOp_37_45 (s : WffState) : WffState :=
  rpnWn (rpnPar1 (wffOp_241 (wffOp_278 (wffOp_247 (wffOp_285 (wffOp_245 (wffOp_274 (s))))))))
theorem wffSpineEval_37_45 : WffSpineEval 37 45 wffSpineOp_37_45 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_37 rfl (by decide) wffSubEval_274) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_38 rfl (by decide) wffSubEval_245) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_39 rfl (by decide) wffSubEval_285) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_40 rfl (by decide) wffSubEval_247) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_41 rfl (by decide) wffSubEval_278) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_42 rfl (by decide) wffSubEval_241) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_43 rfl (by decide) wffSubEval_298) <|
  (wffSpineEval_step walkInternal_spine_44 rfl (by decide) wffSubEval_392)
abbrev wffSpineOp_45_55 (s : WffState) : WffState :=
  rpnWa (wffOp_271 (wffOp_254 (rpnPar3 (wffOp_254 (wffOp_271 (rpnWeq (rpnPar2 (wffOp_226 (rpnPar2
    (s))))))))))
theorem wffSpineEval_45_55 : WffSpineEval 45 55 wffSpineOp_45_55 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_45 rfl (by decide) wffSubEval_300) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_46 rfl (by decide) wffSubEval_226) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_47 rfl (by decide) wffSubEval_300) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_48 rfl (by decide) wffSubEval_329) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_49 rfl (by decide) wffSubEval_271) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_50 rfl (by decide) wffSubEval_254) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_51 rfl (by decide) wffSubEval_302) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_52 rfl (by decide) wffSubEval_254) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_53 rfl (by decide) wffSubEval_271) <|
  (wffSpineEval_step walkInternal_spine_54 rfl (by decide) wffSubEval_323)
abbrev wffSpineOp_55_65 (s : WffState) : WffState :=
  wffOp_253 (rpnWex (rpnWeq (wffOp_231 (rpnZf393B6aCheck2 (rpnZf393B6aCheck1 (s))))))
theorem wffSpineEval_55_65 : WffSpineEval 55 65 wffSpineOp_55_65 :=
  wffSpineEval_trans wffSpineEval_55_58 <|
  wffSpineEval_trans wffSpineEval_58_61 <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_61 rfl (by decide) wffSubEval_231) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_62 rfl (by decide) wffSubEval_329) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_63 rfl (by decide) wffSubEval_331) <|
  (wffSpineEval_step walkInternal_spine_64 rfl (by decide) wffSubEval_253)
abbrev wffSpineOp_65_73 (s : WffState) : WffState :=
  rpnWeq (wffOp_273 (rpnWeq (wffOp_243 (wffOp_259 (rpnWal (wffOp_279 (wffOp_272 (s))))))))
theorem wffSpineEval_65_73 : WffSpineEval 65 73 wffSpineOp_65_73 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_65 rfl (by decide) wffSubEval_272) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_66 rfl (by decide) wffSubEval_279) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_67 rfl (by decide) wffSubEval_325) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_68 rfl (by decide) wffSubEval_259) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_69 rfl (by decide) wffSubEval_243) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_70 rfl (by decide) wffSubEval_329) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_71 rfl (by decide) wffSubEval_273) <|
  (wffSpineEval_step walkInternal_spine_72 rfl (by decide) wffSubEval_329)
abbrev wffSpineOp_73_81 (s : WffState) : WffState :=
  wffOp_274 (wffOp_273 (rpnWim (wffOp_244 (rpnPar2 (rpnPar3 (rpnWel (wffOp_226 (s))))))))
theorem wffSpineEval_73_81 : WffSpineEval 73 81 wffSpineOp_73_81 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_73 rfl (by decide) wffSubEval_226) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_74 rfl (by decide) wffSubEval_327) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_75 rfl (by decide) wffSubEval_302) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_76 rfl (by decide) wffSubEval_300) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_77 rfl (by decide) wffSubEval_244) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_78 rfl (by decide) wffSubEval_390) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_79 rfl (by decide) wffSubEval_273) <|
  (wffSpineEval_step walkInternal_spine_80 rfl (by decide) wffSubEval_274)
abbrev wffSpineOp_81_89 (s : WffState) : WffState :=
  wffOp_263 (wffOp_248 (rpnWel (wffOp_275 ((rpnVk 2) (wffOp_268 (rpnWim (rpnPar3 (s))))))))
theorem wffSpineEval_81_89 : WffSpineEval 81 89 wffSpineOp_81_89 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_81 rfl (by decide) wffSubEval_302) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_82 rfl (by decide) wffSubEval_390) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_83 rfl (by decide) wffSubEval_268) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_84 rfl (by decide) wffSubEval_320) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_85 rfl (by decide) wffSubEval_275) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_86 rfl (by decide) wffSubEval_327) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_87 rfl (by decide) wffSubEval_248) <|
  (wffSpineEval_step walkInternal_spine_88 rfl (by decide) wffSubEval_263)
abbrev wffSpineOp_89_97 (s : WffState) : WffState :=
  rpnWim (wffOp_282 (rpnCparam2 (wffOp_276 (wffOp_257 ((rpnVk 0) (wffOp_250 (wffOp_275 (s))))))))
theorem wffSpineEval_89_97 : WffSpineEval 89 97 wffSpineOp_89_97 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_89 rfl (by decide) wffSubEval_275) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_90 rfl (by decide) wffSubEval_250) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_91 rfl (by decide) wffSubEval_304) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_92 rfl (by decide) wffSubEval_257) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_93 rfl (by decide) wffSubEval_276) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_94 rfl (by decide) wffSubEval_79) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_95 rfl (by decide) wffSubEval_282) <|
  (wffSpineEval_step walkInternal_spine_96 rfl (by decide) wffSubEval_390)
abbrev wffSpineOp_97_106 (s : WffState) : WffState :=
  rpnPar2 (wffOp_270 (wffOp_231 (wffOp_259 (wffOp_276 (rpnDetCheck (s))))))
theorem wffSpineEval_97_106 : WffSpineEval 97 106 wffSpineOp_97_106 :=
  wffSpineEval_trans wffSpineEval_97_101 <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_101 rfl (by decide) wffSubEval_276) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_102 rfl (by decide) wffSubEval_259) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_103 rfl (by decide) wffSubEval_231) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_104 rfl (by decide) wffSubEval_270) <|
  (wffSpineEval_step walkInternal_spine_105 rfl (by decide) wffSubEval_300)
abbrev wffSpineOp_106_114 (s : WffState) : WffState :=
  rpnWel (wffOp_277 ((rpnVk 1) (wffOp_249 (wffOp_260 ((rpnVk 0) (wffOp_260 (wffOp_267 (s))))))))
theorem wffSpineEval_106_114 : WffSpineEval 106 114 wffSpineOp_106_114 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_106 rfl (by decide) wffSubEval_267) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_107 rfl (by decide) wffSubEval_260) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_108 rfl (by decide) wffSubEval_304) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_109 rfl (by decide) wffSubEval_260) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_110 rfl (by decide) wffSubEval_249) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_111 rfl (by decide) wffSubEval_319) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_112 rfl (by decide) wffSubEval_277) <|
  (wffSpineEval_step walkInternal_spine_113 rfl (by decide) wffSubEval_327)
abbrev wffSpineOp_114_123 (s : WffState) : WffState :=
  rpnSelect (wffOp_278 (wffOp_272 (wffOp_278 (wffOp_250 (wffOp_277 (wffOp_261 (rpnWim (wffOp_261
    (s)))))))))
theorem wffSpineEval_114_123 : WffSpineEval 114 123 wffSpineOp_114_123 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_114 rfl (by decide) wffSubEval_261) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_115 rfl (by decide) wffSubEval_390) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_116 rfl (by decide) wffSubEval_261) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_117 rfl (by decide) wffSubEval_277) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_118 rfl (by decide) wffSubEval_250) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_119 rfl (by decide) wffSubEval_278) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_120 rfl (by decide) wffSubEval_272) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_121 rfl (by decide) wffSubEval_278) <|
  (wffSpineEval_step walkInternal_spine_122 rfl (by decide) wffSubEval_305)

def rpnZf393ClauseB6a (s : WffState) : WffState :=
  let s1 :=
    rpnWim (rpnWal (rpnWeq (rpnPar2 (rpnPar1 (rpnPar3 (rpnWeq (rpnPar2 (rpnPar1 s))))))))
  let s2 :=
    rpnWa (rpnWim (rpnWal (rpnWel (rpnPar2 (rpnPar1 (rpnPar3 (rpnWel (rpnPar2 (rpnPar1 s1)))))))))
  rpnSelect (rpnZf393B6aCheck2 (rpnZf393B6aCheck1 s2))

def rpnZf393AllClausesOp (s : WffState) : WffState :=
  let s0 := rpnVk 0 s
  rpnClauseINF (rpnClauseB6c (rpnClauseB6b (rpnClauseGEN (rpnClauseDET
    (rpnClauseEXT (rpnClauseB1 (rpnClauseB8c (rpnClauseB8b (rpnClauseB8a
      (rpnClauseB4 (rpnClauseB7 (rpnClauseB6b (rpnZf393ClauseB6a (rpnClauseB8b
        (rpnClauseB3 (rpnClauseUNI (rpnClauseB2 (rpnClausePOW (rpnClauseREP s0)))))))))))))))))))

def rpnZf393AllClauses (top stk ac p1 p2 p3 : ℕ) : WffState :=
  rpnZf393AllClausesOp ⟨top, stk, ac, p1, p2, p3⟩

theorem wffSpineEval_13_123 : WffSpineEval 13 123 rpnZf393AllClausesOp :=
  wffSpineEval_trans wffSpineEval_13_21 <|
  wffSpineEval_trans wffSpineEval_21_29 <|
  wffSpineEval_trans wffSpineEval_29_37 <|
  wffSpineEval_trans wffSpineEval_37_45 <|
  wffSpineEval_trans wffSpineEval_45_55 <|
  wffSpineEval_trans wffSpineEval_55_65 <|
  wffSpineEval_trans wffSpineEval_65_73 <|
  wffSpineEval_trans wffSpineEval_73_81 <|
  wffSpineEval_trans wffSpineEval_81_89 <|
  wffSpineEval_trans wffSpineEval_89_97 <|
  wffSpineEval_trans wffSpineEval_97_106 <|
  wffSpineEval_trans wffSpineEval_106_114 <|
  wffSpineEval_114_123


@[simp]
theorem rpnZf393ClauseB6a_eval (top stk ac p1 p2 p3 : ℕ) :
    rpnZf393ClauseB6a ⟨top, stk, ac, p1, p2, p3⟩ =
      ⟨if ac > 0 then (if p1 = p3 ∨ p2 = p3 then 0 else axB6a p1 p2 p3) else top,
       stk, ac - 1, p1, p2, p3⟩ := by
  by_cases hp1 : p1 = p3 <;> by_cases hp2 : p2 = p3 <;>
    simp [rpnZf393ClauseB6a, rpnZf393B6aCheck1, rpnZf393B6aCheck2,
      rpnPar1, rpnPar2, rpnPar3, axB6a, hp1, hp2]

/-- Exact 20-clause dispatch of `zf393` (`zf2.tm` / `zf2.py` post-`10fcf152b3`). -/
def zf393ClauseDispatch (topwff wffstack ac p1 p2 p3 : ℕ) : ℕ × ℕ :=
  let stk0 := cantorPair topwff wffstack
  match ac with
  | 0 => (0, stk0)
  | 1 => (axRep p1, stk0)
  | 2 => (axPow, stk0)
  | 3 => (axB2 p1, stk0)
  | 4 => (axUni, stk0)
  | 5 => (axB3 p1 p2, stk0)
  | 6 => (axB8b p1 p2 p3, stk0)
  | 7 => if p1 = p3 ∨ p2 = p3 then (0, stk0) else (axB6a p1 p2 p3, stk0)
  | 8 => (axB6b p1 p2 p3, stk0)
  | 9 => (axB7 p1 p2, stk0)
  | 10 => (axB4 p1 p2 p3, stk0)
  | 11 => (axB8a p1 p2 p3, stk0)
  | 12 => (axB8b p1 p2 p3, stk0)
  | 13 => (axB8c p1 p2 p3, stk0)
  | 14 => (axB1 p1 p2 p3, stk0)
  | 15 => (axExt, stk0)
  | 16 =>
    let pop1 := cantorUnpair stk0
    let φ := pop1.1
    let pop2 := cantorUnpair pop1.2
    let maj := pop2.1
    let stk2 := pop2.2
    if zfImp φ p1 = maj then (p1, stk2) else (0, stk2)
  | 17 =>
    let pop1 := cantorUnpair stk0
    (zfAll p1 pop1.1, pop1.2)
  | 18 => (axB6b p1 p2 p3, stk0)
  | 19 => (axB6c p1 p2, stk0)
  | _ + 20 => (axInf, stk0)

set_option linter.flexible false in
theorem rpnZf393AllClauses_eq_zf393ClauseDispatch (topwff wffstack ac p1 p2 p3 : ℕ) :
    let out := rpnZf393AllClauses topwff wffstack ac p1 p2 p3
    (out.topwff, out.wffstack) = zf393ClauseDispatch topwff wffstack ac p1 p2 p3 := by
  unfold rpnZf393AllClauses rpnZf393AllClausesOp zf393ClauseDispatch
  rcases ac with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ac
  all_goals
    simp [rpnVk, rpnClauseDET, rpnDetCheck, rpnClauseGEN, rpnCparam2, rpnCparam3, rpnPar1, rpnPar3]
  all_goals
    try (split_ifs <;> rfl)

def zf393MainNext (c : ZfMainCfg) : ZfMainCfg :=
  let prooflist₁ := if c.prooflist = 0 then c.nextproof else c.prooflist - 1
  let nextproof' := if c.prooflist = 0 then c.nextproof + 1 else c.nextproof
  let u1 := cantorUnpair prooflist₁
  let ac := u1.1
  let u2 := cantorUnpair u1.2
  let p1 := u2.1
  let u3 := cantorUnpair u2.2
  let p2 := u3.1
  let u4 := cantorUnpair u3.2
  let p3 := u4.1
  let prooflist' := u4.2
  let res := zf393ClauseDispatch c.topwff c.wffstack ac p1 p2 p3
  ⟨prooflist', nextproof', res.1, res.2⟩

def zf393MainStep (c : ZfMainCfg) : Option ZfMainCfg :=
  if (zf393MainNext c).topwff = 1 then none else some (zf393MainNext c)

def zf393MainNSteps : ℕ → ZfMainCfg → Option ZfMainCfg
  | 0, c => some c
  | n + 1, c => (zf393MainStep c).bind (zf393MainNSteps n)

@[simp]
theorem zf393MainNSteps_zero (c : ZfMainCfg) : zf393MainNSteps 0 c = some c := rfl

@[simp]
theorem zf393MainNSteps_succ (n : ℕ) (c : ZfMainCfg) :
    zf393MainNSteps (n + 1) c = (zf393MainStep c).bind (zf393MainNSteps n) := rfl

theorem zf393MainNSteps_add (m n : ℕ) (c : ZfMainCfg) :
    zf393MainNSteps (m + n) c = (zf393MainNSteps m c).bind (zf393MainNSteps n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, zf393MainNSteps_succ, zf393MainNSteps_succ]
    cases zf393MainStep c with
    | none => rfl
    | some c' => exact ih c'

theorem zf393MainNSteps_bind_eq {m n : ℕ} {c₁ c₂ c₃ : ZfMainCfg}
    (h₁ : zf393MainNSteps m c₁ = some c₂) (h₂ : zf393MainNSteps n c₂ = some c₃) :
    zf393MainNSteps (m + n) c₁ = some c₃ := by
  rw [zf393MainNSteps_add, h₁, Option.bind_some, h₂]

def Zf393MainHalts : Prop :=
  ∃ n c, zf393MainNSteps n zfMainInit = some c ∧ zf393MainStep c = none

def RegsInv (regs : List ℕ) : Prop :=
  regs.length = 11 ∧ regs.getD 8 0 = 0 ∧ regs.getD 9 0 = 0 ∧ regs.getD 10 0 = 0

theorem regsInv_init : RegsInv zfLogInit.regs :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem regs_eq_of_regsInv {regs : List ℕ} (hInv : RegsInv regs) :
    regs = [regs.getD 0 0, regs.getD 1 0, regs.getD 2 0, regs.getD 3 0,
            regs.getD 4 0, regs.getD 5 0, regs.getD 6 0, regs.getD 7 0, 0, 0, 0] := by
  rcases hInv with ⟨hlen, h8, h9, h10⟩
  rcases regs with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, _ | ⟨r4, _ | ⟨r5, _ |
    ⟨r6, _ | ⟨r7, _ | ⟨r8, _ | ⟨r9, _ | ⟨r10, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen; done)
  dsimp [List.getD] at h8 h9 h10
  subst h8 h9 h10
  rfl

def regHeader05Op (regs : List ℕ) : List ℕ :=
  ((((reg95Op regs).set 4 0).set 5 0).set 6 0).set 7 0

theorem regSpineEval_0_5 : RegSpineEval 0 5 regHeader05Op :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_0 rfl (by decide) subEval_95) <|
  regSpineEval_trans (regSpineEval_step walkInternal_spine_1 rfl (by decide) subEval_342) <|
  regSpineEval_trans (regSpineEval_step walkInternal_spine_2 rfl (by decide) subEval_346) <|
  regSpineEval_trans (regSpineEval_step walkInternal_spine_3 rfl (by decide) subEval_352) <|
  regSpineEval_step walkInternal_spine_4 rfl (by decide) subEval_356

theorem regHeader05Op_eval (pl np top stk ac0 p1_0 p2_0 p3_0 : ℕ) :
    regHeader05Op [pl, np, top, stk, ac0, p1_0, p2_0, p3_0, 0, 0, 0] =
      [if pl = 0 then np else pl - 1, if pl = 0 then np + 1 else np,
       top, stk, 0, 0, 0, 0, 0, 0, 0] := by
  by_cases hpl : pl = 0 <;>
    simp [regHeader05Op, reg95Op, reg97Op, hpl]

def regUnpairMoveOp (r : ℕ) (regs : List ℕ) : List ℕ :=
  let u := reg269Op regs
  (u.set 8 0).set r (u.getD r 0 + u.getD 8 0)

theorem regSpineEval_5_7 : RegSpineEval 5 7 (regUnpairMoveOp 4) :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_5 rfl (by decide) subEval_269) <|
  regSpineEval_step walkInternal_spine_6 rfl (by decide) subEval_360

theorem regSpineEval_7_9 : RegSpineEval 7 9 (regUnpairMoveOp 5) :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_7 rfl (by decide) subEval_269) <|
  regSpineEval_step walkInternal_spine_8 rfl (by decide) subEval_364

theorem regSpineEval_9_11 : RegSpineEval 9 11 (regUnpairMoveOp 6) :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_9 rfl (by decide) subEval_269) <|
  regSpineEval_step walkInternal_spine_10 rfl (by decide) subEval_366

theorem regSpineEval_11_13 : RegSpineEval 11 13 (regUnpairMoveOp 7) :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_11 rfl (by decide) subEval_269) <|
  regSpineEval_step walkInternal_spine_12 rfl (by decide) subEval_368

theorem regSpineEval_0_13 :
    RegSpineEval 0 13 (fun regs =>
      regUnpairMoveOp 7 (regUnpairMoveOp 6 (regUnpairMoveOp 5
        (regUnpairMoveOp 4 (regHeader05Op regs))))) :=
  regSpineEval_trans regSpineEval_0_5 <|
  regSpineEval_trans regSpineEval_5_7 <|
  regSpineEval_trans regSpineEval_7_9 <|
  regSpineEval_trans regSpineEval_9_11 <|
  regSpineEval_11_13

theorem unpair_header_eval {regs : List ℕ} (hInv : RegsInv regs) :
    let prooflist₁ := if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1
    let nextproof' := if regs.getD 0 0 = 0 then regs.getD 1 0 + 1 else regs.getD 1 0
    let u1 := cantorUnpair prooflist₁
    let ac := u1.1
    let u2 := cantorUnpair u1.2
    let p1 := u2.1
    let u3 := cantorUnpair u2.2
    let p2 := u3.1
    let u4 := cantorUnpair u3.2
    let p3 := u4.1
    let prooflist' := u4.2
    ∃ s ≥ 1, zfReg11NSteps s ⟨[], regs⟩ =
      some ⟨List.replicate 13 1,
        wffStateToRegs prooflist' nextproof' ⟨regs.getD 2 0, regs.getD 3 0, ac, p1, p2, p3⟩⟩ := by
  intro prooflist₁ nextproof' u1 ac u2 p1 u3 p2 u4 p3 prooflist'
  obtain ⟨s, hs, hsteps, _⟩ := regSpineEval_0_13 regs hInv.1
  dsimp only [List.replicate] at hsteps
  have h05 : regHeader05Op regs =
      [prooflist₁, nextproof', regs.getD 2 0, regs.getD 3 0, 0, 0, 0, 0, 0, 0, 0] := by
    conv_lhs => rw [regs_eq_of_regsInv hInv]
    exact regHeader05Op_eval _ _ _ _ _ _ _ _
  rw [h05] at hsteps
  simp only [regUnpairMoveOp, reg269Op_eval, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.set_cons_zero, List.set_cons_succ,
    Nat.zero_add] at hsteps
  exact ⟨s, hs, hsteps⟩

theorem spine_0_123_eval {regs : List ℕ} (hInv : RegsInv regs) :
    let prooflist₁ := if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1
    let nextproof' := if regs.getD 0 0 = 0 then regs.getD 1 0 + 1 else regs.getD 1 0
    let u1 := cantorUnpair prooflist₁
    let ac := u1.1
    let u2 := cantorUnpair u1.2
    let p1 := u2.1
    let u3 := cantorUnpair u2.2
    let p2 := u3.1
    let u4 := cantorUnpair u3.2
    let p3 := u4.1
    let prooflist' := u4.2
    let out := rpnZf393AllClauses (regs.getD 2 0) (regs.getD 3 0) ac p1 p2 p3
    ∃ s ≥ 1, zfReg11NSteps s ⟨[], regs⟩ =
      some ⟨List.replicate 123 1, wffStateToRegs prooflist' nextproof' out⟩ := by
  intro prooflist₁ nextproof' u1 ac u2 p1 u3 p2 u4 p3 prooflist' out
  obtain ⟨s₁, hs₁, hsteps₁⟩ := unpair_header_eval hInv
  obtain ⟨s₂, hs₂, hsteps₂⟩ :=
    wffSpineEval_13_123 prooflist' nextproof' ⟨regs.getD 2 0, regs.getD 3 0, ac, p1, p2, p3⟩
  exact ⟨s₁ + s₂, by omega, zfReg11NSteps_bind_eq hsteps₁ hsteps₂⟩

theorem evalStack_spine_123 :
    evalStack (List.replicate 123 1) = .decnz 2 (List.replicate 124 1) [] := by
  have h := evalStack_leaf0_of_walkInternal walkInternal_spine_123 rfl (by decide) (by decide)
  rw [← List.replicate_succ', retStack_replicate_one] at h
  exact h

theorem evalStack_spine_124 :
    evalStack (List.replicate 124 1) =
      .decnz 2 (List.replicate 124 1 ++ [0] ++ [1]) (List.replicate 125 1) := by
  have h224 : walkInternal 99 (List.replicate 124 1 ++ [0]) = some 224 :=
    walkInternal_snoc walkInternal_spine_124 rfl (by decide)
  have htrim := evalStack_trimZeros_of_walkInternal h224
  rw [trimZeros_append_zero, trimZeros_replicate_one] at htrim
  have h := evalStack_leaf0_of_walkInternal h224 rfl (by decide) (by decide)
  rw [retStack_append_zero, ← List.replicate_succ'] at h
  rw [htrim]
  exact h

theorem evalStack_spine_125 :
    evalStack (List.replicate 125 1) = .halt := by decide

theorem evalStack_225_break :
    evalStack (List.replicate 124 1 ++ [0] ++ [1] ++ [1]) = .jump [] := by
  have h224 : walkInternal 99 (List.replicate 124 1 ++ [0]) = some 224 :=
    walkInternal_snoc walkInternal_spine_124 rfl (by decide)
  have h225 : walkInternal 99 (List.replicate 124 1 ++ [0] ++ [1]) = some 225 :=
    walkInternal_snoc h224 rfl (by decide)
  have hev := evalStack_break1_of_walkInternal (k := 1) (by decide) h225 rfl
  have hpop :
      (popBreakRev 1 (List.replicate 124 (1 : Fin 2) ++ [0] ++ [1]).reverse).reverse = [] := by
    decide
  rw [hev, hpop]

theorem halt_check_eval (regs : List ℕ) (hlen : regs.length = 11) :
    (regs.getD 2 0 = 1 →
      ∃ s ch, zfReg11NSteps s ⟨List.replicate 123 1, regs⟩ = some ch ∧ zfReg11Step ch = none) ∧
    (regs.getD 2 0 ≠ 1 →
      ∃ s ≥ 1, zfReg11NSteps s ⟨List.replicate 123 1, regs⟩ = some ⟨[], regs⟩) := by
  constructor
  · intro h1
    have hstep1 : zfReg11Step ⟨List.replicate 123 1, regs⟩ =
        some ⟨List.replicate 124 1, regs.set 2 0⟩ :=
      zfReg11Step_of_decnz_succ evalStack_spine_123 h1
    have hz : (regs.set 2 0).getD 2 0 = 0 := getD_set_self regs 2 0 (by omega)
    have hstep2 : zfReg11Step ⟨List.replicate 124 1, regs.set 2 0⟩ =
        some ⟨List.replicate 125 1, regs.set 2 0⟩ :=
      zfReg11Step_of_decnz_zero evalStack_spine_124 hz
    have hhalt : zfReg11Step ⟨List.replicate 125 1, regs.set 2 0⟩ = none := by
      unfold zfReg11Step; dsimp only; rw [evalStack_spine_125]
    exact ⟨2, ⟨List.replicate 125 1, regs.set 2 0⟩,
      step_zfReg11NSteps hstep1 (zfReg11Step_one hstep2), hhalt⟩
  · intro hne1
    rcases hv : regs.getD 2 0 with _ | _ | v
    · have hstep1 : zfReg11Step ⟨List.replicate 123 1, regs⟩ = some ⟨[], regs⟩ :=
        zfReg11Step_of_decnz_zero evalStack_spine_123 hv
      exact ⟨1, le_refl 1, zfReg11Step_one hstep1⟩
    · exact absurd hv hne1
    · have hstep1 : zfReg11Step ⟨List.replicate 123 1, regs⟩ =
          some ⟨List.replicate 124 1, regs.set 2 (v + 1)⟩ :=
        zfReg11Step_of_decnz_succ evalStack_spine_123 hv
      have hv1 : (regs.set 2 (v + 1)).getD 2 0 = v + 1 :=
        getD_set_self regs 2 (v + 1) (by omega)
      have hstep2 : zfReg11Step ⟨List.replicate 124 1, regs.set 2 (v + 1)⟩ =
          some ⟨List.replicate 124 1 ++ [0] ++ [1], (regs.set 2 (v + 1)).set 2 v⟩ :=
        zfReg11Step_of_decnz_succ evalStack_spine_124 hv1
      rw [List.set_set] at hstep2
      have h224 : walkInternal 99 (List.replicate 124 1 ++ [0]) = some 224 :=
        walkInternal_snoc walkInternal_spine_124 rfl (by decide)
      have h225 : walkInternal 99 (List.replicate 124 1 ++ [0] ++ [1]) = some 225 :=
        walkInternal_snoc h224 rfl (by decide)
      have h288 : walkInternal 99 (List.replicate 124 1 ++ [0] ++ [1] ++ [0]) = some 288 :=
        walkInternal_snoc h225 rfl (by decide)
      obtain ⟨s₃, hs₃, hsteps3, _⟩ :=
        subEval_288 (List.replicate 124 1 ++ [0] ++ [1] ++ [0]) h288
          (regs.set 2 v) (by simp [hlen])
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps3
      dsimp only at hsteps3
      rw [getD_set_self regs 2 v (by omega), List.set_set, set_eq_self_of_getD_eq hv] at hsteps3
      have hstep4 : zfReg11Step ⟨List.replicate 124 1 ++ [0] ++ [1] ++ [1], regs⟩ =
          some ⟨[], regs⟩ :=
        zfReg11Step_of_jump evalStack_225_break
      have hchain :=
        step_zfReg11NSteps hstep1
          (step_zfReg11NSteps hstep2
            (zfReg11NSteps_bind_eq hsteps3 (zfReg11Step_one hstep4)))
      exact ⟨s₃ + 1 + 1 + 1, by omega, hchain⟩

theorem zfReg11NSteps_of_halt {c : ZfLogCfg} (h : zfReg11Step c = none) {k : ℕ} (hk : 1 ≤ k) :
    zfReg11NSteps k c = none := by
  cases k with
  | zero => omega
  | succ k => simp [zfReg11NSteps_succ, h]

theorem spine_body_eval (regs : List ℕ) (hInv : RegsInv regs) :
    ∃ s ≥ 1, ∃ regs' : List ℕ,
      zfReg11NSteps s ⟨[], regs⟩ = some ⟨List.replicate 123 1, regs'⟩ ∧
      RegsInv regs' ∧
      regsToMainCfg regs' = zf393MainNext (regsToMainCfg regs) := by
  obtain ⟨s, hs, hsteps⟩ := spine_0_123_eval hInv
  refine ⟨s, hs, _, hsteps, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  let pl1 := if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1
  let ac := (cantorUnpair pl1).1
  let u2 := cantorUnpair (cantorUnpair pl1).2
  let p1 := u2.1
  let u3 := cantorUnpair u2.2
  let p2 := u3.1
  let p3 := (cantorUnpair u3.2).1
  have h := rpnZf393AllClauses_eq_zf393ClauseDispatch
    (regs.getD 2 0) (regs.getD 3 0) ac p1 p2 p3
  dsimp only at h
  rw [Prod.mk.injEq] at h
  have hcfg : ∀ pl np st,
      regsToMainCfg (wffStateToRegs pl np st) = ⟨pl, np, st.topwff, st.wffstack⟩ :=
    fun _ _ _ => rfl
  rw [hcfg, h.1, h.2]
  rfl

theorem main_iter_sim {regs : List ℕ} (hInv : RegsInv regs) :
    match zf393MainStep (regsToMainCfg regs) with
    | none =>
      ∃ s ch, zfReg11NSteps s ⟨[], regs⟩ = some ch ∧ zfReg11Step ch = none
    | some c' =>
      ∃ s ≥ 1, ∃ regs' : List ℕ,
        zfReg11NSteps s ⟨[], regs⟩ = some ⟨[], regs'⟩ ∧
        RegsInv regs' ∧
        regsToMainCfg regs' = c' := by
  obtain ⟨s₁, hs₁, regs', hsteps₁, hInv', hnext⟩ := spine_body_eval regs hInv
  have htop_eq : (zf393MainNext (regsToMainCfg regs)).topwff = regs'.getD 2 0 := by
    rw [← hnext]; rfl
  have hhalt := halt_check_eval regs' hInv'.1
  unfold zf393MainStep
  by_cases h1 : (zf393MainNext (regsToMainCfg regs)).topwff = 1
  · simp only [h1, ↓reduceIte]
    rw [htop_eq] at h1
    obtain ⟨s₂, ch, hsteps₂, hnone⟩ := hhalt.1 h1
    exact ⟨s₁ + s₂, ch, zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hnone⟩
  · simp only [h1, ↓reduceIte]
    rw [htop_eq] at h1
    obtain ⟨s₂, hs₂, hsteps₂⟩ := hhalt.2 h1
    exact ⟨s₁ + s₂, by omega, regs', zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hInv', hnext⟩

theorem zf393MainNSteps_sim :
    ∀ (n : ℕ) {regs : List ℕ} {c_end : ZfMainCfg},
      RegsInv regs →
      zf393MainNSteps n (regsToMainCfg regs) = some c_end →
      ∃ s regs_end,
        zfReg11NSteps s ⟨[], regs⟩ = some ⟨[], regs_end⟩ ∧
        RegsInv regs_end ∧
        regsToMainCfg regs_end = c_end := by
  intro n
  induction n with
  | zero =>
    intro regs c_end hInv hn
    injection hn with hn'
    subst hn'
    exact ⟨0, regs, rfl, hInv, rfl⟩
  | succ n ih =>
    intro regs c_end hInv hn
    unfold zf393MainNSteps at hn
    have hiter := main_iter_sim hInv
    rcases hs : zf393MainStep (regsToMainCfg regs) with _ | c₁
    · rw [hs] at hn; cases hn
    · rw [hs] at hiter
      rw [hs, Option.bind_some] at hn
      obtain ⟨s₁, _, regs₁, hsteps₁, hInv₁, hc₁⟩ := hiter
      rw [← hc₁] at hn
      obtain ⟨s₂, regs_end, hsteps₂, hInv_end, hc_end⟩ := ih hInv₁ hn
      exact ⟨s₁ + s₂, regs_end, zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hInv_end, hc_end⟩

theorem zf393MainHalts_of_zfReg11NSteps_halt :
    ∀ (N : ℕ) {regs : List ℕ} {ch : ZfLogCfg},
      RegsInv regs →
      zfReg11NSteps N ⟨[], regs⟩ = some ch →
      zfReg11Step ch = none →
      ∃ n cm, zf393MainNSteps n (regsToMainCfg regs) = some cm ∧ zf393MainStep cm = none := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro regs ch hInv hN hnone
    have hiter := main_iter_sim hInv
    rcases hs : zf393MainStep (regsToMainCfg regs) with _ | c'
    · exact ⟨0, regsToMainCfg regs, rfl, hs⟩
    · rw [hs] at hiter
      obtain ⟨s, hs_pos, regs', hsteps, hInv', hc'⟩ := hiter
      have hle : s ≤ N := by
        by_contra hlt
        have hgt : 1 ≤ s - N := by omega
        have hsplit : s = N + (s - N) := by omega
        rw [hsplit, zfReg11NSteps_add, hN, Option.bind_some,
          zfReg11NSteps_of_halt hnone hgt] at hsteps
        cases hsteps
      have hsplit : N = s + (N - s) := by omega
      rw [hsplit, zfReg11NSteps_add, hsteps, Option.bind_some] at hN
      obtain ⟨n, cm, hn, hcm_none⟩ := ih (N - s) (by omega) hInv' hN hnone
      rw [hc'] at hn
      exact ⟨n + 1, cm, by simp [zf393MainNSteps, hs, hn], hcm_none⟩

theorem zf393RegHalts_iff_zf393MainHalts :
    Zf393RegHalts ↔ Zf393MainHalts := by
  rw [zf393RegHalts_iff_zfLog11Halts]
  have hInit_cfg : regsToMainCfg zfLogInit.regs = zfMainInit := rfl
  constructor
  · rintro ⟨N, ch, hN, hnone⟩
    obtain ⟨n, cm, hn, hcm_none⟩ :=
      zf393MainHalts_of_zfReg11NSteps_halt N regsInv_init hN hnone
    rw [hInit_cfg] at hn
    exact ⟨n, cm, hn, hcm_none⟩
  · rintro ⟨n, cm, hn, hcm_none⟩
    rw [← hInit_cfg] at hn
    obtain ⟨s₁, regs_end, hsteps₁, hInv_end, hc_end⟩ :=
      zf393MainNSteps_sim n regsInv_init hn
    have hiter := main_iter_sim hInv_end
    rw [hc_end, hcm_none] at hiter
    obtain ⟨s₂, ch, hsteps₂, hnone⟩ := hiter
    exact ⟨s₁ + s₂, ch, zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hnone⟩

/-! ## Layer 3: Soundness & Completeness of `zf393MainStep` vs `ZFProvable` -/

def StackAllZfProvable (top stk : ℕ) : Prop :=
  ∀ n : ℕ, ZFProvable (stackGet n top stk)

theorem StackAllZfProvable.top {top stk : ℕ} (h : StackAllZfProvable top stk) :
    ZFProvable top := h 0

theorem StackAllZfProvable.push {φ top stk : ℕ} (hφ : ZFProvable φ)
    (h : StackAllZfProvable top stk) :
    StackAllZfProvable φ (cantorPair top stk) := by
  intro n
  cases n with
  | zero => exact hφ
  | succ n =>
    simp only [stackGet_succ, cantorUnpair_cantorPair]
    exact h n

theorem StackAllZfProvable.pop {top stk : ℕ} (h : StackAllZfProvable top stk) :
    StackAllZfProvable (cantorUnpair stk).1 (cantorUnpair stk).2 :=
  fun n => h (n + 1)

theorem stackAllZfProvable_init : StackAllZfProvable 0 0 := by
  intro n
  rw [stackGet_zero_zero]
  exact ZFProvable.moot

theorem zf393ClauseDispatch_preserves_provable {topwff wffstack : ℕ}
    (h : StackAllZfProvable topwff wffstack) (ac p1 p2 p3 : ℕ) :
    let res := zf393ClauseDispatch topwff wffstack ac p1 p2 p3
    StackAllZfProvable res.1 res.2 := by
  have hmoot : ZFProvable 0 := ZFProvable.moot
  have hpush0 : StackAllZfProvable 0 (cantorPair topwff wffstack) := h.push hmoot
  rcases ac with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ac
  · exact hpush0
  · exact h.push (ZFProvable.rep p1)
  · exact h.push ZFProvable.pow
  · exact h.push (ZFProvable.b2 p1)
  · exact h.push ZFProvable.uni
  · exact h.push (ZFProvable.b3 p1 p2)
  · exact h.push (ZFProvable.b8b p1 p2 p3)
  · dsimp only [zf393ClauseDispatch]
    split_ifs with h6a
    · exact hpush0
    · rcases not_or.mp h6a with ⟨hne1, hne2⟩
      exact h.push (ZFProvable.b6a p1 p2 p3 hne1 (Ne.symm hne2))
  · exact h.push (ZFProvable.b6b p1 p2 p3)
  · exact h.push (ZFProvable.b7 p1 p2)
  · exact h.push (ZFProvable.b4 p1 p2 p3)
  · exact h.push (ZFProvable.b8a p1 p2 p3)
  · exact h.push (ZFProvable.b8b p1 p2 p3)
  · exact h.push (ZFProvable.b8c p1 p2 p3)
  · exact h.push (ZFProvable.b1 p1 p2 p3)
  · exact h.push ZFProvable.ext
  · dsimp only [zf393ClauseDispatch]
    have hpop1 := hpush0.pop
    have hφ : ZFProvable (cantorUnpair (cantorPair topwff wffstack)).1 := hpop1.top
    have hpop2 := hpop1.pop
    have hmaj : ZFProvable (cantorUnpair (cantorUnpair (cantorPair topwff wffstack)).2).1 :=
      hpop2.top
    split_ifs with hmp
    · rw [← hmp] at hmaj
      have hp1 : ZFProvable p1 := ZFProvable.mp hφ hmaj
      intro n
      cases n with
      | zero => exact hp1
      | succ n => exact hpop2 (n + 1)
    · intro n
      cases n with
      | zero => exact hmoot
      | succ n => exact hpop2 (n + 1)
  · dsimp only [zf393ClauseDispatch]
    have hpop1 := hpush0.pop
    have hall : ZFProvable (zfAll p1 (cantorUnpair (cantorPair topwff wffstack)).1) :=
      ZFProvable.gen p1 hpop1.top
    intro n
    cases n with
    | zero => exact hall
    | succ n => exact hpop1 (n + 1)
  · exact h.push (ZFProvable.b6b p1 p2 p3)
  · exact h.push (ZFProvable.b6c p1 p2)
  · exact h.push ZFProvable.inf

theorem zf393MainNext_preserves_provable {c : ZfMainCfg}
    (h : StackAllZfProvable c.topwff c.wffstack) :
    StackAllZfProvable (zf393MainNext c).topwff (zf393MainNext c).wffstack := by
  unfold zf393MainNext
  exact zf393ClauseDispatch_preserves_provable h _ _ _ _

theorem zf393MainNSteps_preserves_provable {n : ℕ} {c₁ c₂ : ZfMainCfg}
    (h : StackAllZfProvable c₁.topwff c₁.wffstack)
    (hsteps : zf393MainNSteps n c₁ = some c₂) :
    StackAllZfProvable c₂.topwff c₂.wffstack := by
  induction n generalizing c₁ with
  | zero =>
    injection hsteps with h'
    subst h'
    exact h
  | succ n ih =>
    unfold zf393MainNSteps at hsteps
    rcases hs : zf393MainStep c₁ with _ | c'
    · rw [hs] at hsteps; cases hsteps
    · rw [hs, Option.bind_some] at hsteps
      unfold zf393MainStep at hs
      split_ifs at hs with h1
      injection hs with hs'
      subst hs'
      exact ih (zf393MainNext_preserves_provable h) hsteps

theorem zfInconsistent_of_zf393MainHalts (hHalts : Zf393MainHalts) : ZFInconsistent := by
  obtain ⟨n, c, hn, hnone⟩ := hHalts
  have hprov := zf393MainNSteps_preserves_provable stackAllZfProvable_init hn
  have hnext := zf393MainNext_preserves_provable hprov
  unfold zf393MainStep at hnone
  split_ifs at hnone with htop1
  have h1 : ZFProvable (zf393MainNext c).topwff := hnext.top
  rw [htop1] at h1
  exact h1

def execStep393 (s : ProofStep) (p : ℕ × ℕ) : ℕ × ℕ :=
  zf393ClauseDispatch p.1 p.2 s.1 s.2.1 s.2.2.1 s.2.2.2

def execList393 : List ProofStep → ℕ × ℕ → ℕ × ℕ
  | [], p => p
  | s :: rest, p => execList393 rest (execStep393 s p)

@[simp]
theorem execList393_append (L₁ L₂ : List ProofStep) (p : ℕ × ℕ) :
    execList393 (L₁ ++ L₂) p = execList393 L₂ (execList393 L₁ p) := by
  induction L₁ generalizing p with
  | nil => rfl
  | cons s rest ih => exact ih (execStep393 s p)

theorem exists_proofList393_of_zfProvable {φ : ℕ} (h : ZFProvable φ) :
    ∃ L : List ProofStep, L ≠ [] ∧
      ∀ top stk : ℕ, execList393 L (top, stk) = (φ, cantorPair top stk) := by
  induction h with
  | moot =>
    exact ⟨[(0, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | @mp φ ψ hφ himp ihφ ihimp =>
    obtain ⟨L_imp, _, himp_eval⟩ := ihimp
    obtain ⟨L_φ, _, hφ_eval⟩ := ihφ
    refine ⟨L_imp ++ L_φ ++ [(16, ψ, 0, 0)], by simp, fun top stk => ?_⟩
    rw [execList393_append, execList393_append, himp_eval, hφ_eval]
    simp [execList393, execStep393, zf393ClauseDispatch]
  | @gen x φ hφ ihφ =>
    obtain ⟨L_φ, _, hφ_eval⟩ := ihφ
    refine ⟨L_φ ++ [(17, x, 0, 0)], by simp, fun top stk => ?_⟩
    rw [execList393_append, hφ_eval]
    simp [execList393, execStep393, zf393ClauseDispatch]
  | b1 φ ψ χ =>
    exact ⟨[(14, φ, ψ, χ)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b2 φ =>
    exact ⟨[(3, φ, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b3 φ ψ =>
    exact ⟨[(5, φ, ψ, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b4 x φ ψ =>
    exact ⟨[(10, x, φ, ψ)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b6a x y z hxz hzy =>
    refine ⟨[(7, x, y, z)], List.cons_ne_nil _ _, fun top stk => ?_⟩
    have hcond : ¬ (x = z ∨ y = z) := not_or.mpr ⟨hxz, Ne.symm hzy⟩
    simp [execList393, execStep393, zf393ClauseDispatch, hcond]
  | b6b x y φ =>
    exact ⟨[(8, x, y, φ)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b6c x φ =>
    exact ⟨[(19, x, φ, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b7 x y =>
    exact ⟨[(9, x, y, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b8a x y z =>
    exact ⟨[(11, x, y, z)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b8b x y z =>
    exact ⟨[(6, x, y, z)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | b8c x y z =>
    exact ⟨[(13, x, y, z)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | ext =>
    exact ⟨[(15, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | rep φ =>
    exact ⟨[(1, φ, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | pow =>
    exact ⟨[(2, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | uni =>
    exact ⟨[(4, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩
  | inf =>
    exact ⟨[(20, 0, 0, 0)], List.cons_ne_nil _ _, fun _ _ => rfl⟩

theorem zf393MainNext_packProofStep (s : ProofStep) (rest np top stk : ℕ) :
    zf393MainNext ⟨packProofStep s rest, np, top, stk⟩ =
      ⟨rest, np, (execStep393 s (top, stk)).1, (execStep393 s (top, stk)).2⟩ := by
  unfold zf393MainNext
  simp [packProofStep, execStep393]

theorem zf393MainNext_zero_prooflist (P top stk : ℕ) :
    zf393MainNext ⟨0, P, top, stk⟩ = zf393MainNext ⟨P + 1, P + 1, top, stk⟩ := by
  unfold zf393MainNext; simp

theorem zf393MainNext_prooflist_lt {c : ZfMainCfg} (hpos : 0 < c.prooflist) :
    (zf393MainNext c).prooflist < c.prooflist ∧ (zf393MainNext c).nextproof = c.nextproof := by
  have hne : c.prooflist ≠ 0 := by omega
  simp only [zf393MainNext, hne, ↓reduceIte]
  have h1 := cantorUnpair_snd_le (c.prooflist - 1)
  have h2 := cantorUnpair_snd_le (cantorUnpair (c.prooflist - 1)).2
  have h3 := cantorUnpair_snd_le (cantorUnpair (cantorUnpair (c.prooflist - 1)).2).2
  have h4 :=
    cantorUnpair_snd_le (cantorUnpair (cantorUnpair (cantorUnpair (c.prooflist - 1)).2).2).2
  exact ⟨by omega, trivial⟩

private theorem step393_some_of_not_halts {n : ℕ} {c : ZfMainCfg}
    (hNotHalts : ¬ Zf393MainHalts) (hn : zf393MainNSteps n zfMainInit = some c) :
    zf393MainStep c = some (zf393MainNext c) := by
  rcases hs : zf393MainStep c with _ | c'
  · exact False.elim (hNotHalts ⟨n, c, hn, hs⟩)
  · unfold zf393MainStep at hs
    split_ifs at hs with h1
    exact hs.symm

private theorem drain393_prooflist_of_not_halts (hNotHalts : ¬ Zf393MainHalts) (pl : ℕ) :
    ∀ {n : ℕ} {c : ZfMainCfg},
      zf393MainNSteps n zfMainInit = some c →
      c.prooflist = pl →
      ∃ m c',
        zf393MainNSteps m zfMainInit = some c' ∧ c'.prooflist = 0 ∧ c'.nextproof = c.nextproof := by
  induction pl using Nat.strong_induction_on with
  | h pl ih =>
    intro n c hn hpl
    by_cases hzero : pl = 0
    · exact ⟨n, c, hn, hpl.trans hzero, rfl⟩
    · have hpos : 0 < c.prooflist := by omega
      have hstep := step393_some_of_not_halts hNotHalts hn
      have hn1 : zf393MainNSteps (n + 1) zfMainInit = some (zf393MainNext c) :=
        zf393MainNSteps_bind_eq hn (by simp [zf393MainNSteps, hstep])
      obtain ⟨hlt, hnp⟩ := zf393MainNext_prooflist_lt hpos
      rw [hpl] at hlt
      obtain ⟨m, c', hm, hpl', hnp'⟩ := ih (zf393MainNext c).prooflist hlt hn1 rfl
      exact ⟨m, c', hm, hpl', hnp'.trans hnp⟩

private theorem reaches393_nextproof_of_not_halts (hNotHalts : ¬ Zf393MainHalts) (N : ℕ) :
    ∃ n c, zf393MainNSteps n zfMainInit = some c ∧ c.prooflist = 0 ∧ c.nextproof = N := by
  induction N with
  | zero => exact ⟨0, zfMainInit, rfl, rfl, rfl⟩
  | succ N ih =>
    obtain ⟨n, c, hn, hpl0, hnp⟩ := ih
    have hstep := step393_some_of_not_halts hNotHalts hn
    have hn1 : zf393MainNSteps (n + 1) zfMainInit = some (zf393MainNext c) :=
      zf393MainNSteps_bind_eq hn (by simp [zf393MainNSteps, hstep])
    have hnp_next : (zf393MainNext c).nextproof = N + 1 := by
      unfold zf393MainNext; simp [hpl0, hnp]
    obtain ⟨m, c', hm, hpl', hnp'⟩ :=
      drain393_prooflist_of_not_halts hNotHalts (zf393MainNext c).prooflist hn1 rfl
    exact ⟨m, c', hm, hpl', hnp'.trans hnp_next⟩

private theorem exec393_encodeProofList_of_not_halts (hNotHalts : ¬ Zf393MainHalts)
    (L : List ProofStep) :
    ∀ {n : ℕ} {np top stk : ℕ},
      zf393MainNSteps n zfMainInit = some ⟨encodeProofList L, np, top, stk⟩ →
      zf393MainNSteps (n + L.length) zfMainInit =
        some ⟨0, np, (execList393 L (top, stk)).1, (execList393 L (top, stk)).2⟩ := by
  induction L with
  | nil =>
    intro n np top stk hn
    exact hn
  | cons s rest ih =>
    intro n np top stk hn
    have hstep := step393_some_of_not_halts hNotHalts hn
    rw [encodeProofList_cons, zf393MainNext_packProofStep] at hstep
    have hn1 : zf393MainNSteps (n + 1) zfMainInit =
        some ⟨encodeProofList rest, np,
          (execStep393 s (top, stk)).1, (execStep393 s (top, stk)).2⟩ :=
      zf393MainNSteps_bind_eq hn (by simp [zf393MainNSteps, hstep])
    have hrest := ih hn1
    have hlen : n + 1 + rest.length = n + (s :: rest).length := by simp; omega
    rwa [hlen] at hrest

theorem zf393MainHalts_of_zfInconsistent (hInc : ZFInconsistent) : Zf393MainHalts := by
  by_contra hNotHalts
  obtain ⟨L, hL_ne, hL_eval⟩ := exists_proofList393_of_zfProvable hInc
  let s₀ : ProofStep := (0, 0, 0, 0)
  let P : ℕ := encodeProofList (s₀ :: L) - 1
  have hP_succ : P + 1 = packProofStep s₀ (encodeProofList L) := by
    simp only [P, encodeProofList_cons, packProofStep]; omega
  obtain ⟨n, c, hn, hpl0, hnp⟩ := reaches393_nextproof_of_not_halts hNotHalts P
  have hc_eq : c = ⟨0, P, c.topwff, c.wffstack⟩ := by
    cases c
    dsimp at hpl0 hnp
    subst hpl0 hnp
    rfl
  rw [hc_eq] at hn
  have hstep0 := step393_some_of_not_halts hNotHalts hn
  have hnext0 : zf393MainNext ⟨0, P, c.topwff, c.wffstack⟩ =
      ⟨encodeProofList L, P + 1, (execStep393 s₀ (c.topwff, c.wffstack)).1,
        (execStep393 s₀ (c.topwff, c.wffstack)).2⟩ := by
    rw [zf393MainNext_zero_prooflist, hP_succ]
    exact zf393MainNext_packProofStep s₀ (encodeProofList L) (P + 1) c.topwff c.wffstack
  rw [hnext0] at hstep0
  have hn1 : zf393MainNSteps (n + 1) zfMainInit =
      some ⟨encodeProofList L, P + 1, (execStep393 s₀ (c.topwff, c.wffstack)).1,
            (execStep393 s₀ (c.topwff, c.wffstack)).2⟩ :=
    zf393MainNSteps_bind_eq hn (by simp [zf393MainNSteps, hstep0])
  have hL_ne_nil : ∃ LInit sLast, L = LInit ++ [sLast] :=
    ⟨L.dropLast, L.getLast hL_ne, (List.dropLast_append_getLast hL_ne).symm⟩
  obtain ⟨LInit, sLast, rfl⟩ := hL_ne_nil
  have hn_all := exec393_encodeProofList_of_not_halts hNotHalts (LInit ++ [sLast]) hn1
  rw [hL_eval] at hn_all
  have hlen_split : n + 1 + (LInit ++ [sLast]).length = (n + 1 + LInit.length) + 1 := by
    simp; omega
  rw [hlen_split, zf393MainNSteps_add] at hn_all
  rcases hmid : zf393MainNSteps (n + 1 + LInit.length) zfMainInit with _ | cmid
  · rw [hmid] at hn_all; cases hn_all
  · rw [hmid, Option.bind_some, zf393MainNSteps_succ] at hn_all
    unfold zf393MainStep at hn_all
    split_ifs at hn_all with h1
    · cases hn_all
    · simp only [Option.bind_some, zf393MainNSteps_zero, Option.some.injEq] at hn_all
      have htop : (zf393MainNext cmid).topwff = zfMem 0 0 := by rw [hn_all]
      exact h1 htop

/-- Layer 3 main equivalence: `Zf393MainHalts ↔ ZFInconsistent`. -/
theorem zf393MainHalts_iff_zfInconsistent :
    Zf393MainHalts ↔ ZFInconsistent :=
  ⟨zfInconsistent_of_zf393MainHalts, zf393MainHalts_of_zfInconsistent⟩

/-- Combined Layer 2 + Layer 3 theorem: the abstract call-stack machine `Zf393RegHalts` halts if
and only if `ZFProvable` is inconsistent (`ZFInconsistent`). -/
theorem zf393RegHalts_iff_zfInconsistent :
    Zf393RegHalts ↔ ZFInconsistent :=
  zf393RegHalts_iff_zf393MainHalts.trans zf393MainHalts_iff_zfInconsistent

/-- Unconditional non-halting of `zf393`'s call-stack register machine in Mathlib's `ZFSet.{0}`
model (`not_zfInconsistent`). -/
theorem not_zf393RegHalts : ¬ Zf393RegHalts :=
  fun h => not_zfInconsistent (zf393RegHalts_iff_zfInconsistent.mp h)

end ConjectureMachines.Zf393.Layer2
