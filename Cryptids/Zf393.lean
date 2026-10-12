/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Zf.Boot

/-!
# Wade's 393-State ZF Consistency Turing Machine (`Cryptids.Zf393`)

Defines Andrew Wade's 393-state, 2-symbol Turing machine `zf393 : TM 393 2`
(`ajwade/turing_machine_explorer` commit `9c5c2e82`, August 2026), proves its `O(log Q)` binary
decision tree transition lookup `@[simp] theorem zf393Trans_eq`, and establishes the symbolic
single-step and scan execution lemmas (`step_mkL_left`, `step_mkL_right`, `step_mk'_right`,
`step_mk'_left`, `step_mk'_none`, `nSteps_mkL_left_scan`, `nSteps_mk'_right_scan`).
-/

@[expose] public section

namespace ConjectureMachines.Zf393

open Turing StateTransition ConjectureMachines
open ConjectureMachines.Semantics.Riemann.Layer1 (nSteps nSteps_succ Tape.mkL append_replicate_cons)

abbrev TM (states symbols : ℕ) := Machine states symbols

set_option maxRecDepth 200000

abbrev LB01 : ListBlank (Fin 2) := ListBlank.cons 1 default

abbrev zf393 : Machine 393 2 := Machines.zf393

theorem zf393_states : zf393.bundle.states = 393 := rfl

def zf393Trans_0 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 6 then
    if q.val < 3 then
      if q.val < 1 then
        if a == 0 then some (1, .right, 1) else some (0, .left, 2)
      else
        if q.val < 2 then
          if a == 0 then some (0, .right, 2) else some (0, .right, 1)
        else
          if a == 0 then some (1, .left, 3) else some (0, .right, 4)
    else
      if q.val < 4 then
        if a == 0 then some (0, .left, 4) else some (0, .left, 68)
      else
        if q.val < 5 then
          if a == 0 then some (1, .left, 0) else some (0, .left, 1)
        else
          if a == 0 then some (1, .right, 6) else some (1, .left, 10)
  else
    if q.val < 9 then
      if q.val < 7 then
        if a == 0 then some (0, .right, 6) else some (0, .right, 7)
      else
        if q.val < 8 then
          if a == 0 then some (1, .right, 8) else some (1, .right, 7)
        else
          if a == 0 then some (0, .right, 9) else some (0, .right, 7)
    else
      if q.val < 10 then
        if a == 0 then some (0, .left, 5) else some (1, .right, 9)
      else
        if q.val < 11 then
          if a == 0 then some (0, .left, 26) else some (1, .right, 11)
        else
          if a == 0 then some (1, .right, 12) else some (0, .right, 11)
def zf393Trans_1 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 18 then
    if q.val < 15 then
      if q.val < 13 then
        if a == 0 then some (0, .left, 17) else some (1, .right, 9)
      else
        if q.val < 14 then
          if a == 0 then some (1, .right, 14) else none
        else
          if a == 0 then some (0, .right, 14) else some (1, .right, 15)
    else
      if q.val < 16 then
        if a == 0 then some (0, .right, 16) else some (1, .right, 15)
      else
        if q.val < 17 then
          if a == 0 then some (1, .left, 23) else some (1, .right, 15)
        else
          if a == 0 then some (1, .right, 18) else some (0, .left, 23)
  else
    if q.val < 21 then
      if q.val < 19 then
        if a == 0 then some (0, .right, 18) else some (1, .right, 19)
      else
        if q.val < 20 then
          if a == 0 then some (0, .right, 20) else some (1, .right, 19)
        else
          if a == 0 then some (0, .left, 21) else some (1, .right, 19)
    else
      if q.val < 22 then
        if a == 0 then some (1, .left, 22) else some (0, .left, 23)
      else
        if q.val < 23 then
          if a == 0 then some (0, .right, 21) else some (1, .left, 22)
        else
          if a == 0 then some (0, .left, 24) else some (1, .left, 23)
def zf393Trans_2 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 30 then
    if q.val < 27 then
      if q.val < 25 then
        if a == 0 then some (0, .left, 25) else some (1, .left, 23)
      else
        if q.val < 26 then
          if a == 0 then some (0, .left, 25) else some (0, .left, 61)
        else
          if a == 0 then some (0, .left, 27) else some (1, .left, 26)
    else
      if q.val < 28 then
        if a == 0 then some (0, .left, 28) else some (1, .left, 26)
      else
        if q.val < 29 then
          if a == 0 then some (0, .left, 28) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 49)
  else
    if q.val < 33 then
      if q.val < 31 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 50)
      else
        if q.val < 32 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 39)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 40)
    else
      if q.val < 34 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 29)
      else
        if q.val < 35 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 30)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 33)
def zf393Trans_3 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 42 then
    if q.val < 39 then
      if q.val < 37 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 34)
      else
        if q.val < 38 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 35)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 36)
    else
      if q.val < 40 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 5)
      else
        if q.val < 41 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 13)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 37)
  else
    if q.val < 45 then
      if q.val < 43 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 38)
      else
        if q.val < 44 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 41)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 42)
    else
      if q.val < 47 then
        if q.val < 46 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 43)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 44)
      else
        if q.val < 48 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 31)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 32)
def zf393Trans_4 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 55 then
    if q.val < 52 then
      if q.val < 50 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 47)
      else
        if q.val < 51 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 48)
        else
          if a == 0 then some (0, .left, 52) else some (1, .left, 64)
    else
      if q.val < 53 then
        if a == 0 then some (0, .left, 53) else some (1, .left, 64)
      else
        if q.val < 54 then
          if a == 0 then some (0, .left, 54) else some (1, .left, 64)
        else
          if a == 0 then some (0, .left, 55) else some (1, .left, 64)
  else
    if q.val < 58 then
      if q.val < 56 then
        if a == 0 then some (0, .left, 56) else some (1, .left, 64)
      else
        if q.val < 57 then
          if a == 0 then some (0, .left, 57) else some (1, .left, 64)
        else
          if a == 0 then some (0, .left, 58) else some (1, .left, 64)
    else
      if q.val < 59 then
        if a == 0 then some (0, .left, 59) else some (1, .left, 64)
      else
        if q.val < 60 then
          if a == 0 then some (0, .right, 60) else some (1, .left, 64)
        else
          if a == 0 then some (0, .right, 60) else some (1, .right, 99)
def zf393Trans_5 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 67 then
    if q.val < 64 then
      if q.val < 62 then
        if a == 0 then some (1, .left, 64) else some (0, .left, 61)
      else
        if q.val < 63 then
          if a == 0 then some (0, .left, 61) else some (0, .left, 62)
        else
          if a == 0 then some (0, .left, 62) else some (0, .left, 63)
    else
      if q.val < 65 then
        if a == 0 then some (0, .left, 51) else some (1, .left, 64)
      else
        if q.val < 66 then
          if a == 0 then some (0, .left, 65) else some (0, .left, 64)
        else
          if a == 0 then some (0, .left, 66) else some (0, .left, 65)
  else
    if q.val < 70 then
      if q.val < 68 then
        if a == 0 then some (0, .left, 67) else some (0, .left, 66)
      else
        if q.val < 69 then
          if a == 0 then some (0, .left, 68) else some (0, .left, 67)
        else
          if a == 0 then some (0, .right, 289) else some (1, .right, 70)
    else
      if q.val < 71 then
        if a == 0 then some (0, .right, 294) else some (1, .right, 379)
      else
        if q.val < 72 then
          if a == 0 then some (0, .right, 72) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 29) else some (1, .right, 73)
def zf393Trans_6 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 79 then
    if q.val < 76 then
      if q.val < 74 then
        if a == 0 then some (0, .right, 74) else some (1, .right, 77)
      else
        if q.val < 75 then
          if a == 0 then some (0, .right, 29) else some (1, .right, 75)
        else
          if a == 0 then some (0, .right, 76) else some (0, .left, 62)
    else
      if q.val < 77 then
        if a == 0 then some (0, .right, 30) else some (1, .right, 30)
      else
        if q.val < 78 then
          if a == 0 then some (0, .right, 78) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 30) else some (1, .right, 289)
  else
    if q.val < 82 then
      if q.val < 80 then
        if a == 0 then some (0, .right, 71) else some (1, .right, 80)
      else
        if q.val < 81 then
          if a == 0 then some (0, .right, 352) else some (1, .right, 366)
        else
          if a == 0 then some (0, .right, 71) else some (1, .right, 82)
    else
      if q.val < 83 then
        if a == 0 then some (0, .right, 356) else some (1, .right, 368)
      else
        if q.val < 84 then
          if a == 0 then some (0, .right, 29) else some (1, .right, 84)
        else
          if a == 0 then some (0, .right, 382) else some (1, .right, 371)
def zf393Trans_7 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 91 then
    if q.val < 88 then
      if q.val < 86 then
        if a == 0 then some (0, .right, 86) else some (1, .right, 90)
      else
        if q.val < 87 then
          if a == 0 then some (0, .right, 43) else some (1, .right, 87)
        else
          if a == 0 then some (0, .right, 88) else some (1, .right, 89)
    else
      if q.val < 89 then
        if a == 0 then some (0, .right, 45) else some (0, .left, 65)
      else
        if q.val < 90 then
          if a == 0 then some (0, .right, 376) else some (0, .left, 63)
        else
          if a == 0 then some (0, .right, 45) else some (1, .right, 91)
  else
    if q.val < 94 then
      if q.val < 92 then
        if a == 0 then some (0, .right, 381) else some (0, .left, 62)
      else
        if q.val < 93 then
          if a == 0 then some (0, .right, 85) else some (1, .right, 382)
        else
          if a == 0 then some (0, .right, 85) else some (1, .right, 94)
    else
      if q.val < 96 then
        if q.val < 95 then
          if a == 0 then some (0, .right, 348) else some (1, .right, 364)
        else
          if a == 0 then some (0, .right, 96) else some (1, .right, 97)
      else
        if q.val < 97 then
          if a == 0 then some (0, .right, 39) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 343) else some (1, .right, 98)
def zf393Trans_8 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 104 then
    if q.val < 101 then
      if q.val < 99 then
        if a == 0 then some (0, .right, 362) else some (1, .right, 32)
      else
        if q.val < 100 then
          if a == 0 then some (0, .right, 95) else some (1, .right, 100)
        else
          if a == 0 then some (0, .right, 342) else some (1, .right, 101)
    else
      if q.val < 102 then
        if a == 0 then some (0, .right, 346) else some (1, .right, 102)
      else
        if q.val < 103 then
          if a == 0 then some (0, .right, 352) else some (1, .right, 103)
        else
          if a == 0 then some (0, .right, 356) else some (1, .right, 104)
  else
    if q.val < 107 then
      if q.val < 105 then
        if a == 0 then some (0, .right, 269) else some (1, .right, 105)
      else
        if q.val < 106 then
          if a == 0 then some (0, .right, 360) else some (1, .right, 106)
        else
          if a == 0 then some (0, .right, 269) else some (1, .right, 107)
    else
      if q.val < 108 then
        if a == 0 then some (0, .right, 364) else some (1, .right, 108)
      else
        if q.val < 109 then
          if a == 0 then some (0, .right, 269) else some (1, .right, 109)
        else
          if a == 0 then some (0, .right, 366) else some (1, .right, 110)
def zf393Trans_9 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 116 then
    if q.val < 113 then
      if q.val < 111 then
        if a == 0 then some (0, .right, 269) else some (1, .right, 111)
      else
        if q.val < 112 then
          if a == 0 then some (0, .right, 368) else some (1, .right, 112)
        else
          if a == 0 then some (0, .right, 304) else some (1, .right, 113)
    else
      if q.val < 114 then
        if a == 0 then some (0, .right, 321) else some (1, .right, 114)
      else
        if q.val < 115 then
          if a == 0 then some (0, .right, 277) else some (1, .right, 115)
        else
          if a == 0 then some (0, .right, 265) else some (1, .right, 116)
  else
    if q.val < 119 then
      if q.val < 117 then
        if a == 0 then some (0, .right, 320) else some (1, .right, 117)
      else
        if q.val < 118 then
          if a == 0 then some (0, .right, 257) else some (1, .right, 118)
        else
          if a == 0 then some (0, .right, 270) else some (1, .right, 119)
    else
      if q.val < 120 then
        if a == 0 then some (0, .right, 325) else some (1, .right, 120)
      else
        if q.val < 121 then
          if a == 0 then some (0, .right, 319) else some (1, .right, 121)
        else
          if a == 0 then some (0, .right, 249) else some (1, .right, 122)
def zf393Trans_10 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 128 then
    if q.val < 125 then
      if q.val < 123 then
        if a == 0 then some (0, .right, 238) else some (1, .right, 123)
      else
        if q.val < 124 then
          if a == 0 then some (0, .right, 390) else some (1, .right, 124)
        else
          if a == 0 then some (0, .right, 238) else some (1, .right, 125)
    else
      if q.val < 126 then
        if a == 0 then some (0, .right, 248) else some (1, .right, 126)
      else
        if q.val < 127 then
          if a == 0 then some (0, .right, 323) else some (1, .right, 127)
        else
          if a == 0 then some (0, .right, 270) else some (1, .right, 128)
  else
    if q.val < 131 then
      if q.val < 129 then
        if a == 0 then some (0, .right, 245) else some (1, .right, 129)
      else
        if q.val < 130 then
          if a == 0 then some (0, .right, 321) else some (1, .right, 130)
        else
          if a == 0 then some (0, .right, 320) else some (1, .right, 131)
    else
      if q.val < 133 then
        if q.val < 132 then
          if a == 0 then some (0, .right, 247) else some (1, .right, 132)
        else
          if a == 0 then some (0, .right, 272) else some (1, .right, 133)
      else
        if q.val < 134 then
          if a == 0 then some (0, .right, 241) else some (1, .right, 134)
        else
          if a == 0 then some (0, .right, 392) else some (1, .right, 135)
def zf393Trans_11 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 141 then
    if q.val < 138 then
      if q.val < 136 then
        if a == 0 then some (0, .right, 298) else some (1, .right, 136)
      else
        if q.val < 137 then
          if a == 0 then some (0, .right, 274) else some (1, .right, 137)
        else
          if a == 0 then some (0, .right, 245) else some (1, .right, 138)
    else
      if q.val < 139 then
        if a == 0 then some (0, .right, 285) else some (1, .right, 139)
      else
        if q.val < 140 then
          if a == 0 then some (0, .right, 247) else some (1, .right, 140)
        else
          if a == 0 then some (0, .right, 278) else some (1, .right, 141)
  else
    if q.val < 144 then
      if q.val < 142 then
        if a == 0 then some (0, .right, 241) else some (1, .right, 142)
      else
        if q.val < 143 then
          if a == 0 then some (0, .right, 298) else some (1, .right, 143)
        else
          if a == 0 then some (0, .right, 392) else some (1, .right, 144)
    else
      if q.val < 145 then
        if a == 0 then some (0, .right, 300) else some (1, .right, 145)
      else
        if q.val < 146 then
          if a == 0 then some (0, .right, 226) else some (1, .right, 146)
        else
          if a == 0 then some (0, .right, 300) else some (1, .right, 147)
def zf393Trans_12 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 153 then
    if q.val < 150 then
      if q.val < 148 then
        if a == 0 then some (0, .right, 329) else some (1, .right, 148)
      else
        if q.val < 149 then
          if a == 0 then some (0, .right, 271) else some (1, .right, 149)
        else
          if a == 0 then some (0, .right, 254) else some (1, .right, 150)
    else
      if q.val < 151 then
        if a == 0 then some (0, .right, 302) else some (1, .right, 151)
      else
        if q.val < 152 then
          if a == 0 then some (0, .right, 254) else some (1, .right, 152)
        else
          if a == 0 then some (0, .right, 271) else some (1, .right, 153)
  else
    if q.val < 156 then
      if q.val < 154 then
        if a == 0 then some (0, .right, 323) else some (1, .right, 154)
      else
        if q.val < 155 then
          if a == 0 then some (0, .right, 351) else some (1, .right, 155)
        else
          if a == 0 then some (0, .right, 364) else some (1, .right, 156)
    else
      if q.val < 157 then
        if a == 0 then some (0, .right, 255) else some (1, .right, 157)
      else
        if q.val < 158 then
          if a == 0 then some (0, .right, 355) else some (1, .right, 158)
        else
          if a == 0 then some (0, .right, 366) else some (1, .right, 159)
def zf393Trans_13 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 165 then
    if q.val < 162 then
      if q.val < 160 then
        if a == 0 then some (0, .right, 255) else some (1, .right, 160)
      else
        if q.val < 161 then
          if a == 0 then some (0, .right, 231) else some (1, .right, 161)
        else
          if a == 0 then some (0, .right, 329) else some (1, .right, 162)
    else
      if q.val < 163 then
        if a == 0 then some (0, .right, 331) else some (1, .right, 163)
      else
        if q.val < 164 then
          if a == 0 then some (0, .right, 253) else some (1, .right, 164)
        else
          if a == 0 then some (0, .right, 272) else some (1, .right, 165)
  else
    if q.val < 168 then
      if q.val < 166 then
        if a == 0 then some (0, .right, 279) else some (1, .right, 166)
      else
        if q.val < 167 then
          if a == 0 then some (0, .right, 325) else some (1, .right, 167)
        else
          if a == 0 then some (0, .right, 259) else some (1, .right, 168)
    else
      if q.val < 169 then
        if a == 0 then some (0, .right, 243) else some (1, .right, 169)
      else
        if q.val < 170 then
          if a == 0 then some (0, .right, 329) else some (1, .right, 170)
        else
          if a == 0 then some (0, .right, 273) else some (1, .right, 171)
def zf393Trans_14 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 177 then
    if q.val < 174 then
      if q.val < 172 then
        if a == 0 then some (0, .right, 329) else some (1, .right, 172)
      else
        if q.val < 173 then
          if a == 0 then some (0, .right, 226) else some (1, .right, 173)
        else
          if a == 0 then some (0, .right, 327) else some (1, .right, 174)
    else
      if q.val < 175 then
        if a == 0 then some (0, .right, 302) else some (1, .right, 175)
      else
        if q.val < 176 then
          if a == 0 then some (0, .right, 300) else some (1, .right, 176)
        else
          if a == 0 then some (0, .right, 244) else some (1, .right, 177)
  else
    if q.val < 180 then
      if q.val < 178 then
        if a == 0 then some (0, .right, 390) else some (1, .right, 178)
      else
        if q.val < 179 then
          if a == 0 then some (0, .right, 273) else some (1, .right, 179)
        else
          if a == 0 then some (0, .right, 274) else some (1, .right, 180)
    else
      if q.val < 182 then
        if q.val < 181 then
          if a == 0 then some (0, .right, 302) else some (1, .right, 181)
        else
          if a == 0 then some (0, .right, 390) else some (1, .right, 182)
      else
        if q.val < 183 then
          if a == 0 then some (0, .right, 268) else some (1, .right, 183)
        else
          if a == 0 then some (0, .right, 320) else some (1, .right, 184)
def zf393Trans_15 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 190 then
    if q.val < 187 then
      if q.val < 185 then
        if a == 0 then some (0, .right, 275) else some (1, .right, 185)
      else
        if q.val < 186 then
          if a == 0 then some (0, .right, 327) else some (1, .right, 186)
        else
          if a == 0 then some (0, .right, 248) else some (1, .right, 187)
    else
      if q.val < 188 then
        if a == 0 then some (0, .right, 263) else some (1, .right, 188)
      else
        if q.val < 189 then
          if a == 0 then some (0, .right, 275) else some (1, .right, 189)
        else
          if a == 0 then some (0, .right, 250) else some (1, .right, 190)
  else
    if q.val < 193 then
      if q.val < 191 then
        if a == 0 then some (0, .right, 304) else some (1, .right, 191)
      else
        if q.val < 192 then
          if a == 0 then some (0, .right, 257) else some (1, .right, 192)
        else
          if a == 0 then some (0, .right, 276) else some (1, .right, 193)
    else
      if q.val < 194 then
        if a == 0 then some (0, .right, 79) else some (1, .right, 194)
      else
        if q.val < 195 then
          if a == 0 then some (0, .right, 282) else some (1, .right, 195)
        else
          if a == 0 then some (0, .right, 390) else some (1, .right, 196)
def zf393Trans_16 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 202 then
    if q.val < 199 then
      if q.val < 197 then
        if a == 0 then some (0, .right, 388) else some (1, .right, 197)
      else
        if q.val < 198 then
          if a == 0 then some (0, .right, 354) else some (1, .right, 198)
        else
          if a == 0 then some (0, .right, 366) else some (1, .right, 199)
    else
      if q.val < 200 then
        if a == 0 then some (0, .right, 93) else some (1, .right, 200)
      else
        if q.val < 201 then
          if a == 0 then some (0, .right, 276) else some (1, .right, 201)
        else
          if a == 0 then some (0, .right, 259) else some (1, .right, 202)
  else
    if q.val < 205 then
      if q.val < 203 then
        if a == 0 then some (0, .right, 231) else some (1, .right, 203)
      else
        if q.val < 204 then
          if a == 0 then some (0, .right, 270) else some (1, .right, 204)
        else
          if a == 0 then some (0, .right, 300) else some (1, .right, 205)
    else
      if q.val < 206 then
        if a == 0 then some (0, .right, 267) else some (1, .right, 206)
      else
        if q.val < 207 then
          if a == 0 then some (0, .right, 260) else some (1, .right, 207)
        else
          if a == 0 then some (0, .right, 304) else some (1, .right, 208)
def zf393Trans_17 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 214 then
    if q.val < 211 then
      if q.val < 209 then
        if a == 0 then some (0, .right, 260) else some (1, .right, 209)
      else
        if q.val < 210 then
          if a == 0 then some (0, .right, 249) else some (1, .right, 210)
        else
          if a == 0 then some (0, .right, 319) else some (1, .right, 211)
    else
      if q.val < 212 then
        if a == 0 then some (0, .right, 277) else some (1, .right, 212)
      else
        if q.val < 213 then
          if a == 0 then some (0, .right, 327) else some (1, .right, 213)
        else
          if a == 0 then some (0, .right, 261) else some (1, .right, 214)
  else
    if q.val < 217 then
      if q.val < 215 then
        if a == 0 then some (0, .right, 390) else some (1, .right, 215)
      else
        if q.val < 216 then
          if a == 0 then some (0, .right, 261) else some (1, .right, 216)
        else
          if a == 0 then some (0, .right, 277) else some (1, .right, 217)
    else
      if q.val < 219 then
        if q.val < 218 then
          if a == 0 then some (0, .right, 250) else some (1, .right, 218)
        else
          if a == 0 then some (0, .right, 278) else some (1, .right, 219)
      else
        if q.val < 220 then
          if a == 0 then some (0, .right, 272) else some (1, .right, 220)
        else
          if a == 0 then some (0, .right, 278) else some (1, .right, 221)
def zf393Trans_18 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 227 then
    if q.val < 224 then
      if q.val < 222 then
        if a == 0 then some (0, .right, 305) else some (1, .right, 222)
      else
        if q.val < 223 then
          if a == 0 then some (0, .right, 47) else some (1, .right, 223)
        else
          if a == 0 then some (0, .right, 224) else none
    else
      if q.val < 225 then
        if a == 0 then some (0, .right, 47) else some (1, .right, 225)
      else
        if q.val < 226 then
          if a == 0 then some (0, .right, 288) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 243) else some (1, .right, 227)
  else
    if q.val < 230 then
      if q.val < 228 then
        if a == 0 then some (0, .right, 327) else some (1, .right, 228)
      else
        if q.val < 229 then
          if a == 0 then some (0, .right, 273) else some (1, .right, 229)
        else
          if a == 0 then some (0, .right, 244) else some (1, .right, 230)
    else
      if q.val < 231 then
        if a == 0 then some (0, .right, 329) else some (1, .right, 282)
      else
        if q.val < 232 then
          if a == 0 then some (0, .right, 253) else some (1, .right, 232)
        else
          if a == 0 then some (0, .right, 325) else some (1, .right, 233)
def zf393Trans_19 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 239 then
    if q.val < 236 then
      if q.val < 234 then
        if a == 0 then some (0, .right, 325) else some (1, .right, 234)
      else
        if q.val < 235 then
          if a == 0 then some (0, .right, 300) else some (1, .right, 235)
        else
          if a == 0 then some (0, .right, 259) else some (1, .right, 236)
    else
      if q.val < 237 then
        if a == 0 then some (0, .right, 271) else some (1, .right, 237)
      else
        if q.val < 238 then
          if a == 0 then some (0, .right, 283) else some (1, .right, 279)
        else
          if a == 0 then some (0, .right, 321) else some (1, .right, 239)
  else
    if q.val < 242 then
      if q.val < 240 then
        if a == 0 then some (0, .right, 264) else some (1, .right, 240)
      else
        if q.val < 241 then
          if a == 0 then some (0, .right, 265) else some (1, .right, 278)
        else
          if a == 0 then some (0, .right, 248) else some (1, .right, 242)
    else
      if q.val < 243 then
        if a == 0 then some (0, .right, 270) else some (1, .right, 283)
      else
        if q.val < 244 then
          if a == 0 then some (0, .right, 246) else some (1, .right, 286)
        else
          if a == 0 then some (0, .right, 327) else some (1, .right, 246)
def zf393Trans_20 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 251 then
    if q.val < 248 then
      if q.val < 246 then
        if a == 0 then some (0, .right, 267) else some (1, .right, 285)
      else
        if q.val < 247 then
          if a == 0 then some (0, .right, 268) else some (1, .right, 279)
        else
          if a == 0 then some (0, .right, 327) else some (1, .right, 264)
    else
      if q.val < 249 then
        if a == 0 then some (0, .right, 263) else some (1, .right, 390)
      else
        if q.val < 250 then
          if a == 0 then some (0, .right, 320) else some (1, .right, 263)
        else
          if a == 0 then some (0, .right, 327) else some (1, .right, 251)
  else
    if q.val < 254 then
      if q.val < 252 then
        if a == 0 then some (0, .right, 390) else some (1, .right, 252)
      else
        if q.val < 253 then
          if a == 0 then some (0, .right, 323) else some (1, .right, 325)
        else
          if a == 0 then some (0, .right, 283) else some (1, .right, 273)
    else
      if q.val < 255 then
        if a == 0 then some (0, .right, 279) else some (1, .right, 327)
      else
        if q.val < 256 then
          if a == 0 then some (0, .right, 358) else some (1, .right, 256)
        else
          if a == 0 then some (0, .right, 368) else some (1, .right, 92)
def zf393Trans_21 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 263 then
    if q.val < 260 then
      if q.val < 258 then
        if a == 0 then some (0, .right, 319) else some (1, .right, 258)
      else
        if q.val < 259 then
          if a == 0 then some (0, .right, 329) else some (1, .right, 390)
        else
          if a == 0 then some (0, .right, 284) else some (1, .right, 325)
    else
      if q.val < 261 then
        if a == 0 then some (0, .right, 304) else some (1, .right, 280)
      else
        if q.val < 262 then
          if a == 0 then some (0, .right, 319) else some (1, .right, 262)
        else
          if a == 0 then some (0, .right, 304) else some (1, .right, 329)
  else
    if q.val < 266 then
      if q.val < 264 then
        if a == 0 then some (0, .right, 320) else some (1, .right, 280)
      else
        if q.val < 265 then
          if a == 0 then some (0, .right, 321) else some (1, .right, 287)
        else
          if a == 0 then some (0, .right, 319) else some (1, .right, 266)
    else
      if q.val < 268 then
        if q.val < 267 then
          if a == 0 then some (0, .right, 298) else some (1, .right, 325)
        else
          if a == 0 then some (0, .right, 281) else some (1, .right, 319)
      else
        if q.val < 269 then
          if a == 0 then some (0, .right, 390) else some (1, .right, 281)
        else
          if a == 0 then some (0, .right, 313) else some (1, .right, 377)
def zf393Trans_22 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 276 then
    if q.val < 273 then
      if q.val < 271 then
        if a == 0 then some (0, .right, 325) else some (1, .right, 331)
      else
        if q.val < 272 then
          if a == 0 then some (0, .right, 325) else some (1, .right, 390)
        else
          if a == 0 then some (0, .right, 390) else some (1, .right, 325)
    else
      if q.val < 274 then
        if a == 0 then some (0, .right, 300) else some (1, .right, 302)
      else
        if q.val < 275 then
          if a == 0 then some (0, .right, 390) else some (1, .right, 298)
        else
          if a == 0 then some (0, .right, 320) else some (1, .right, 304)
  else
    if q.val < 279 then
      if q.val < 277 then
        if a == 0 then some (0, .right, 305) else some (1, .right, 81)
      else
        if q.val < 278 then
          if a == 0 then some (0, .right, 319) else some (1, .right, 320)
        else
          if a == 0 then some (0, .right, 323) else some (1, .right, 331)
    else
      if q.val < 280 then
        if a == 0 then some (0, .right, 298) else some (1, .right, 300)
      else
        if q.val < 281 then
          if a == 0 then some (0, .right, 319) else some (1, .right, 327)
        else
          if a == 0 then some (0, .right, 390) else some (1, .right, 305)
def zf393Trans_23 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 288 then
    if q.val < 285 then
      if q.val < 283 then
        if a == 0 then some (0, .right, 302) else some (1, .right, 298)
      else
        if q.val < 284 then
          if a == 0 then some (0, .right, 305) else some (1, .right, 298)
        else
          if a == 0 then some (0, .right, 298) else some (1, .right, 302)
    else
      if q.val < 286 then
        if a == 0 then some (0, .right, 320) else some (1, .right, 321)
      else
        if q.val < 287 then
          if a == 0 then some (0, .right, 329) else some (1, .right, 284)
        else
          if a == 0 then some (0, .right, 304) else some (1, .right, 327)
  else
    if q.val < 291 then
      if q.val < 289 then
        if a == 0 then some (0, .right, 48) else some (1, .right, 48)
      else
        if q.val < 290 then
          if a == 0 then some (0, .right, 314) else some (1, .right, 380)
        else
          if a == 0 then some (0, .right, 383) else some (1, .right, 291)
    else
      if q.val < 292 then
        if a == 0 then some (0, .right, 49) else some (1, .right, 292)
      else
        if q.val < 293 then
          if a == 0 then some (0, .right, 293) else some (0, .left, 66)
        else
          if a == 0 then some (0, .right, 42) else some (1, .right, 389)
def zf393Trans_24 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 300 then
    if q.val < 297 then
      if q.val < 295 then
        if a == 0 then some (0, .right, 373) else some (1, .right, 295)
      else
        if q.val < 296 then
          if a == 0 then some (0, .right, 47) else some (1, .right, 296)
        else
          if a == 0 then some (0, .right, 297) else some (0, .left, 66)
    else
      if q.val < 298 then
        if a == 0 then some (0, .right, 44) else some (1, .right, 386)
      else
        if q.val < 299 then
          if a == 0 then some (0, .right, 304) else some (1, .right, 299)
        else
          if a == 0 then some (0, .right, 347) else some (1, .right, 364)
  else
    if q.val < 303 then
      if q.val < 301 then
        if a == 0 then some (0, .right, 304) else some (1, .right, 301)
      else
        if q.val < 302 then
          if a == 0 then some (0, .right, 353) else some (1, .right, 366)
        else
          if a == 0 then some (0, .right, 304) else some (1, .right, 303)
    else
      if q.val < 305 then
        if q.val < 304 then
          if a == 0 then some (0, .right, 357) else some (1, .right, 368)
        else
          if a == 0 then some (0, .right, 290) else some (1, .right, 372)
      else
        if q.val < 306 then
          if a == 0 then some (0, .right, 386) else some (1, .right, 306)
        else
          if a == 0 then some (0, .right, 315) else some (1, .right, 307)
def zf393Trans_25 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 313 then
    if q.val < 310 then
      if q.val < 308 then
        if a == 0 then some (0, .right, 380) else some (1, .right, 308)
      else
        if q.val < 309 then
          if a == 0 then some (0, .right, 83) else some (1, .right, 359)
        else
          if a == 0 then some (0, .right, 43) else some (0, .left, 66)
    else
      if q.val < 311 then
        if a == 0 then some (0, .right, 42) else some (1, .right, 311)
      else
        if q.val < 312 then
          if a == 0 then some (0, .right, 309) else some (1, .right, 312)
        else
          if a == 0 then some (0, .right, 370) else some (0, .left, 67)
  else
    if q.val < 316 then
      if q.val < 314 then
        if a == 0 then some (0, .right, 39) else some (1, .right, 310)
      else
        if q.val < 315 then
          if a == 0 then some (0, .right, 49) else some (1, .right, 310)
        else
          if a == 0 then some (0, .right, 49) else some (1, .right, 316)
    else
      if q.val < 317 then
        if a == 0 then some (0, .right, 48) else some (1, .right, 317)
      else
        if q.val < 318 then
          if a == 0 then some (0, .right, 309) else some (1, .right, 318)
        else
          if a == 0 then some (0, .right, 388) else some (0, .left, 67)
def zf393Trans_26 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 325 then
    if q.val < 322 then
      if q.val < 320 then
        if a == 0 then some (0, .right, 304) else some (1, .right, 48)
      else
        if q.val < 321 then
          if a == 0 then some (0, .right, 304) else some (1, .right, 288)
        else
          if a == 0 then some (0, .right, 319) else some (1, .right, 288)
    else
      if q.val < 323 then
        if a == 0 then some (0, .right, 320) else some (1, .right, 288)
      else
        if q.val < 324 then
          if a == 0 then some (0, .right, 392) else some (1, .right, 324)
        else
          if a == 0 then some (0, .right, 390) else some (1, .right, 392)
  else
    if q.val < 328 then
      if q.val < 326 then
        if a == 0 then some (0, .right, 69) else some (1, .right, 326)
      else
        if q.val < 327 then
          if a == 0 then some (0, .right, 322) else some (1, .right, 69)
        else
          if a == 0 then some (0, .right, 69) else some (1, .right, 328)
    else
      if q.val < 329 then
        if a == 0 then some (0, .right, 319) else some (1, .right, 69)
      else
        if q.val < 330 then
          if a == 0 then some (0, .right, 69) else some (1, .right, 330)
        else
          if a == 0 then some (0, .right, 304) else some (1, .right, 69)
def zf393Trans_27 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 337 then
    if q.val < 334 then
      if q.val < 332 then
        if a == 0 then some (0, .right, 392) else some (1, .right, 332)
      else
        if q.val < 333 then
          if a == 0 then some (0, .right, 325) else some (1, .right, 392)
        else
          if a == 0 then some (0, .right, 44) else some (0, .left, 65)
    else
      if q.val < 335 then
        if a == 0 then some (0, .right, 50) else some (0, .left, 65)
      else
        if q.val < 336 then
          if a == 0 then some (0, .right, 48) else some (0, .left, 65)
        else
          if a == 0 then some (0, .right, 337) else some (0, .left, 65)
  else
    if q.val < 340 then
      if q.val < 338 then
        if a == 0 then some (0, .right, 48) else some (1, .right, 42)
      else
        if q.val < 339 then
          if a == 0 then some (0, .right, 339) else some (0, .left, 65)
        else
          if a == 0 then some (0, .right, 42) else some (1, .right, 46)
    else
      if q.val < 341 then
        if a == 0 then some (0, .right, 341) else some (0, .left, 65)
      else
        if q.val < 342 then
          if a == 0 then some (0, .right, 42) else some (1, .right, 44)
        else
          if a == 0 then some (0, .right, 29) else some (0, .left, 64)
def zf393Trans_28 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 349 then
    if q.val < 346 then
      if q.val < 344 then
        if a == 0 then some (0, .right, 31) else some (1, .right, 344)
      else
        if q.val < 345 then
          if a == 0 then some (0, .right, 345) else some (0, .left, 65)
        else
          if a == 0 then some (0, .right, 42) else some (1, .right, 40)
    else
      if q.val < 347 then
        if a == 0 then some (0, .right, 33) else some (0, .left, 64)
      else
        if q.val < 348 then
          if a == 0 then some (0, .right, 33) else some (1, .right, 336)
        else
          if a == 0 then some (0, .right, 33) else some (1, .right, 349)
  else
    if q.val < 352 then
      if q.val < 350 then
        if a == 0 then some (0, .right, 350) else some (0, .left, 65)
      else
        if q.val < 351 then
          if a == 0 then some (0, .right, 42) else some (1, .right, 48)
        else
          if a == 0 then some (0, .right, 33) else some (1, .right, 340)
    else
      if q.val < 354 then
        if q.val < 353 then
          if a == 0 then some (0, .right, 35) else some (0, .left, 64)
        else
          if a == 0 then some (0, .right, 35) else some (1, .right, 336)
      else
        if q.val < 355 then
          if a == 0 then some (0, .right, 35) else some (1, .right, 338)
        else
          if a == 0 then some (0, .right, 35) else some (1, .right, 340)
def zf393Trans_29 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 362 then
    if q.val < 359 then
      if q.val < 357 then
        if a == 0 then some (0, .right, 37) else some (0, .left, 64)
      else
        if q.val < 358 then
          if a == 0 then some (0, .right, 37) else some (1, .right, 336)
        else
          if a == 0 then some (0, .right, 37) else some (1, .right, 338)
    else
      if q.val < 360 then
        if a == 0 then some (0, .right, 41) else some (0, .left, 64)
      else
        if q.val < 361 then
          if a == 0 then some (0, .right, 41) else some (1, .right, 361)
        else
          if a == 0 then some (0, .right, 30) else some (0, .left, 65)
  else
    if q.val < 365 then
      if q.val < 363 then
        if a == 0 then some (0, .right, 41) else some (1, .right, 363)
      else
        if q.val < 364 then
          if a == 0 then some (0, .right, 32) else some (0, .left, 65)
        else
          if a == 0 then some (0, .right, 41) else some (1, .right, 365)
    else
      if q.val < 366 then
        if a == 0 then some (0, .right, 34) else some (0, .left, 65)
      else
        if q.val < 367 then
          if a == 0 then some (0, .right, 41) else some (1, .right, 367)
        else
          if a == 0 then some (0, .right, 36) else some (0, .left, 65)
def zf393Trans_30 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 374 then
    if q.val < 371 then
      if q.val < 369 then
        if a == 0 then some (0, .right, 41) else some (1, .right, 369)
      else
        if q.val < 370 then
          if a == 0 then some (0, .right, 38) else some (0, .left, 65)
        else
          if a == 0 then some (0, .right, 41) else some (1, .right, 333)
    else
      if q.val < 372 then
        if a == 0 then some (0, .right, 41) else some (1, .right, 335)
      else
        if q.val < 373 then
          if a == 0 then some (0, .right, 41) else some (1, .right, 334)
        else
          if a == 0 then some (0, .right, 41) else some (1, .right, 374)
  else
    if q.val < 377 then
      if q.val < 375 then
        if a == 0 then some (0, .right, 375) else some (0, .left, 65)
      else
        if q.val < 376 then
          if a == 0 then some (0, .right, 48) else some (1, .right, 44)
        else
          if a == 0 then some (0, .right, 43) else some (0, .left, 64)
    else
      if q.val < 378 then
        if a == 0 then some (0, .right, 43) else some (1, .right, 378)
      else
        if q.val < 379 then
          if a == 0 then some (0, .right, 40) else some (0, .left, 65)
        else
          if a == 0 then some (0, .right, 43) else some (1, .right, 335)
def zf393Trans_31 (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 386 then
    if q.val < 383 then
      if q.val < 381 then
        if a == 0 then some (0, .right, 43) else some (1, .right, 334)
      else
        if q.val < 382 then
          if a == 0 then some (0, .right, 45) else some (0, .left, 64)
        else
          if a == 0 then some (0, .right, 47) else some (0, .left, 64)
    else
      if q.val < 384 then
        if a == 0 then some (0, .right, 47) else some (1, .right, 384)
      else
        if q.val < 385 then
          if a == 0 then some (0, .right, 385) else some (0, .left, 65)
        else
          if a == 0 then some (0, .right, 50) else some (1, .right, 42)
  else
    if q.val < 389 then
      if q.val < 387 then
        if a == 0 then some (0, .right, 47) else some (1, .right, 387)
      else
        if q.val < 388 then
          if a == 0 then some (0, .right, 42) else some (0, .left, 65)
        else
          if a == 0 then some (0, .right, 47) else some (1, .right, 333)
    else
      if q.val < 391 then
        if q.val < 390 then
          if a == 0 then some (0, .right, 49) else some (1, .right, 335)
        else
          if a == 0 then some (0, .right, 69) else some (1, .right, 391)
      else
        if q.val < 392 then
          if a == 0 then some (0, .right, 320) else some (1, .right, 69)
        else
          if a == 0 then some (0, .right, 321) else some (1, .right, 69)

def zf393Trans (q : Fin 393) (a : Fin 2) : Option (Fin 2 × Dir × Fin 393) :=
  if q.val < 196 then
    if q.val < 98 then
      if q.val < 49 then
        if q.val < 24 then
          if q.val < 12 then
            zf393Trans_0 q a
          else
            zf393Trans_1 q a
        else
          if q.val < 36 then
            zf393Trans_2 q a
          else
            zf393Trans_3 q a
      else
        if q.val < 73 then
          if q.val < 61 then
            zf393Trans_4 q a
          else
            zf393Trans_5 q a
        else
          if q.val < 85 then
            zf393Trans_6 q a
          else
            zf393Trans_7 q a
    else
      if q.val < 147 then
        if q.val < 122 then
          if q.val < 110 then
            zf393Trans_8 q a
          else
            zf393Trans_9 q a
        else
          if q.val < 135 then
            zf393Trans_10 q a
          else
            zf393Trans_11 q a
      else
        if q.val < 171 then
          if q.val < 159 then
            zf393Trans_12 q a
          else
            zf393Trans_13 q a
        else
          if q.val < 184 then
            zf393Trans_14 q a
          else
            zf393Trans_15 q a
  else
    if q.val < 294 then
      if q.val < 245 then
        if q.val < 221 then
          if q.val < 208 then
            zf393Trans_16 q a
          else
            zf393Trans_17 q a
        else
          if q.val < 233 then
            zf393Trans_18 q a
          else
            zf393Trans_19 q a
      else
        if q.val < 270 then
          if q.val < 257 then
            zf393Trans_20 q a
          else
            zf393Trans_21 q a
        else
          if q.val < 282 then
            zf393Trans_22 q a
          else
            zf393Trans_23 q a
    else
      if q.val < 343 then
        if q.val < 319 then
          if q.val < 307 then
            zf393Trans_24 q a
          else
            zf393Trans_25 q a
        else
          if q.val < 331 then
            zf393Trans_26 q a
          else
            zf393Trans_27 q a
      else
        if q.val < 368 then
          if q.val < 356 then
            zf393Trans_28 q a
          else
            zf393Trans_29 q a
        else
          if q.val < 380 then
            zf393Trans_30 q a
          else
            zf393Trans_31 q a

set_option maxHeartbeats 0 in
-- Exhaustive decision-tree transition lookup over all 393 states and 2 symbols.
@[simp] theorem zf393Trans_eq (q : Fin 393) (a : Fin 2) :
    zf393.transition q a = zf393Trans q a := by
  revert q a; decide

theorem step_mkL_left {q q' : Fin 393} {a b : Fin 2}
    (h : zf393Trans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step zf393 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, zf393Trans_eq, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 393} {a b : Fin 2}
    (h : zf393Trans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step zf393 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, zf393Trans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {q q' : Fin 393} {a b : Fin 2}
    (h : zf393Trans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step zf393 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, zf393Trans_eq, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {q q' : Fin 393} {a b : Fin 2}
    (h : zf393Trans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step zf393 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, zf393Trans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_none {q : Fin 393} {a : Fin 2}
    (h : zf393Trans q a = none) (L R : ListBlank (Fin 2)) :
    step zf393 ⟨q, Tape.mk' L (R.cons a)⟩ = none := by
  simp [step, zf393Trans_eq, h, Tape.mk']

theorem nSteps_mkL_left_scan {q : Fin 393} {a b : Fin 2}
    (h : zf393Trans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {q : Fin 393} {a b : Fin 2}
    (h : zf393Trans q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps zf393 k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]


/-!
## Shared Call-Stack Abstract Machine Definitions for `zf393`
-/

/-- Reversed stack pop for `6.break.k`. -/
def popBreakRev (k : ℕ) : List (Fin 2) → List (Fin 2)
  | [] => []
  | b :: rest =>
    if b == 1 then popBreakRev k rest
    else match k with | 0 => 1 :: rest | k' + 1 => popBreakRev k' rest

@[simp] theorem popBreakRev_nil (k : ℕ) : popBreakRev k [] = [] := rfl
@[simp] theorem popBreakRev_one (k : ℕ) (rest : List (Fin 2)) :
    popBreakRev k (1 :: rest) = popBreakRev k rest := rfl
@[simp] theorem popBreakRev_zero (rest : List (Fin 2)) :
    popBreakRev 0 (0 :: rest) = 1 :: rest := rfl
@[simp] theorem popBreakRev_succ (k : ℕ) (rest : List (Fin 2)) :
    popBreakRev (k + 1) (0 :: rest) = popBreakRev k rest := rfl

/-- Reversed stack pop for `6.continue.k`. -/
def popContinueRev (k : ℕ) : List (Fin 2) → List (Fin 2)
  | [] => []
  | b :: rest =>
    if b == 0 then popContinueRev k rest
    else match k with | 0 => 1 :: rest | k' + 1 => popContinueRev k' rest

@[simp] theorem popContinueRev_nil (k : ℕ) : popContinueRev k [] = [] := rfl
@[simp] theorem popContinueRev_zero (k : ℕ) (rest : List (Fin 2)) :
    popContinueRev k (0 :: rest) = popContinueRev k rest := rfl
@[simp] theorem popContinueRev_zero_one (rest : List (Fin 2)) :
    popContinueRev 0 (1 :: rest) = 1 :: rest := rfl
@[simp] theorem popContinueRev_succ_one (k : ℕ) (rest : List (Fin 2)) :
    popContinueRev (k + 1) (1 :: rest) = popContinueRev k rest := rfl

/-- Returned stack after `6.break.0`. -/
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

/-- Physical left-to-right tape register index (`0..10`). -/
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

/-- 11-register call-stack configuration for `zf393` (`regs` in left-to-right tape order). -/
structure Zf393RegCfg where
  ip : List (Fin 2)
  regs : List ℕ
  deriving DecidableEq, Repr

def zf393RegInit : Zf393RegCfg :=
  ⟨[], List.replicate 11 0⟩

/-- Single abstract macro-step of `zf393` starting at `main().0` (`State 99`). -/
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


inductive BootState where
  | b0 | b1 | b2 | b3 | b4 | b68
  deriving DecidableEq

def stateOfBoot : BootState → Fin 393
  | .b0 => 0 | .b1 => 1 | .b2 => 2 | .b3 => 3 | .b4 => 4 | .b68 => 68

def bitOfBool : Bool → Fin 2
  | false => 0 | true => 1

def stepBootR (q' : BootState) (w : Bool) (L : List Bool) (R : List Bool) :
    Option (BootState × List Bool × Bool × List Bool) :=
  match R with
  | [] => some (q', w :: L, false, [])
  | r :: rs => some (q', w :: L, r, rs)

def stepBootL (q' : BootState) (w : Bool) (L : List Bool) (R : List Bool) :
    Option (BootState × List Bool × Bool × List Bool) :=
  match L with
  | [] => some (q', [], false, w :: R)
  | l :: ls => some (q', ls, l, w :: R)

def stepBoot (q : BootState) (L : List Bool) (h : Bool) (R : List Bool) :
    Option (BootState × List Bool × Bool × List Bool) :=
  match q, h with
  | .b0, false => stepBootR .b1 true L R
  | .b0, true => stepBootL .b2 false L R
  | .b1, false => stepBootR .b2 false L R
  | .b1, true => stepBootR .b1 false L R
  | .b2, false => stepBootL .b3 true L R
  | .b2, true => stepBootR .b4 false L R
  | .b3, false => stepBootL .b4 false L R
  | .b3, true => stepBootL .b68 false L R
  | .b4, false => stepBootL .b0 true L R
  | .b4, true => stepBootL .b1 false L R
  | .b68, _ => none

def runBoot : ℕ → BootState → List Bool → Bool → List Bool →
    Option (BootState × List Bool × Bool × List Bool)
  | 0, q, L, h, R => some (q, L, h, R)
  | n + 1, q, L, h, R =>
    match stepBoot q L h R with
    | none => none
    | some (q', L', h', R') => runBoot n q' L' h' R'

theorem runBoot_add (m n : ℕ) (q : BootState) (L : List Bool) (h : Bool)
    (R : List Bool) :
    runBoot (m + n) q L h R =
      match runBoot m q L h R with
      | none => none
      | some (q', L', h', R') => runBoot n q' L' h' R' := by
  induction m generalizing q L h R with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.succ_add, runBoot, runBoot]
    rcases stepBoot q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'


def bootChkL_0 : List Bool := [
  true, true, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  true]

def bootChkR_0 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true]

theorem boot_chk_0 :
    runBoot 5000 .b0 [] false [] =
      some (.b1, bootChkL_0, true, bootChkR_0) := by
  decide

def bootChkL_1 : List Bool := [
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, true, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, true, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, true, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, true]

def bootChkR_1 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true]

theorem boot_chk_1 :
    runBoot 5000 .b1 bootChkL_0 true bootChkR_0 =
      some (.b4, bootChkL_1, false, bootChkR_1) := by
  decide

def bootChkL_2 : List Bool := [
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, true, true, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, true, true, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, true, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, true]

def bootChkR_2 : List Bool := [
  true, true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true]

theorem boot_chk_2 :
    runBoot 5000 .b4 bootChkL_1 false bootChkR_1 =
      some (.b0, bootChkL_2, false, bootChkR_2) := by
  decide

def bootChkL_3 : List Bool := [
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  true, true, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, true, true, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, true, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, true]

def bootChkR_3 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true]

theorem boot_chk_3 :
    runBoot 5000 .b0 bootChkL_2 false bootChkR_2 =
      some (.b1, bootChkL_3, true, bootChkR_3) := by
  decide

def bootChkL_4 : List Bool := [
  false, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, true, false, true, false, false, false, true, false, false, false, true, false,
  false, true, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, true, true, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, true]

def bootChkR_4 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true]

theorem boot_chk_4 :
    runBoot 5000 .b1 bootChkL_3 true bootChkR_3 =
      some (.b4, bootChkL_4, false, bootChkR_4) := by
  decide

def bootChkL_5 : List Bool := [
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, true, true, false, false, false, true, false, false,
  true, true, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, true]

def bootChkR_5 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true]

theorem boot_chk_5 :
    runBoot 5000 .b4 bootChkL_4 false bootChkR_4 =
      some (.b1, bootChkL_5, true, bootChkR_5) := by
  decide

def bootChkL_6 : List Bool := [
  false, false, false, true, false, false, false, true, false, false, true, true, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, false, true, false, false, false, true,
  false, false, false, true, false, false, false, true, false, false, true, true, true,
  false, false, true, true, false, false, true, false, false, false, true, false, false,
  false, true, false, false, false, true, false, false, false, true, false, false, true]

def bootChkR_6 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true]

theorem boot_chk_6 :
    runBoot 5000 .b1 bootChkL_5 true bootChkR_5 =
      some (.b0, bootChkL_6, true, bootChkR_6) := by
  decide

def bootChkL_7 : List Bool := [
  false, false, true, false, false, false, true, false, false, false, true, false, false,
  false, true, false, false, true]

def bootChkR_7 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, true]

theorem boot_chk_7 :
    runBoot 4734 .b0 bootChkL_6 true bootChkR_6 =
      some (.b68, bootChkL_7, false, bootChkR_7) := by
  decide

theorem boot_phase1_39734 :
    runBoot 39734 .b0 [] false [] = some (.b68, bootChkL_7, false, bootChkR_7) := by
  have h : (39734 : ℕ) = 5000 + (5000 + (5000 + (5000 + (5000 + (5000 + (5000 + 4734)))))) := rfl
  simp only [h, runBoot_add, boot_chk_0, boot_chk_1, boot_chk_2, boot_chk_3, boot_chk_4,
    boot_chk_5, boot_chk_6, boot_chk_7]

end ConjectureMachines.Zf393

end
