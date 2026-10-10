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
open ConjectureMachines.Riemann543.Layer1 (nSteps nSteps_succ Tape.mkL append_replicate_cons)

abbrev TM (states symbols : ℕ) := Machine states symbols

abbrev TMRow (states : ℕ) := Array (Option (Fin 2 × Dir × Fin states))

set_option maxRecDepth 200000

def zf393Rows : Array (TMRow 393) := #[
  #[some (1, .right, 1), some (0, .left, 2)],
  #[some (0, .right, 2), some (0, .right, 1)],
  #[some (1, .left, 3), some (0, .right, 4)],
  #[some (0, .left, 4), some (0, .left, 68)],
  #[some (1, .left, 0), some (0, .left, 1)],
  #[some (1, .right, 6), some (1, .left, 10)],
  #[some (0, .right, 6), some (0, .right, 7)],
  #[some (1, .right, 8), some (1, .right, 7)],
  #[some (0, .right, 9), some (0, .right, 7)],
  #[some (0, .left, 5), some (1, .right, 9)],
  #[some (0, .left, 26), some (1, .right, 11)],
  #[some (1, .right, 12), some (0, .right, 11)],
  #[some (0, .left, 17), some (1, .right, 9)],
  #[some (1, .right, 14), none],
  #[some (0, .right, 14), some (1, .right, 15)],
  #[some (0, .right, 16), some (1, .right, 15)],
  #[some (1, .left, 23), some (1, .right, 15)],
  #[some (1, .right, 18), some (0, .left, 23)],
  #[some (0, .right, 18), some (1, .right, 19)],
  #[some (0, .right, 20), some (1, .right, 19)],
  #[some (0, .left, 21), some (1, .right, 19)],
  #[some (1, .left, 22), some (0, .left, 23)],
  #[some (0, .right, 21), some (1, .left, 22)],
  #[some (0, .left, 24), some (1, .left, 23)],
  #[some (0, .left, 25), some (1, .left, 23)],
  #[some (0, .left, 25), some (0, .left, 61)],
  #[some (0, .left, 27), some (1, .left, 26)],
  #[some (0, .left, 28), some (1, .left, 26)],
  #[some (0, .left, 28), some (0, .left, 62)],
  #[some (0, .right, 17), some (1, .right, 49)],
  #[some (0, .right, 17), some (1, .right, 50)],
  #[some (0, .right, 17), some (1, .right, 39)],
  #[some (0, .right, 17), some (1, .right, 40)],
  #[some (0, .right, 17), some (1, .right, 29)],
  #[some (0, .right, 17), some (1, .right, 30)],
  #[some (0, .right, 17), some (1, .right, 33)],
  #[some (0, .right, 17), some (1, .right, 34)],
  #[some (0, .right, 17), some (1, .right, 35)],
  #[some (0, .right, 17), some (1, .right, 36)],
  #[some (0, .right, 17), some (1, .right, 5)],
  #[some (0, .right, 17), some (1, .right, 13)],
  #[some (0, .right, 17), some (1, .right, 37)],
  #[some (0, .right, 17), some (1, .right, 38)],
  #[some (0, .right, 17), some (1, .right, 41)],
  #[some (0, .right, 17), some (1, .right, 42)],
  #[some (0, .right, 17), some (1, .right, 43)],
  #[some (0, .right, 17), some (1, .right, 44)],
  #[some (0, .right, 17), some (1, .right, 31)],
  #[some (0, .right, 17), some (1, .right, 32)],
  #[some (0, .right, 17), some (1, .right, 47)],
  #[some (0, .right, 17), some (1, .right, 48)],
  #[some (0, .left, 52), some (1, .left, 64)],
  #[some (0, .left, 53), some (1, .left, 64)],
  #[some (0, .left, 54), some (1, .left, 64)],
  #[some (0, .left, 55), some (1, .left, 64)],
  #[some (0, .left, 56), some (1, .left, 64)],
  #[some (0, .left, 57), some (1, .left, 64)],
  #[some (0, .left, 58), some (1, .left, 64)],
  #[some (0, .left, 59), some (1, .left, 64)],
  #[some (0, .right, 60), some (1, .left, 64)],
  #[some (0, .right, 60), some (1, .right, 99)],
  #[some (1, .left, 64), some (0, .left, 61)],
  #[some (0, .left, 61), some (0, .left, 62)],
  #[some (0, .left, 62), some (0, .left, 63)],
  #[some (0, .left, 51), some (1, .left, 64)],
  #[some (0, .left, 65), some (0, .left, 64)],
  #[some (0, .left, 66), some (0, .left, 65)],
  #[some (0, .left, 67), some (0, .left, 66)],
  #[some (0, .left, 68), some (0, .left, 67)],
  #[some (0, .right, 289), some (1, .right, 70)],
  #[some (0, .right, 294), some (1, .right, 379)],
  #[some (0, .right, 72), some (0, .left, 62)],
  #[some (0, .right, 29), some (1, .right, 73)],
  #[some (0, .right, 74), some (1, .right, 77)],
  #[some (0, .right, 29), some (1, .right, 75)],
  #[some (0, .right, 76), some (0, .left, 62)],
  #[some (0, .right, 30), some (1, .right, 30)],
  #[some (0, .right, 78), some (0, .left, 62)],
  #[some (0, .right, 30), some (1, .right, 289)],
  #[some (0, .right, 71), some (1, .right, 80)],
  #[some (0, .right, 352), some (1, .right, 366)],
  #[some (0, .right, 71), some (1, .right, 82)],
  #[some (0, .right, 356), some (1, .right, 368)],
  #[some (0, .right, 29), some (1, .right, 84)],
  #[some (0, .right, 382), some (1, .right, 371)],
  #[some (0, .right, 86), some (1, .right, 90)],
  #[some (0, .right, 43), some (1, .right, 87)],
  #[some (0, .right, 88), some (1, .right, 89)],
  #[some (0, .right, 45), some (0, .left, 65)],
  #[some (0, .right, 376), some (0, .left, 63)],
  #[some (0, .right, 45), some (1, .right, 91)],
  #[some (0, .right, 381), some (0, .left, 62)],
  #[some (0, .right, 85), some (1, .right, 382)],
  #[some (0, .right, 85), some (1, .right, 94)],
  #[some (0, .right, 348), some (1, .right, 364)],
  #[some (0, .right, 96), some (1, .right, 97)],
  #[some (0, .right, 39), some (0, .left, 62)],
  #[some (0, .right, 343), some (1, .right, 98)],
  #[some (0, .right, 362), some (1, .right, 32)],
  #[some (0, .right, 95), some (1, .right, 100)],
  #[some (0, .right, 342), some (1, .right, 101)],
  #[some (0, .right, 346), some (1, .right, 102)],
  #[some (0, .right, 352), some (1, .right, 103)],
  #[some (0, .right, 356), some (1, .right, 104)],
  #[some (0, .right, 269), some (1, .right, 105)],
  #[some (0, .right, 360), some (1, .right, 106)],
  #[some (0, .right, 269), some (1, .right, 107)],
  #[some (0, .right, 364), some (1, .right, 108)],
  #[some (0, .right, 269), some (1, .right, 109)],
  #[some (0, .right, 366), some (1, .right, 110)],
  #[some (0, .right, 269), some (1, .right, 111)],
  #[some (0, .right, 368), some (1, .right, 112)],
  #[some (0, .right, 304), some (1, .right, 113)],
  #[some (0, .right, 321), some (1, .right, 114)],
  #[some (0, .right, 277), some (1, .right, 115)],
  #[some (0, .right, 265), some (1, .right, 116)],
  #[some (0, .right, 320), some (1, .right, 117)],
  #[some (0, .right, 257), some (1, .right, 118)],
  #[some (0, .right, 270), some (1, .right, 119)],
  #[some (0, .right, 325), some (1, .right, 120)],
  #[some (0, .right, 319), some (1, .right, 121)],
  #[some (0, .right, 249), some (1, .right, 122)],
  #[some (0, .right, 238), some (1, .right, 123)],
  #[some (0, .right, 390), some (1, .right, 124)],
  #[some (0, .right, 238), some (1, .right, 125)],
  #[some (0, .right, 248), some (1, .right, 126)],
  #[some (0, .right, 323), some (1, .right, 127)],
  #[some (0, .right, 270), some (1, .right, 128)],
  #[some (0, .right, 245), some (1, .right, 129)],
  #[some (0, .right, 321), some (1, .right, 130)],
  #[some (0, .right, 320), some (1, .right, 131)],
  #[some (0, .right, 247), some (1, .right, 132)],
  #[some (0, .right, 272), some (1, .right, 133)],
  #[some (0, .right, 241), some (1, .right, 134)],
  #[some (0, .right, 392), some (1, .right, 135)],
  #[some (0, .right, 298), some (1, .right, 136)],
  #[some (0, .right, 274), some (1, .right, 137)],
  #[some (0, .right, 245), some (1, .right, 138)],
  #[some (0, .right, 285), some (1, .right, 139)],
  #[some (0, .right, 247), some (1, .right, 140)],
  #[some (0, .right, 278), some (1, .right, 141)],
  #[some (0, .right, 241), some (1, .right, 142)],
  #[some (0, .right, 298), some (1, .right, 143)],
  #[some (0, .right, 392), some (1, .right, 144)],
  #[some (0, .right, 300), some (1, .right, 145)],
  #[some (0, .right, 226), some (1, .right, 146)],
  #[some (0, .right, 300), some (1, .right, 147)],
  #[some (0, .right, 329), some (1, .right, 148)],
  #[some (0, .right, 271), some (1, .right, 149)],
  #[some (0, .right, 254), some (1, .right, 150)],
  #[some (0, .right, 302), some (1, .right, 151)],
  #[some (0, .right, 254), some (1, .right, 152)],
  #[some (0, .right, 271), some (1, .right, 153)],
  #[some (0, .right, 323), some (1, .right, 154)],
  #[some (0, .right, 351), some (1, .right, 155)],
  #[some (0, .right, 364), some (1, .right, 156)],
  #[some (0, .right, 255), some (1, .right, 157)],
  #[some (0, .right, 355), some (1, .right, 158)],
  #[some (0, .right, 366), some (1, .right, 159)],
  #[some (0, .right, 255), some (1, .right, 160)],
  #[some (0, .right, 231), some (1, .right, 161)],
  #[some (0, .right, 329), some (1, .right, 162)],
  #[some (0, .right, 331), some (1, .right, 163)],
  #[some (0, .right, 253), some (1, .right, 164)],
  #[some (0, .right, 272), some (1, .right, 165)],
  #[some (0, .right, 279), some (1, .right, 166)],
  #[some (0, .right, 325), some (1, .right, 167)],
  #[some (0, .right, 259), some (1, .right, 168)],
  #[some (0, .right, 243), some (1, .right, 169)],
  #[some (0, .right, 329), some (1, .right, 170)],
  #[some (0, .right, 273), some (1, .right, 171)],
  #[some (0, .right, 329), some (1, .right, 172)],
  #[some (0, .right, 226), some (1, .right, 173)],
  #[some (0, .right, 327), some (1, .right, 174)],
  #[some (0, .right, 302), some (1, .right, 175)],
  #[some (0, .right, 300), some (1, .right, 176)],
  #[some (0, .right, 244), some (1, .right, 177)],
  #[some (0, .right, 390), some (1, .right, 178)],
  #[some (0, .right, 273), some (1, .right, 179)],
  #[some (0, .right, 274), some (1, .right, 180)],
  #[some (0, .right, 302), some (1, .right, 181)],
  #[some (0, .right, 390), some (1, .right, 182)],
  #[some (0, .right, 268), some (1, .right, 183)],
  #[some (0, .right, 320), some (1, .right, 184)],
  #[some (0, .right, 275), some (1, .right, 185)],
  #[some (0, .right, 327), some (1, .right, 186)],
  #[some (0, .right, 248), some (1, .right, 187)],
  #[some (0, .right, 263), some (1, .right, 188)],
  #[some (0, .right, 275), some (1, .right, 189)],
  #[some (0, .right, 250), some (1, .right, 190)],
  #[some (0, .right, 304), some (1, .right, 191)],
  #[some (0, .right, 257), some (1, .right, 192)],
  #[some (0, .right, 276), some (1, .right, 193)],
  #[some (0, .right, 79), some (1, .right, 194)],
  #[some (0, .right, 282), some (1, .right, 195)],
  #[some (0, .right, 390), some (1, .right, 196)],
  #[some (0, .right, 388), some (1, .right, 197)],
  #[some (0, .right, 354), some (1, .right, 198)],
  #[some (0, .right, 366), some (1, .right, 199)],
  #[some (0, .right, 93), some (1, .right, 200)],
  #[some (0, .right, 276), some (1, .right, 201)],
  #[some (0, .right, 259), some (1, .right, 202)],
  #[some (0, .right, 231), some (1, .right, 203)],
  #[some (0, .right, 270), some (1, .right, 204)],
  #[some (0, .right, 300), some (1, .right, 205)],
  #[some (0, .right, 267), some (1, .right, 206)],
  #[some (0, .right, 260), some (1, .right, 207)],
  #[some (0, .right, 304), some (1, .right, 208)],
  #[some (0, .right, 260), some (1, .right, 209)],
  #[some (0, .right, 249), some (1, .right, 210)],
  #[some (0, .right, 319), some (1, .right, 211)],
  #[some (0, .right, 277), some (1, .right, 212)],
  #[some (0, .right, 327), some (1, .right, 213)],
  #[some (0, .right, 261), some (1, .right, 214)],
  #[some (0, .right, 390), some (1, .right, 215)],
  #[some (0, .right, 261), some (1, .right, 216)],
  #[some (0, .right, 277), some (1, .right, 217)],
  #[some (0, .right, 250), some (1, .right, 218)],
  #[some (0, .right, 278), some (1, .right, 219)],
  #[some (0, .right, 272), some (1, .right, 220)],
  #[some (0, .right, 278), some (1, .right, 221)],
  #[some (0, .right, 305), some (1, .right, 222)],
  #[some (0, .right, 47), some (1, .right, 223)],
  #[some (0, .right, 224), none],
  #[some (0, .right, 47), some (1, .right, 225)],
  #[some (0, .right, 288), some (0, .left, 62)],
  #[some (0, .right, 243), some (1, .right, 227)],
  #[some (0, .right, 327), some (1, .right, 228)],
  #[some (0, .right, 273), some (1, .right, 229)],
  #[some (0, .right, 244), some (1, .right, 230)],
  #[some (0, .right, 329), some (1, .right, 282)],
  #[some (0, .right, 253), some (1, .right, 232)],
  #[some (0, .right, 325), some (1, .right, 233)],
  #[some (0, .right, 325), some (1, .right, 234)],
  #[some (0, .right, 300), some (1, .right, 235)],
  #[some (0, .right, 259), some (1, .right, 236)],
  #[some (0, .right, 271), some (1, .right, 237)],
  #[some (0, .right, 283), some (1, .right, 279)],
  #[some (0, .right, 321), some (1, .right, 239)],
  #[some (0, .right, 264), some (1, .right, 240)],
  #[some (0, .right, 265), some (1, .right, 278)],
  #[some (0, .right, 248), some (1, .right, 242)],
  #[some (0, .right, 270), some (1, .right, 283)],
  #[some (0, .right, 246), some (1, .right, 286)],
  #[some (0, .right, 327), some (1, .right, 246)],
  #[some (0, .right, 267), some (1, .right, 285)],
  #[some (0, .right, 268), some (1, .right, 279)],
  #[some (0, .right, 327), some (1, .right, 264)],
  #[some (0, .right, 263), some (1, .right, 390)],
  #[some (0, .right, 320), some (1, .right, 263)],
  #[some (0, .right, 327), some (1, .right, 251)],
  #[some (0, .right, 390), some (1, .right, 252)],
  #[some (0, .right, 323), some (1, .right, 325)],
  #[some (0, .right, 283), some (1, .right, 273)],
  #[some (0, .right, 279), some (1, .right, 327)],
  #[some (0, .right, 358), some (1, .right, 256)],
  #[some (0, .right, 368), some (1, .right, 92)],
  #[some (0, .right, 319), some (1, .right, 258)],
  #[some (0, .right, 329), some (1, .right, 390)],
  #[some (0, .right, 284), some (1, .right, 325)],
  #[some (0, .right, 304), some (1, .right, 280)],
  #[some (0, .right, 319), some (1, .right, 262)],
  #[some (0, .right, 304), some (1, .right, 329)],
  #[some (0, .right, 320), some (1, .right, 280)],
  #[some (0, .right, 321), some (1, .right, 287)],
  #[some (0, .right, 319), some (1, .right, 266)],
  #[some (0, .right, 298), some (1, .right, 325)],
  #[some (0, .right, 281), some (1, .right, 319)],
  #[some (0, .right, 390), some (1, .right, 281)],
  #[some (0, .right, 313), some (1, .right, 377)],
  #[some (0, .right, 325), some (1, .right, 331)],
  #[some (0, .right, 325), some (1, .right, 390)],
  #[some (0, .right, 390), some (1, .right, 325)],
  #[some (0, .right, 300), some (1, .right, 302)],
  #[some (0, .right, 390), some (1, .right, 298)],
  #[some (0, .right, 320), some (1, .right, 304)],
  #[some (0, .right, 305), some (1, .right, 81)],
  #[some (0, .right, 319), some (1, .right, 320)],
  #[some (0, .right, 323), some (1, .right, 331)],
  #[some (0, .right, 298), some (1, .right, 300)],
  #[some (0, .right, 319), some (1, .right, 327)],
  #[some (0, .right, 390), some (1, .right, 305)],
  #[some (0, .right, 302), some (1, .right, 298)],
  #[some (0, .right, 305), some (1, .right, 298)],
  #[some (0, .right, 298), some (1, .right, 302)],
  #[some (0, .right, 320), some (1, .right, 321)],
  #[some (0, .right, 329), some (1, .right, 284)],
  #[some (0, .right, 304), some (1, .right, 327)],
  #[some (0, .right, 48), some (1, .right, 48)],
  #[some (0, .right, 314), some (1, .right, 380)],
  #[some (0, .right, 383), some (1, .right, 291)],
  #[some (0, .right, 49), some (1, .right, 292)],
  #[some (0, .right, 293), some (0, .left, 66)],
  #[some (0, .right, 42), some (1, .right, 389)],
  #[some (0, .right, 373), some (1, .right, 295)],
  #[some (0, .right, 47), some (1, .right, 296)],
  #[some (0, .right, 297), some (0, .left, 66)],
  #[some (0, .right, 44), some (1, .right, 386)],
  #[some (0, .right, 304), some (1, .right, 299)],
  #[some (0, .right, 347), some (1, .right, 364)],
  #[some (0, .right, 304), some (1, .right, 301)],
  #[some (0, .right, 353), some (1, .right, 366)],
  #[some (0, .right, 304), some (1, .right, 303)],
  #[some (0, .right, 357), some (1, .right, 368)],
  #[some (0, .right, 290), some (1, .right, 372)],
  #[some (0, .right, 386), some (1, .right, 306)],
  #[some (0, .right, 315), some (1, .right, 307)],
  #[some (0, .right, 380), some (1, .right, 308)],
  #[some (0, .right, 83), some (1, .right, 359)],
  #[some (0, .right, 43), some (0, .left, 66)],
  #[some (0, .right, 42), some (1, .right, 311)],
  #[some (0, .right, 309), some (1, .right, 312)],
  #[some (0, .right, 370), some (0, .left, 67)],
  #[some (0, .right, 39), some (1, .right, 310)],
  #[some (0, .right, 49), some (1, .right, 310)],
  #[some (0, .right, 49), some (1, .right, 316)],
  #[some (0, .right, 48), some (1, .right, 317)],
  #[some (0, .right, 309), some (1, .right, 318)],
  #[some (0, .right, 388), some (0, .left, 67)],
  #[some (0, .right, 304), some (1, .right, 48)],
  #[some (0, .right, 304), some (1, .right, 288)],
  #[some (0, .right, 319), some (1, .right, 288)],
  #[some (0, .right, 320), some (1, .right, 288)],
  #[some (0, .right, 392), some (1, .right, 324)],
  #[some (0, .right, 390), some (1, .right, 392)],
  #[some (0, .right, 69), some (1, .right, 326)],
  #[some (0, .right, 322), some (1, .right, 69)],
  #[some (0, .right, 69), some (1, .right, 328)],
  #[some (0, .right, 319), some (1, .right, 69)],
  #[some (0, .right, 69), some (1, .right, 330)],
  #[some (0, .right, 304), some (1, .right, 69)],
  #[some (0, .right, 392), some (1, .right, 332)],
  #[some (0, .right, 325), some (1, .right, 392)],
  #[some (0, .right, 44), some (0, .left, 65)],
  #[some (0, .right, 50), some (0, .left, 65)],
  #[some (0, .right, 48), some (0, .left, 65)],
  #[some (0, .right, 337), some (0, .left, 65)],
  #[some (0, .right, 48), some (1, .right, 42)],
  #[some (0, .right, 339), some (0, .left, 65)],
  #[some (0, .right, 42), some (1, .right, 46)],
  #[some (0, .right, 341), some (0, .left, 65)],
  #[some (0, .right, 42), some (1, .right, 44)],
  #[some (0, .right, 29), some (0, .left, 64)],
  #[some (0, .right, 31), some (1, .right, 344)],
  #[some (0, .right, 345), some (0, .left, 65)],
  #[some (0, .right, 42), some (1, .right, 40)],
  #[some (0, .right, 33), some (0, .left, 64)],
  #[some (0, .right, 33), some (1, .right, 336)],
  #[some (0, .right, 33), some (1, .right, 349)],
  #[some (0, .right, 350), some (0, .left, 65)],
  #[some (0, .right, 42), some (1, .right, 48)],
  #[some (0, .right, 33), some (1, .right, 340)],
  #[some (0, .right, 35), some (0, .left, 64)],
  #[some (0, .right, 35), some (1, .right, 336)],
  #[some (0, .right, 35), some (1, .right, 338)],
  #[some (0, .right, 35), some (1, .right, 340)],
  #[some (0, .right, 37), some (0, .left, 64)],
  #[some (0, .right, 37), some (1, .right, 336)],
  #[some (0, .right, 37), some (1, .right, 338)],
  #[some (0, .right, 41), some (0, .left, 64)],
  #[some (0, .right, 41), some (1, .right, 361)],
  #[some (0, .right, 30), some (0, .left, 65)],
  #[some (0, .right, 41), some (1, .right, 363)],
  #[some (0, .right, 32), some (0, .left, 65)],
  #[some (0, .right, 41), some (1, .right, 365)],
  #[some (0, .right, 34), some (0, .left, 65)],
  #[some (0, .right, 41), some (1, .right, 367)],
  #[some (0, .right, 36), some (0, .left, 65)],
  #[some (0, .right, 41), some (1, .right, 369)],
  #[some (0, .right, 38), some (0, .left, 65)],
  #[some (0, .right, 41), some (1, .right, 333)],
  #[some (0, .right, 41), some (1, .right, 335)],
  #[some (0, .right, 41), some (1, .right, 334)],
  #[some (0, .right, 41), some (1, .right, 374)],
  #[some (0, .right, 375), some (0, .left, 65)],
  #[some (0, .right, 48), some (1, .right, 44)],
  #[some (0, .right, 43), some (0, .left, 64)],
  #[some (0, .right, 43), some (1, .right, 378)],
  #[some (0, .right, 40), some (0, .left, 65)],
  #[some (0, .right, 43), some (1, .right, 335)],
  #[some (0, .right, 43), some (1, .right, 334)],
  #[some (0, .right, 45), some (0, .left, 64)],
  #[some (0, .right, 47), some (0, .left, 64)],
  #[some (0, .right, 47), some (1, .right, 384)],
  #[some (0, .right, 385), some (0, .left, 65)],
  #[some (0, .right, 50), some (1, .right, 42)],
  #[some (0, .right, 47), some (1, .right, 387)],
  #[some (0, .right, 42), some (0, .left, 65)],
  #[some (0, .right, 47), some (1, .right, 333)],
  #[some (0, .right, 49), some (1, .right, 335)],
  #[some (0, .right, 69), some (1, .right, 391)],
  #[some (0, .right, 320), some (1, .right, 69)],
  #[some (0, .right, 321), some (1, .right, 69)]
]

abbrev LB01 : ListBlank (Fin 2) := ListBlank.cons 1 default

def zf393 : TM 393 2 :=
  ⟨fun q a => (zf393Rows.getD q.val #[]).getD a.val none⟩

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

end ConjectureMachines.Zf393

end
