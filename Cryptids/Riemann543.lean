/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cryptids.Machines

/-!
# Riemann543

543-state Turing machine halting-equivalent to the 744-state Riemann machine.
-/

namespace ConjectureMachines.Riemann543

open Turing StateTransition

/-- 744 states, 2 symbols,
SHA-256 `4f629ed5be1715747f3d467dbb35bded647a25dc740a80b5208c14f65d7d5f44`. -/
def reference : Machine 744 2 := Machine.ofRows [
  [some (0, .right, 523), some (1, .right, 523)],
  [some (0, .left, 3), some (1, .right, 5)],
  [some (0, .right, 1), some (0, .right, 1)],
  [some (1, .left, 566), some (1, .left, 566)],
  [some (0, .left, 6), some (1, .right, 5)],
  [some (0, .right, 4), some (1, .right, 5)],
  [some (0, .left, 7), some (1, .left, 7)],
  [some (0, .left, 567), some (0, .left, 8)],
  [some (1, .left, 7), some (1, .left, 8)],
  [some (1, .left, 10), some (0, .left, 11)],
  [some (0, .left, 14), some (1, .left, 14)],
  [some (1, .left, 14), some (0, .left, 15)],
  [some (0, .left, 0), some (1, .left, 0)],
  [some (1, .left, 0), some (0, .left, 0)],
  [some (0, .left, 16), some (1, .left, 16)],
  [some (1, .left, 16), some (0, .left, 17)],
  [some (0, .left, 18), some (1, .left, 18)],
  [some (1, .left, 18), some (0, .left, 19)],
  [some (0, .left, 20), some (1, .left, 20)],
  [some (1, .left, 20), some (0, .left, 21)],
  [some (0, .left, 22), some (1, .left, 22)],
  [some (1, .left, 22), some (0, .left, 23)],
  [some (0, .left, 24), some (1, .left, 24)],
  [some (1, .left, 24), some (0, .left, 25)],
  [some (0, .left, 26), some (1, .left, 26)],
  [some (1, .left, 26), some (0, .left, 27)],
  [some (0, .left, 28), some (1, .left, 28)],
  [some (1, .left, 28), some (0, .left, 29)],
  [some (0, .left, 12), some (1, .left, 12)],
  [some (1, .left, 12), some (0, .left, 13)],
  [some (0, .left, 565), some (0, .right, 31)],
  [some (1, .right, 30), some (1, .right, 31)],
  [some (0, .right, 33), some (1, .right, 33)],
  [some (0, .right, 34), some (1, .right, 34)],
  [some (1, .left, 566), some (1, .right, 35)],
  [some (0, .right, 34), some (1, .right, 35)],
  [some (0, .left, 37), some (1, .left, 37)],
  [some (1, .left, 38), some (1, .left, 38)],
  [some (1, .left, 177), some (1, .left, 177)],
  [some (0, .left, 40), some (1, .left, 40)],
  [some (0, .left, 41), some (0, .left, 41)],
  [some (1, .left, 42), some (1, .left, 42)],
  [some (0, .left, 43), some (0, .left, 43)],
  [some (0, .left, 59), some (0, .left, 59)],
  [some (0, .left, 45), some (1, .left, 45)],
  [some (0, .left, 46), some (0, .left, 46)],
  [some (0, .left, 47), some (0, .left, 47)],
  [some (1, .left, 172), some (1, .left, 172)],
  [some (0, .left, 49), some (1, .left, 49)],
  [some (0, .left, 50), some (0, .left, 50)],
  [some (0, .left, 51), some (0, .left, 51)],
  [some (1, .left, 52), some (1, .left, 52)],
  [some (1, .left, 53), some (1, .left, 53)],
  [some (0, .left, 121), some (0, .left, 121)],
  [some (0, .left, 55), some (1, .left, 55)],
  [some (0, .left, 56), some (0, .left, 56)],
  [some (0, .left, 57), some (0, .left, 57)],
  [some (0, .left, 58), some (0, .left, 58)],
  [some (1, .left, 59), some (1, .left, 59)],
  [some (1, .left, 60), some (1, .left, 60)],
  [some (1, .left, 23), some (1, .left, 23)],
  [some (0, .left, 62), some (1, .left, 62)],
  [some (0, .left, 63), some (0, .left, 63)],
  [some (1, .left, 57), some (1, .left, 57)],
  [some (0, .left, 65), some (1, .left, 65)],
  [some (1, .left, 66), some (1, .left, 66)],
  [some (0, .left, 67), some (0, .left, 67)],
  [some (1, .left, 68), some (1, .left, 68)],
  [some (1, .left, 69), some (1, .left, 69)],
  [some (1, .left, 70), some (1, .left, 70)],
  [some (1, .left, 71), some (1, .left, 71)],
  [some (1, .left, 72), some (1, .left, 72)],
  [some (0, .left, 26), some (0, .left, 26)],
  [some (0, .left, 74), some (1, .left, 74)],
  [some (1, .left, 46), some (1, .left, 46)],
  [some (0, .left, 76), some (1, .left, 76)],
  [some (0, .left, 77), some (0, .left, 77)],
  [some (0, .left, 78), some (0, .left, 78)],
  [some (0, .left, 79), some (0, .left, 79)],
  [some (0, .left, 120), some (0, .left, 120)],
  [some (0, .left, 81), some (1, .left, 81)],
  [some (1, .left, 82), some (1, .left, 82)],
  [some (0, .left, 83), some (0, .left, 83)],
  [some (0, .left, 84), some (0, .left, 84)],
  [some (0, .left, 19), some (0, .left, 19)],
  [some (0, .left, 86), some (1, .left, 86)],
  [some (0, .left, 87), some (0, .left, 87)],
  [some (0, .left, 88), some (0, .left, 88)],
  [some (1, .left, 79), some (1, .left, 79)],
  [some (0, .left, 90), some (1, .left, 90)],
  [some (1, .left, 93), some (1, .left, 93)],
  [some (0, .left, 92), some (0, .left, 92)],
  [some (0, .left, 0), some (0, .left, 0)],
  [some (0, .left, 94), some (0, .left, 94)],
  [some (1, .left, 95), some (1, .left, 95)],
  [some (0, .left, 96), some (0, .left, 96)],
  [some (1, .left, 97), some (1, .left, 97)],
  [some (0, .left, 98), some (0, .left, 98)],
  [some (0, .left, 99), some (0, .left, 99)],
  [some (0, .left, 100), some (0, .left, 100)],
  [some (0, .left, 91), some (0, .left, 91)],
  [some (0, .left, 102), some (1, .left, 102)],
  [some (1, .left, 103), some (1, .left, 103)],
  [some (0, .left, 104), some (0, .left, 104)],
  [some (1, .left, 84), some (1, .left, 84)],
  [some (0, .left, 106), some (1, .left, 106)],
  [some (0, .left, 109), some (0, .left, 109)],
  [some (0, .left, 108), some (1, .left, 108)],
  [some (1, .left, 109), some (1, .left, 109)],
  [some (0, .left, 113), some (0, .left, 113)],
  [some (0, .left, 111), some (1, .left, 111)],
  [some (0, .left, 112), some (0, .left, 112)],
  [some (1, .left, 113), some (1, .left, 113)],
  [some (0, .left, 114), some (0, .left, 114)],
  [some (1, .left, 19), some (1, .left, 19)],
  [some (0, .left, 116), some (1, .left, 116)],
  [some (0, .left, 117), some (0, .left, 117)],
  [some (0, .left, 118), some (0, .left, 118)],
  [some (1, .left, 119), some (1, .left, 119)],
  [some (1, .left, 120), some (1, .left, 120)],
  [some (1, .left, 121), some (1, .left, 121)],
  [some (0, .left, 22), some (0, .left, 22)],
  [some (0, .left, 123), some (1, .left, 123)],
  [some (1, .left, 124), some (1, .left, 124)],
  [some (0, .left, 125), some (0, .left, 125)],
  [some (1, .left, 114), some (1, .left, 114)],
  [some (0, .left, 127), some (1, .left, 127)],
  [some (1, .left, 128), some (1, .left, 128)],
  [some (0, .left, 129), some (0, .left, 129)],
  [some (1, .left, 130), some (1, .left, 130)],
  [some (1, .left, 131), some (1, .left, 131)],
  [some (1, .left, 132), some (1, .left, 132)],
  [some (0, .left, 145), some (0, .left, 145)],
  [some (0, .left, 134), some (1, .left, 134)],
  [some (0, .left, 135), some (0, .left, 135)],
  [some (0, .left, 136), some (0, .left, 136)],
  [some (1, .left, 137), some (1, .left, 137)],
  [some (0, .left, 173), some (0, .left, 173)],
  [some (0, .left, 139), some (1, .left, 139)],
  [some (0, .left, 140), some (0, .left, 140)],
  [some (0, .left, 141), some (0, .left, 141)],
  [some (1, .left, 142), some (1, .left, 142)],
  [some (1, .left, 143), some (1, .left, 143)],
  [some (0, .left, 144), some (0, .left, 144)],
  [some (1, .left, 145), some (1, .left, 145)],
  [some (0, .left, 72), some (0, .left, 72)],
  [some (0, .left, 147), some (1, .left, 147)],
  [some (1, .left, 135), some (1, .left, 135)],
  [some (0, .left, 149), some (1, .left, 149)],
  [some (0, .left, 150), some (0, .left, 150)],
  [some (0, .left, 151), some (0, .left, 151)],
  [some (1, .left, 152), some (1, .left, 152)],
  [some (0, .left, 153), some (0, .left, 153)],
  [some (1, .left, 154), some (1, .left, 154)],
  [some (1, .left, 155), some (1, .left, 155)],
  [some (0, .left, 24), some (0, .left, 24)],
  [some (0, .left, 157), some (1, .left, 157)],
  [some (0, .left, 165), some (0, .left, 165)],
  [some (0, .left, 159), some (1, .left, 159)],
  [some (0, .left, 160), some (0, .left, 160)],
  [some (0, .left, 161), some (0, .left, 161)],
  [some (1, .left, 162), some (1, .left, 162)],
  [some (1, .left, 153), some (1, .left, 153)],
  [some (0, .left, 164), some (1, .left, 164)],
  [some (1, .left, 165), some (1, .left, 165)],
  [some (1, .left, 15), some (1, .left, 15)],
  [some (0, .left, 167), some (1, .left, 167)],
  [some (0, .left, 176), some (0, .left, 176)],
  [some (0, .left, 169), some (1, .left, 169)],
  [some (0, .left, 170), some (0, .left, 170)],
  [some (0, .left, 171), some (0, .left, 171)],
  [some (0, .left, 172), some (0, .left, 172)],
  [some (1, .left, 173), some (1, .left, 173)],
  [some (0, .left, 20), some (0, .left, 20)],
  [some (0, .left, 175), some (1, .left, 175)],
  [some (1, .left, 176), some (1, .left, 176)],
  [some (0, .left, 177), some (0, .left, 177)],
  [some (0, .left, 17), some (0, .left, 17)],
  [some (0, .left, 179), some (1, .left, 179)],
  [some (1, .left, 180), some (1, .left, 180)],
  [some (0, .left, 181), some (0, .left, 181)],
  [some (0, .left, 182), some (0, .left, 182)],
  [some (0, .left, 183), some (0, .left, 183)],
  [some (0, .left, 70), some (0, .left, 70)],
  [some (0, .right, 32), some (1, .right, 32)],
  [some (0, .right, 184), some (1, .right, 184)],
  [some (0, .right, 185), some (1, .right, 185)],
  [some (0, .right, 186), some (1, .right, 186)],
  [some (0, .right, 551), some (1, .right, 188)],
  [some (0, .right, 188), some (1, .right, 524)],
  [some (0, .right, 639), some (1, .right, 189)],
  [some (0, .right, 190), some (1, .right, 652)],
  [some (0, .right, 187), some (1, .right, 191)],
  [some (0, .right, 714), some (1, .right, 625)],
  [some (0, .right, 694), some (1, .right, 526)],
  [some (0, .right, 193), some (1, .right, 194)],
  [some (0, .right, 714), some (1, .right, 526)],
  [some (0, .right, 652), some (1, .right, 196)],
  [some (0, .right, 195), some (1, .right, 197)],
  [some (0, .right, 192), some (1, .right, 198)],
  [some (0, .right, 741), some (1, .right, 526)],
  [some (0, .right, 661), some (1, .right, 200)],
  [some (0, .right, 547), some (1, .right, 644)],
  [some (0, .right, 546), some (1, .right, 163)],
  [some (0, .right, 202), some (1, .right, 203)],
  [some (0, .right, 739), some (1, .right, 204)],
  [some (0, .right, 631), some (1, .right, 205)],
  [some (0, .right, 201), some (1, .right, 206)],
  [some (0, .right, 115), some (1, .right, 560)],
  [some (0, .right, 48), some (1, .right, 525)],
  [some (0, .right, 208), some (1, .right, 209)],
  [some (0, .right, 210), some (1, .right, 734)],
  [some (0, .right, 545), some (1, .right, 64)],
  [some (0, .right, 212), some (1, .right, 524)],
  [some (0, .right, 213), some (1, .right, 526)],
  [some (0, .right, 211), some (1, .right, 214)],
  [some (0, .right, 168), some (1, .right, 543)],
  [some (0, .right, 156), some (1, .right, 542)],
  [some (0, .right, 216), some (1, .right, 217)],
  [some (0, .right, 737), some (1, .right, 218)],
  [some (0, .right, 628), some (1, .right, 219)],
  [some (0, .right, 215), some (1, .right, 220)],
  [some (0, .right, 207), some (1, .right, 221)],
  [some (0, .right, 199), some (1, .right, 222)],
  [some (0, .right, 174), some (1, .right, 64)],
  [some (0, .right, 542), some (1, .right, 80)],
  [some (0, .right, 224), some (1, .right, 225)],
  [some (0, .right, 226), some (1, .right, 684)],
  [some (0, .right, 54), some (1, .right, 525)],
  [some (0, .right, 228), some (1, .right, 524)],
  [some (0, .right, 229), some (1, .right, 700)],
  [some (0, .right, 227), some (1, .right, 230)],
  [some (0, .right, 229), some (1, .right, 526)],
  [some (0, .right, 232), some (1, .right, 655)],
  [some (0, .right, 231), some (1, .right, 233)],
  [some (0, .right, 695), some (1, .right, 526)],
  [some (0, .right, 235), some (1, .right, 663)],
  [some (0, .right, 200), some (1, .right, 682)],
  [some (0, .right, 236), some (1, .right, 237)],
  [some (0, .right, 234), some (1, .right, 238)],
  [some (0, .right, 546), some (1, .right, 644)],
  [some (0, .right, 547), some (1, .right, 163)],
  [some (0, .right, 240), some (1, .right, 241)],
  [some (0, .right, 743), some (1, .right, 242)],
  [some (0, .right, 133), some (1, .right, 560)],
  [some (0, .right, 148), some (1, .right, 525)],
  [some (0, .right, 244), some (1, .right, 245)],
  [some (0, .right, 246), some (1, .right, 728)],
  [some (0, .right, 243), some (1, .right, 247)],
  [some (0, .right, 545), some (1, .right, 101)],
  [some (0, .right, 249), some (1, .right, 524)],
  [some (0, .right, 250), some (1, .right, 526)],
  [some (0, .right, 251), some (1, .right, 674)],
  [some (0, .right, 248), some (1, .right, 252)],
  [some (0, .right, 75), some (1, .right, 542)],
  [some (0, .right, 156), some (1, .right, 543)],
  [some (0, .right, 254), some (1, .right, 255)],
  [some (0, .right, 732), some (1, .right, 256)],
  [some (0, .right, 80), some (1, .right, 146)],
  [some (0, .right, 543), some (1, .right, 110)],
  [some (0, .right, 258), some (1, .right, 259)],
  [some (0, .right, 260), some (1, .right, 700)],
  [some (0, .right, 257), some (1, .right, 261)],
  [some (0, .right, 166), some (1, .right, 525)],
  [some (0, .right, 263), some (1, .right, 524)],
  [some (0, .right, 264), some (1, .right, 684)],
  [some (0, .right, 551), some (1, .right, 138)],
  [some (0, .right, 266), some (1, .right, 524)],
  [some (0, .right, 267), some (1, .right, 526)],
  [some (0, .right, 265), some (1, .right, 268)],
  [some (0, .right, 262), some (1, .right, 269)],
  [some (0, .right, 253), some (1, .right, 270)],
  [some (0, .right, 239), some (1, .right, 271)],
  [some (0, .right, 223), some (1, .right, 272)],
  [some (0, .right, 542), some (1, .right, 89)],
  [some (0, .right, 274), some (1, .right, 274)],
  [some (0, .right, 716), some (1, .right, 275)],
  [some (0, .right, 671), some (1, .right, 276)],
  [some (0, .right, 275), some (1, .right, 275)],
  [some (0, .right, 278), some (1, .right, 278)],
  [some (0, .right, 277), some (1, .right, 279)],
  [some (0, .right, 279), some (1, .right, 279)],
  [some (0, .right, 280), some (1, .right, 281)],
  [some (0, .right, 281), some (1, .right, 281)],
  [some (0, .right, 282), some (1, .right, 283)],
  [some (0, .right, 283), some (1, .right, 283)],
  [some (0, .right, 284), some (1, .right, 285)],
  [some (0, .right, 273), some (1, .right, 286)],
  [some (0, .right, 285), some (1, .right, 285)],
  [some (0, .right, 684), some (1, .right, 665)],
  [some (0, .right, 278), some (1, .right, 289)],
  [some (0, .right, 552), some (1, .right, 525)],
  [some (0, .right, 291), some (1, .right, 524)],
  [some (0, .right, 605), some (1, .right, 292)],
  [some (0, .right, 553), some (1, .right, 525)],
  [some (0, .right, 294), some (1, .right, 524)],
  [some (0, .right, 616), some (1, .right, 295)],
  [some (0, .right, 293), some (1, .right, 296)],
  [some (0, .right, 290), some (1, .right, 297)],
  [some (0, .right, 709), some (1, .right, 526)],
  [some (0, .right, 619), some (1, .right, 299)],
  [some (0, .right, 543), some (1, .right, 644)],
  [some (0, .right, 542), some (1, .right, 107)],
  [some (0, .right, 301), some (1, .right, 302)],
  [some (0, .right, 724), some (1, .right, 303)],
  [some (0, .right, 658), some (1, .right, 304)],
  [some (0, .right, 300), some (1, .right, 305)],
  [some (0, .right, 298), some (1, .right, 306)],
  [some (0, .right, 158), some (1, .right, 542)],
  [some (0, .right, 75), some (1, .right, 525)],
  [some (0, .right, 308), some (1, .right, 309)],
  [some (0, .right, 310), some (1, .right, 684)],
  [some (0, .right, 39), some (1, .right, 525)],
  [some (0, .right, 312), some (1, .right, 524)],
  [some (0, .right, 313), some (1, .right, 700)],
  [some (0, .right, 311), some (1, .right, 314)],
  [some (0, .right, 542), some (1, .right, 122)],
  [some (0, .right, 316), some (1, .right, 524)],
  [some (0, .right, 726), some (1, .right, 317)],
  [some (0, .right, 669), some (1, .right, 318)],
  [some (0, .right, 315), some (1, .right, 319)],
  [some (0, .right, 115), some (1, .right, 525)],
  [some (0, .right, 321), some (1, .right, 524)],
  [some (0, .right, 722), some (1, .right, 322)],
  [some (0, .right, 621), some (1, .right, 323)],
  [some (0, .right, 690), some (1, .right, 665)],
  [some (0, .right, 610), some (1, .right, 325)],
  [some (0, .right, 324), some (1, .right, 326)],
  [some (0, .right, 320), some (1, .right, 327)],
  [some (0, .right, 307), some (1, .right, 328)],
  [some (0, .right, 715), some (1, .right, 526)],
  [some (0, .right, 330), some (1, .right, 607)],
  [some (0, .right, 542), some (1, .right, 101)],
  [some (0, .right, 332), some (1, .right, 524)],
  [some (0, .right, 721), some (1, .right, 333)],
  [some (0, .right, 334), some (1, .right, 621)],
  [some (0, .right, 331), some (1, .right, 335)],
  [some (0, .right, 85), some (1, .right, 525)],
  [some (0, .right, 337), some (1, .right, 524)],
  [some (0, .right, 722), some (1, .right, 338)],
  [some (0, .right, 605), some (1, .right, 707)],
  [some (0, .right, 339), some (1, .right, 340)],
  [some (0, .right, 553), some (1, .right, 126)],
  [some (0, .right, 342), some (1, .right, 524)],
  [some (0, .right, 343), some (1, .right, 526)],
  [some (0, .right, 344), some (1, .right, 669)],
  [some (0, .right, 341), some (1, .right, 345)],
  [some (0, .right, 336), some (1, .right, 346)],
  [some (0, .right, 726), some (1, .right, 526)],
  [some (0, .right, 348), some (1, .right, 614)],
  [some (0, .right, 546), some (1, .right, 101)],
  [some (0, .right, 350), some (1, .right, 524)],
  [some (0, .right, 735), some (1, .right, 351)],
  [some (0, .right, 352), some (1, .right, 679)],
  [some (0, .right, 349), some (1, .right, 353)],
  [some (0, .right, 738), some (1, .right, 338)],
  [some (0, .right, 545), some (1, .right, 644)],
  [some (0, .right, 543), some (1, .right, 525)],
  [some (0, .right, 356), some (1, .right, 357)],
  [some (0, .right, 698), some (1, .right, 358)],
  [some (0, .right, 355), some (1, .right, 359)],
  [some (0, .right, 44), some (1, .right, 525)],
  [some (0, .right, 361), some (1, .right, 524)],
  [some (0, .right, 362), some (1, .right, 570)],
  [some (0, .right, 702), some (1, .right, 526)],
  [some (0, .right, 363), some (1, .right, 364)],
  [some (0, .right, 360), some (1, .right, 365)],
  [some (0, .right, 354), some (1, .right, 366)],
  [some (0, .right, 347), some (1, .right, 367)],
  [some (0, .right, 329), some (1, .right, 368)],
  [some (0, .right, 288), some (1, .right, 369)],
  [some (0, .right, 287), some (1, .right, 370)],
  [some (0, .right, 545), some (1, .right, 126)],
  [some (0, .right, 372), some (1, .right, 524)],
  [some (0, .right, 685), some (1, .right, 373)],
  [some (0, .right, 576), some (1, .right, 374)],
  [some (0, .right, 209), some (1, .right, 524)],
  [some (0, .right, 685), some (1, .right, 376)],
  [some (0, .right, 572), some (1, .right, 377)],
  [some (0, .right, 375), some (1, .right, 378)],
  [some (0, .right, 570), some (1, .right, 702)],
  [some (0, .right, 380), some (1, .right, 612)],
  [some (0, .right, 690), some (1, .right, 250)],
  [some (0, .right, 382), some (1, .right, 610)],
  [some (0, .right, 381), some (1, .right, 383)],
  [some (0, .right, 379), some (1, .right, 384)],
  [some (0, .right, 245), some (1, .right, 524)],
  [some (0, .right, 690), some (1, .right, 386)],
  [some (0, .right, 578), some (1, .right, 704)],
  [some (0, .right, 387), some (1, .right, 388)],
  [some (0, .right, 583), some (1, .right, 595)],
  [some (0, .right, 557), some (1, .right, 525)],
  [some (0, .right, 391), some (1, .right, 524)],
  [some (0, .right, 392), some (1, .right, 616)],
  [some (0, .right, 390), some (1, .right, 393)],
  [some (0, .right, 389), some (1, .right, 394)],
  [some (0, .right, 295), some (1, .right, 526)],
  [some (0, .right, 396), some (1, .right, 621)],
  [some (0, .right, 722), some (1, .right, 526)],
  [some (0, .right, 398), some (1, .right, 676)],
  [some (0, .right, 397), some (1, .right, 399)],
  [some (0, .right, 395), some (1, .right, 400)],
  [some (0, .right, 385), some (1, .right, 401)],
  [some (0, .right, 543), some (1, .right, 80)],
  [some (0, .right, 356), some (1, .right, 403)],
  [some (0, .right, 696), some (1, .right, 404)],
  [some (0, .right, 133), some (1, .right, 543)],
  [some (0, .right, 105), some (1, .right, 525)],
  [some (0, .right, 406), some (1, .right, 407)],
  [some (0, .right, 408), some (1, .right, 700)],
  [some (0, .right, 405), some (1, .right, 409)],
  [some (0, .right, 61), some (1, .right, 525)],
  [some (0, .right, 411), some (1, .right, 524)],
  [some (0, .right, 412), some (1, .right, 718)],
  [some (0, .right, 413), some (1, .right, 588)],
  [some (0, .right, 410), some (1, .right, 414)],
  [some (0, .right, 543), some (1, .right, 101)],
  [some (0, .right, 416), some (1, .right, 524)],
  [some (0, .right, 687), some (1, .right, 417)],
  [some (0, .right, 418), some (1, .right, 623)],
  [some (0, .right, 133), some (1, .right, 525)],
  [some (0, .right, 420), some (1, .right, 524)],
  [some (0, .right, 691), some (1, .right, 421)],
  [some (0, .right, 422), some (1, .right, 603)],
  [some (0, .right, 419), some (1, .right, 423)],
  [some (0, .right, 415), some (1, .right, 424)],
  [some (0, .right, 706), some (1, .right, 583)],
  [some (0, .right, 719), some (1, .right, 526)],
  [some (0, .right, 426), some (1, .right, 427)],
  [some (0, .right, 543), some (1, .right, 122)],
  [some (0, .right, 429), some (1, .right, 524)],
  [some (0, .right, 688), some (1, .right, 430)],
  [some (0, .right, 597), some (1, .right, 431)],
  [some (0, .right, 428), some (1, .right, 432)],
  [some (0, .right, 691), some (1, .right, 322)],
  [some (0, .right, 623), some (1, .right, 434)],
  [some (0, .right, 595), some (1, .right, 720)],
  [some (0, .right, 553), some (1, .right, 178)],
  [some (0, .right, 437), some (1, .right, 524)],
  [some (0, .right, 438), some (1, .right, 526)],
  [some (0, .right, 436), some (1, .right, 439)],
  [some (0, .right, 435), some (1, .right, 440)],
  [some (0, .right, 433), some (1, .right, 441)],
  [some (0, .right, 425), some (1, .right, 442)],
  [some (0, .right, 402), some (1, .right, 443)],
  [some (0, .right, 543), some (1, .right, 126)],
  [some (0, .right, 445), some (1, .right, 524)],
  [some (0, .right, 687), some (1, .right, 446)],
  [some (0, .right, 588), some (1, .right, 447)],
  [some (0, .right, 687), some (1, .right, 376)],
  [some (0, .right, 593), some (1, .right, 449)],
  [some (0, .right, 448), some (1, .right, 450)],
  [some (0, .right, 583), some (1, .right, 719)],
  [some (0, .right, 452), some (1, .right, 585)],
  [some (0, .right, 730), some (1, .right, 333)],
  [some (0, .right, 454), some (1, .right, 591)],
  [some (0, .right, 453), some (1, .right, 455)],
  [some (0, .right, 451), some (1, .right, 456)],
  [some (0, .right, 148), some (1, .right, 543)],
  [some (0, .right, 101), some (1, .right, 525)],
  [some (0, .right, 458), some (1, .right, 459)],
  [some (0, .right, 730), some (1, .right, 460)],
  [some (0, .right, 461), some (1, .right, 676)],
  [some (0, .right, 146), some (1, .right, 525)],
  [some (0, .right, 463), some (1, .right, 524)],
  [some (0, .right, 696), some (1, .right, 464)],
  [some (0, .right, 465), some (1, .right, 452)],
  [some (0, .right, 462), some (1, .right, 466)],
  [some (0, .right, 543), some (1, .right, 64)],
  [some (0, .right, 468), some (1, .right, 524)],
  [some (0, .right, 688), some (1, .right, 469)],
  [some (0, .right, 597), some (1, .right, 470)],
  [some (0, .right, 688), some (1, .right, 362)],
  [some (0, .right, 599), some (1, .right, 472)],
  [some (0, .right, 471), some (1, .right, 473)],
  [some (0, .right, 467), some (1, .right, 474)],
  [some (0, .right, 457), some (1, .right, 475)],
  [some (0, .right, 436), some (1, .right, 597)],
  [some (0, .right, 688), some (1, .right, 417)],
  [some (0, .right, 478), some (1, .right, 599)],
  [some (0, .right, 477), some (1, .right, 479)],
  [some (0, .right, 688), some (1, .right, 338)],
  [some (0, .right, 481), some (1, .right, 436)],
  [some (0, .right, 685), some (1, .right, 430)],
  [some (0, .right, 572), some (1, .right, 483)],
  [some (0, .right, 482), some (1, .right, 484)],
  [some (0, .right, 480), some (1, .right, 485)],
  [some (0, .right, 158), some (1, .right, 525)],
  [some (0, .right, 487), some (1, .right, 524)],
  [some (0, .right, 688), some (1, .right, 488)],
  [some (0, .right, 599), some (1, .right, 489)],
  [some (0, .right, 729), some (1, .right, 317)],
  [some (0, .right, 581), some (1, .right, 491)],
  [some (0, .right, 490), some (1, .right, 492)],
  [some (0, .right, 115), some (1, .right, 543)],
  [some (0, .right, 156), some (1, .right, 545)],
  [some (0, .right, 494), some (1, .right, 495)],
  [some (0, .right, 730), some (1, .right, 496)],
  [some (0, .right, 591), some (1, .right, 497)],
  [some (0, .right, 174), some (1, .right, 73)],
  [some (0, .right, 545), some (1, .right, 89)],
  [some (0, .right, 499), some (1, .right, 500)],
  [some (0, .right, 501), some (1, .right, 718)],
  [some (0, .right, 36), some (1, .right, 525)],
  [some (0, .right, 503), some (1, .right, 524)],
  [some (0, .right, 504), some (1, .right, 700)],
  [some (0, .right, 502), some (1, .right, 505)],
  [some (0, .right, 498), some (1, .right, 506)],
  [some (0, .right, 493), some (1, .right, 507)],
  [some (0, .right, 486), some (1, .right, 508)],
  [some (0, .right, 476), some (1, .right, 509)],
  [some (0, .right, 444), some (1, .right, 510)],
  [some (0, .right, 89), some (1, .right, 635)],
  [some (0, .right, 89), none],
  [some (0, .right, 512), some (1, .right, 513)],
  [some (0, .right, 514), some (1, .right, 526)],
  [some (0, .right, 515), some (1, .right, 527)],
  [some (0, .right, 516), some (1, .right, 528)],
  [some (0, .right, 517), some (1, .right, 529)],
  [some (0, .right, 518), some (1, .right, 530)],
  [some (0, .right, 519), some (1, .right, 531)],
  [some (0, .right, 520), some (1, .right, 532)],
  [some (0, .right, 511), some (1, .right, 521)],
  [some (0, .right, 371), some (1, .right, 522)],
  [some (0, .left, 11), some (1, .left, 11)],
  [some (0, .left, 9), some (1, .left, 9)],
  [some (0, .left, 15), some (1, .left, 15)],
  [some (0, .left, 17), some (1, .left, 17)],
  [some (0, .left, 19), some (1, .left, 19)],
  [some (0, .left, 21), some (1, .left, 21)],
  [some (0, .left, 23), some (1, .left, 23)],
  [some (0, .left, 25), some (1, .left, 25)],
  [some (0, .left, 27), some (1, .left, 27)],
  [some (0, .right, 2), some (1, .right, 533)],
  [some (0, .right, 533), some (1, .right, 534)],
  [some (0, .right, 534), some (1, .right, 535)],
  [some (0, .right, 549), some (1, .right, 536)],
  [some (0, .right, 536), some (1, .right, 537)],
  [some (0, .right, 537), some (1, .right, 538)],
  [some (0, .right, 538), some (1, .right, 539)],
  [some (0, .right, 539), some (1, .right, 540)],
  [some (0, .right, 540), some (1, .right, 541)],
  [some (0, .right, 535), some (1, .right, 542)],
  [some (0, .right, 542), some (1, .right, 543)],
  [some (0, .right, 543), some (1, .right, 544)],
  [some (0, .right, 544), some (1, .right, 545)],
  [some (0, .right, 545), some (1, .right, 546)],
  [some (0, .right, 546), some (1, .right, 547)],
  [some (0, .right, 547), some (1, .right, 548)],
  [some (0, .right, 548), some (1, .right, 549)],
  [some (0, .right, 31), some (1, .right, 550)],
  [some (0, .right, 550), some (1, .right, 551)],
  [some (0, .right, 564), some (1, .right, 552)],
  [some (0, .right, 552), some (1, .right, 553)],
  [some (0, .right, 553), some (1, .right, 554)],
  [some (0, .right, 554), some (1, .right, 555)],
  [some (0, .right, 555), some (1, .right, 556)],
  [some (0, .right, 556), some (1, .right, 557)],
  [some (0, .right, 188), some (1, .right, 558)],
  [some (0, .right, 648), some (1, .right, 559)],
  [some (0, .right, 559), some (1, .right, 560)],
  [some (0, .right, 560), some (1, .right, 561)],
  [some (0, .right, 561), some (1, .right, 562)],
  [some (0, .right, 562), some (1, .right, 563)],
  [some (0, .right, 563), some (1, .right, 564)],
  [some (0, .left, 9), some (1, .left, 566)],
  [some (0, .left, 565), some (1, .left, 566)],
  [some (0, .left, 524), some (1, .left, 568)],
  [some (0, .left, 567), some (1, .left, 568)],
  [some (0, .right, 538), some (1, .right, 635)],
  [some (0, .right, 569), some (1, .right, 638)],
  [some (0, .right, 573), some (1, .right, 653)],
  [some (0, .right, 571), some (1, .right, 651)],
  [some (0, .right, 538), some (1, .right, 644)],
  [some (0, .right, 560), some (1, .right, 558)],
  [some (0, .right, 573), some (1, .right, 574)],
  [some (0, .right, 575), some (1, .right, 651)],
  [some (0, .right, 539), some (1, .right, 635)],
  [some (0, .right, 577), some (1, .right, 638)],
  [some (0, .right, 539), some (1, .right, 644)],
  [some (0, .right, 579), some (1, .right, 672)],
  [some (0, .right, 580), some (1, .right, 651)],
  [some (0, .right, 540), some (1, .right, 635)],
  [some (0, .right, 582), some (1, .right, 638)],
  [some (0, .right, 586), some (1, .right, 672)],
  [some (0, .right, 584), some (1, .right, 651)],
  [some (0, .right, 540), some (1, .right, 644)],
  [some (0, .right, 586), some (1, .right, 653)],
  [some (0, .right, 587), some (1, .right, 651)],
  [some (0, .right, 648), some (1, .right, 561)],
  [some (0, .right, 586), some (1, .right, 589)],
  [some (0, .right, 590), some (1, .right, 651)],
  [some (0, .right, 586), some (1, .right, 574)],
  [some (0, .right, 592), some (1, .right, 651)],
  [some (0, .right, 541), some (1, .right, 635)],
  [some (0, .right, 594), some (1, .right, 638)],
  [some (0, .right, 600), some (1, .right, 653)],
  [some (0, .right, 596), some (1, .right, 651)],
  [some (0, .right, 600), some (1, .right, 574)],
  [some (0, .right, 598), some (1, .right, 651)],
  [some (0, .right, 541), some (1, .right, 644)],
  [some (0, .right, 560), some (1, .right, 648)],
  [some (0, .right, 600), some (1, .right, 601)],
  [some (0, .right, 602), some (1, .right, 651)],
  [some (0, .right, 536), some (1, .right, 635)],
  [some (0, .right, 604), some (1, .right, 638)],
  [some (0, .right, 608), some (1, .right, 667)],
  [some (0, .right, 606), some (1, .right, 651)],
  [some (0, .right, 536), some (1, .right, 644)],
  [some (0, .right, 608), some (1, .right, 653)],
  [some (0, .right, 609), some (1, .right, 651)],
  [some (0, .right, 608), some (1, .right, 574)],
  [some (0, .right, 611), some (1, .right, 651)],
  [some (0, .right, 608), some (1, .right, 562)],
  [some (0, .right, 613), some (1, .right, 651)],
  [some (0, .right, 537), some (1, .right, 635)],
  [some (0, .right, 615), some (1, .right, 638)],
  [some (0, .right, 537), some (1, .right, 644)],
  [some (0, .right, 617), some (1, .right, 648)],
  [some (0, .right, 618), some (1, .right, 651)],
  [some (0, .right, 617), some (1, .right, 656)],
  [some (0, .right, 620), some (1, .right, 651)],
  [some (0, .right, 617), some (1, .right, 574)],
  [some (0, .right, 622), some (1, .right, 651)],
  [some (0, .right, 544), some (1, .right, 635)],
  [some (0, .right, 624), some (1, .right, 638)],
  [some (0, .right, 648), some (1, .right, 562)],
  [some (0, .right, 629), some (1, .right, 626)],
  [some (0, .right, 627), some (1, .right, 651)],
  [some (0, .right, 544), some (1, .right, 644)],
  [some (0, .right, 629), some (1, .right, 563)],
  [some (0, .right, 630), some (1, .right, 651)],
  [some (0, .left, 633), some (1, .left, 633)],
  [some (0, .left, 634), some (0, .left, 634)],
  [some (0, .left, 14), some (0, .left, 14)],
  [some (0, .left, 636), some (1, .left, 636)],
  [some (1, .left, 11), some (1, .left, 11)],
  [some (0, .right, 534), some (1, .right, 635)],
  [some (0, .right, 632), some (1, .right, 525)],
  [some (0, .right, 637), some (1, .right, 638)],
  [some (0, .left, 641), some (1, .left, 641)],
  [some (0, .left, 642), some (0, .left, 642)],
  [some (0, .left, 643), some (0, .left, 643)],
  [some (0, .left, 16), some (0, .left, 16)],
  [some (0, .left, 645), some (1, .left, 645)],
  [some (1, .left, 646), some (1, .left, 646)],
  [some (0, .left, 15), some (0, .left, 15)],
  [some (0, .right, 534), some (1, .right, 644)],
  [some (0, .right, 558), some (1, .right, 648)],
  [some (0, .right, 647), some (1, .right, 648)],
  [some (0, .right, 640), some (1, .right, 525)],
  [some (0, .right, 650), some (1, .right, 524)],
  [some (0, .right, 649), some (1, .right, 651)],
  [some (0, .right, 648), some (1, .right, 558)],
  [some (0, .right, 647), some (1, .right, 653)],
  [some (0, .right, 654), some (1, .right, 651)],
  [some (0, .right, 648), some (1, .right, 560)],
  [some (0, .right, 647), some (1, .right, 656)],
  [some (0, .right, 657), some (1, .right, 651)],
  [some (0, .right, 561), some (1, .right, 563)],
  [some (0, .right, 647), some (1, .right, 659)],
  [some (0, .right, 660), some (1, .right, 651)],
  [some (0, .right, 647), some (1, .right, 563)],
  [some (0, .right, 662), some (1, .right, 651)],
  [some (0, .right, 549), some (1, .right, 635)],
  [some (0, .right, 664), some (1, .right, 638)],
  [some (0, .right, 549), some (1, .right, 644)],
  [some (0, .right, 558), some (1, .right, 560)],
  [some (0, .right, 666), some (1, .right, 667)],
  [some (0, .right, 668), some (1, .right, 651)],
  [some (0, .right, 680), some (1, .right, 648)],
  [some (0, .right, 670), some (1, .right, 651)],
  [some (0, .right, 558), some (1, .right, 561)],
  [some (0, .right, 680), some (1, .right, 672)],
  [some (0, .right, 673), some (1, .right, 651)],
  [some (0, .right, 680), some (1, .right, 574)],
  [some (0, .right, 675), some (1, .right, 651)],
  [some (0, .right, 560), some (1, .right, 562)],
  [some (0, .right, 680), some (1, .right, 677)],
  [some (0, .right, 678), some (1, .right, 651)],
  [some (0, .right, 535), some (1, .right, 644)],
  [some (0, .right, 680), some (1, .right, 659)],
  [some (0, .right, 681), some (1, .right, 651)],
  [some (0, .right, 542), some (1, .right, 635)],
  [some (0, .right, 683), some (1, .right, 638)],
  [some (0, .right, 692), some (1, .right, 701)],
  [some (0, .right, 556), some (1, .right, 632)],
  [some (0, .right, 692), some (1, .right, 686)],
  [some (0, .right, 692), some (1, .right, 705)],
  [some (0, .right, 552), some (1, .right, 632)],
  [some (0, .right, 692), some (1, .right, 689)],
  [some (0, .right, 692), some (1, .right, 708)],
  [some (0, .right, 542), some (1, .right, 710)],
  [some (0, .right, 559), some (1, .right, 632)],
  [some (0, .right, 692), some (1, .right, 693)],
  [some (0, .right, 692), some (1, .right, 713)],
  [some (0, .right, 692), some (1, .right, 742)],
  [some (0, .right, 648), some (1, .right, 632)],
  [some (0, .right, 692), some (1, .right, 697)],
  [some (0, .right, 543), some (1, .right, 635)],
  [some (0, .right, 699), some (1, .right, 638)],
  [some (0, .right, 554), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 701)],
  [some (0, .right, 555), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 703)],
  [some (0, .right, 557), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 705)],
  [some (0, .right, 712), some (1, .right, 689)],
  [some (0, .right, 553), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 708)],
  [some (0, .left, 711), some (1, .left, 711)],
  [some (0, .left, 646), some (0, .left, 646)],
  [some (0, .right, 543), some (1, .right, 710)],
  [some (0, .right, 551), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 713)],
  [some (0, .right, 712), some (1, .right, 725)],
  [some (0, .right, 712), some (1, .right, 742)],
  [some (0, .right, 545), some (1, .right, 635)],
  [some (0, .right, 717), some (1, .right, 638)],
  [some (0, .right, 723), some (1, .right, 686)],
  [some (0, .right, 723), some (1, .right, 705)],
  [some (0, .right, 723), some (1, .right, 689)],
  [some (0, .right, 723), some (1, .right, 708)],
  [some (0, .right, 545), some (1, .right, 710)],
  [some (0, .right, 723), some (1, .right, 713)],
  [some (0, .right, 564), some (1, .right, 632)],
  [some (0, .right, 723), some (1, .right, 725)],
  [some (0, .right, 546), some (1, .right, 635)],
  [some (0, .right, 727), some (1, .right, 638)],
  [some (0, .right, 731), some (1, .right, 703)],
  [some (0, .right, 731), some (1, .right, 686)],
  [some (0, .right, 546), some (1, .right, 710)],
  [some (0, .right, 731), some (1, .right, 742)],
  [some (0, .right, 547), some (1, .right, 635)],
  [some (0, .right, 733), some (1, .right, 638)],
  [some (0, .right, 736), some (1, .right, 689)],
  [some (0, .right, 547), some (1, .right, 710)],
  [some (0, .right, 736), some (1, .right, 693)],
  [some (0, .right, 736), some (1, .right, 742)],
  [some (0, .right, 740), some (1, .right, 693)],
  [some (0, .right, 548), some (1, .right, 710)],
  [some (0, .right, 740), some (1, .right, 713)],
  [some (0, .right, 188), some (1, .right, 632)],
  [some (0, .right, 740), some (1, .right, 742)]]

/-- 543 states, 2 symbols,
SHA-256 `14c7d827a8ef5ff7671f4642fe31d956c4880a0ce8270c74286b453313f4824e`. -/
def candidate : Machine 543 2 := Machine.ofRows [
  [some (0, .right, 235), some (1, .right, 353)],
  [some (0, .left, 31), some (1, .right, 4)],
  [some (0, .right, 1), some (0, .right, 1)],
  [some (0, .left, 5), some (1, .right, 4)],
  [some (0, .right, 3), some (1, .right, 4)],
  [some (0, .left, 6), some (0, .left, 20)],
  [some (0, .left, 385), some (0, .left, 7)],
  [some (1, .left, 6), some (1, .left, 7)],
  [some (1, .left, 9), some (0, .left, 10)],
  [some (0, .left, 12), some (1, .left, 12)],
  [some (1, .left, 12), some (0, .left, 13)],
  [some (1, .right, 353), some (0, .right, 235)],
  [some (0, .left, 14), some (1, .left, 14)],
  [some (1, .left, 14), some (0, .left, 15)],
  [some (0, .left, 16), some (1, .left, 16)],
  [some (1, .left, 16), some (0, .left, 17)],
  [some (0, .left, 18), some (1, .left, 18)],
  [some (1, .left, 18), some (0, .left, 19)],
  [some (0, .left, 20), some (1, .left, 20)],
  [some (1, .left, 20), some (0, .left, 21)],
  [some (0, .left, 22), some (1, .left, 22)],
  [some (1, .left, 22), some (0, .left, 23)],
  [some (0, .left, 24), some (1, .left, 24)],
  [some (1, .left, 24), some (0, .left, 25)],
  [some (0, .left, 26), some (1, .left, 26)],
  [some (1, .left, 26), some (0, .left, 27)],
  [some (0, .left, 0), some (1, .left, 0)],
  [some (1, .left, 0), some (0, .left, 11)],
  [some (0, .left, 383), some (0, .right, 29)],
  [some (1, .right, 28), some (1, .right, 29)],
  [some (0, .right, 32), some (0, .left, 63)],
  [some (1, .left, 384), some (1, .right, 32)],
  [some (0, .right, 31), some (1, .right, 32)],
  [some (0, .left, 34), some (0, .left, 24)],
  [some (1, .left, 38), some (0, .left, 38)],
  [some (0, .left, 36), some (0, .left, 61)],
  [some (0, .left, 37), some (0, .left, 14)],
  [some (1, .left, 38), some (1, .left, 38)],
  [some (1, .left, 39), some (1, .left, 39)],
  [some (1, .left, 21), none],
  [some (1, .left, 33), some (0, .left, 64)],
  [some (0, .left, 42), some (0, .left, 61)],
  [some (1, .left, 43), some (1, .left, 43)],
  [some (0, .left, 17), some (1, .left, 17)],
  [some (0, .left, 96), some (1, .left, 33)],
  [some (0, .left, 66), some (1, .left, 66)],
  [some (0, .left, 15), some (1, .left, 45)],
  [some (0, .left, 46), some (0, .left, 42)],
  [some (0, .left, 49), some (0, .left, 49)],
  [some (0, .right, 235), some (0, .right, 235)],
  [some (0, .left, 51), some (0, .left, 51)],
  [some (1, .left, 52), some (1, .left, 52)],
  [some (0, .left, 53), some (0, .left, 53)],
  [some (1, .left, 54), some (1, .left, 54)],
  [some (0, .left, 55), some (0, .left, 55)],
  [some (0, .left, 56), some (0, .left, 56)],
  [some (0, .left, 57), some (0, .left, 57)],
  [some (0, .left, 48), some (0, .left, 48)],
  [some (0, .left, 59), some (0, .left, 12)],
  [some (1, .left, 59), some (1, .left, 30)],
  [some (0, .left, 13), some (1, .left, 61)],
  [some (0, .left, 43), some (0, .left, 43)],
  [some (1, .left, 66), some (0, .left, 16)],
  [some (0, .left, 33), some (1, .left, 55)],
  [some (1, .left, 65), some (0, .left, 287)],
  [some (1, .left, 3), some (0, .left, 66)],
  [some (1, .left, 67), some (0, .left, 18)],
  [some (1, .left, 68), some (0, .left, 20)],
  [some (1, .left, 33), some (0, .left, 22)],
  [some (0, .left, 70), some (1, .left, 13)],
  [some (1, .left, 62), some (0, .left, 45)],
  [some (0, .right, 30), some (1, .right, 30)],
  [some (0, .right, 71), some (1, .right, 71)],
  [some (0, .right, 72), some (1, .right, 72)],
  [some (0, .right, 73), some (1, .right, 73)],
  [some (0, .right, 371), some (1, .right, 75)],
  [some (0, .right, 75), some (0, .left, 13)],
  [some (0, .right, 453), some (1, .right, 76)],
  [some (0, .right, 77), some (1, .right, 458)],
  [some (0, .right, 74), some (1, .right, 78)],
  [some (0, .right, 513), some (1, .right, 443)],
  [some (0, .right, 499), some (0, .left, 15)],
  [some (0, .right, 80), some (1, .right, 81)],
  [some (0, .right, 513), some (0, .left, 15)],
  [some (0, .right, 458), some (1, .right, 83)],
  [some (0, .right, 82), some (1, .right, 84)],
  [some (0, .right, 79), some (1, .right, 85)],
  [some (0, .right, 540), some (0, .left, 15)],
  [some (0, .right, 467), some (1, .right, 87)],
  [some (0, .right, 367), some (1, .left, 454)],
  [some (0, .right, 366), some (1, .left, 454)],
  [some (0, .right, 89), some (1, .right, 90)],
  [some (0, .right, 538), some (1, .right, 91)],
  [some (0, .right, 449), some (1, .right, 92)],
  [some (0, .right, 88), some (1, .right, 93)],
  [some (0, .left, 69), some (1, .right, 378)],
  [some (0, .left, 40), some (0, .left, 10)],
  [some (0, .right, 95), some (1, .right, 96)],
  [some (0, .right, 97), some (1, .right, 533)],
  [some (0, .right, 365), some (1, .left, 41)],
  [some (0, .right, 99), some (0, .left, 13)],
  [some (0, .right, 100), some (0, .left, 15)],
  [some (0, .right, 98), some (1, .right, 101)],
  [some (0, .left, 69), some (1, .right, 363)],
  [some (0, .left, 69), some (1, .right, 362)],
  [some (0, .right, 103), some (1, .right, 104)],
  [some (0, .right, 536), some (1, .right, 105)],
  [some (0, .right, 446), some (1, .right, 106)],
  [some (0, .right, 102), some (1, .right, 107)],
  [some (0, .right, 94), some (1, .right, 108)],
  [some (0, .right, 86), some (1, .right, 109)],
  [some (1, .left, 47), some (1, .left, 69)],
  [some (0, .right, 362), some (1, .left, 41)],
  [some (0, .right, 111), some (1, .right, 112)],
  [some (0, .right, 113), some (1, .right, 490)],
  [some (0, .left, 35), some (0, .left, 10)],
  [some (0, .right, 115), some (0, .left, 13)],
  [some (0, .right, 116), some (1, .right, 505)],
  [some (0, .right, 114), some (1, .right, 117)],
  [some (0, .right, 116), some (0, .left, 15)],
  [some (0, .right, 119), some (1, .right, 461)],
  [some (0, .right, 118), some (1, .right, 120)],
  [some (0, .right, 500), some (0, .left, 15)],
  [some (0, .right, 122), some (1, .right, 469)],
  [some (0, .right, 87), some (1, .right, 488)],
  [some (0, .right, 123), some (1, .right, 124)],
  [some (0, .right, 121), some (1, .right, 125)],
  [some (0, .right, 90), some (1, .right, 89)],
  [some (0, .right, 542), some (1, .right, 127)],
  [some (0, .right, 97), some (1, .right, 527)],
  [some (0, .right, 128), some (1, .right, 129)],
  [some (0, .right, 101), some (1, .right, 480)],
  [some (0, .right, 130), some (1, .right, 131)],
  [some (0, .right, 104), some (1, .right, 103)],
  [some (0, .right, 531), some (1, .right, 133)],
  [some (0, .right, 363), some (0, .left, 60)],
  [some (0, .right, 111), some (1, .right, 135)],
  [some (0, .right, 136), some (1, .right, 505)],
  [some (0, .right, 134), some (1, .right, 137)],
  [some (0, .left, 47), some (0, .left, 10)],
  [some (0, .right, 139), some (0, .left, 13)],
  [some (0, .right, 140), some (1, .right, 490)],
  [some (0, .right, 371), some (0, .left, 58)],
  [some (0, .right, 142), some (0, .left, 13)],
  [some (0, .right, 143), some (0, .left, 15)],
  [some (0, .right, 141), some (1, .right, 144)],
  [some (0, .right, 138), some (1, .right, 145)],
  [some (0, .right, 132), some (1, .right, 146)],
  [some (0, .right, 126), some (1, .right, 147)],
  [some (0, .right, 110), some (1, .right, 148)],
  [some (0, .right, 362), some (1, .left, 50)],
  [some (0, .right, 150), some (1, .right, 150)],
  [some (0, .right, 515), some (1, .right, 151)],
  [some (0, .right, 477), some (1, .right, 152)],
  [some (0, .right, 151), some (1, .right, 151)],
  [some (0, .right, 154), some (1, .right, 154)],
  [some (0, .right, 153), some (1, .right, 155)],
  [some (0, .right, 155), some (1, .right, 155)],
  [some (0, .right, 156), some (1, .right, 157)],
  [some (0, .right, 157), some (1, .right, 157)],
  [some (0, .right, 158), some (1, .right, 159)],
  [some (0, .right, 159), some (1, .right, 159)],
  [some (0, .right, 160), some (1, .right, 161)],
  [some (0, .right, 149), some (1, .right, 162)],
  [some (0, .right, 161), some (1, .right, 161)],
  [some (0, .right, 490), some (1, .right, 471)],
  [some (0, .right, 154), some (1, .right, 165)],
  [some (0, .right, 372), some (0, .left, 450)],
  [some (0, .right, 167), some (0, .left, 13)],
  [some (0, .right, 423), some (1, .right, 168)],
  [some (0, .right, 373), some (0, .left, 450)],
  [some (0, .right, 170), some (0, .left, 13)],
  [some (0, .right, 434), some (1, .right, 171)],
  [some (0, .right, 169), some (1, .right, 172)],
  [some (0, .right, 166), some (1, .right, 173)],
  [some (0, .right, 512), some (0, .left, 15)],
  [some (0, .right, 437), some (1, .right, 175)],
  [some (0, .right, 363), some (1, .left, 454)],
  [some (0, .right, 177), some (1, .right, 112)],
  [some (0, .right, 523), some (1, .right, 178)],
  [some (0, .right, 464), some (1, .right, 179)],
  [some (0, .right, 176), some (1, .right, 180)],
  [some (0, .right, 174), some (1, .right, 181)],
  [some (0, .right, 104), some (1, .right, 115)],
  [some (0, .right, 183), some (1, .right, 490)],
  [some (0, .right, 96), some (0, .left, 13)],
  [some (0, .right, 185), some (1, .right, 505)],
  [some (0, .right, 184), some (1, .right, 186)],
  [some (0, .right, 112), some (0, .left, 13)],
  [some (0, .right, 525), some (1, .right, 188)],
  [some (0, .right, 475), some (1, .right, 189)],
  [some (0, .right, 187), some (1, .right, 190)],
  [some (0, .right, 521), some (1, .right, 140)],
  [some (0, .right, 439), some (1, .right, 192)],
  [some (0, .right, 495), some (1, .right, 471)],
  [some (0, .right, 428), some (1, .right, 194)],
  [some (0, .right, 193), some (1, .right, 195)],
  [some (0, .right, 191), some (1, .right, 196)],
  [some (0, .right, 182), some (1, .right, 197)],
  [some (0, .right, 514), some (0, .left, 15)],
  [some (0, .right, 199), some (1, .right, 425)],
  [some (0, .right, 520), some (1, .right, 188)],
  [some (0, .right, 201), some (1, .right, 439)],
  [some (0, .right, 200), some (1, .right, 202)],
  [some (0, .right, 423), some (1, .right, 511)],
  [some (0, .right, 192), some (1, .right, 204)],
  [some (0, .right, 373), some (1, .left, 58)],
  [some (0, .right, 206), some (0, .left, 13)],
  [some (0, .right, 207), some (0, .left, 15)],
  [some (0, .right, 208), some (1, .right, 475)],
  [some (0, .right, 205), some (1, .right, 209)],
  [some (0, .right, 203), some (1, .right, 210)],
  [some (0, .right, 525), some (0, .left, 15)],
  [some (0, .right, 212), some (1, .right, 432)],
  [some (0, .right, 366), some (1, .left, 41)],
  [some (0, .right, 214), some (0, .left, 13)],
  [some (0, .right, 534), some (1, .right, 215)],
  [some (0, .right, 216), some (1, .right, 485)],
  [some (0, .right, 213), some (1, .right, 217)],
  [some (0, .right, 537), some (1, .right, 140)],
  [some (0, .right, 365), some (1, .left, 454)],
  [some (0, .right, 363), some (0, .left, 10)],
  [some (0, .right, 220), some (1, .right, 221)],
  [some (0, .right, 503), some (1, .right, 222)],
  [some (0, .right, 219), some (1, .right, 223)],
  [some (0, .left, 69), some (0, .left, 10)],
  [some (0, .right, 225), some (0, .left, 13)],
  [some (0, .right, 226), some (1, .right, 388)],
  [some (0, .right, 507), some (0, .left, 15)],
  [some (0, .right, 227), some (1, .right, 228)],
  [some (0, .right, 224), some (1, .right, 229)],
  [some (0, .right, 218), some (1, .right, 230)],
  [some (0, .right, 211), some (1, .right, 231)],
  [some (0, .right, 198), some (1, .right, 232)],
  [some (0, .right, 164), some (1, .right, 233)],
  [some (0, .right, 163), some (1, .right, 234)],
  [some (0, .right, 491), some (1, .right, 100)],
  [some (0, .right, 394), some (1, .right, 236)],
  [some (0, .right, 491), some (1, .right, 140)],
  [some (0, .right, 390), some (1, .right, 238)],
  [some (0, .right, 237), some (1, .right, 239)],
  [some (0, .right, 388), some (1, .right, 507)],
  [some (0, .right, 241), some (1, .right, 430)],
  [some (0, .right, 495), some (1, .right, 100)],
  [some (0, .right, 243), some (1, .right, 428)],
  [some (0, .right, 242), some (1, .right, 244)],
  [some (0, .right, 240), some (1, .right, 245)],
  [some (0, .right, 495), some (1, .right, 140)],
  [some (0, .right, 396), some (1, .right, 509)],
  [some (0, .right, 247), some (1, .right, 248)],
  [some (0, .right, 401), some (1, .right, 413)],
  [some (0, .right, 492), some (0, .left, 450)],
  [some (0, .right, 251), some (0, .left, 13)],
  [some (0, .right, 252), some (1, .right, 434)],
  [some (0, .right, 250), some (1, .right, 253)],
  [some (0, .right, 249), some (1, .right, 254)],
  [some (0, .right, 171), some (0, .left, 15)],
  [some (0, .right, 256), some (1, .right, 439)],
  [some (0, .right, 521), some (0, .left, 15)],
  [some (0, .right, 258), some (1, .right, 482)],
  [some (0, .right, 257), some (1, .right, 259)],
  [some (0, .right, 255), some (1, .right, 260)],
  [some (0, .right, 246), some (1, .right, 261)],
  [some (0, .right, 363), some (1, .left, 41)],
  [some (0, .right, 220), some (1, .right, 263)],
  [some (0, .right, 501), some (1, .right, 264)],
  [some (0, .right, 103), some (1, .right, 115)],
  [some (0, .right, 266), some (1, .right, 505)],
  [some (0, .right, 265), some (1, .right, 267)],
  [some (0, .right, 185), some (1, .right, 517)],
  [some (0, .right, 269), some (1, .right, 406)],
  [some (0, .right, 268), some (1, .right, 270)],
  [some (0, .right, 263), some (0, .left, 13)],
  [some (0, .right, 493), some (1, .right, 272)],
  [some (0, .right, 273), some (1, .right, 441)],
  [some (0, .right, 496), some (1, .right, 140)],
  [some (0, .right, 275), some (1, .right, 421)],
  [some (0, .right, 274), some (1, .right, 276)],
  [some (0, .right, 271), some (1, .right, 277)],
  [some (0, .right, 510), some (1, .right, 401)],
  [some (0, .right, 518), some (0, .left, 15)],
  [some (0, .right, 279), some (1, .right, 280)],
  [some (0, .right, 494), some (1, .right, 272)],
  [some (0, .right, 415), some (1, .right, 282)],
  [some (0, .right, 281), some (1, .right, 283)],
  [some (0, .right, 441), some (1, .right, 275)],
  [some (0, .right, 413), some (1, .right, 519)],
  [some (0, .right, 373), some (1, .left, 44)],
  [some (0, .right, 287), some (0, .left, 13)],
  [some (0, .right, 288), some (0, .left, 15)],
  [some (0, .right, 286), some (1, .right, 289)],
  [some (0, .right, 285), some (1, .right, 290)],
  [some (0, .right, 284), some (1, .right, 291)],
  [some (0, .right, 278), some (1, .right, 292)],
  [some (0, .right, 262), some (1, .right, 293)],
  [some (0, .right, 406), some (1, .right, 273)],
  [some (0, .right, 493), some (1, .right, 140)],
  [some (0, .right, 411), some (1, .right, 296)],
  [some (0, .right, 295), some (1, .right, 297)],
  [some (0, .right, 401), some (1, .right, 518)],
  [some (0, .right, 299), some (1, .right, 403)],
  [some (0, .right, 529), some (1, .right, 188)],
  [some (0, .right, 301), some (1, .right, 409)],
  [some (0, .right, 300), some (1, .right, 302)],
  [some (0, .right, 298), some (1, .right, 303)],
  [some (0, .left, 47), some (1, .right, 363)],
  [some (1, .left, 47), some (0, .left, 10)],
  [some (0, .right, 305), some (1, .right, 306)],
  [some (0, .right, 529), some (1, .right, 307)],
  [some (0, .right, 308), some (1, .right, 482)],
  [some (0, .right, 306), some (0, .left, 13)],
  [some (0, .right, 501), some (1, .right, 310)],
  [some (0, .right, 311), some (1, .right, 299)],
  [some (0, .right, 309), some (1, .right, 312)],
  [some (0, .right, 494), some (1, .right, 140)],
  [some (0, .right, 417), some (1, .right, 314)],
  [some (0, .right, 283), some (1, .right, 315)],
  [some (0, .right, 313), some (1, .right, 316)],
  [some (0, .right, 304), some (1, .right, 317)],
  [some (0, .right, 286), some (1, .right, 415)],
  [some (0, .right, 282), some (1, .right, 417)],
  [some (0, .right, 319), some (1, .right, 320)],
  [some (0, .right, 314), some (1, .right, 286)],
  [some (0, .right, 491), some (1, .right, 272)],
  [some (0, .right, 390), some (1, .right, 323)],
  [some (0, .right, 322), some (1, .right, 324)],
  [some (0, .right, 321), some (1, .right, 325)],
  [some (0, .right, 528), some (1, .right, 188)],
  [some (0, .right, 399), some (1, .right, 327)],
  [some (0, .right, 315), some (1, .right, 328)],
  [some (0, .left, 69), some (1, .right, 365)],
  [some (0, .right, 305), some (1, .right, 330)],
  [some (0, .right, 529), some (1, .right, 331)],
  [some (0, .right, 409), some (1, .right, 332)],
  [some (0, .right, 365), some (1, .left, 50)],
  [some (0, .right, 111), some (1, .right, 334)],
  [some (0, .right, 335), some (1, .right, 517)],
  [some (0, .right, 336), some (1, .right, 117)],
  [some (0, .right, 333), some (1, .right, 337)],
  [some (0, .right, 329), some (1, .right, 338)],
  [some (0, .right, 326), some (1, .right, 339)],
  [some (0, .right, 318), some (1, .right, 340)],
  [some (0, .right, 294), some (1, .right, 341)],
  [some (1, .left, 50), some (1, .left, 10)],
  [some (1, .left, 50), none],
  [some (0, .right, 343), some (1, .right, 344)],
  [some (0, .right, 345), some (0, .left, 15)],
  [some (0, .right, 346), some (0, .left, 17)],
  [some (0, .right, 347), some (0, .left, 19)],
  [some (0, .right, 348), some (0, .left, 21)],
  [some (0, .right, 349), some (0, .left, 23)],
  [some (0, .right, 350), some (0, .left, 25)],
  [some (0, .right, 351), some (0, .left, 27)],
  [some (0, .right, 342), some (1, .right, 352)],
  [some (0, .left, 10), some (1, .left, 10)],
  [some (0, .right, 2), some (1, .right, 355)],
  [some (0, .right, 355), some (1, .right, 356)],
  [some (0, .right, 356), some (1, .right, 357)],
  [some (0, .right, 369), some (1, .right, 358)],
  [some (0, .right, 358), some (1, .right, 359)],
  [some (0, .right, 359), some (1, .right, 360)],
  [some (0, .right, 360), some (1, .right, 361)],
  [some (0, .right, 357), some (1, .right, 362)],
  [some (0, .right, 362), some (1, .right, 363)],
  [some (0, .right, 363), some (1, .right, 364)],
  [some (0, .right, 364), some (1, .right, 365)],
  [some (0, .right, 365), some (1, .right, 366)],
  [some (0, .right, 366), some (1, .right, 367)],
  [some (0, .right, 367), some (1, .right, 368)],
  [some (0, .right, 368), some (1, .right, 369)],
  [some (0, .right, 29), some (1, .right, 370)],
  [some (0, .right, 370), some (1, .right, 371)],
  [some (0, .right, 382), some (1, .right, 372)],
  [some (0, .right, 372), some (1, .right, 373)],
  [some (0, .right, 373), some (1, .right, 374)],
  [some (0, .right, 374), some (1, .right, 375)],
  [some (0, .right, 75), some (1, .right, 376)],
  [some (0, .right, 456), some (1, .right, 377)],
  [some (0, .right, 377), some (1, .right, 378)],
  [some (0, .right, 378), some (1, .right, 379)],
  [some (0, .right, 379), some (1, .right, 380)],
  [some (0, .right, 380), some (1, .right, 381)],
  [some (0, .right, 381), some (1, .right, 382)],
  [some (0, .left, 8), some (1, .left, 384)],
  [some (0, .left, 383), some (1, .left, 384)],
  [some (0, .left, 354), some (1, .left, 386)],
  [some (0, .left, 385), some (1, .left, 386)],
  [some (0, .right, 360), some (1, .left, 10)],
  [some (0, .right, 387), some (1, .right, 452)],
  [some (0, .right, 391), some (1, .right, 459)],
  [some (0, .right, 389), some (1, .right, 116)],
  [some (0, .right, 360), some (1, .left, 454)],
  [some (0, .right, 378), some (1, .right, 376)],
  [some (0, .right, 391), some (1, .right, 392)],
  [some (0, .right, 393), some (1, .right, 116)],
  [some (0, .right, 361), some (1, .left, 10)],
  [some (0, .right, 395), some (1, .right, 452)],
  [some (0, .right, 361), some (1, .left, 454)],
  [some (0, .right, 397), some (1, .right, 478)],
  [some (0, .right, 398), some (1, .right, 116)],
  [some (0, .right, 395), some (1, .left, 10)],
  [some (0, .right, 400), some (1, .right, 452)],
  [some (0, .right, 404), some (1, .right, 478)],
  [some (0, .right, 402), some (1, .right, 116)],
  [some (0, .right, 395), some (1, .left, 454)],
  [some (0, .right, 404), some (1, .right, 459)],
  [some (0, .right, 405), some (1, .right, 116)],
  [some (0, .right, 456), some (1, .right, 379)],
  [some (0, .right, 404), some (1, .right, 407)],
  [some (0, .right, 408), some (1, .right, 116)],
  [some (0, .right, 404), some (1, .right, 392)],
  [some (0, .right, 410), some (1, .right, 116)],
  [some (0, .right, 400), some (1, .left, 10)],
  [some (0, .right, 412), some (1, .right, 452)],
  [some (0, .right, 418), some (1, .right, 459)],
  [some (0, .right, 414), some (1, .right, 116)],
  [some (0, .right, 418), some (1, .right, 392)],
  [some (0, .right, 416), some (1, .right, 116)],
  [some (0, .right, 400), some (1, .left, 454)],
  [some (0, .right, 378), some (1, .right, 456)],
  [some (0, .right, 418), some (1, .right, 419)],
  [some (0, .right, 420), some (1, .right, 116)],
  [some (0, .right, 358), some (1, .left, 10)],
  [some (0, .right, 422), some (1, .right, 452)],
  [some (0, .right, 426), some (1, .right, 473)],
  [some (0, .right, 424), some (1, .right, 116)],
  [some (0, .right, 358), some (1, .left, 454)],
  [some (0, .right, 426), some (1, .right, 459)],
  [some (0, .right, 427), some (1, .right, 116)],
  [some (0, .right, 426), some (1, .right, 392)],
  [some (0, .right, 429), some (1, .right, 116)],
  [some (0, .right, 426), some (1, .right, 380)],
  [some (0, .right, 431), some (1, .right, 116)],
  [some (0, .right, 359), some (1, .left, 10)],
  [some (0, .right, 433), some (1, .right, 452)],
  [some (0, .right, 359), some (1, .left, 454)],
  [some (0, .right, 435), some (1, .right, 456)],
  [some (0, .right, 436), some (1, .right, 116)],
  [some (0, .right, 435), some (1, .right, 462)],
  [some (0, .right, 438), some (1, .right, 116)],
  [some (0, .right, 435), some (1, .right, 392)],
  [some (0, .right, 440), some (1, .right, 116)],
  [some (0, .right, 364), some (1, .left, 10)],
  [some (0, .right, 442), some (1, .right, 452)],
  [some (0, .right, 456), some (1, .right, 380)],
  [some (0, .right, 447), some (1, .right, 444)],
  [some (0, .right, 445), some (1, .right, 116)],
  [some (0, .right, 364), some (1, .left, 454)],
  [some (0, .right, 447), some (1, .right, 381)],
  [some (0, .right, 448), some (1, .right, 116)],
  [some (1, .left, 12), some (0, .left, 12)],
  [some (0, .right, 356), some (1, .left, 10)],
  [some (0, .left, 450), some (0, .left, 10)],
  [some (0, .right, 451), some (1, .right, 452)],
  [some (0, .left, 13), some (1, .left, 13)],
  [some (0, .right, 356), some (1, .left, 454)],
  [some (0, .right, 376), some (1, .right, 456)],
  [some (0, .right, 455), some (1, .right, 456)],
  [some (0, .right, 457), some (1, .right, 116)],
  [some (0, .right, 456), some (1, .right, 376)],
  [some (0, .right, 455), some (1, .right, 459)],
  [some (0, .right, 460), some (1, .right, 116)],
  [some (0, .right, 456), some (1, .right, 378)],
  [some (0, .right, 455), some (1, .right, 462)],
  [some (0, .right, 463), some (1, .right, 116)],
  [some (0, .right, 379), some (1, .right, 381)],
  [some (0, .right, 455), some (1, .right, 465)],
  [some (0, .right, 466), some (1, .right, 116)],
  [some (0, .right, 455), some (1, .right, 381)],
  [some (0, .right, 468), some (1, .right, 116)],
  [some (0, .right, 369), some (1, .left, 10)],
  [some (0, .right, 470), some (1, .right, 452)],
  [some (0, .right, 369), some (1, .left, 454)],
  [some (0, .right, 376), some (1, .right, 378)],
  [some (0, .right, 472), some (1, .right, 473)],
  [some (0, .right, 474), some (1, .right, 116)],
  [some (0, .right, 486), some (1, .right, 456)],
  [some (0, .right, 476), some (1, .right, 116)],
  [some (0, .right, 376), some (1, .right, 379)],
  [some (0, .right, 486), some (1, .right, 478)],
  [some (0, .right, 479), some (1, .right, 116)],
  [some (0, .right, 486), some (1, .right, 392)],
  [some (0, .right, 481), some (1, .right, 116)],
  [some (0, .right, 378), some (1, .right, 380)],
  [some (0, .right, 486), some (1, .right, 483)],
  [some (0, .right, 484), some (1, .right, 116)],
  [some (0, .right, 357), some (1, .left, 454)],
  [some (0, .right, 486), some (1, .right, 465)],
  [some (0, .right, 487), some (1, .right, 116)],
  [some (0, .right, 362), some (1, .left, 10)],
  [some (0, .right, 489), some (1, .right, 452)],
  [some (0, .right, 497), some (1, .right, 506)],
  [some (0, .right, 508), some (0, .left, 450)],
  [some (0, .right, 497), some (1, .right, 492)],
  [some (0, .right, 497), some (1, .right, 251)],
  [some (0, .right, 497), some (1, .right, 167)],
  [some (0, .right, 497), some (1, .right, 170)],
  [some (0, .right, 362), some (0, .left, 454)],
  [some (0, .right, 377), some (0, .left, 450)],
  [some (0, .right, 497), some (1, .right, 498)],
  [some (0, .right, 497), some (1, .right, 142)],
  [some (0, .right, 497), some (1, .right, 541)],
  [some (0, .right, 456), some (0, .left, 450)],
  [some (0, .right, 497), some (1, .right, 502)],
  [some (0, .right, 363), some (1, .left, 10)],
  [some (0, .right, 504), some (1, .right, 452)],
  [some (0, .right, 374), some (0, .left, 450)],
  [some (0, .right, 135), some (1, .right, 506)],
  [some (0, .right, 375), some (0, .left, 450)],
  [some (0, .right, 135), some (1, .right, 508)],
  [some (0, .right, 135), some (1, .right, 251)],
  [some (0, .right, 135), some (1, .right, 167)],
  [some (0, .right, 135), some (1, .right, 170)],
  [some (0, .right, 135), some (1, .right, 142)],
  [some (0, .right, 135), some (1, .right, 524)],
  [some (0, .right, 135), some (1, .right, 541)],
  [some (0, .right, 365), some (1, .left, 10)],
  [some (0, .right, 516), some (1, .right, 452)],
  [some (0, .right, 522), some (1, .right, 492)],
  [some (0, .right, 522), some (1, .right, 251)],
  [some (0, .right, 522), some (1, .right, 167)],
  [some (0, .right, 522), some (1, .right, 170)],
  [some (0, .right, 365), some (0, .left, 454)],
  [some (0, .right, 522), some (1, .right, 142)],
  [some (0, .right, 382), some (0, .left, 450)],
  [some (0, .right, 522), some (1, .right, 524)],
  [some (0, .right, 366), some (1, .left, 10)],
  [some (0, .right, 526), some (1, .right, 452)],
  [some (0, .right, 530), some (1, .right, 508)],
  [some (0, .right, 530), some (1, .right, 492)],
  [some (0, .right, 366), some (0, .left, 454)],
  [some (0, .right, 530), some (1, .right, 541)],
  [some (0, .right, 367), some (1, .left, 10)],
  [some (0, .right, 532), some (1, .right, 452)],
  [some (0, .right, 535), some (1, .right, 167)],
  [some (0, .right, 367), some (0, .left, 454)],
  [some (0, .right, 535), some (1, .right, 498)],
  [some (0, .right, 535), some (1, .right, 541)],
  [some (0, .right, 539), some (1, .right, 498)],
  [some (0, .right, 368), some (0, .left, 454)],
  [some (0, .right, 539), some (1, .right, 142)],
  [some (0, .right, 75), some (0, .left, 450)],
  [some (0, .right, 539), some (1, .right, 541)]]

-- 543-state reduction of riemann_744 via Bounce Elimination + W=(11,13) Window Invariant.

def refRows : List (List (Option (Fin 2 × Dir × Fin 744))) := [
  [some (0, .right, 523), some (1, .right, 523)],
  [some (0, .left, 3), some (1, .right, 5)],
  [some (0, .right, 1), some (0, .right, 1)],
  [some (1, .left, 566), some (1, .left, 566)],
  [some (0, .left, 6), some (1, .right, 5)],
  [some (0, .right, 4), some (1, .right, 5)],
  [some (0, .left, 7), some (1, .left, 7)],
  [some (0, .left, 567), some (0, .left, 8)],
  [some (1, .left, 7), some (1, .left, 8)],
  [some (1, .left, 10), some (0, .left, 11)],
  [some (0, .left, 14), some (1, .left, 14)],
  [some (1, .left, 14), some (0, .left, 15)],
  [some (0, .left, 0), some (1, .left, 0)],
  [some (1, .left, 0), some (0, .left, 0)],
  [some (0, .left, 16), some (1, .left, 16)],
  [some (1, .left, 16), some (0, .left, 17)],
  [some (0, .left, 18), some (1, .left, 18)],
  [some (1, .left, 18), some (0, .left, 19)],
  [some (0, .left, 20), some (1, .left, 20)],
  [some (1, .left, 20), some (0, .left, 21)],
  [some (0, .left, 22), some (1, .left, 22)],
  [some (1, .left, 22), some (0, .left, 23)],
  [some (0, .left, 24), some (1, .left, 24)],
  [some (1, .left, 24), some (0, .left, 25)],
  [some (0, .left, 26), some (1, .left, 26)],
  [some (1, .left, 26), some (0, .left, 27)],
  [some (0, .left, 28), some (1, .left, 28)],
  [some (1, .left, 28), some (0, .left, 29)],
  [some (0, .left, 12), some (1, .left, 12)],
  [some (1, .left, 12), some (0, .left, 13)],
  [some (0, .left, 565), some (0, .right, 31)],
  [some (1, .right, 30), some (1, .right, 31)],
  [some (0, .right, 33), some (1, .right, 33)],
  [some (0, .right, 34), some (1, .right, 34)],
  [some (1, .left, 566), some (1, .right, 35)],
  [some (0, .right, 34), some (1, .right, 35)],
  [some (0, .left, 37), some (1, .left, 37)],
  [some (1, .left, 38), some (1, .left, 38)],
  [some (1, .left, 177), some (1, .left, 177)],
  [some (0, .left, 40), some (1, .left, 40)],
  [some (0, .left, 41), some (0, .left, 41)],
  [some (1, .left, 42), some (1, .left, 42)],
  [some (0, .left, 43), some (0, .left, 43)],
  [some (0, .left, 59), some (0, .left, 59)],
  [some (0, .left, 45), some (1, .left, 45)],
  [some (0, .left, 46), some (0, .left, 46)],
  [some (0, .left, 47), some (0, .left, 47)],
  [some (1, .left, 172), some (1, .left, 172)],
  [some (0, .left, 49), some (1, .left, 49)],
  [some (0, .left, 50), some (0, .left, 50)],
  [some (0, .left, 51), some (0, .left, 51)],
  [some (1, .left, 52), some (1, .left, 52)],
  [some (1, .left, 53), some (1, .left, 53)],
  [some (0, .left, 121), some (0, .left, 121)],
  [some (0, .left, 55), some (1, .left, 55)],
  [some (0, .left, 56), some (0, .left, 56)],
  [some (0, .left, 57), some (0, .left, 57)],
  [some (0, .left, 58), some (0, .left, 58)],
  [some (1, .left, 59), some (1, .left, 59)],
  [some (1, .left, 60), some (1, .left, 60)],
  [some (1, .left, 23), some (1, .left, 23)],
  [some (0, .left, 62), some (1, .left, 62)],
  [some (0, .left, 63), some (0, .left, 63)],
  [some (1, .left, 57), some (1, .left, 57)],
  [some (0, .left, 65), some (1, .left, 65)],
  [some (1, .left, 66), some (1, .left, 66)],
  [some (0, .left, 67), some (0, .left, 67)],
  [some (1, .left, 68), some (1, .left, 68)],
  [some (1, .left, 69), some (1, .left, 69)],
  [some (1, .left, 70), some (1, .left, 70)],
  [some (1, .left, 71), some (1, .left, 71)],
  [some (1, .left, 72), some (1, .left, 72)],
  [some (0, .left, 26), some (0, .left, 26)],
  [some (0, .left, 74), some (1, .left, 74)],
  [some (1, .left, 46), some (1, .left, 46)],
  [some (0, .left, 76), some (1, .left, 76)],
  [some (0, .left, 77), some (0, .left, 77)],
  [some (0, .left, 78), some (0, .left, 78)],
  [some (0, .left, 79), some (0, .left, 79)],
  [some (0, .left, 120), some (0, .left, 120)],
  [some (0, .left, 81), some (1, .left, 81)],
  [some (1, .left, 82), some (1, .left, 82)],
  [some (0, .left, 83), some (0, .left, 83)],
  [some (0, .left, 84), some (0, .left, 84)],
  [some (0, .left, 19), some (0, .left, 19)],
  [some (0, .left, 86), some (1, .left, 86)],
  [some (0, .left, 87), some (0, .left, 87)],
  [some (0, .left, 88), some (0, .left, 88)],
  [some (1, .left, 79), some (1, .left, 79)],
  [some (0, .left, 90), some (1, .left, 90)],
  [some (1, .left, 93), some (1, .left, 93)],
  [some (0, .left, 92), some (0, .left, 92)],
  [some (0, .left, 0), some (0, .left, 0)],
  [some (0, .left, 94), some (0, .left, 94)],
  [some (1, .left, 95), some (1, .left, 95)],
  [some (0, .left, 96), some (0, .left, 96)],
  [some (1, .left, 97), some (1, .left, 97)],
  [some (0, .left, 98), some (0, .left, 98)],
  [some (0, .left, 99), some (0, .left, 99)],
  [some (0, .left, 100), some (0, .left, 100)],
  [some (0, .left, 91), some (0, .left, 91)],
  [some (0, .left, 102), some (1, .left, 102)],
  [some (1, .left, 103), some (1, .left, 103)],
  [some (0, .left, 104), some (0, .left, 104)],
  [some (1, .left, 84), some (1, .left, 84)],
  [some (0, .left, 106), some (1, .left, 106)],
  [some (0, .left, 109), some (0, .left, 109)],
  [some (0, .left, 108), some (1, .left, 108)],
  [some (1, .left, 109), some (1, .left, 109)],
  [some (0, .left, 113), some (0, .left, 113)],
  [some (0, .left, 111), some (1, .left, 111)],
  [some (0, .left, 112), some (0, .left, 112)],
  [some (1, .left, 113), some (1, .left, 113)],
  [some (0, .left, 114), some (0, .left, 114)],
  [some (1, .left, 19), some (1, .left, 19)],
  [some (0, .left, 116), some (1, .left, 116)],
  [some (0, .left, 117), some (0, .left, 117)],
  [some (0, .left, 118), some (0, .left, 118)],
  [some (1, .left, 119), some (1, .left, 119)],
  [some (1, .left, 120), some (1, .left, 120)],
  [some (1, .left, 121), some (1, .left, 121)],
  [some (0, .left, 22), some (0, .left, 22)],
  [some (0, .left, 123), some (1, .left, 123)],
  [some (1, .left, 124), some (1, .left, 124)],
  [some (0, .left, 125), some (0, .left, 125)],
  [some (1, .left, 114), some (1, .left, 114)],
  [some (0, .left, 127), some (1, .left, 127)],
  [some (1, .left, 128), some (1, .left, 128)],
  [some (0, .left, 129), some (0, .left, 129)],
  [some (1, .left, 130), some (1, .left, 130)],
  [some (1, .left, 131), some (1, .left, 131)],
  [some (1, .left, 132), some (1, .left, 132)],
  [some (0, .left, 145), some (0, .left, 145)],
  [some (0, .left, 134), some (1, .left, 134)],
  [some (0, .left, 135), some (0, .left, 135)],
  [some (0, .left, 136), some (0, .left, 136)],
  [some (1, .left, 137), some (1, .left, 137)],
  [some (0, .left, 173), some (0, .left, 173)],
  [some (0, .left, 139), some (1, .left, 139)],
  [some (0, .left, 140), some (0, .left, 140)],
  [some (0, .left, 141), some (0, .left, 141)],
  [some (1, .left, 142), some (1, .left, 142)],
  [some (1, .left, 143), some (1, .left, 143)],
  [some (0, .left, 144), some (0, .left, 144)],
  [some (1, .left, 145), some (1, .left, 145)],
  [some (0, .left, 72), some (0, .left, 72)],
  [some (0, .left, 147), some (1, .left, 147)],
  [some (1, .left, 135), some (1, .left, 135)],
  [some (0, .left, 149), some (1, .left, 149)],
  [some (0, .left, 150), some (0, .left, 150)],
  [some (0, .left, 151), some (0, .left, 151)],
  [some (1, .left, 152), some (1, .left, 152)],
  [some (0, .left, 153), some (0, .left, 153)],
  [some (1, .left, 154), some (1, .left, 154)],
  [some (1, .left, 155), some (1, .left, 155)],
  [some (0, .left, 24), some (0, .left, 24)],
  [some (0, .left, 157), some (1, .left, 157)],
  [some (0, .left, 165), some (0, .left, 165)],
  [some (0, .left, 159), some (1, .left, 159)],
  [some (0, .left, 160), some (0, .left, 160)],
  [some (0, .left, 161), some (0, .left, 161)],
  [some (1, .left, 162), some (1, .left, 162)],
  [some (1, .left, 153), some (1, .left, 153)],
  [some (0, .left, 164), some (1, .left, 164)],
  [some (1, .left, 165), some (1, .left, 165)],
  [some (1, .left, 15), some (1, .left, 15)],
  [some (0, .left, 167), some (1, .left, 167)],
  [some (0, .left, 176), some (0, .left, 176)],
  [some (0, .left, 169), some (1, .left, 169)],
  [some (0, .left, 170), some (0, .left, 170)],
  [some (0, .left, 171), some (0, .left, 171)],
  [some (0, .left, 172), some (0, .left, 172)],
  [some (1, .left, 173), some (1, .left, 173)],
  [some (0, .left, 20), some (0, .left, 20)],
  [some (0, .left, 175), some (1, .left, 175)],
  [some (1, .left, 176), some (1, .left, 176)],
  [some (0, .left, 177), some (0, .left, 177)],
  [some (0, .left, 17), some (0, .left, 17)],
  [some (0, .left, 179), some (1, .left, 179)],
  [some (1, .left, 180), some (1, .left, 180)],
  [some (0, .left, 181), some (0, .left, 181)],
  [some (0, .left, 182), some (0, .left, 182)],
  [some (0, .left, 183), some (0, .left, 183)],
  [some (0, .left, 70), some (0, .left, 70)],
  [some (0, .right, 32), some (1, .right, 32)],
  [some (0, .right, 184), some (1, .right, 184)],
  [some (0, .right, 185), some (1, .right, 185)],
  [some (0, .right, 186), some (1, .right, 186)],
  [some (0, .right, 551), some (1, .right, 188)],
  [some (0, .right, 188), some (1, .right, 524)],
  [some (0, .right, 639), some (1, .right, 189)],
  [some (0, .right, 190), some (1, .right, 652)],
  [some (0, .right, 187), some (1, .right, 191)],
  [some (0, .right, 714), some (1, .right, 625)],
  [some (0, .right, 694), some (1, .right, 526)],
  [some (0, .right, 193), some (1, .right, 194)],
  [some (0, .right, 714), some (1, .right, 526)],
  [some (0, .right, 652), some (1, .right, 196)],
  [some (0, .right, 195), some (1, .right, 197)],
  [some (0, .right, 192), some (1, .right, 198)],
  [some (0, .right, 741), some (1, .right, 526)],
  [some (0, .right, 661), some (1, .right, 200)],
  [some (0, .right, 547), some (1, .right, 644)],
  [some (0, .right, 546), some (1, .right, 163)],
  [some (0, .right, 202), some (1, .right, 203)],
  [some (0, .right, 739), some (1, .right, 204)],
  [some (0, .right, 631), some (1, .right, 205)],
  [some (0, .right, 201), some (1, .right, 206)],
  [some (0, .right, 115), some (1, .right, 560)],
  [some (0, .right, 48), some (1, .right, 525)],
  [some (0, .right, 208), some (1, .right, 209)],
  [some (0, .right, 210), some (1, .right, 734)],
  [some (0, .right, 545), some (1, .right, 64)],
  [some (0, .right, 212), some (1, .right, 524)],
  [some (0, .right, 213), some (1, .right, 526)],
  [some (0, .right, 211), some (1, .right, 214)],
  [some (0, .right, 168), some (1, .right, 543)],
  [some (0, .right, 156), some (1, .right, 542)],
  [some (0, .right, 216), some (1, .right, 217)],
  [some (0, .right, 737), some (1, .right, 218)],
  [some (0, .right, 628), some (1, .right, 219)],
  [some (0, .right, 215), some (1, .right, 220)],
  [some (0, .right, 207), some (1, .right, 221)],
  [some (0, .right, 199), some (1, .right, 222)],
  [some (0, .right, 174), some (1, .right, 64)],
  [some (0, .right, 542), some (1, .right, 80)],
  [some (0, .right, 224), some (1, .right, 225)],
  [some (0, .right, 226), some (1, .right, 684)],
  [some (0, .right, 54), some (1, .right, 525)],
  [some (0, .right, 228), some (1, .right, 524)],
  [some (0, .right, 229), some (1, .right, 700)],
  [some (0, .right, 227), some (1, .right, 230)],
  [some (0, .right, 229), some (1, .right, 526)],
  [some (0, .right, 232), some (1, .right, 655)],
  [some (0, .right, 231), some (1, .right, 233)],
  [some (0, .right, 695), some (1, .right, 526)],
  [some (0, .right, 235), some (1, .right, 663)],
  [some (0, .right, 200), some (1, .right, 682)],
  [some (0, .right, 236), some (1, .right, 237)],
  [some (0, .right, 234), some (1, .right, 238)],
  [some (0, .right, 546), some (1, .right, 644)],
  [some (0, .right, 547), some (1, .right, 163)],
  [some (0, .right, 240), some (1, .right, 241)],
  [some (0, .right, 743), some (1, .right, 242)],
  [some (0, .right, 133), some (1, .right, 560)],
  [some (0, .right, 148), some (1, .right, 525)],
  [some (0, .right, 244), some (1, .right, 245)],
  [some (0, .right, 246), some (1, .right, 728)],
  [some (0, .right, 243), some (1, .right, 247)],
  [some (0, .right, 545), some (1, .right, 101)],
  [some (0, .right, 249), some (1, .right, 524)],
  [some (0, .right, 250), some (1, .right, 526)],
  [some (0, .right, 251), some (1, .right, 674)],
  [some (0, .right, 248), some (1, .right, 252)],
  [some (0, .right, 75), some (1, .right, 542)],
  [some (0, .right, 156), some (1, .right, 543)],
  [some (0, .right, 254), some (1, .right, 255)],
  [some (0, .right, 732), some (1, .right, 256)],
  [some (0, .right, 80), some (1, .right, 146)],
  [some (0, .right, 543), some (1, .right, 110)],
  [some (0, .right, 258), some (1, .right, 259)],
  [some (0, .right, 260), some (1, .right, 700)],
  [some (0, .right, 257), some (1, .right, 261)],
  [some (0, .right, 166), some (1, .right, 525)],
  [some (0, .right, 263), some (1, .right, 524)],
  [some (0, .right, 264), some (1, .right, 684)],
  [some (0, .right, 551), some (1, .right, 138)],
  [some (0, .right, 266), some (1, .right, 524)],
  [some (0, .right, 267), some (1, .right, 526)],
  [some (0, .right, 265), some (1, .right, 268)],
  [some (0, .right, 262), some (1, .right, 269)],
  [some (0, .right, 253), some (1, .right, 270)],
  [some (0, .right, 239), some (1, .right, 271)],
  [some (0, .right, 223), some (1, .right, 272)],
  [some (0, .right, 542), some (1, .right, 89)],
  [some (0, .right, 274), some (1, .right, 274)],
  [some (0, .right, 716), some (1, .right, 275)],
  [some (0, .right, 671), some (1, .right, 276)],
  [some (0, .right, 275), some (1, .right, 275)],
  [some (0, .right, 278), some (1, .right, 278)],
  [some (0, .right, 277), some (1, .right, 279)],
  [some (0, .right, 279), some (1, .right, 279)],
  [some (0, .right, 280), some (1, .right, 281)],
  [some (0, .right, 281), some (1, .right, 281)],
  [some (0, .right, 282), some (1, .right, 283)],
  [some (0, .right, 283), some (1, .right, 283)],
  [some (0, .right, 284), some (1, .right, 285)],
  [some (0, .right, 273), some (1, .right, 286)],
  [some (0, .right, 285), some (1, .right, 285)],
  [some (0, .right, 684), some (1, .right, 665)],
  [some (0, .right, 278), some (1, .right, 289)],
  [some (0, .right, 552), some (1, .right, 525)],
  [some (0, .right, 291), some (1, .right, 524)],
  [some (0, .right, 605), some (1, .right, 292)],
  [some (0, .right, 553), some (1, .right, 525)],
  [some (0, .right, 294), some (1, .right, 524)],
  [some (0, .right, 616), some (1, .right, 295)],
  [some (0, .right, 293), some (1, .right, 296)],
  [some (0, .right, 290), some (1, .right, 297)],
  [some (0, .right, 709), some (1, .right, 526)],
  [some (0, .right, 619), some (1, .right, 299)],
  [some (0, .right, 543), some (1, .right, 644)],
  [some (0, .right, 542), some (1, .right, 107)],
  [some (0, .right, 301), some (1, .right, 302)],
  [some (0, .right, 724), some (1, .right, 303)],
  [some (0, .right, 658), some (1, .right, 304)],
  [some (0, .right, 300), some (1, .right, 305)],
  [some (0, .right, 298), some (1, .right, 306)],
  [some (0, .right, 158), some (1, .right, 542)],
  [some (0, .right, 75), some (1, .right, 525)],
  [some (0, .right, 308), some (1, .right, 309)],
  [some (0, .right, 310), some (1, .right, 684)],
  [some (0, .right, 39), some (1, .right, 525)],
  [some (0, .right, 312), some (1, .right, 524)],
  [some (0, .right, 313), some (1, .right, 700)],
  [some (0, .right, 311), some (1, .right, 314)],
  [some (0, .right, 542), some (1, .right, 122)],
  [some (0, .right, 316), some (1, .right, 524)],
  [some (0, .right, 726), some (1, .right, 317)],
  [some (0, .right, 669), some (1, .right, 318)],
  [some (0, .right, 315), some (1, .right, 319)],
  [some (0, .right, 115), some (1, .right, 525)],
  [some (0, .right, 321), some (1, .right, 524)],
  [some (0, .right, 722), some (1, .right, 322)],
  [some (0, .right, 621), some (1, .right, 323)],
  [some (0, .right, 690), some (1, .right, 665)],
  [some (0, .right, 610), some (1, .right, 325)],
  [some (0, .right, 324), some (1, .right, 326)],
  [some (0, .right, 320), some (1, .right, 327)],
  [some (0, .right, 307), some (1, .right, 328)],
  [some (0, .right, 715), some (1, .right, 526)],
  [some (0, .right, 330), some (1, .right, 607)],
  [some (0, .right, 542), some (1, .right, 101)],
  [some (0, .right, 332), some (1, .right, 524)],
  [some (0, .right, 721), some (1, .right, 333)],
  [some (0, .right, 334), some (1, .right, 621)],
  [some (0, .right, 331), some (1, .right, 335)],
  [some (0, .right, 85), some (1, .right, 525)],
  [some (0, .right, 337), some (1, .right, 524)],
  [some (0, .right, 722), some (1, .right, 338)],
  [some (0, .right, 605), some (1, .right, 707)],
  [some (0, .right, 339), some (1, .right, 340)],
  [some (0, .right, 553), some (1, .right, 126)],
  [some (0, .right, 342), some (1, .right, 524)],
  [some (0, .right, 343), some (1, .right, 526)],
  [some (0, .right, 344), some (1, .right, 669)],
  [some (0, .right, 341), some (1, .right, 345)],
  [some (0, .right, 336), some (1, .right, 346)],
  [some (0, .right, 726), some (1, .right, 526)],
  [some (0, .right, 348), some (1, .right, 614)],
  [some (0, .right, 546), some (1, .right, 101)],
  [some (0, .right, 350), some (1, .right, 524)],
  [some (0, .right, 735), some (1, .right, 351)],
  [some (0, .right, 352), some (1, .right, 679)],
  [some (0, .right, 349), some (1, .right, 353)],
  [some (0, .right, 738), some (1, .right, 338)],
  [some (0, .right, 545), some (1, .right, 644)],
  [some (0, .right, 543), some (1, .right, 525)],
  [some (0, .right, 356), some (1, .right, 357)],
  [some (0, .right, 698), some (1, .right, 358)],
  [some (0, .right, 355), some (1, .right, 359)],
  [some (0, .right, 44), some (1, .right, 525)],
  [some (0, .right, 361), some (1, .right, 524)],
  [some (0, .right, 362), some (1, .right, 570)],
  [some (0, .right, 702), some (1, .right, 526)],
  [some (0, .right, 363), some (1, .right, 364)],
  [some (0, .right, 360), some (1, .right, 365)],
  [some (0, .right, 354), some (1, .right, 366)],
  [some (0, .right, 347), some (1, .right, 367)],
  [some (0, .right, 329), some (1, .right, 368)],
  [some (0, .right, 288), some (1, .right, 369)],
  [some (0, .right, 287), some (1, .right, 370)],
  [some (0, .right, 545), some (1, .right, 126)],
  [some (0, .right, 372), some (1, .right, 524)],
  [some (0, .right, 685), some (1, .right, 373)],
  [some (0, .right, 576), some (1, .right, 374)],
  [some (0, .right, 209), some (1, .right, 524)],
  [some (0, .right, 685), some (1, .right, 376)],
  [some (0, .right, 572), some (1, .right, 377)],
  [some (0, .right, 375), some (1, .right, 378)],
  [some (0, .right, 570), some (1, .right, 702)],
  [some (0, .right, 380), some (1, .right, 612)],
  [some (0, .right, 690), some (1, .right, 250)],
  [some (0, .right, 382), some (1, .right, 610)],
  [some (0, .right, 381), some (1, .right, 383)],
  [some (0, .right, 379), some (1, .right, 384)],
  [some (0, .right, 245), some (1, .right, 524)],
  [some (0, .right, 690), some (1, .right, 386)],
  [some (0, .right, 578), some (1, .right, 704)],
  [some (0, .right, 387), some (1, .right, 388)],
  [some (0, .right, 583), some (1, .right, 595)],
  [some (0, .right, 557), some (1, .right, 525)],
  [some (0, .right, 391), some (1, .right, 524)],
  [some (0, .right, 392), some (1, .right, 616)],
  [some (0, .right, 390), some (1, .right, 393)],
  [some (0, .right, 389), some (1, .right, 394)],
  [some (0, .right, 295), some (1, .right, 526)],
  [some (0, .right, 396), some (1, .right, 621)],
  [some (0, .right, 722), some (1, .right, 526)],
  [some (0, .right, 398), some (1, .right, 676)],
  [some (0, .right, 397), some (1, .right, 399)],
  [some (0, .right, 395), some (1, .right, 400)],
  [some (0, .right, 385), some (1, .right, 401)],
  [some (0, .right, 543), some (1, .right, 80)],
  [some (0, .right, 356), some (1, .right, 403)],
  [some (0, .right, 696), some (1, .right, 404)],
  [some (0, .right, 133), some (1, .right, 543)],
  [some (0, .right, 105), some (1, .right, 525)],
  [some (0, .right, 406), some (1, .right, 407)],
  [some (0, .right, 408), some (1, .right, 700)],
  [some (0, .right, 405), some (1, .right, 409)],
  [some (0, .right, 61), some (1, .right, 525)],
  [some (0, .right, 411), some (1, .right, 524)],
  [some (0, .right, 412), some (1, .right, 718)],
  [some (0, .right, 413), some (1, .right, 588)],
  [some (0, .right, 410), some (1, .right, 414)],
  [some (0, .right, 543), some (1, .right, 101)],
  [some (0, .right, 416), some (1, .right, 524)],
  [some (0, .right, 687), some (1, .right, 417)],
  [some (0, .right, 418), some (1, .right, 623)],
  [some (0, .right, 133), some (1, .right, 525)],
  [some (0, .right, 420), some (1, .right, 524)],
  [some (0, .right, 691), some (1, .right, 421)],
  [some (0, .right, 422), some (1, .right, 603)],
  [some (0, .right, 419), some (1, .right, 423)],
  [some (0, .right, 415), some (1, .right, 424)],
  [some (0, .right, 706), some (1, .right, 583)],
  [some (0, .right, 719), some (1, .right, 526)],
  [some (0, .right, 426), some (1, .right, 427)],
  [some (0, .right, 543), some (1, .right, 122)],
  [some (0, .right, 429), some (1, .right, 524)],
  [some (0, .right, 688), some (1, .right, 430)],
  [some (0, .right, 597), some (1, .right, 431)],
  [some (0, .right, 428), some (1, .right, 432)],
  [some (0, .right, 691), some (1, .right, 322)],
  [some (0, .right, 623), some (1, .right, 434)],
  [some (0, .right, 595), some (1, .right, 720)],
  [some (0, .right, 553), some (1, .right, 178)],
  [some (0, .right, 437), some (1, .right, 524)],
  [some (0, .right, 438), some (1, .right, 526)],
  [some (0, .right, 436), some (1, .right, 439)],
  [some (0, .right, 435), some (1, .right, 440)],
  [some (0, .right, 433), some (1, .right, 441)],
  [some (0, .right, 425), some (1, .right, 442)],
  [some (0, .right, 402), some (1, .right, 443)],
  [some (0, .right, 543), some (1, .right, 126)],
  [some (0, .right, 445), some (1, .right, 524)],
  [some (0, .right, 687), some (1, .right, 446)],
  [some (0, .right, 588), some (1, .right, 447)],
  [some (0, .right, 687), some (1, .right, 376)],
  [some (0, .right, 593), some (1, .right, 449)],
  [some (0, .right, 448), some (1, .right, 450)],
  [some (0, .right, 583), some (1, .right, 719)],
  [some (0, .right, 452), some (1, .right, 585)],
  [some (0, .right, 730), some (1, .right, 333)],
  [some (0, .right, 454), some (1, .right, 591)],
  [some (0, .right, 453), some (1, .right, 455)],
  [some (0, .right, 451), some (1, .right, 456)],
  [some (0, .right, 148), some (1, .right, 543)],
  [some (0, .right, 101), some (1, .right, 525)],
  [some (0, .right, 458), some (1, .right, 459)],
  [some (0, .right, 730), some (1, .right, 460)],
  [some (0, .right, 461), some (1, .right, 676)],
  [some (0, .right, 146), some (1, .right, 525)],
  [some (0, .right, 463), some (1, .right, 524)],
  [some (0, .right, 696), some (1, .right, 464)],
  [some (0, .right, 465), some (1, .right, 452)],
  [some (0, .right, 462), some (1, .right, 466)],
  [some (0, .right, 543), some (1, .right, 64)],
  [some (0, .right, 468), some (1, .right, 524)],
  [some (0, .right, 688), some (1, .right, 469)],
  [some (0, .right, 597), some (1, .right, 470)],
  [some (0, .right, 688), some (1, .right, 362)],
  [some (0, .right, 599), some (1, .right, 472)],
  [some (0, .right, 471), some (1, .right, 473)],
  [some (0, .right, 467), some (1, .right, 474)],
  [some (0, .right, 457), some (1, .right, 475)],
  [some (0, .right, 436), some (1, .right, 597)],
  [some (0, .right, 688), some (1, .right, 417)],
  [some (0, .right, 478), some (1, .right, 599)],
  [some (0, .right, 477), some (1, .right, 479)],
  [some (0, .right, 688), some (1, .right, 338)],
  [some (0, .right, 481), some (1, .right, 436)],
  [some (0, .right, 685), some (1, .right, 430)],
  [some (0, .right, 572), some (1, .right, 483)],
  [some (0, .right, 482), some (1, .right, 484)],
  [some (0, .right, 480), some (1, .right, 485)],
  [some (0, .right, 158), some (1, .right, 525)],
  [some (0, .right, 487), some (1, .right, 524)],
  [some (0, .right, 688), some (1, .right, 488)],
  [some (0, .right, 599), some (1, .right, 489)],
  [some (0, .right, 729), some (1, .right, 317)],
  [some (0, .right, 581), some (1, .right, 491)],
  [some (0, .right, 490), some (1, .right, 492)],
  [some (0, .right, 115), some (1, .right, 543)],
  [some (0, .right, 156), some (1, .right, 545)],
  [some (0, .right, 494), some (1, .right, 495)],
  [some (0, .right, 730), some (1, .right, 496)],
  [some (0, .right, 591), some (1, .right, 497)],
  [some (0, .right, 174), some (1, .right, 73)],
  [some (0, .right, 545), some (1, .right, 89)],
  [some (0, .right, 499), some (1, .right, 500)],
  [some (0, .right, 501), some (1, .right, 718)],
  [some (0, .right, 36), some (1, .right, 525)],
  [some (0, .right, 503), some (1, .right, 524)],
  [some (0, .right, 504), some (1, .right, 700)],
  [some (0, .right, 502), some (1, .right, 505)],
  [some (0, .right, 498), some (1, .right, 506)],
  [some (0, .right, 493), some (1, .right, 507)],
  [some (0, .right, 486), some (1, .right, 508)],
  [some (0, .right, 476), some (1, .right, 509)],
  [some (0, .right, 444), some (1, .right, 510)],
  [some (0, .right, 89), some (1, .right, 635)],
  [some (0, .right, 89), none],
  [some (0, .right, 512), some (1, .right, 513)],
  [some (0, .right, 514), some (1, .right, 526)],
  [some (0, .right, 515), some (1, .right, 527)],
  [some (0, .right, 516), some (1, .right, 528)],
  [some (0, .right, 517), some (1, .right, 529)],
  [some (0, .right, 518), some (1, .right, 530)],
  [some (0, .right, 519), some (1, .right, 531)],
  [some (0, .right, 520), some (1, .right, 532)],
  [some (0, .right, 511), some (1, .right, 521)],
  [some (0, .right, 371), some (1, .right, 522)],
  [some (0, .left, 11), some (1, .left, 11)],
  [some (0, .left, 9), some (1, .left, 9)],
  [some (0, .left, 15), some (1, .left, 15)],
  [some (0, .left, 17), some (1, .left, 17)],
  [some (0, .left, 19), some (1, .left, 19)],
  [some (0, .left, 21), some (1, .left, 21)],
  [some (0, .left, 23), some (1, .left, 23)],
  [some (0, .left, 25), some (1, .left, 25)],
  [some (0, .left, 27), some (1, .left, 27)],
  [some (0, .right, 2), some (1, .right, 533)],
  [some (0, .right, 533), some (1, .right, 534)],
  [some (0, .right, 534), some (1, .right, 535)],
  [some (0, .right, 549), some (1, .right, 536)],
  [some (0, .right, 536), some (1, .right, 537)],
  [some (0, .right, 537), some (1, .right, 538)],
  [some (0, .right, 538), some (1, .right, 539)],
  [some (0, .right, 539), some (1, .right, 540)],
  [some (0, .right, 540), some (1, .right, 541)],
  [some (0, .right, 535), some (1, .right, 542)],
  [some (0, .right, 542), some (1, .right, 543)],
  [some (0, .right, 543), some (1, .right, 544)],
  [some (0, .right, 544), some (1, .right, 545)],
  [some (0, .right, 545), some (1, .right, 546)],
  [some (0, .right, 546), some (1, .right, 547)],
  [some (0, .right, 547), some (1, .right, 548)],
  [some (0, .right, 548), some (1, .right, 549)],
  [some (0, .right, 31), some (1, .right, 550)],
  [some (0, .right, 550), some (1, .right, 551)],
  [some (0, .right, 564), some (1, .right, 552)],
  [some (0, .right, 552), some (1, .right, 553)],
  [some (0, .right, 553), some (1, .right, 554)],
  [some (0, .right, 554), some (1, .right, 555)],
  [some (0, .right, 555), some (1, .right, 556)],
  [some (0, .right, 556), some (1, .right, 557)],
  [some (0, .right, 188), some (1, .right, 558)],
  [some (0, .right, 648), some (1, .right, 559)],
  [some (0, .right, 559), some (1, .right, 560)],
  [some (0, .right, 560), some (1, .right, 561)],
  [some (0, .right, 561), some (1, .right, 562)],
  [some (0, .right, 562), some (1, .right, 563)],
  [some (0, .right, 563), some (1, .right, 564)],
  [some (0, .left, 9), some (1, .left, 566)],
  [some (0, .left, 565), some (1, .left, 566)],
  [some (0, .left, 524), some (1, .left, 568)],
  [some (0, .left, 567), some (1, .left, 568)],
  [some (0, .right, 538), some (1, .right, 635)],
  [some (0, .right, 569), some (1, .right, 638)],
  [some (0, .right, 573), some (1, .right, 653)],
  [some (0, .right, 571), some (1, .right, 651)],
  [some (0, .right, 538), some (1, .right, 644)],
  [some (0, .right, 560), some (1, .right, 558)],
  [some (0, .right, 573), some (1, .right, 574)],
  [some (0, .right, 575), some (1, .right, 651)],
  [some (0, .right, 539), some (1, .right, 635)],
  [some (0, .right, 577), some (1, .right, 638)],
  [some (0, .right, 539), some (1, .right, 644)],
  [some (0, .right, 579), some (1, .right, 672)],
  [some (0, .right, 580), some (1, .right, 651)],
  [some (0, .right, 540), some (1, .right, 635)],
  [some (0, .right, 582), some (1, .right, 638)],
  [some (0, .right, 586), some (1, .right, 672)],
  [some (0, .right, 584), some (1, .right, 651)],
  [some (0, .right, 540), some (1, .right, 644)],
  [some (0, .right, 586), some (1, .right, 653)],
  [some (0, .right, 587), some (1, .right, 651)],
  [some (0, .right, 648), some (1, .right, 561)],
  [some (0, .right, 586), some (1, .right, 589)],
  [some (0, .right, 590), some (1, .right, 651)],
  [some (0, .right, 586), some (1, .right, 574)],
  [some (0, .right, 592), some (1, .right, 651)],
  [some (0, .right, 541), some (1, .right, 635)],
  [some (0, .right, 594), some (1, .right, 638)],
  [some (0, .right, 600), some (1, .right, 653)],
  [some (0, .right, 596), some (1, .right, 651)],
  [some (0, .right, 600), some (1, .right, 574)],
  [some (0, .right, 598), some (1, .right, 651)],
  [some (0, .right, 541), some (1, .right, 644)],
  [some (0, .right, 560), some (1, .right, 648)],
  [some (0, .right, 600), some (1, .right, 601)],
  [some (0, .right, 602), some (1, .right, 651)],
  [some (0, .right, 536), some (1, .right, 635)],
  [some (0, .right, 604), some (1, .right, 638)],
  [some (0, .right, 608), some (1, .right, 667)],
  [some (0, .right, 606), some (1, .right, 651)],
  [some (0, .right, 536), some (1, .right, 644)],
  [some (0, .right, 608), some (1, .right, 653)],
  [some (0, .right, 609), some (1, .right, 651)],
  [some (0, .right, 608), some (1, .right, 574)],
  [some (0, .right, 611), some (1, .right, 651)],
  [some (0, .right, 608), some (1, .right, 562)],
  [some (0, .right, 613), some (1, .right, 651)],
  [some (0, .right, 537), some (1, .right, 635)],
  [some (0, .right, 615), some (1, .right, 638)],
  [some (0, .right, 537), some (1, .right, 644)],
  [some (0, .right, 617), some (1, .right, 648)],
  [some (0, .right, 618), some (1, .right, 651)],
  [some (0, .right, 617), some (1, .right, 656)],
  [some (0, .right, 620), some (1, .right, 651)],
  [some (0, .right, 617), some (1, .right, 574)],
  [some (0, .right, 622), some (1, .right, 651)],
  [some (0, .right, 544), some (1, .right, 635)],
  [some (0, .right, 624), some (1, .right, 638)],
  [some (0, .right, 648), some (1, .right, 562)],
  [some (0, .right, 629), some (1, .right, 626)],
  [some (0, .right, 627), some (1, .right, 651)],
  [some (0, .right, 544), some (1, .right, 644)],
  [some (0, .right, 629), some (1, .right, 563)],
  [some (0, .right, 630), some (1, .right, 651)],
  [some (0, .left, 633), some (1, .left, 633)],
  [some (0, .left, 634), some (0, .left, 634)],
  [some (0, .left, 14), some (0, .left, 14)],
  [some (0, .left, 636), some (1, .left, 636)],
  [some (1, .left, 11), some (1, .left, 11)],
  [some (0, .right, 534), some (1, .right, 635)],
  [some (0, .right, 632), some (1, .right, 525)],
  [some (0, .right, 637), some (1, .right, 638)],
  [some (0, .left, 641), some (1, .left, 641)],
  [some (0, .left, 642), some (0, .left, 642)],
  [some (0, .left, 643), some (0, .left, 643)],
  [some (0, .left, 16), some (0, .left, 16)],
  [some (0, .left, 645), some (1, .left, 645)],
  [some (1, .left, 646), some (1, .left, 646)],
  [some (0, .left, 15), some (0, .left, 15)],
  [some (0, .right, 534), some (1, .right, 644)],
  [some (0, .right, 558), some (1, .right, 648)],
  [some (0, .right, 647), some (1, .right, 648)],
  [some (0, .right, 640), some (1, .right, 525)],
  [some (0, .right, 650), some (1, .right, 524)],
  [some (0, .right, 649), some (1, .right, 651)],
  [some (0, .right, 648), some (1, .right, 558)],
  [some (0, .right, 647), some (1, .right, 653)],
  [some (0, .right, 654), some (1, .right, 651)],
  [some (0, .right, 648), some (1, .right, 560)],
  [some (0, .right, 647), some (1, .right, 656)],
  [some (0, .right, 657), some (1, .right, 651)],
  [some (0, .right, 561), some (1, .right, 563)],
  [some (0, .right, 647), some (1, .right, 659)],
  [some (0, .right, 660), some (1, .right, 651)],
  [some (0, .right, 647), some (1, .right, 563)],
  [some (0, .right, 662), some (1, .right, 651)],
  [some (0, .right, 549), some (1, .right, 635)],
  [some (0, .right, 664), some (1, .right, 638)],
  [some (0, .right, 549), some (1, .right, 644)],
  [some (0, .right, 558), some (1, .right, 560)],
  [some (0, .right, 666), some (1, .right, 667)],
  [some (0, .right, 668), some (1, .right, 651)],
  [some (0, .right, 680), some (1, .right, 648)],
  [some (0, .right, 670), some (1, .right, 651)],
  [some (0, .right, 558), some (1, .right, 561)],
  [some (0, .right, 680), some (1, .right, 672)],
  [some (0, .right, 673), some (1, .right, 651)],
  [some (0, .right, 680), some (1, .right, 574)],
  [some (0, .right, 675), some (1, .right, 651)],
  [some (0, .right, 560), some (1, .right, 562)],
  [some (0, .right, 680), some (1, .right, 677)],
  [some (0, .right, 678), some (1, .right, 651)],
  [some (0, .right, 535), some (1, .right, 644)],
  [some (0, .right, 680), some (1, .right, 659)],
  [some (0, .right, 681), some (1, .right, 651)],
  [some (0, .right, 542), some (1, .right, 635)],
  [some (0, .right, 683), some (1, .right, 638)],
  [some (0, .right, 692), some (1, .right, 701)],
  [some (0, .right, 556), some (1, .right, 632)],
  [some (0, .right, 692), some (1, .right, 686)],
  [some (0, .right, 692), some (1, .right, 705)],
  [some (0, .right, 552), some (1, .right, 632)],
  [some (0, .right, 692), some (1, .right, 689)],
  [some (0, .right, 692), some (1, .right, 708)],
  [some (0, .right, 542), some (1, .right, 710)],
  [some (0, .right, 559), some (1, .right, 632)],
  [some (0, .right, 692), some (1, .right, 693)],
  [some (0, .right, 692), some (1, .right, 713)],
  [some (0, .right, 692), some (1, .right, 742)],
  [some (0, .right, 648), some (1, .right, 632)],
  [some (0, .right, 692), some (1, .right, 697)],
  [some (0, .right, 543), some (1, .right, 635)],
  [some (0, .right, 699), some (1, .right, 638)],
  [some (0, .right, 554), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 701)],
  [some (0, .right, 555), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 703)],
  [some (0, .right, 557), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 705)],
  [some (0, .right, 712), some (1, .right, 689)],
  [some (0, .right, 553), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 708)],
  [some (0, .left, 711), some (1, .left, 711)],
  [some (0, .left, 646), some (0, .left, 646)],
  [some (0, .right, 543), some (1, .right, 710)],
  [some (0, .right, 551), some (1, .right, 632)],
  [some (0, .right, 712), some (1, .right, 713)],
  [some (0, .right, 712), some (1, .right, 725)],
  [some (0, .right, 712), some (1, .right, 742)],
  [some (0, .right, 545), some (1, .right, 635)],
  [some (0, .right, 717), some (1, .right, 638)],
  [some (0, .right, 723), some (1, .right, 686)],
  [some (0, .right, 723), some (1, .right, 705)],
  [some (0, .right, 723), some (1, .right, 689)],
  [some (0, .right, 723), some (1, .right, 708)],
  [some (0, .right, 545), some (1, .right, 710)],
  [some (0, .right, 723), some (1, .right, 713)],
  [some (0, .right, 564), some (1, .right, 632)],
  [some (0, .right, 723), some (1, .right, 725)],
  [some (0, .right, 546), some (1, .right, 635)],
  [some (0, .right, 727), some (1, .right, 638)],
  [some (0, .right, 731), some (1, .right, 703)],
  [some (0, .right, 731), some (1, .right, 686)],
  [some (0, .right, 546), some (1, .right, 710)],
  [some (0, .right, 731), some (1, .right, 742)],
  [some (0, .right, 547), some (1, .right, 635)],
  [some (0, .right, 733), some (1, .right, 638)],
  [some (0, .right, 736), some (1, .right, 689)],
  [some (0, .right, 547), some (1, .right, 710)],
  [some (0, .right, 736), some (1, .right, 693)],
  [some (0, .right, 736), some (1, .right, 742)],
  [some (0, .right, 740), some (1, .right, 693)],
  [some (0, .right, 548), some (1, .right, 710)],
  [some (0, .right, 740), some (1, .right, 713)],
  [some (0, .right, 188), some (1, .right, 632)],
  [some (0, .right, 740), some (1, .right, 742)]]
def candRows : List (List (Option (Fin 2 × Dir × Fin 543))) := [
  [some (0, .right, 235), some (1, .right, 353)],
  [some (0, .left, 31), some (1, .right, 4)],
  [some (0, .right, 1), some (0, .right, 1)],
  [some (0, .left, 5), some (1, .right, 4)],
  [some (0, .right, 3), some (1, .right, 4)],
  [some (0, .left, 6), some (0, .left, 20)],
  [some (0, .left, 385), some (0, .left, 7)],
  [some (1, .left, 6), some (1, .left, 7)],
  [some (1, .left, 9), some (0, .left, 10)],
  [some (0, .left, 12), some (1, .left, 12)],
  [some (1, .left, 12), some (0, .left, 13)],
  [some (1, .right, 353), some (0, .right, 235)],
  [some (0, .left, 14), some (1, .left, 14)],
  [some (1, .left, 14), some (0, .left, 15)],
  [some (0, .left, 16), some (1, .left, 16)],
  [some (1, .left, 16), some (0, .left, 17)],
  [some (0, .left, 18), some (1, .left, 18)],
  [some (1, .left, 18), some (0, .left, 19)],
  [some (0, .left, 20), some (1, .left, 20)],
  [some (1, .left, 20), some (0, .left, 21)],
  [some (0, .left, 22), some (1, .left, 22)],
  [some (1, .left, 22), some (0, .left, 23)],
  [some (0, .left, 24), some (1, .left, 24)],
  [some (1, .left, 24), some (0, .left, 25)],
  [some (0, .left, 26), some (1, .left, 26)],
  [some (1, .left, 26), some (0, .left, 27)],
  [some (0, .left, 0), some (1, .left, 0)],
  [some (1, .left, 0), some (0, .left, 11)],
  [some (0, .left, 383), some (0, .right, 29)],
  [some (1, .right, 28), some (1, .right, 29)],
  [some (0, .right, 32), some (0, .left, 63)],
  [some (1, .left, 384), some (1, .right, 32)],
  [some (0, .right, 31), some (1, .right, 32)],
  [some (0, .left, 34), some (0, .left, 24)],
  [some (1, .left, 38), some (0, .left, 38)],
  [some (0, .left, 36), some (0, .left, 61)],
  [some (0, .left, 37), some (0, .left, 14)],
  [some (1, .left, 38), some (1, .left, 38)],
  [some (1, .left, 39), some (1, .left, 39)],
  [some (1, .left, 21), none],
  [some (1, .left, 33), some (0, .left, 64)],
  [some (0, .left, 42), some (0, .left, 61)],
  [some (1, .left, 43), some (1, .left, 43)],
  [some (0, .left, 17), some (1, .left, 17)],
  [some (0, .left, 96), some (1, .left, 33)],
  [some (0, .left, 66), some (1, .left, 66)],
  [some (0, .left, 15), some (1, .left, 45)],
  [some (0, .left, 46), some (0, .left, 42)],
  [some (0, .left, 49), some (0, .left, 49)],
  [some (0, .right, 235), some (0, .right, 235)],
  [some (0, .left, 51), some (0, .left, 51)],
  [some (1, .left, 52), some (1, .left, 52)],
  [some (0, .left, 53), some (0, .left, 53)],
  [some (1, .left, 54), some (1, .left, 54)],
  [some (0, .left, 55), some (0, .left, 55)],
  [some (0, .left, 56), some (0, .left, 56)],
  [some (0, .left, 57), some (0, .left, 57)],
  [some (0, .left, 48), some (0, .left, 48)],
  [some (0, .left, 59), some (0, .left, 12)],
  [some (1, .left, 59), some (1, .left, 30)],
  [some (0, .left, 13), some (1, .left, 61)],
  [some (0, .left, 43), some (0, .left, 43)],
  [some (1, .left, 66), some (0, .left, 16)],
  [some (0, .left, 33), some (1, .left, 55)],
  [some (1, .left, 65), some (0, .left, 287)],
  [some (1, .left, 3), some (0, .left, 66)],
  [some (1, .left, 67), some (0, .left, 18)],
  [some (1, .left, 68), some (0, .left, 20)],
  [some (1, .left, 33), some (0, .left, 22)],
  [some (0, .left, 70), some (1, .left, 13)],
  [some (1, .left, 62), some (0, .left, 45)],
  [some (0, .right, 30), some (1, .right, 30)],
  [some (0, .right, 71), some (1, .right, 71)],
  [some (0, .right, 72), some (1, .right, 72)],
  [some (0, .right, 73), some (1, .right, 73)],
  [some (0, .right, 371), some (1, .right, 75)],
  [some (0, .right, 75), some (0, .left, 13)],
  [some (0, .right, 453), some (1, .right, 76)],
  [some (0, .right, 77), some (1, .right, 458)],
  [some (0, .right, 74), some (1, .right, 78)],
  [some (0, .right, 513), some (1, .right, 443)],
  [some (0, .right, 499), some (0, .left, 15)],
  [some (0, .right, 80), some (1, .right, 81)],
  [some (0, .right, 513), some (0, .left, 15)],
  [some (0, .right, 458), some (1, .right, 83)],
  [some (0, .right, 82), some (1, .right, 84)],
  [some (0, .right, 79), some (1, .right, 85)],
  [some (0, .right, 540), some (0, .left, 15)],
  [some (0, .right, 467), some (1, .right, 87)],
  [some (0, .right, 367), some (1, .left, 454)],
  [some (0, .right, 366), some (1, .left, 454)],
  [some (0, .right, 89), some (1, .right, 90)],
  [some (0, .right, 538), some (1, .right, 91)],
  [some (0, .right, 449), some (1, .right, 92)],
  [some (0, .right, 88), some (1, .right, 93)],
  [some (0, .left, 69), some (1, .right, 378)],
  [some (0, .left, 40), some (0, .left, 10)],
  [some (0, .right, 95), some (1, .right, 96)],
  [some (0, .right, 97), some (1, .right, 533)],
  [some (0, .right, 365), some (1, .left, 41)],
  [some (0, .right, 99), some (0, .left, 13)],
  [some (0, .right, 100), some (0, .left, 15)],
  [some (0, .right, 98), some (1, .right, 101)],
  [some (0, .left, 69), some (1, .right, 363)],
  [some (0, .left, 69), some (1, .right, 362)],
  [some (0, .right, 103), some (1, .right, 104)],
  [some (0, .right, 536), some (1, .right, 105)],
  [some (0, .right, 446), some (1, .right, 106)],
  [some (0, .right, 102), some (1, .right, 107)],
  [some (0, .right, 94), some (1, .right, 108)],
  [some (0, .right, 86), some (1, .right, 109)],
  [some (1, .left, 47), some (1, .left, 69)],
  [some (0, .right, 362), some (1, .left, 41)],
  [some (0, .right, 111), some (1, .right, 112)],
  [some (0, .right, 113), some (1, .right, 490)],
  [some (0, .left, 35), some (0, .left, 10)],
  [some (0, .right, 115), some (0, .left, 13)],
  [some (0, .right, 116), some (1, .right, 505)],
  [some (0, .right, 114), some (1, .right, 117)],
  [some (0, .right, 116), some (0, .left, 15)],
  [some (0, .right, 119), some (1, .right, 461)],
  [some (0, .right, 118), some (1, .right, 120)],
  [some (0, .right, 500), some (0, .left, 15)],
  [some (0, .right, 122), some (1, .right, 469)],
  [some (0, .right, 87), some (1, .right, 488)],
  [some (0, .right, 123), some (1, .right, 124)],
  [some (0, .right, 121), some (1, .right, 125)],
  [some (0, .right, 90), some (1, .right, 89)],
  [some (0, .right, 542), some (1, .right, 127)],
  [some (0, .right, 97), some (1, .right, 527)],
  [some (0, .right, 128), some (1, .right, 129)],
  [some (0, .right, 101), some (1, .right, 480)],
  [some (0, .right, 130), some (1, .right, 131)],
  [some (0, .right, 104), some (1, .right, 103)],
  [some (0, .right, 531), some (1, .right, 133)],
  [some (0, .right, 363), some (0, .left, 60)],
  [some (0, .right, 111), some (1, .right, 135)],
  [some (0, .right, 136), some (1, .right, 505)],
  [some (0, .right, 134), some (1, .right, 137)],
  [some (0, .left, 47), some (0, .left, 10)],
  [some (0, .right, 139), some (0, .left, 13)],
  [some (0, .right, 140), some (1, .right, 490)],
  [some (0, .right, 371), some (0, .left, 58)],
  [some (0, .right, 142), some (0, .left, 13)],
  [some (0, .right, 143), some (0, .left, 15)],
  [some (0, .right, 141), some (1, .right, 144)],
  [some (0, .right, 138), some (1, .right, 145)],
  [some (0, .right, 132), some (1, .right, 146)],
  [some (0, .right, 126), some (1, .right, 147)],
  [some (0, .right, 110), some (1, .right, 148)],
  [some (0, .right, 362), some (1, .left, 50)],
  [some (0, .right, 150), some (1, .right, 150)],
  [some (0, .right, 515), some (1, .right, 151)],
  [some (0, .right, 477), some (1, .right, 152)],
  [some (0, .right, 151), some (1, .right, 151)],
  [some (0, .right, 154), some (1, .right, 154)],
  [some (0, .right, 153), some (1, .right, 155)],
  [some (0, .right, 155), some (1, .right, 155)],
  [some (0, .right, 156), some (1, .right, 157)],
  [some (0, .right, 157), some (1, .right, 157)],
  [some (0, .right, 158), some (1, .right, 159)],
  [some (0, .right, 159), some (1, .right, 159)],
  [some (0, .right, 160), some (1, .right, 161)],
  [some (0, .right, 149), some (1, .right, 162)],
  [some (0, .right, 161), some (1, .right, 161)],
  [some (0, .right, 490), some (1, .right, 471)],
  [some (0, .right, 154), some (1, .right, 165)],
  [some (0, .right, 372), some (0, .left, 450)],
  [some (0, .right, 167), some (0, .left, 13)],
  [some (0, .right, 423), some (1, .right, 168)],
  [some (0, .right, 373), some (0, .left, 450)],
  [some (0, .right, 170), some (0, .left, 13)],
  [some (0, .right, 434), some (1, .right, 171)],
  [some (0, .right, 169), some (1, .right, 172)],
  [some (0, .right, 166), some (1, .right, 173)],
  [some (0, .right, 512), some (0, .left, 15)],
  [some (0, .right, 437), some (1, .right, 175)],
  [some (0, .right, 363), some (1, .left, 454)],
  [some (0, .right, 177), some (1, .right, 112)],
  [some (0, .right, 523), some (1, .right, 178)],
  [some (0, .right, 464), some (1, .right, 179)],
  [some (0, .right, 176), some (1, .right, 180)],
  [some (0, .right, 174), some (1, .right, 181)],
  [some (0, .right, 104), some (1, .right, 115)],
  [some (0, .right, 183), some (1, .right, 490)],
  [some (0, .right, 96), some (0, .left, 13)],
  [some (0, .right, 185), some (1, .right, 505)],
  [some (0, .right, 184), some (1, .right, 186)],
  [some (0, .right, 112), some (0, .left, 13)],
  [some (0, .right, 525), some (1, .right, 188)],
  [some (0, .right, 475), some (1, .right, 189)],
  [some (0, .right, 187), some (1, .right, 190)],
  [some (0, .right, 521), some (1, .right, 140)],
  [some (0, .right, 439), some (1, .right, 192)],
  [some (0, .right, 495), some (1, .right, 471)],
  [some (0, .right, 428), some (1, .right, 194)],
  [some (0, .right, 193), some (1, .right, 195)],
  [some (0, .right, 191), some (1, .right, 196)],
  [some (0, .right, 182), some (1, .right, 197)],
  [some (0, .right, 514), some (0, .left, 15)],
  [some (0, .right, 199), some (1, .right, 425)],
  [some (0, .right, 520), some (1, .right, 188)],
  [some (0, .right, 201), some (1, .right, 439)],
  [some (0, .right, 200), some (1, .right, 202)],
  [some (0, .right, 423), some (1, .right, 511)],
  [some (0, .right, 192), some (1, .right, 204)],
  [some (0, .right, 373), some (1, .left, 58)],
  [some (0, .right, 206), some (0, .left, 13)],
  [some (0, .right, 207), some (0, .left, 15)],
  [some (0, .right, 208), some (1, .right, 475)],
  [some (0, .right, 205), some (1, .right, 209)],
  [some (0, .right, 203), some (1, .right, 210)],
  [some (0, .right, 525), some (0, .left, 15)],
  [some (0, .right, 212), some (1, .right, 432)],
  [some (0, .right, 366), some (1, .left, 41)],
  [some (0, .right, 214), some (0, .left, 13)],
  [some (0, .right, 534), some (1, .right, 215)],
  [some (0, .right, 216), some (1, .right, 485)],
  [some (0, .right, 213), some (1, .right, 217)],
  [some (0, .right, 537), some (1, .right, 140)],
  [some (0, .right, 365), some (1, .left, 454)],
  [some (0, .right, 363), some (0, .left, 10)],
  [some (0, .right, 220), some (1, .right, 221)],
  [some (0, .right, 503), some (1, .right, 222)],
  [some (0, .right, 219), some (1, .right, 223)],
  [some (0, .left, 69), some (0, .left, 10)],
  [some (0, .right, 225), some (0, .left, 13)],
  [some (0, .right, 226), some (1, .right, 388)],
  [some (0, .right, 507), some (0, .left, 15)],
  [some (0, .right, 227), some (1, .right, 228)],
  [some (0, .right, 224), some (1, .right, 229)],
  [some (0, .right, 218), some (1, .right, 230)],
  [some (0, .right, 211), some (1, .right, 231)],
  [some (0, .right, 198), some (1, .right, 232)],
  [some (0, .right, 164), some (1, .right, 233)],
  [some (0, .right, 163), some (1, .right, 234)],
  [some (0, .right, 491), some (1, .right, 100)],
  [some (0, .right, 394), some (1, .right, 236)],
  [some (0, .right, 491), some (1, .right, 140)],
  [some (0, .right, 390), some (1, .right, 238)],
  [some (0, .right, 237), some (1, .right, 239)],
  [some (0, .right, 388), some (1, .right, 507)],
  [some (0, .right, 241), some (1, .right, 430)],
  [some (0, .right, 495), some (1, .right, 100)],
  [some (0, .right, 243), some (1, .right, 428)],
  [some (0, .right, 242), some (1, .right, 244)],
  [some (0, .right, 240), some (1, .right, 245)],
  [some (0, .right, 495), some (1, .right, 140)],
  [some (0, .right, 396), some (1, .right, 509)],
  [some (0, .right, 247), some (1, .right, 248)],
  [some (0, .right, 401), some (1, .right, 413)],
  [some (0, .right, 492), some (0, .left, 450)],
  [some (0, .right, 251), some (0, .left, 13)],
  [some (0, .right, 252), some (1, .right, 434)],
  [some (0, .right, 250), some (1, .right, 253)],
  [some (0, .right, 249), some (1, .right, 254)],
  [some (0, .right, 171), some (0, .left, 15)],
  [some (0, .right, 256), some (1, .right, 439)],
  [some (0, .right, 521), some (0, .left, 15)],
  [some (0, .right, 258), some (1, .right, 482)],
  [some (0, .right, 257), some (1, .right, 259)],
  [some (0, .right, 255), some (1, .right, 260)],
  [some (0, .right, 246), some (1, .right, 261)],
  [some (0, .right, 363), some (1, .left, 41)],
  [some (0, .right, 220), some (1, .right, 263)],
  [some (0, .right, 501), some (1, .right, 264)],
  [some (0, .right, 103), some (1, .right, 115)],
  [some (0, .right, 266), some (1, .right, 505)],
  [some (0, .right, 265), some (1, .right, 267)],
  [some (0, .right, 185), some (1, .right, 517)],
  [some (0, .right, 269), some (1, .right, 406)],
  [some (0, .right, 268), some (1, .right, 270)],
  [some (0, .right, 263), some (0, .left, 13)],
  [some (0, .right, 493), some (1, .right, 272)],
  [some (0, .right, 273), some (1, .right, 441)],
  [some (0, .right, 496), some (1, .right, 140)],
  [some (0, .right, 275), some (1, .right, 421)],
  [some (0, .right, 274), some (1, .right, 276)],
  [some (0, .right, 271), some (1, .right, 277)],
  [some (0, .right, 510), some (1, .right, 401)],
  [some (0, .right, 518), some (0, .left, 15)],
  [some (0, .right, 279), some (1, .right, 280)],
  [some (0, .right, 494), some (1, .right, 272)],
  [some (0, .right, 415), some (1, .right, 282)],
  [some (0, .right, 281), some (1, .right, 283)],
  [some (0, .right, 441), some (1, .right, 275)],
  [some (0, .right, 413), some (1, .right, 519)],
  [some (0, .right, 373), some (1, .left, 44)],
  [some (0, .right, 287), some (0, .left, 13)],
  [some (0, .right, 288), some (0, .left, 15)],
  [some (0, .right, 286), some (1, .right, 289)],
  [some (0, .right, 285), some (1, .right, 290)],
  [some (0, .right, 284), some (1, .right, 291)],
  [some (0, .right, 278), some (1, .right, 292)],
  [some (0, .right, 262), some (1, .right, 293)],
  [some (0, .right, 406), some (1, .right, 273)],
  [some (0, .right, 493), some (1, .right, 140)],
  [some (0, .right, 411), some (1, .right, 296)],
  [some (0, .right, 295), some (1, .right, 297)],
  [some (0, .right, 401), some (1, .right, 518)],
  [some (0, .right, 299), some (1, .right, 403)],
  [some (0, .right, 529), some (1, .right, 188)],
  [some (0, .right, 301), some (1, .right, 409)],
  [some (0, .right, 300), some (1, .right, 302)],
  [some (0, .right, 298), some (1, .right, 303)],
  [some (0, .left, 47), some (1, .right, 363)],
  [some (1, .left, 47), some (0, .left, 10)],
  [some (0, .right, 305), some (1, .right, 306)],
  [some (0, .right, 529), some (1, .right, 307)],
  [some (0, .right, 308), some (1, .right, 482)],
  [some (0, .right, 306), some (0, .left, 13)],
  [some (0, .right, 501), some (1, .right, 310)],
  [some (0, .right, 311), some (1, .right, 299)],
  [some (0, .right, 309), some (1, .right, 312)],
  [some (0, .right, 494), some (1, .right, 140)],
  [some (0, .right, 417), some (1, .right, 314)],
  [some (0, .right, 283), some (1, .right, 315)],
  [some (0, .right, 313), some (1, .right, 316)],
  [some (0, .right, 304), some (1, .right, 317)],
  [some (0, .right, 286), some (1, .right, 415)],
  [some (0, .right, 282), some (1, .right, 417)],
  [some (0, .right, 319), some (1, .right, 320)],
  [some (0, .right, 314), some (1, .right, 286)],
  [some (0, .right, 491), some (1, .right, 272)],
  [some (0, .right, 390), some (1, .right, 323)],
  [some (0, .right, 322), some (1, .right, 324)],
  [some (0, .right, 321), some (1, .right, 325)],
  [some (0, .right, 528), some (1, .right, 188)],
  [some (0, .right, 399), some (1, .right, 327)],
  [some (0, .right, 315), some (1, .right, 328)],
  [some (0, .left, 69), some (1, .right, 365)],
  [some (0, .right, 305), some (1, .right, 330)],
  [some (0, .right, 529), some (1, .right, 331)],
  [some (0, .right, 409), some (1, .right, 332)],
  [some (0, .right, 365), some (1, .left, 50)],
  [some (0, .right, 111), some (1, .right, 334)],
  [some (0, .right, 335), some (1, .right, 517)],
  [some (0, .right, 336), some (1, .right, 117)],
  [some (0, .right, 333), some (1, .right, 337)],
  [some (0, .right, 329), some (1, .right, 338)],
  [some (0, .right, 326), some (1, .right, 339)],
  [some (0, .right, 318), some (1, .right, 340)],
  [some (0, .right, 294), some (1, .right, 341)],
  [some (1, .left, 50), some (1, .left, 10)],
  [some (1, .left, 50), none],
  [some (0, .right, 343), some (1, .right, 344)],
  [some (0, .right, 345), some (0, .left, 15)],
  [some (0, .right, 346), some (0, .left, 17)],
  [some (0, .right, 347), some (0, .left, 19)],
  [some (0, .right, 348), some (0, .left, 21)],
  [some (0, .right, 349), some (0, .left, 23)],
  [some (0, .right, 350), some (0, .left, 25)],
  [some (0, .right, 351), some (0, .left, 27)],
  [some (0, .right, 342), some (1, .right, 352)],
  [some (0, .left, 10), some (1, .left, 10)],
  [some (0, .right, 2), some (1, .right, 355)],
  [some (0, .right, 355), some (1, .right, 356)],
  [some (0, .right, 356), some (1, .right, 357)],
  [some (0, .right, 369), some (1, .right, 358)],
  [some (0, .right, 358), some (1, .right, 359)],
  [some (0, .right, 359), some (1, .right, 360)],
  [some (0, .right, 360), some (1, .right, 361)],
  [some (0, .right, 357), some (1, .right, 362)],
  [some (0, .right, 362), some (1, .right, 363)],
  [some (0, .right, 363), some (1, .right, 364)],
  [some (0, .right, 364), some (1, .right, 365)],
  [some (0, .right, 365), some (1, .right, 366)],
  [some (0, .right, 366), some (1, .right, 367)],
  [some (0, .right, 367), some (1, .right, 368)],
  [some (0, .right, 368), some (1, .right, 369)],
  [some (0, .right, 29), some (1, .right, 370)],
  [some (0, .right, 370), some (1, .right, 371)],
  [some (0, .right, 382), some (1, .right, 372)],
  [some (0, .right, 372), some (1, .right, 373)],
  [some (0, .right, 373), some (1, .right, 374)],
  [some (0, .right, 374), some (1, .right, 375)],
  [some (0, .right, 75), some (1, .right, 376)],
  [some (0, .right, 456), some (1, .right, 377)],
  [some (0, .right, 377), some (1, .right, 378)],
  [some (0, .right, 378), some (1, .right, 379)],
  [some (0, .right, 379), some (1, .right, 380)],
  [some (0, .right, 380), some (1, .right, 381)],
  [some (0, .right, 381), some (1, .right, 382)],
  [some (0, .left, 8), some (1, .left, 384)],
  [some (0, .left, 383), some (1, .left, 384)],
  [some (0, .left, 354), some (1, .left, 386)],
  [some (0, .left, 385), some (1, .left, 386)],
  [some (0, .right, 360), some (1, .left, 10)],
  [some (0, .right, 387), some (1, .right, 452)],
  [some (0, .right, 391), some (1, .right, 459)],
  [some (0, .right, 389), some (1, .right, 116)],
  [some (0, .right, 360), some (1, .left, 454)],
  [some (0, .right, 378), some (1, .right, 376)],
  [some (0, .right, 391), some (1, .right, 392)],
  [some (0, .right, 393), some (1, .right, 116)],
  [some (0, .right, 361), some (1, .left, 10)],
  [some (0, .right, 395), some (1, .right, 452)],
  [some (0, .right, 361), some (1, .left, 454)],
  [some (0, .right, 397), some (1, .right, 478)],
  [some (0, .right, 398), some (1, .right, 116)],
  [some (0, .right, 395), some (1, .left, 10)],
  [some (0, .right, 400), some (1, .right, 452)],
  [some (0, .right, 404), some (1, .right, 478)],
  [some (0, .right, 402), some (1, .right, 116)],
  [some (0, .right, 395), some (1, .left, 454)],
  [some (0, .right, 404), some (1, .right, 459)],
  [some (0, .right, 405), some (1, .right, 116)],
  [some (0, .right, 456), some (1, .right, 379)],
  [some (0, .right, 404), some (1, .right, 407)],
  [some (0, .right, 408), some (1, .right, 116)],
  [some (0, .right, 404), some (1, .right, 392)],
  [some (0, .right, 410), some (1, .right, 116)],
  [some (0, .right, 400), some (1, .left, 10)],
  [some (0, .right, 412), some (1, .right, 452)],
  [some (0, .right, 418), some (1, .right, 459)],
  [some (0, .right, 414), some (1, .right, 116)],
  [some (0, .right, 418), some (1, .right, 392)],
  [some (0, .right, 416), some (1, .right, 116)],
  [some (0, .right, 400), some (1, .left, 454)],
  [some (0, .right, 378), some (1, .right, 456)],
  [some (0, .right, 418), some (1, .right, 419)],
  [some (0, .right, 420), some (1, .right, 116)],
  [some (0, .right, 358), some (1, .left, 10)],
  [some (0, .right, 422), some (1, .right, 452)],
  [some (0, .right, 426), some (1, .right, 473)],
  [some (0, .right, 424), some (1, .right, 116)],
  [some (0, .right, 358), some (1, .left, 454)],
  [some (0, .right, 426), some (1, .right, 459)],
  [some (0, .right, 427), some (1, .right, 116)],
  [some (0, .right, 426), some (1, .right, 392)],
  [some (0, .right, 429), some (1, .right, 116)],
  [some (0, .right, 426), some (1, .right, 380)],
  [some (0, .right, 431), some (1, .right, 116)],
  [some (0, .right, 359), some (1, .left, 10)],
  [some (0, .right, 433), some (1, .right, 452)],
  [some (0, .right, 359), some (1, .left, 454)],
  [some (0, .right, 435), some (1, .right, 456)],
  [some (0, .right, 436), some (1, .right, 116)],
  [some (0, .right, 435), some (1, .right, 462)],
  [some (0, .right, 438), some (1, .right, 116)],
  [some (0, .right, 435), some (1, .right, 392)],
  [some (0, .right, 440), some (1, .right, 116)],
  [some (0, .right, 364), some (1, .left, 10)],
  [some (0, .right, 442), some (1, .right, 452)],
  [some (0, .right, 456), some (1, .right, 380)],
  [some (0, .right, 447), some (1, .right, 444)],
  [some (0, .right, 445), some (1, .right, 116)],
  [some (0, .right, 364), some (1, .left, 454)],
  [some (0, .right, 447), some (1, .right, 381)],
  [some (0, .right, 448), some (1, .right, 116)],
  [some (1, .left, 12), some (0, .left, 12)],
  [some (0, .right, 356), some (1, .left, 10)],
  [some (0, .left, 450), some (0, .left, 10)],
  [some (0, .right, 451), some (1, .right, 452)],
  [some (0, .left, 13), some (1, .left, 13)],
  [some (0, .right, 356), some (1, .left, 454)],
  [some (0, .right, 376), some (1, .right, 456)],
  [some (0, .right, 455), some (1, .right, 456)],
  [some (0, .right, 457), some (1, .right, 116)],
  [some (0, .right, 456), some (1, .right, 376)],
  [some (0, .right, 455), some (1, .right, 459)],
  [some (0, .right, 460), some (1, .right, 116)],
  [some (0, .right, 456), some (1, .right, 378)],
  [some (0, .right, 455), some (1, .right, 462)],
  [some (0, .right, 463), some (1, .right, 116)],
  [some (0, .right, 379), some (1, .right, 381)],
  [some (0, .right, 455), some (1, .right, 465)],
  [some (0, .right, 466), some (1, .right, 116)],
  [some (0, .right, 455), some (1, .right, 381)],
  [some (0, .right, 468), some (1, .right, 116)],
  [some (0, .right, 369), some (1, .left, 10)],
  [some (0, .right, 470), some (1, .right, 452)],
  [some (0, .right, 369), some (1, .left, 454)],
  [some (0, .right, 376), some (1, .right, 378)],
  [some (0, .right, 472), some (1, .right, 473)],
  [some (0, .right, 474), some (1, .right, 116)],
  [some (0, .right, 486), some (1, .right, 456)],
  [some (0, .right, 476), some (1, .right, 116)],
  [some (0, .right, 376), some (1, .right, 379)],
  [some (0, .right, 486), some (1, .right, 478)],
  [some (0, .right, 479), some (1, .right, 116)],
  [some (0, .right, 486), some (1, .right, 392)],
  [some (0, .right, 481), some (1, .right, 116)],
  [some (0, .right, 378), some (1, .right, 380)],
  [some (0, .right, 486), some (1, .right, 483)],
  [some (0, .right, 484), some (1, .right, 116)],
  [some (0, .right, 357), some (1, .left, 454)],
  [some (0, .right, 486), some (1, .right, 465)],
  [some (0, .right, 487), some (1, .right, 116)],
  [some (0, .right, 362), some (1, .left, 10)],
  [some (0, .right, 489), some (1, .right, 452)],
  [some (0, .right, 497), some (1, .right, 506)],
  [some (0, .right, 508), some (0, .left, 450)],
  [some (0, .right, 497), some (1, .right, 492)],
  [some (0, .right, 497), some (1, .right, 251)],
  [some (0, .right, 497), some (1, .right, 167)],
  [some (0, .right, 497), some (1, .right, 170)],
  [some (0, .right, 362), some (0, .left, 454)],
  [some (0, .right, 377), some (0, .left, 450)],
  [some (0, .right, 497), some (1, .right, 498)],
  [some (0, .right, 497), some (1, .right, 142)],
  [some (0, .right, 497), some (1, .right, 541)],
  [some (0, .right, 456), some (0, .left, 450)],
  [some (0, .right, 497), some (1, .right, 502)],
  [some (0, .right, 363), some (1, .left, 10)],
  [some (0, .right, 504), some (1, .right, 452)],
  [some (0, .right, 374), some (0, .left, 450)],
  [some (0, .right, 135), some (1, .right, 506)],
  [some (0, .right, 375), some (0, .left, 450)],
  [some (0, .right, 135), some (1, .right, 508)],
  [some (0, .right, 135), some (1, .right, 251)],
  [some (0, .right, 135), some (1, .right, 167)],
  [some (0, .right, 135), some (1, .right, 170)],
  [some (0, .right, 135), some (1, .right, 142)],
  [some (0, .right, 135), some (1, .right, 524)],
  [some (0, .right, 135), some (1, .right, 541)],
  [some (0, .right, 365), some (1, .left, 10)],
  [some (0, .right, 516), some (1, .right, 452)],
  [some (0, .right, 522), some (1, .right, 492)],
  [some (0, .right, 522), some (1, .right, 251)],
  [some (0, .right, 522), some (1, .right, 167)],
  [some (0, .right, 522), some (1, .right, 170)],
  [some (0, .right, 365), some (0, .left, 454)],
  [some (0, .right, 522), some (1, .right, 142)],
  [some (0, .right, 382), some (0, .left, 450)],
  [some (0, .right, 522), some (1, .right, 524)],
  [some (0, .right, 366), some (1, .left, 10)],
  [some (0, .right, 526), some (1, .right, 452)],
  [some (0, .right, 530), some (1, .right, 508)],
  [some (0, .right, 530), some (1, .right, 492)],
  [some (0, .right, 366), some (0, .left, 454)],
  [some (0, .right, 530), some (1, .right, 541)],
  [some (0, .right, 367), some (1, .left, 10)],
  [some (0, .right, 532), some (1, .right, 452)],
  [some (0, .right, 535), some (1, .right, 167)],
  [some (0, .right, 367), some (0, .left, 454)],
  [some (0, .right, 535), some (1, .right, 498)],
  [some (0, .right, 535), some (1, .right, 541)],
  [some (0, .right, 539), some (1, .right, 498)],
  [some (0, .right, 368), some (0, .left, 454)],
  [some (0, .right, 539), some (1, .right, 142)],
  [some (0, .right, 75), some (0, .left, 450)],
  [some (0, .right, 539), some (1, .right, 541)],
]

theorem reference_eq : reference = Machine.ofRows refRows := rfl
theorem candidate_eq : candidate = Machine.ofRows candRows := rfl

def fNat (n : Nat) : Fin 543 :=
  (if n < 372 then (if n < 186 then (if n < 93 then (if n < 47 then (if n < 24 then (if n < 12
  then (if n < 6 then (if n < 3 then (if n < 2 then (if n < 1 then 0 else 1) else 2) else (if n <
  5 then (if n < 4 then 31 else 3) else 4)) else (if n < 9 then (if n < 8 then (if n < 7 then 5
  else 6) else 7) else (if n < 11 then (if n < 10 then 8 else 9) else 10))) else (if n < 18 then
  (if n < 15 then (if n < 14 then (if n < 13 then 0 else 11) else 12) else (if n < 17 then (if n <
  16 then 13 else 14) else 15)) else (if n < 21 then (if n < 20 then (if n < 19 then 16 else 17)
  else 18) else (if n < 23 then (if n < 22 then 19 else 20) else 21)))) else (if n < 36 then (if n
  < 30 then (if n < 27 then (if n < 26 then (if n < 25 then 22 else 23) else 24) else (if n < 29
  then (if n < 28 then 25 else 26) else 27)) else (if n < 33 then (if n < 32 then (if n < 31 then
  28 else 29) else 30) else (if n < 35 then (if n < 34 then 32 else 31) else 32))) else (if n < 42
  then (if n < 39 then (if n < 38 then (if n < 37 then 0 else 0) else 0) else (if n < 41 then (if
  n < 40 then 0 else 0) else 40)) else (if n < 45 then (if n < 44 then (if n < 43 then 33 else 34)
  else 0) else (if n < 46 then 0 else 30))))) else (if n < 70 then (if n < 59 then (if n < 53 then
  (if n < 50 then (if n < 49 then (if n < 48 then 0 else 0) else 0) else (if n < 52 then (if n <
  51 then 0 else 0) else 0)) else (if n < 56 then (if n < 55 then (if n < 54 then 0 else 0) else
  0) else (if n < 58 then (if n < 57 then 35 else 36) else 37))) else (if n < 65 then (if n < 62
  then (if n < 61 then (if n < 60 then 38 else 39) else 0) else (if n < 64 then (if n < 63 then 0
  else 40) else 0)) else (if n < 68 then (if n < 67 then (if n < 66 then 0 else 41) else 42) else
  (if n < 69 then 43 else 0)))) else (if n < 82 then (if n < 76 then (if n < 73 then (if n < 72
  then (if n < 71 then 287 else 44) else 33) else (if n < 75 then (if n < 74 then 0 else 0) else
  0)) else (if n < 79 then (if n < 78 then (if n < 77 then 0 else 0) else 0) else (if n < 81 then
  (if n < 80 then 45 else 0) else 0))) else (if n < 88 then (if n < 85 then (if n < 84 then (if n
  < 83 then 47 else 46) else 15) else (if n < 87 then (if n < 86 then 0 else 0) else 47)) else (if
  n < 91 then (if n < 90 then (if n < 89 then 46 else 0) else 0) else (if n < 92 then 48 else
  49)))))) else (if n < 140 then (if n < 117 then (if n < 105 then (if n < 99 then (if n < 96 then
  (if n < 95 then (if n < 94 then 50 else 51) else 52) else (if n < 98 then (if n < 97 then 53
  else 54) else 55)) else (if n < 102 then (if n < 101 then (if n < 100 then 56 else 57) else 0)
  else (if n < 104 then (if n < 103 then 0 else 58) else 59))) else (if n < 111 then (if n < 108
  then (if n < 107 then (if n < 106 then 0 else 0) else 0) else (if n < 110 then (if n < 109 then
  0 else 0) else 0)) else (if n < 114 then (if n < 113 then (if n < 112 then 0 else 60) else 61)
  else (if n < 116 then (if n < 115 then 43 else 0) else 0)))) else (if n < 129 then (if n < 123
  then (if n < 120 then (if n < 119 then (if n < 118 then 0 else 0) else 0) else (if n < 122 then
  (if n < 121 then 0 else 0) else 0)) else (if n < 126 then (if n < 125 then (if n < 124 then 0
  else 0) else 0) else (if n < 128 then (if n < 127 then 0 else 0) else 0))) else (if n < 135 then
  (if n < 132 then (if n < 131 then (if n < 130 then 0 else 0) else 0) else (if n < 134 then (if n
  < 133 then 0 else 0) else 0)) else (if n < 138 then (if n < 137 then (if n < 136 then 0 else 0)
  else 62) else (if n < 139 then 0 else 0))))) else (if n < 163 then (if n < 152 then (if n < 146
  then (if n < 143 then (if n < 142 then (if n < 141 then 0 else 0) else 0) else (if n < 145 then
  (if n < 144 then 0 else 0) else 63)) else (if n < 149 then (if n < 148 then (if n < 147 then 0
  else 0) else 0) else (if n < 151 then (if n < 150 then 0 else 0) else 64))) else (if n < 158
  then (if n < 155 then (if n < 154 then (if n < 153 then 65 else 66) else 67) else (if n < 157
  then (if n < 156 then 68 else 0) else 0)) else (if n < 161 then (if n < 160 then (if n < 159
  then 0 else 0) else 0) else (if n < 162 then 0 else 0)))) else (if n < 175 then (if n < 169 then
  (if n < 166 then (if n < 165 then (if n < 164 then 0 else 0) else 69) else (if n < 168 then (if
  n < 167 then 0 else 0) else 0)) else (if n < 172 then (if n < 171 then (if n < 170 then 0 else
  69) else 70) else (if n < 174 then (if n < 173 then 0 else 16) else 0))) else (if n < 181 then
  (if n < 178 then (if n < 177 then (if n < 176 then 0 else 47) else 46) else (if n < 180 then (if
  n < 179 then 0 else 0) else 44)) else (if n < 184 then (if n < 183 then (if n < 182 then 96 else
  40) else 64) else (if n < 185 then 71 else 72))))))) else (if n < 279 then (if n < 233 then (if
  n < 210 then (if n < 198 then (if n < 192 then (if n < 189 then (if n < 188 then (if n < 187
  then 73 else 74) else 75) else (if n < 191 then (if n < 190 then 76 else 77) else 78)) else (if
  n < 195 then (if n < 194 then (if n < 193 then 79 else 80) else 81) else (if n < 197 then (if n
  < 196 then 82 else 83) else 84))) else (if n < 204 then (if n < 201 then (if n < 200 then (if n
  < 199 then 85 else 86) else 87) else (if n < 203 then (if n < 202 then 88 else 89) else 90))
  else (if n < 207 then (if n < 206 then (if n < 205 then 91 else 92) else 93) else (if n < 209
  then (if n < 208 then 94 else 95) else 96)))) else (if n < 222 then (if n < 216 then (if n < 213
  then (if n < 212 then (if n < 211 then 97 else 98) else 99) else (if n < 215 then (if n < 214
  then 100 else 101) else 102)) else (if n < 219 then (if n < 218 then (if n < 217 then 103 else
  104) else 105) else (if n < 221 then (if n < 220 then 106 else 107) else 108))) else (if n < 228
  then (if n < 225 then (if n < 224 then (if n < 223 then 109 else 110) else 111) else (if n < 227
  then (if n < 226 then 112 else 113) else 114)) else (if n < 231 then (if n < 230 then (if n <
  229 then 115 else 116) else 117) else (if n < 232 then 118 else 119))))) else (if n < 256 then
  (if n < 245 then (if n < 239 then (if n < 236 then (if n < 235 then (if n < 234 then 120 else
  121) else 122) else (if n < 238 then (if n < 237 then 123 else 124) else 125)) else (if n < 242
  then (if n < 241 then (if n < 240 then 126 else 90) else 89) else (if n < 244 then (if n < 243
  then 127 else 128) else 95))) else (if n < 251 then (if n < 248 then (if n < 247 then (if n <
  246 then 96 else 97) else 129) else (if n < 250 then (if n < 249 then 130 else 99) else 100))
  else (if n < 254 then (if n < 253 then (if n < 252 then 101 else 131) else 132) else (if n < 255
  then 104 else 103)))) else (if n < 268 then (if n < 262 then (if n < 259 then (if n < 258 then
  (if n < 257 then 133 else 134) else 111) else (if n < 261 then (if n < 260 then 135 else 136)
  else 137)) else (if n < 265 then (if n < 264 then (if n < 263 then 138 else 139) else 140) else
  (if n < 267 then (if n < 266 then 141 else 142) else 143))) else (if n < 274 then (if n < 271
  then (if n < 270 then (if n < 269 then 144 else 145) else 146) else (if n < 273 then (if n < 272
  then 147 else 148) else 149)) else (if n < 277 then (if n < 276 then (if n < 275 then 150 else
  151) else 152) else (if n < 278 then 153 else 154)))))) else (if n < 326 then (if n < 303 then
  (if n < 291 then (if n < 285 then (if n < 282 then (if n < 281 then (if n < 280 then 155 else
  156) else 157) else (if n < 284 then (if n < 283 then 158 else 159) else 160)) else (if n < 288
  then (if n < 287 then (if n < 286 then 161 else 162) else 163) else (if n < 290 then (if n < 289
  then 164 else 165) else 166))) else (if n < 297 then (if n < 294 then (if n < 293 then (if n <
  292 then 167 else 168) else 169) else (if n < 296 then (if n < 295 then 170 else 171) else 172))
  else (if n < 300 then (if n < 299 then (if n < 298 then 173 else 174) else 175) else (if n < 302
  then (if n < 301 then 176 else 177) else 112)))) else (if n < 315 then (if n < 309 then (if n <
  306 then (if n < 305 then (if n < 304 then 178 else 179) else 180) else (if n < 308 then (if n <
  307 then 181 else 182) else 104)) else (if n < 312 then (if n < 311 then (if n < 310 then 115
  else 183) else 184) else (if n < 314 then (if n < 313 then 96 else 185) else 186))) else (if n <
  321 then (if n < 318 then (if n < 317 then (if n < 316 then 187 else 112) else 188) else (if n <
  320 then (if n < 319 then 189 else 190) else 191)) else (if n < 324 then (if n < 323 then (if n
  < 322 then 139 else 140) else 192) else (if n < 325 then 193 else 194))))) else (if n < 349 then
  (if n < 338 then (if n < 332 then (if n < 329 then (if n < 328 then (if n < 327 then 195 else
  196) else 197) else (if n < 331 then (if n < 330 then 198 else 199) else 200)) else (if n < 335
  then (if n < 334 then (if n < 333 then 112 else 188) else 201) else (if n < 337 then (if n < 336
  then 202 else 203) else 139))) else (if n < 344 then (if n < 341 then (if n < 340 then (if n <
  339 then 140 else 192) else 204) else (if n < 343 then (if n < 342 then 205 else 206) else 207))
  else (if n < 347 then (if n < 346 then (if n < 345 then 208 else 209) else 210) else (if n < 348
  then 211 else 212)))) else (if n < 361 then (if n < 355 then (if n < 352 then (if n < 351 then
  (if n < 350 then 213 else 214) else 215) else (if n < 354 then (if n < 353 then 216 else 217)
  else 218)) else (if n < 358 then (if n < 357 then (if n < 356 then 219 else 220) else 221) else
  (if n < 360 then (if n < 359 then 222 else 223) else 224))) else (if n < 367 then (if n < 364
  then (if n < 363 then (if n < 362 then 225 else 226) else 227) else (if n < 366 then (if n < 365
  then 228 else 229) else 230)) else (if n < 370 then (if n < 369 then (if n < 368 then 231 else
  232) else 233) else (if n < 371 then 234 else 235)))))))) else (if n < 558 then (if n < 465 then
  (if n < 419 then (if n < 396 then (if n < 384 then (if n < 378 then (if n < 375 then (if n < 374
  then (if n < 373 then 99 else 100) else 236) else (if n < 377 then (if n < 376 then 237 else
  140) else 238)) else (if n < 381 then (if n < 380 then (if n < 379 then 239 else 240) else 241)
  else (if n < 383 then (if n < 382 then 242 else 243) else 244))) else (if n < 390 then (if n <
  387 then (if n < 386 then (if n < 385 then 245 else 246) else 140) else (if n < 389 then (if n <
  388 then 247 else 248) else 249)) else (if n < 393 then (if n < 392 then (if n < 391 then 250
  else 251) else 252) else (if n < 395 then (if n < 394 then 253 else 254) else 255)))) else (if n
  < 408 then (if n < 402 then (if n < 399 then (if n < 398 then (if n < 397 then 256 else 257)
  else 258) else (if n < 401 then (if n < 400 then 259 else 260) else 261)) else (if n < 405 then
  (if n < 404 then (if n < 403 then 262 else 263) else 264) else (if n < 407 then (if n < 406 then
  265 else 103) else 115))) else (if n < 414 then (if n < 411 then (if n < 410 then (if n < 409
  then 266 else 267) else 268) else (if n < 413 then (if n < 412 then 96 else 185) else 269)) else
  (if n < 417 then (if n < 416 then (if n < 415 then 270 else 271) else 263) else (if n < 418 then
  272 else 273))))) else (if n < 442 then (if n < 431 then (if n < 425 then (if n < 422 then (if n
  < 421 then (if n < 420 then 274 else 139) else 140) else (if n < 424 then (if n < 423 then 275
  else 276) else 277)) else (if n < 428 then (if n < 427 then (if n < 426 then 278 else 279) else
  280) else (if n < 430 then (if n < 429 then 281 else 263) else 272))) else (if n < 437 then (if
  n < 434 then (if n < 433 then (if n < 432 then 282 else 283) else 284) else (if n < 436 then (if
  n < 435 then 275 else 285) else 286)) else (if n < 440 then (if n < 439 then (if n < 438 then
  287 else 288) else 289) else (if n < 441 then 290 else 291)))) else (if n < 454 then (if n < 448
  then (if n < 445 then (if n < 444 then (if n < 443 then 292 else 293) else 294) else (if n < 447
  then (if n < 446 then 263 else 272) else 273)) else (if n < 451 then (if n < 450 then (if n <
  449 then 295 else 296) else 297) else (if n < 453 then (if n < 452 then 298 else 299) else
  300))) else (if n < 460 then (if n < 457 then (if n < 456 then (if n < 455 then 301 else 302)
  else 303) else (if n < 459 then (if n < 458 then 304 else 305) else 306)) else (if n < 463 then
  (if n < 462 then (if n < 461 then 307 else 308) else 309) else (if n < 464 then 306 else
  310)))))) else (if n < 512 then (if n < 489 then (if n < 477 then (if n < 471 then (if n < 468
  then (if n < 467 then (if n < 466 then 311 else 312) else 313) else (if n < 470 then (if n < 469
  then 263 else 272) else 282)) else (if n < 474 then (if n < 473 then (if n < 472 then 283 else
  314) else 315) else (if n < 476 then (if n < 475 then 316 else 317) else 318))) else (if n < 483
  then (if n < 480 then (if n < 479 then (if n < 478 then 319 else 282) else 320) else (if n < 482
  then (if n < 481 then 321 else 314) else 322)) else (if n < 486 then (if n < 485 then (if n <
  484 then 323 else 324) else 325) else (if n < 488 then (if n < 487 then 326 else 139) else
  140)))) else (if n < 501 then (if n < 495 then (if n < 492 then (if n < 491 then (if n < 490
  then 314 else 315) else 327) else (if n < 494 then (if n < 493 then 328 else 329) else 305))
  else (if n < 498 then (if n < 497 then (if n < 496 then 330 else 331) else 332) else (if n < 500
  then (if n < 499 then 333 else 111) else 334))) else (if n < 507 then (if n < 504 then (if n <
  503 then (if n < 502 then 335 else 336) else 115) else (if n < 506 then (if n < 505 then 116
  else 117) else 337)) else (if n < 510 then (if n < 509 then (if n < 508 then 338 else 339) else
  340) else (if n < 511 then 341 else 342))))) else (if n < 535 then (if n < 524 then (if n < 518
  then (if n < 515 then (if n < 514 then (if n < 513 then 343 else 344) else 345) else (if n < 517
  then (if n < 516 then 346 else 347) else 348)) else (if n < 521 then (if n < 520 then (if n <
  519 then 349 else 350) else 351) else (if n < 523 then (if n < 522 then 352 else 353) else 0)))
  else (if n < 530 then (if n < 527 then (if n < 526 then (if n < 525 then 354 else 0) else 0)
  else (if n < 529 then (if n < 528 then 0 else 0) else 0)) else (if n < 533 then (if n < 532 then
  (if n < 531 then 0 else 0) else 0) else (if n < 534 then 355 else 356)))) else (if n < 547 then
  (if n < 541 then (if n < 538 then (if n < 537 then (if n < 536 then 357 else 358) else 359) else
  (if n < 540 then (if n < 539 then 360 else 361) else 395)) else (if n < 544 then (if n < 543
  then (if n < 542 then 400 else 362) else 363) else (if n < 546 then (if n < 545 then 364 else
  365) else 366))) else (if n < 553 then (if n < 550 then (if n < 549 then (if n < 548 then 367
  else 368) else 369) else (if n < 552 then (if n < 551 then 370 else 371) else 372)) else (if n <
  556 then (if n < 555 then (if n < 554 then 373 else 374) else 375) else (if n < 557 then 508
  else 492))))))) else (if n < 651 then (if n < 605 then (if n < 582 then (if n < 570 then (if n <
  564 then (if n < 561 then (if n < 560 then (if n < 559 then 376 else 377) else 378) else (if n <
  563 then (if n < 562 then 379 else 380) else 381)) else (if n < 567 then (if n < 566 then (if n
  < 565 then 382 else 383) else 384) else (if n < 569 then (if n < 568 then 385 else 386) else
  387))) else (if n < 576 then (if n < 573 then (if n < 572 then (if n < 571 then 388 else 389)
  else 390) else (if n < 575 then (if n < 574 then 391 else 392) else 393)) else (if n < 579 then
  (if n < 578 then (if n < 577 then 394 else 395) else 396) else (if n < 581 then (if n < 580 then
  397 else 398) else 399)))) else (if n < 594 then (if n < 588 then (if n < 585 then (if n < 584
  then (if n < 583 then 400 else 401) else 402) else (if n < 587 then (if n < 586 then 403 else
  404) else 405)) else (if n < 591 then (if n < 590 then (if n < 589 then 406 else 407) else 408)
  else (if n < 593 then (if n < 592 then 409 else 410) else 411))) else (if n < 600 then (if n <
  597 then (if n < 596 then (if n < 595 then 412 else 413) else 414) else (if n < 599 then (if n <
  598 then 415 else 416) else 417)) else (if n < 603 then (if n < 602 then (if n < 601 then 418
  else 419) else 420) else (if n < 604 then 421 else 422))))) else (if n < 628 then (if n < 617
  then (if n < 611 then (if n < 608 then (if n < 607 then (if n < 606 then 423 else 424) else 425)
  else (if n < 610 then (if n < 609 then 426 else 427) else 428)) else (if n < 614 then (if n <
  613 then (if n < 612 then 429 else 430) else 431) else (if n < 616 then (if n < 615 then 432
  else 433) else 434))) else (if n < 623 then (if n < 620 then (if n < 619 then (if n < 618 then
  435 else 436) else 437) else (if n < 622 then (if n < 621 then 438 else 439) else 440)) else (if
  n < 626 then (if n < 625 then (if n < 624 then 441 else 442) else 443) else (if n < 627 then 444
  else 445)))) else (if n < 640 then (if n < 634 then (if n < 631 then (if n < 630 then (if n <
  629 then 446 else 447) else 448) else (if n < 633 then (if n < 632 then 449 else 0) else 0))
  else (if n < 637 then (if n < 636 then (if n < 635 then 450 else 0) else 0) else (if n < 639
  then (if n < 638 then 451 else 452) else 453))) else (if n < 646 then (if n < 643 then (if n <
  642 then (if n < 641 then 0 else 0) else 35) else (if n < 645 then (if n < 644 then 36 else 0)
  else 0)) else (if n < 649 then (if n < 648 then (if n < 647 then 454 else 455) else 456) else
  (if n < 650 then 457 else 115)))))) else (if n < 698 then (if n < 675 then (if n < 663 then (if
  n < 657 then (if n < 654 then (if n < 653 then (if n < 652 then 116 else 458) else 459) else (if
  n < 656 then (if n < 655 then 460 else 461) else 462)) else (if n < 660 then (if n < 659 then
  (if n < 658 then 463 else 464) else 465) else (if n < 662 then (if n < 661 then 466 else 467)
  else 468))) else (if n < 669 then (if n < 666 then (if n < 665 then (if n < 664 then 469 else
  470) else 471) else (if n < 668 then (if n < 667 then 472 else 473) else 474)) else (if n < 672
  then (if n < 671 then (if n < 670 then 475 else 476) else 477) else (if n < 674 then (if n < 673
  then 478 else 479) else 480)))) else (if n < 687 then (if n < 681 then (if n < 678 then (if n <
  677 then (if n < 676 then 481 else 482) else 483) else (if n < 680 then (if n < 679 then 484
  else 485) else 486)) else (if n < 684 then (if n < 683 then (if n < 682 then 487 else 488) else
  489) else (if n < 686 then (if n < 685 then 490 else 491) else 492))) else (if n < 693 then (if
  n < 690 then (if n < 689 then (if n < 688 then 493 else 494) else 167) else (if n < 692 then (if
  n < 691 then 495 else 496) else 497)) else (if n < 696 then (if n < 695 then (if n < 694 then
  498 else 499) else 500) else (if n < 697 then 501 else 502))))) else (if n < 721 then (if n <
  710 then (if n < 704 then (if n < 701 then (if n < 700 then (if n < 699 then 503 else 504) else
  505) else (if n < 703 then (if n < 702 then 506 else 507) else 508)) else (if n < 707 then (if n
  < 706 then (if n < 705 then 509 else 251) else 510) else (if n < 709 then (if n < 708 then 511
  else 170) else 512))) else (if n < 716 then (if n < 713 then (if n < 712 then (if n < 711 then 0
  else 0) else 135) else (if n < 715 then (if n < 714 then 142 else 513) else 514)) else (if n <
  719 then (if n < 718 then (if n < 717 then 515 else 516) else 517) else (if n < 720 then 518
  else 519)))) else (if n < 733 then (if n < 727 then (if n < 724 then (if n < 723 then (if n <
  722 then 520 else 521) else 522) else (if n < 726 then (if n < 725 then 523 else 524) else 525))
  else (if n < 730 then (if n < 729 then (if n < 728 then 526 else 527) else 528) else (if n < 732
  then (if n < 731 then 529 else 530) else 531))) else (if n < 739 then (if n < 736 then (if n <
  735 then (if n < 734 then 532 else 533) else 534) else (if n < 738 then (if n < 737 then 535
  else 536) else 537)) else (if n < 742 then (if n < 741 then (if n < 740 then 538 else 539) else
  540) else (if n < 743 then 541 else 542)))))))))
def f (q : Fin 744) : Fin 543 := fNat q.val

def m0Nat (n : Nat) : Nat :=
  (if n < 372 then (if n < 186 then (if n < 93 then (if n < 47 then (if n < 24 then (if n < 12
  then (if n < 6 then (if n < 3 then (if n < 2 then (if n < 1 then 0 else 33554431) else 33554431)
  else (if n < 5 then (if n < 4 then 33554431 else 33553919) else 33553407)) else (if n < 9 then
  (if n < 8 then (if n < 7 then 33553407 else 33554431) else 33554431) else (if n < 11 then (if n
  < 10 then 33554431 else 33550335) else 33554431))) else (if n < 18 then (if n < 15 then (if n <
  14 then (if n < 13 then 33554431 else 33554431) else 33554431) else (if n < 17 then (if n < 16
  then 33554431 else 33554431) else 33554431)) else (if n < 21 then (if n < 20 then (if n < 19
  then 33554431 else 33554431) else 33554431) else (if n < 23 then (if n < 22 then 33554431 else
  33554431) else 33554431)))) else (if n < 36 then (if n < 30 then (if n < 27 then (if n < 26 then
  (if n < 25 then 33554431 else 33554431) else 33554431) else (if n < 29 then (if n < 28 then
  33554431 else 33554431) else 33554431)) else (if n < 33 then (if n < 32 then (if n < 31 then
  33553407 else 33554431) else 33554431) else (if n < 35 then (if n < 34 then 33554431 else
  33554431) else 33553407))) else (if n < 42 then (if n < 39 then (if n < 38 then (if n < 37 then
  0 else 0) else 0) else (if n < 41 then (if n < 40 then 0 else 0) else 33553831)) else (if n < 45
  then (if n < 44 then (if n < 43 then 33549135 else 33543839) else 0) else (if n < 46 then 0 else
  0))))) else (if n < 70 then (if n < 59 then (if n < 53 then (if n < 50 then (if n < 49 then (if
  n < 48 then 0 else 0) else 0) else (if n < 52 then (if n < 51 then 0 else 0) else 0)) else (if n
  < 56 then (if n < 55 then (if n < 54 then 0 else 0) else 0) else (if n < 58 then (if n < 57 then
  33554399 else 33554367) else 33554303))) else (if n < 65 then (if n < 62 then (if n < 61 then
  (if n < 60 then 33554431 else 33550335) else 0) else (if n < 64 then (if n < 63 then 0 else
  33554139) else 0)) else (if n < 68 then (if n < 67 then (if n < 66 then 0 else 0) else 0) else
  (if n < 69 then 0 else 0)))) else (if n < 82 then (if n < 76 then (if n < 73 then (if n < 72
  then (if n < 71 then 33485247 else 33416063) else 33290239) else (if n < 75 then (if n < 74 then
  0 else 0) else 0)) else (if n < 79 then (if n < 78 then (if n < 77 then 0 else 0) else 0) else
  (if n < 81 then (if n < 80 then 0 else 0) else 0))) else (if n < 88 then (if n < 85 then (if n <
  84 then (if n < 83 then 33549599 else 33544767) else 33535103) else (if n < 87 then (if n < 86
  then 0 else 0) else 0)) else (if n < 91 then (if n < 90 then (if n < 89 then 0 else 0) else 0)
  else (if n < 92 then 32178175 else 30801919)))))) else (if n < 140 then (if n < 117 then (if n <
  105 then (if n < 99 then (if n < 96 then (if n < 95 then (if n < 94 then 33550335 else 33546239)
  else 33533951) else (if n < 98 then (if n < 97 then 33513471 else 33468415) else 33382399)) else
  (if n < 102 then (if n < 101 then (if n < 100 then 33210367 else 32866303) else 0) else (if n <
  104 then (if n < 103 then 0 else 0) else 0))) else (if n < 111 then (if n < 108 then (if n < 107
  then (if n < 106 then 0 else 0) else 0) else (if n < 110 then (if n < 109 then 0 else 0) else
  0)) else (if n < 114 then (if n < 113 then (if n < 112 then 0 else 33551647) else 33553407) else
  (if n < 116 then (if n < 115 then 33552383 else 0) else 0)))) else (if n < 129 then (if n < 123
  then (if n < 120 then (if n < 119 then (if n < 118 then 0 else 0) else 0) else (if n < 122 then
  (if n < 121 then 0 else 0) else 0)) else (if n < 126 then (if n < 125 then (if n < 124 then 0
  else 0) else 0) else (if n < 128 then (if n < 127 then 0 else 0) else 0))) else (if n < 135 then
  (if n < 132 then (if n < 131 then (if n < 130 then 0 else 0) else 0) else (if n < 134 then (if n
  < 133 then 0 else 0) else 0)) else (if n < 138 then (if n < 137 then (if n < 136 then 0 else 0)
  else 0) else (if n < 139 then 0 else 0))))) else (if n < 163 then (if n < 152 then (if n < 146
  then (if n < 143 then (if n < 142 then (if n < 141 then 0 else 0) else 0) else (if n < 145 then
  (if n < 144 then 0 else 0) else 33364223)) else (if n < 149 then (if n < 148 then (if n < 147
  then 0 else 0) else 0) else (if n < 151 then (if n < 150 then 0 else 0) else 33553215))) else
  (if n < 158 then (if n < 155 then (if n < 154 then (if n < 153 then 33547903 else 33545471) else
  33532415) else (if n < 157 then (if n < 156 then 33507327 else 0) else 0)) else (if n < 161 then
  (if n < 160 then (if n < 159 then 0 else 0) else 0) else (if n < 162 then 0 else 0)))) else (if
  n < 175 then (if n < 169 then (if n < 166 then (if n < 165 then (if n < 164 then 0 else 0) else
  33550603) else (if n < 168 then (if n < 167 then 0 else 0) else 0)) else (if n < 172 then (if n
  < 171 then (if n < 170 then 0 else 0) else 0) else (if n < 174 then (if n < 173 then 0 else
  33545983) else 0))) else (if n < 181 then (if n < 178 then (if n < 177 then (if n < 176 then 0
  else 33554399) else 33554367) else (if n < 180 then (if n < 179 then 0 else 0) else 33549339))
  else (if n < 184 then (if n < 183 then (if n < 182 then 33544247 else 33534063) else 33517791)
  else (if n < 185 then 33554431 else 33554431))))))) else (if n < 279 then (if n < 233 then (if n
  < 210 then (if n < 198 then (if n < 192 then (if n < 189 then (if n < 188 then (if n < 187 then
  33554431 else 33554431) else 33554431) else (if n < 191 then (if n < 190 then 33553151 else
  33553919) else 33553407)) else (if n < 195 then (if n < 194 then (if n < 193 then 33554431 else
  33554175) else 33553151) else (if n < 197 then (if n < 196 then 33553919 else 33552639) else
  33552895))) else (if n < 204 then (if n < 201 then (if n < 200 then (if n < 199 then 33553407
  else 33554431) else 33554431) else (if n < 203 then (if n < 202 then 33554175 else 33553503)
  else 33552479)) else (if n < 207 then (if n < 206 then (if n < 205 then 33552575 else 33552767)
  else 33553151) else (if n < 209 then (if n < 208 then 33553919 else 33554335) else 33553311))))
  else (if n < 222 then (if n < 216 then (if n < 213 then (if n < 212 then (if n < 211 then
  33554239 else 33554047) else 33554079) else (if n < 215 then (if n < 214 then 33553727 else
  33553023) else 33553663)) else (if n < 219 then (if n < 218 then (if n < 217 then 33553439 else
  33552415) else 33552447) else (if n < 221 then (if n < 220 then 33552511 else 33552639) else
  33552895))) else (if n < 228 then (if n < 225 then (if n < 224 then (if n < 223 then 33553407
  else 33554431) else 33554415) else (if n < 227 then (if n < 226 then 33553391 else 33554399)
  else 33554367)) else (if n < 231 then (if n < 230 then (if n < 229 then 33554415 else 33554399)
  else 33553343) else (if n < 232 then 33554303 else 33553855))))) else (if n < 256 then (if n <
  245 then (if n < 239 then (if n < 236 then (if n < 235 then (if n < 234 then 33553279 else
  33554175) else 33554111) else (if n < 238 then (if n < 237 then 33553791 else 33552767) else
  33553151)) else (if n < 242 then (if n < 241 then (if n < 240 then 33553919 else 33553871) else
  33552847) else (if n < 244 then (if n < 243 then 33553311 else 33554239) else 33554127))) else
  (if n < 251 then (if n < 248 then (if n < 247 then (if n < 246 then 33553103 else 33553823) else
  33553215) else (if n < 250 then (if n < 249 then 33554047 else 33553725) else 33553019)) else
  (if n < 254 then (if n < 253 then (if n < 252 then 33553727 else 33553023) else 33553663) else
  (if n < 255 then 33553807 else 33552783)))) else (if n < 268 then (if n < 262 then (if n < 259
  then (if n < 258 then (if n < 257 then 33553183 else 33553983) else 33554063) else (if n < 261
  then (if n < 260 then 33553039 else 33553695) else 33552959)) else (if n < 265 then (if n < 264
  then (if n < 263 then 33553535 else 33554191) else 33553951) else (if n < 267 then (if n < 266
  then 33553471 else 33553935) else 33553439))) else (if n < 274 then (if n < 271 then (if n < 270
  then (if n < 269 then 33552447 else 33552511) else 33552639) else (if n < 273 then (if n < 272
  then 33552895 else 33553407) else 33554431)) else (if n < 277 then (if n < 276 then (if n < 275
  then 33554431 else 33554431) else 33553375) else (if n < 278 then 33554367 else 33554431))))))
  else (if n < 326 then (if n < 303 then (if n < 291 then (if n < 285 then (if n < 282 then (if n
  < 281 then (if n < 280 then 33554431 else 33554303) else 33554431) else (if n < 284 then (if n <
  283 then 33554175 else 33554431) else 33553919)) else (if n < 288 then (if n < 287 then (if n <
  286 then 33554431 else 33553407) else 33554431) else (if n < 290 then (if n < 289 then 33553919
  else 33553359) else 33554335))) else (if n < 297 then (if n < 294 then (if n < 293 then (if n <
  292 then 33553779 else 33553127) else 33553871) else (if n < 296 then (if n < 295 then 33554431
  else 33554431) else 33552847)) else (if n < 300 then (if n < 299 then (if n < 298 then 33553311
  else 33554239) else 33553103) else (if n < 302 then (if n < 301 then 33553823 else 33553459)
  else 33552435)))) else (if n < 315 then (if n < 309 then (if n < 306 then (if n < 305 then (if n
  < 304 then 33552487 else 33552591) else 33552799) else (if n < 308 then (if n < 307 then
  33553215 else 33554047) else 33554387)) else (if n < 312 then (if n < 311 then (if n < 310 then
  33553363 else 33554343) else 33554255) else (if n < 314 then (if n < 313 then 33554131 else
  33553831) else 33553231))) else (if n < 321 then (if n < 318 then (if n < 317 then (if n < 316
  then 33554079 else 33553495) else 33552559) else (if n < 320 then (if n < 319 then 33552719 else
  33553055) else 33553727)) else (if n < 324 then (if n < 323 then (if n < 322 then 33553567 else
  33552703) else 33552975) else (if n < 325 then 33553567 else 33552463))))) else (if n < 349 then
  (if n < 338 then (if n < 332 then (if n < 329 then (if n < 328 then (if n < 327 then 33552543
  else 33552703) else 33553023) else (if n < 331 then (if n < 330 then 33553663 else 33554319)
  else 33554207)) else (if n < 335 then (if n < 334 then (if n < 333 then 33553783 else 33553135)
  else 33553807) else (if n < 337 then (if n < 336 then 33553183 else 33553983) else 33553831)))
  else (if n < 344 then (if n < 341 then (if n < 340 then (if n < 339 then 33553231 else 33554063)
  else 33553039) else (if n < 343 then (if n < 342 then 33553695 else 33554211) else 33553991))
  else (if n < 347 then (if n < 346 then (if n < 345 then 33553551 else 33552671) else 33552959)
  else (if n < 348 then 33553535 else 33554191)))) else (if n < 361 then (if n < 355 then (if n <
  352 then (if n < 351 then (if n < 350 then 33553951 else 33553731) else 33553031) else (if n <
  354 then (if n < 353 then 33553679 else 33552927) else 33553471)) else (if n < 358 then (if n <
  357 then (if n < 356 then 33553935 else 33553903) else 33552515) else (if n < 360 then (if n <
  359 then 33552647 else 33552911) else 33553439))) else (if n < 367 then (if n < 364 then (if n <
  363 then (if n < 362 then 33554179 else 33553927) else 33553423) else (if n < 366 then (if n <
  365 then 33552399 else 33552415) else 33552447)) else (if n < 370 then (if n < 369 then (if n <
  368 then 33552511 else 33552639) else 33552895) else (if n < 371 then 33553407 else
  33554431)))))))) else (if n < 558 then (if n < 465 then (if n < 419 then (if n < 396 then (if n
  < 384 then (if n < 378 then (if n < 375 then (if n < 374 then (if n < 373 then 33553661 else
  33552891) else 33553399) else (if n < 377 then (if n < 376 then 33554415 else 33552635) else
  33552887)) else (if n < 381 then (if n < 380 then (if n < 379 then 33553391 else 33554399) else
  33554167) else (if n < 383 then (if n < 382 then 33553903 else 33553655) else 33552879))) else
  (if n < 390 then (if n < 387 then (if n < 386 then (if n < 385 then 33553375 else 33554367) else
  33553339) else (if n < 389 then (if n < 388 then 33554295 else 33553271) else 33554159)) else
  (if n < 393 then (if n < 392 then (if n < 391 then 33553783 else 33554013) else 33553595) else
  (if n < 395 then (if n < 394 then 33552759 else 33553135) else 33553887)))) else (if n < 408
  then (if n < 402 then (if n < 399 then (if n < 398 then (if n < 397 then 33554039 else 33553647)
  else 33553527) else (if n < 401 then (if n < 400 then 33552623 else 33552863) else 33553343))
  else (if n < 405 then (if n < 404 then (if n < 403 then 33554303 else 33552877) else 33553371)
  else (if n < 407 then (if n < 406 then 33554359 else 33554157) else 33553133))) else (if n < 414
  then (if n < 411 then (if n < 410 then (if n < 409 then 33553883 else 33553335) else 33554287)
  else (if n < 413 then (if n < 412 then 33554285 else 33554139) else 33553847)) else (if n < 417
  then (if n < 416 then (if n < 415 then 33553263 else 33554143) else 33553901) else (if n < 418
  then 33553371 else 33554103))))) else (if n < 442 then (if n < 431 then (if n < 425 then (if n <
  422 then (if n < 421 then (if n < 420 then 33553775 else 33553709) else 33552987) else (if n <
  424 then (if n < 423 then 33553591 else 33552751) else 33553119)) else (if n < 428 then (if n <
  427 then (if n < 426 then 33553855 else 33554231) else 33553207) else (if n < 430 then (if n <
  429 then 33554031 else 33553517) else 33552603))) else (if n < 437 then (if n < 434 then (if n <
  433 then (if n < 432 then 33552695 else 33553007) else 33553631) else (if n < 436 then (if n <
  435 then 33552951 else 33553519) else 33554359)) else (if n < 440 then (if n < 439 then (if n <
  438 then 33553933 else 33553435) else 33552439) else (if n < 441 then 33552495 else 33552607))))
  else (if n < 454 then (if n < 448 then (if n < 445 then (if n < 444 then (if n < 443 then
  33552831 else 33553279) else 33554175) else (if n < 447 then (if n < 446 then 33553653 else
  33552875) else 33553367)) else (if n < 451 then (if n < 450 then (if n < 449 then 33554351 else
  33552855) else 33553327) else (if n < 453 then (if n < 452 then 33554271 else 33554391) else
  33553839))) else (if n < 460 then (if n < 457 then (if n < 456 then (if n < 455 then 33553623
  else 33552815) else 33553247) else (if n < 459 then (if n < 458 then 33554111 else 33553877)
  else 33552853)) else (if n < 463 then (if n < 462 then (if n < 461 then 33553323 else 33554263)
  else 33554095) else (if n < 464 then 33553749 else 33553067)))))) else (if n < 512 then (if n <
  489 then (if n < 477 then (if n < 471 then (if n < 468 then (if n < 467 then (if n < 466 then
  33553751 else 33553071) else 33553759) else (if n < 470 then (if n < 469 then 33553557 else
  33552683) else 33552983)) else (if n < 474 then (if n < 473 then (if n < 472 then 33553583 else
  33552471) else 33552559) else (if n < 476 then (if n < 475 then 33552735 else 33553087) else
  33553791))) else (if n < 483 then (if n < 480 then (if n < 479 then (if n < 478 then 33554223
  else 33553815) else 33553199) else (if n < 482 then (if n < 481 then 33554015 else 33554071)
  else 33553711)) else (if n < 486 then (if n < 485 then (if n < 484 then 33552535 else 33552687)
  else 33552991) else (if n < 488 then (if n < 487 then 33553599 else 33553605) else 33552779))))
  else (if n < 501 then (if n < 495 then (if n < 492 then (if n < 491 then (if n < 490 then
  33553175 else 33553967) else 33552663) else (if n < 494 then (if n < 493 then 33552943 else
  33553503) else 33553541)) else (if n < 498 then (if n < 497 then (if n < 496 then 33552517 else
  33552651) else 33552919) else (if n < 500 then (if n < 499 then 33553455 else 33554181) else
  33553157))) else (if n < 507 then (if n < 504 then (if n < 503 then (if n < 502 then 33553931
  else 33553431) else 33553925) else (if n < 506 then (if n < 505 then 33553419 else 33552407)
  else 33552431)) else (if n < 510 then (if n < 509 then (if n < 508 then 33552479 else 33552575)
  else 33552767) else (if n < 511 then 33553151 else 33553919))))) else (if n < 535 then (if n <
  524 then (if n < 518 then (if n < 515 then (if n < 514 then (if n < 513 then 33554425 else
  33553401) else 33554419) else (if n < 517 then (if n < 516 then 33554407 else 33554383) else
  33554335)) else (if n < 521 then (if n < 520 then (if n < 519 then 33554239 else 33554047) else
  33553663) else (if n < 523 then (if n < 522 then 33552895 else 33553407) else 0))) else (if n <
  530 then (if n < 527 then (if n < 526 then (if n < 525 then 33554431 else 0) else 0) else (if n
  < 529 then (if n < 528 then 0 else 0) else 0)) else (if n < 533 then (if n < 532 then (if n <
  531 then 0 else 0) else 0) else (if n < 534 then 33554431 else 33554431)))) else (if n < 547
  then (if n < 541 then (if n < 538 then (if n < 537 then (if n < 536 then 33554431 else 33554431)
  else 33554431) else (if n < 540 then (if n < 539 then 33554431 else 33554431) else 33554431))
  else (if n < 544 then (if n < 543 then (if n < 542 then 33554430 else 33554431) else 33554431)
  else (if n < 546 then (if n < 545 then 33554431 else 33554431) else 33554431))) else (if n < 553
  then (if n < 550 then (if n < 549 then (if n < 548 then 33554431 else 33554431) else 33554431)
  else (if n < 552 then (if n < 551 then 33554431 else 33554431) else 33554431)) else (if n < 556
  then (if n < 555 then (if n < 554 then 33554431 else 33554431) else 33554431) else (if n < 557
  then 33554431 else 33554430))))))) else (if n < 651 then (if n < 605 then (if n < 582 then (if n
  < 570 then (if n < 564 then (if n < 561 then (if n < 560 then (if n < 559 then 33554431 else
  33554431) else 33554431) else (if n < 563 then (if n < 562 then 33554431 else 33554431) else
  33554431)) else (if n < 567 then (if n < 566 then (if n < 565 then 33554431 else 33554431) else
  33550335) else (if n < 569 then (if n < 568 then 33554431 else 33550335) else 33554367))) else
  (if n < 576 then (if n < 573 then (if n < 572 then (if n < 571 then 33554303 else 33554171) else
  33553911) else (if n < 575 then (if n < 574 then 33554429 else 33553405) else 33554427)) else
  (if n < 579 then (if n < 578 then (if n < 577 then 33554423 else 33554141) else 33553851) else
  (if n < 581 then (if n < 580 then 33554245 else 33554059) else 33553687)))) else (if n < 594
  then (if n < 588 then (if n < 585 then (if n < 584 then (if n < 583 then 33554429 else 33554427)
  else 33553771) else (if n < 587 then (if n < 586 then 33553111 else 33554429) else 33554427))
  else (if n < 591 then (if n < 590 then (if n < 589 then 33554423 else 33553333) else 33554283)
  else (if n < 593 then (if n < 592 then 33554135 else 33554155) else 33553879))) else (if n < 600
  then (if n < 597 then (if n < 596 then (if n < 595 then 33554429 else 33554427) else 33554427)
  else (if n < 599 then (if n < 598 then 33554423 else 33554411) else 33554391)) else (if n < 603
  then (if n < 602 then (if n < 601 then 33554429 else 33552941) else 33553499) else (if n < 604
  then 33552567 else 33554419))))) else (if n < 628 then (if n < 617 then (if n < 611 then (if n <
  608 then (if n < 607 then (if n < 606 then 33554407 else 33553863) else 33553295) else (if n <
  610 then (if n < 609 then 33554431 else 33554047) else 33553663)) else (if n < 614 then (if n <
  613 then (if n < 612 then 33553787 else 33553143) else 33553799) else (if n < 616 then (if n <
  615 then 33553167 else 33554047) else 33553663))) else (if n < 623 then (if n < 620 then (if n <
  619 then (if n < 618 then 33554431 else 33554279) else 33554127) else (if n < 622 then (if n <
  621 then 33554431 else 33554431) else 33554267)) else (if n < 626 then (if n < 625 then (if n <
  624 then 33554103 else 33553855) else 33553279) else (if n < 627 then 33553183 else 33553983))))
  else (if n < 640 then (if n < 634 then (if n < 631 then (if n < 630 then (if n < 629 then
  33553535 else 33554271) else 33554111) else (if n < 633 then (if n < 632 then 33553791 else 0)
  else 0)) else (if n < 637 then (if n < 636 then (if n < 635 then 33552383 else 0) else 0) else
  (if n < 639 then (if n < 638 then 33554303 else 33553407) else 33554175))) else (if n < 646 then
  (if n < 643 then (if n < 642 then (if n < 641 then 0 else 0) else 33553407) else (if n < 645
  then (if n < 644 then 33552383 else 0) else 0)) else (if n < 649 then (if n < 648 then (if n <
  647 then 33554431 else 33554431) else 33554431) else (if n < 650 then 33554175 else
  33553919)))))) else (if n < 698 then (if n < 675 then (if n < 663 then (if n < 657 then (if n <
  654 then (if n < 653 then (if n < 652 then 33553407 else 33553919) else 33553407) else (if n <
  656 then (if n < 655 then 33553631 else 33552831) else 33553407)) else (if n < 660 then (if n <
  659 then (if n < 658 then 33554023 else 33553615) else 33553407) else (if n < 662 then (if n <
  661 then 33554367 else 33554303) else 33553759))) else (if n < 669 then (if n < 666 then (if n <
  665 then (if n < 664 then 33553087 else 33553651) else 33552871) else (if n < 668 then (if n <
  667 then 33554291 else 33553395) else 33554151)) else (if n < 672 then (if n < 671 then (if n <
  670 then 33553871 else 33554415) else 33554399) else (if n < 674 then (if n < 673 then 33553407
  else 33553567) else 33552703)))) else (if n < 687 then (if n < 681 then (if n < 678 then (if n <
  677 then (if n < 676 then 33553851 else 33553271) else 33552963) else (if n < 680 then (if n <
  679 then 33553543 else 33552655) else 33554431)) else (if n < 684 then (if n < 683 then (if n <
  682 then 33553503 else 33552575) else 33554431) else (if n < 686 then (if n < 685 then 33554431
  else 33553915) else 33553405))) else (if n < 693 then (if n < 690 then (if n < 689 then (if n <
  688 then 33554427 else 33554427) else 33553407) else (if n < 692 then (if n < 691 then 33554431
  else 33554267) else 33554431)) else (if n < 696 then (if n < 695 then (if n < 694 then 33553151
  else 33553791) else 33554271) else (if n < 697 then 33554427 else 33553027))))) else (if n < 721
  then (if n < 710 then (if n < 704 then (if n < 701 then (if n < 700 then (if n < 699 then
  33553671 else 33553663) else 33552895) else (if n < 703 then (if n < 702 then 33553407 else
  33554303) else 33553117)) else (if n < 707 then (if n < 706 then (if n < 705 then 33552827 else
  33553405) else 33554331) else (if n < 709 then (if n < 708 then 33552711 else 33553343) else
  33553767))) else (if n < 716 then (if n < 713 then (if n < 712 then (if n < 711 then 0 else 0)
  else 33554431) else (if n < 715 then (if n < 714 then 33553407 else 33554303) else 33554375))
  else (if n < 719 then (if n < 718 then (if n < 717 then 33553903 else 33553773) else 33553115)
  else (if n < 720 then 33554427 else 33553371)))) else (if n < 733 then (if n < 727 then (if n <
  724 then (if n < 723 then (if n < 722 then 33554119 else 33554303) else 33554431) else (if n <
  726 then (if n < 725 then 33553511 else 33553395) else 33554343)) else (if n < 730 then (if n <
  729 then (if n < 728 then 33553615 else 33552799) else 33553547) else (if n < 732 then (if n <
  731 then 33554411 else 33554431) else 33554207))) else (if n < 739 then (if n < 736 then (if n <
  735 then (if n < 734 then 33553823 else 33553215) else 33554055) else (if n < 738 then (if n <
  737 then 33554399 else 33553471) else 33554183)) else (if n < 742 then (if n < 741 then (if n <
  740 then 33553599 else 33554431) else 33554431) else (if n < 743 then 33553407 else
  33554335)))))))))
def m1Nat (n : Nat) : Nat :=
  (if n < 372 then (if n < 186 then (if n < 93 then (if n < 47 then (if n < 24 then (if n < 12
  then (if n < 6 then (if n < 3 then (if n < 2 then (if n < 1 then 0 else 33552895) else 33553407)
  else (if n < 5 then (if n < 4 then 33547263 else 33553407) else 33554431)) else (if n < 9 then
  (if n < 8 then (if n < 7 then 33548287 else 33554431) else 33554431) else (if n < 11 then (if n
  < 10 then 33542143 else 33529855) else 33529855))) else (if n < 18 then (if n < 15 then (if n <
  14 then (if n < 13 then 20971519 else 20959231) else 33505279) else (if n < 17 then (if n < 16
  then 33505279 else 33456127) else 33452031)) else (if n < 21 then (if n < 20 then (if n < 19
  then 33357823 else 33357823) else 33161215) else (if n < 23 then (if n < 22 then 33157119 else
  32767999) else 32767999)))) else (if n < 36 then (if n < 30 then (if n < 27 then (if n < 26 then
  (if n < 25 then 31981567 else 31977471) else 30408703) else (if n < 29 then (if n < 28 then
  30404607 else 27262975) else 27258879)) else (if n < 33 then (if n < 32 then (if n < 31 then
  33554431 else 33554431) else 33548160) else (if n < 35 then (if n < 34 then 33551296 else
  33553407) else 33554431))) else (if n < 42 then (if n < 39 then (if n < 38 then (if n < 37 then
  0 else 0) else 0) else (if n < 41 then (if n < 40 then 0 else 0) else 33522267)) else (if n < 45
  then (if n < 44 then (if n < 43 then 33494199 else 33433967) else 0) else (if n < 46 then 0 else
  0))))) else (if n < 70 then (if n < 59 then (if n < 53 then (if n < 50 then (if n < 49 then (if
  n < 48 then 0 else 0) else 0) else (if n < 52 then (if n < 51 then 0 else 0) else 0)) else (if n
  < 56 then (if n < 55 then (if n < 54 then 0 else 0) else 0) else (if n < 58 then (if n < 57 then
  33522467 else 33490503) else 33426575))) else (if n < 65 then (if n < 62 then (if n < 61 then
  (if n < 60 then 33315839 else 33077247) else 0) else (if n < 64 then (if n < 63 then 0 else
  33521959) else 0)) else (if n < 68 then (if n < 67 then (if n < 66 then 0 else 0) else 0) else
  (if n < 69 then 0 else 0)))) else (if n < 82 then (if n < 76 then (if n < 73 then (if n < 72
  then (if n < 71 then 33099391 else 32644351) else 31850495) else (if n < 75 then (if n < 74 then
  0 else 0) else 0)) else (if n < 79 then (if n < 78 then (if n < 77 then 0 else 0) else 0) else
  (if n < 81 then (if n < 80 then 0 else 0) else 0))) else (if n < 88 then (if n < 85 then (if n <
  84 then (if n < 83 then 33526499 else 33498567) else 33442703) else (if n < 87 then (if n < 86
  then 0 else 0) else 0)) else (if n < 91 then (if n < 90 then (if n < 89 then 0 else 0) else 0)
  else (if n < 92 then 26546175 else 19533823)))))) else (if n < 140 then (if n < 117 then (if n <
  105 then (if n < 99 then (if n < 96 then (if n < 95 then (if n < 94 then 33529855 else 33501183)
  else 33447935) else (if n < 98 then (if n < 97 then 33337343 else 33120255) else 32681983)) else
  (if n < 102 then (if n < 101 then (if n < 100 then 31805439 else 30052351) else 0) else (if n <
  104 then (if n < 103 then 0 else 0) else 0))) else (if n < 111 then (if n < 108 then (if n < 107
  then (if n < 106 then 0 else 0) else 0) else (if n < 110 then (if n < 109 then 0 else 0) else
  0)) else (if n < 114 then (if n < 113 then (if n < 112 then 0 else 33524451) else 33505279) else
  (if n < 116 then (if n < 115 then 33452031 else 0) else 0)))) else (if n < 129 then (if n < 123
  then (if n < 120 then (if n < 119 then (if n < 118 then 0 else 0) else 0) else (if n < 122 then
  (if n < 121 then 0 else 0) else 0)) else (if n < 126 then (if n < 125 then (if n < 124 then 0
  else 0) else 0) else (if n < 128 then (if n < 127 then 0 else 0) else 0))) else (if n < 135 then
  (if n < 132 then (if n < 131 then (if n < 130 then 0 else 0) else 0) else (if n < 134 then (if n
  < 133 then 0 else 0) else 0)) else (if n < 138 then (if n < 137 then (if n < 136 then 0 else 0)
  else 0) else (if n < 139 then 0 else 0))))) else (if n < 163 then (if n < 152 then (if n < 146
  then (if n < 143 then (if n < 142 then (if n < 141 then 0 else 0) else 0) else (if n < 145 then
  (if n < 144 then 0 else 0) else 32696191)) else (if n < 149 then (if n < 148 then (if n < 147
  then 0 else 0) else 0) else (if n < 151 then (if n < 150 then 0 else 0) else 33490119))) else
  (if n < 158 then (if n < 155 then (if n < 154 then (if n < 153 then 33429903 else 33301279) else
  33052223) else (if n < 157 then (if n < 156 then 32571391 else 0) else 0)) else (if n < 161 then
  (if n < 160 then (if n < 159 then 0 else 0) else 0) else (if n < 162 then 0 else 0)))) else (if
  n < 175 then (if n < 169 then (if n < 166 then (if n < 165 then (if n < 164 then 0 else 0) else
  33525495) else (if n < 168 then (if n < 167 then 0 else 0) else 0)) else (if n < 172 then (if n
  < 171 then (if n < 170 then 0 else 0) else 0) else (if n < 174 then (if n < 173 then 0 else
  33335103) else 0))) else (if n < 181 then (if n < 178 then (if n < 177 then (if n < 176 then 0
  else 33526263) else 33498095) else (if n < 180 then (if n < 179 then 0 else 0) else 33526759))
  else (if n < 184 then (if n < 183 then (if n < 182 then 33499087 else 33443743) else 33328959)
  else (if n < 185 then 33541889 else 33529347))))))) else (if n < 279 then (if n < 233 then (if n
  < 210 then (if n < 198 then (if n < 192 then (if n < 189 then (if n < 188 then (if n < 187 then
  33504263 else 33454095) else 33554431) else (if n < 191 then (if n < 190 then 33529091 else
  33503751) else 33455119)) else (if n < 195 then (if n < 194 then (if n < 193 then 33355807 else
  33503495) else 33504519) else (if n < 197 then (if n < 196 then 33454607 else 33505031) else
  33455631))) else (if n < 204 then (if n < 201 then (if n < 200 then (if n < 199 then 33356831
  else 33159231) else 33505223) else (if n < 203 then (if n < 202 then 33454351 else 33541025)
  else 33542049)) else (if n < 207 then (if n < 206 then (if n < 205 then 33529667 else 33504903)
  else 33455375) else (if n < 209 then (if n < 208 then 33356319 else 33540193) else 33541217))))
  else (if n < 222 then (if n < 216 then (if n < 213 then (if n < 212 then (if n < 211 then
  33528003 else 33503623) else 33540449) else (if n < 215 then (if n < 214 then 33528515 else
  33504647) else 33454863)) else (if n < 219 then (if n < 218 then (if n < 217 then 33541089 else
  33542113) else 33529795) else (if n < 221 then (if n < 220 then 33505159 else 33455887) else
  33357343))) else (if n < 228 then (if n < 225 then (if n < 224 then (if n < 223 then 33160255
  else 32766079) else 33540113) else (if n < 227 then (if n < 226 then 33541137 else 33527843)
  else 33503303)) else (if n < 231 then (if n < 230 then (if n < 229 then 33540497 else 33528611)
  else 33504327) else (if n < 232 then 33454223 else 33503815))))) else (if n < 256 then (if n <
  245 then (if n < 239 then (if n < 236 then (if n < 235 then (if n < 234 then 33455247 else
  33356063) else 33503559) else (if n < 238 then (if n < 237 then 33454735 else 33455759) else
  33357087)) else (if n < 242 then (if n < 241 then (if n < 240 then 33159743 else 33540657) else
  33541681) else (if n < 244 then (if n < 243 then 33528931 else 33503431) else 33540401))) else
  (if n < 251 then (if n < 248 then (if n < 247 then (if n < 246 then 33541425 else 33528419) else
  33504455) else (if n < 250 then (if n < 249 then 33454479 else 33540803) else 33529223)) else
  (if n < 254 then (if n < 253 then (if n < 252 then 33503943 else 33455503) else 33356575) else
  (if n < 255 then 33540721 else 33541745)))) else (if n < 268 then (if n < 262 then (if n < 259
  then (if n < 258 then (if n < 257 then 33529059 else 33503687) else 33540465) else (if n < 261
  then (if n < 260 then 33541489 else 33528547) else 33504711)) else (if n < 265 then (if n < 264
  then (if n < 263 then 33454991 else 33540337) else 33528291) else (if n < 267 then (if n < 266
  then 33504199 else 33540593) else 33528803))) else (if n < 274 then (if n < 271 then (if n < 270
  then (if n < 269 then 33505223 else 33456015) else 33357599) else (if n < 273 then (if n < 272
  then 33160767 else 32767103) else 31979775)) else (if n < 277 then (if n < 276 then (if n < 275
  then 33542141 else 33529851) else 33504295) else (if n < 278 then 33454159 else 33505271))))))
  else (if n < 326 then (if n < 303 then (if n < 291 then (if n < 285 then (if n < 282 then (if n
  < 281 then (if n < 280 then 33456111 else 33355935) else 33357791) else (if n < 284 then (if n <
  283 then 33159487 else 33161151) else 32766591)) else (if n < 288 then (if n < 287 then (if n <
  286 then 32767871 else 31980799) else 30407167) else (if n < 290 then (if n < 289 then 31980287
  else 33504311) else 33454191))) else (if n < 297 then (if n < 294 then (if n < 293 then (if n <
  292 then 33540749 else 33529115) else 33503799) else (if n < 296 then (if n < 295 then 33541103
  else 33529823) else 33504823)) else (if n < 300 then (if n < 299 then (if n < 298 then 33455215
  else 33355999) else 33504567) else (if n < 302 then (if n < 301 then 33454703 else 33541069)
  else 33542093)))) else (if n < 315 then (if n < 309 then (if n < 306 then (if n < 305 then (if n
  < 304 then 33529755 else 33505079) else 33455727) else (if n < 308 then (if n < 307 then
  33357023 else 33159615) else 33540141)) else (if n < 312 then (if n < 311 then (if n < 310 then
  33541165 else 33527899) else 33503415) else (if n < 314 then (if n < 313 then 33540397 else
  33528411) else 33504439))) else (if n < 321 then (if n < 318 then (if n < 317 then (if n < 316
  then 33454447 else 33541055) else 33529727) else (if n < 320 then (if n < 319 then 33504951 else
  33455471) else 33356511)) else (if n < 324 then (if n < 323 then (if n < 322 then 33540991 else
  33529599) else 33504695) else (if n < 325 then 33454959 else 33505207))))) else (if n < 349 then
  (if n < 338 then (if n < 332 then (if n < 329 then (if n < 328 then (if n < 327 then 33455983
  else 33357535) else 33160639) else (if n < 331 then (if n < 330 then 32766847 else 33503351)
  else 33454319)) else (if n < 335 then (if n < 334 then (if n < 333 then 33540831 else 33529279)
  else 33503863) else (if n < 337 then (if n < 336 then 33455343 else 33356255) else 33540735)))
  else (if n < 344 then (if n < 341 then (if n < 340 then (if n < 339 then 33529087 else 33503607)
  else 33504631) else (if n < 343 then (if n < 342 then 33454831 else 33540317) else 33528251))
  else (if n < 347 then (if n < 346 then (if n < 345 then 33504119 else 33455855) else 33357279)
  else (if n < 348 then 33160127 else 33503479)))) else (if n < 361 then (if n < 355 then (if n <
  352 then (if n < 351 then (if n < 350 then 33454575 else 33540797) else 33529211) else (if n <
  354 then (if n < 353 then 33503991 else 33455599) else 33356767)) else (if n < 358 then (if n <
  357 then (if n < 356 then 33503735 else 33540991) else 33542013) else (if n < 360 then (if n <
  359 then 33529595 else 33504759) else 33455087))) else (if n < 367 then (if n < 364 then (if n <
  363 then (if n < 362 then 33540349 else 33528315) else 33504247) else (if n < 366 then (if n <
  365 then 33505271 else 33456111) else 33357791)) else (if n < 370 then (if n < 369 then (if n <
  368 then 33161151 else 32767871) else 31981311) else (if n < 371 then 30408191 else
  27261951)))))))) else (if n < 558 then (if n < 465 then (if n < 419 then (if n < 396 then (if n
  < 384 then (if n < 378 then (if n < 375 then (if n < 374 then (if n < 373 then 33540867 else
  33529351) else 33504271) else (if n < 377 then (if n < 376 then 33454111 else 33529623) else
  33504783)) else (if n < 381 then (if n < 380 then (if n < 379 then 33455135 else 33355839) else
  33503503) else (if n < 383 then (if n < 382 then 33454623 else 33504015) else 33455647))) else
  (if n < 390 then (if n < 387 then (if n < 386 then (if n < 385 then 33356863 else 33159295) else
  33528903) else (if n < 389 then (if n < 388 then 33503375 else 33504399) else 33454367)) else
  (if n < 393 then (if n < 392 then (if n < 391 then 33503887 else 33540515) else 33528647) else
  (if n < 395 then (if n < 394 then 33504911 else 33455391) else 33356351)))) else (if n < 408
  then (if n < 402 then (if n < 399 then (if n < 398 then (if n < 397 then 33503631 else 33454879)
  else 33504143) else (if n < 401 then (if n < 400 then 33455903 else 33357375) else 33160319))
  else (if n < 405 then (if n < 404 then (if n < 403 then 32766207 else 33541651) else 33528871)
  else (if n < 407 then (if n < 406 then 33503311 else 33540371) else 33541395))) else (if n < 414
  then (if n < 411 then (if n < 410 then (if n < 409 then 33528359 else 33504335) else 33454239)
  else (if n < 413 then (if n < 412 then 33540243 else 33528103) else 33503823)) else (if n < 417
  then (if n < 416 then (if n < 415 then 33455263 else 33356095) else 33540827) else (if n < 418
  then 33529271 else 33503567))))) else (if n < 442 then (if n < 431 then (if n < 425 then (if n <
  422 then (if n < 421 then (if n < 420 then 33454751 else 33540819) else 33529255) else (if n <
  424 then (if n < 423 then 33504079 else 33455775) else 33357119)) else (if n < 428 then (if n <
  427 then (if n < 426 then 33159807 else 33503439) else 33504463) else (if n < 430 then (if n <
  429 then 33454495 else 33541115) else 33529847))) else (if n < 437 then (if n < 434 then (if n <
  433 then (if n < 432 then 33504975 else 33455519) else 33356607) else (if n < 436 then (if n <
  435 then 33504719 else 33455007) else 33505263)) else (if n < 440 then (if n < 439 then (if n <
  438 then 33540595 else 33528807) else 33505231) else (if n < 441 then 33456031 else 33357631))))
  else (if n < 454 then (if n < 448 then (if n < 445 then (if n < 444 then (if n < 443 then
  33160831 else 32767231) else 31980031) else (if n < 447 then (if n < 446 then 33540875 else
  33529367) else 33504303)) else (if n < 451 then (if n < 450 then (if n < 449 then 33454175 else
  33504815) else 33455199) else (if n < 453 then (if n < 452 then 33355967 else 33505199) else
  33454687))) else (if n < 460 then (if n < 457 then (if n < 456 then (if n < 455 then 33504047
  else 33455711) else 33356991) else (if n < 459 then (if n < 458 then 33159551 else 33540651)
  else 33541675)) else (if n < 463 then (if n < 462 then (if n < 461 then 33528919 else 33503407)
  else 33454431) else (if n < 464 then 33540779 else 33529175)))))) else (if n < 512 then (if n <
  489 then (if n < 477 then (if n < 471 then (if n < 468 then (if n < 467 then (if n < 466 then
  33503919 else 33455455) else 33356479) else (if n < 470 then (if n < 469 then 33540971 else
  33529559) else 33504687)) else (if n < 474 then (if n < 473 then (if n < 472 then 33454943 else
  33505199) else 33455967) else (if n < 476 then (if n < 475 then 33357503 else 33160575) else
  32766719))) else (if n < 483 then (if n < 480 then (if n < 479 then (if n < 478 then 33454303
  else 33503855) else 33455327) else (if n < 482 then (if n < 481 then 33356223 else 33503599)
  else 33454815)) else (if n < 486 then (if n < 485 then (if n < 484 then 33505135 else 33455839)
  else 33357247) else (if n < 488 then (if n < 487 then 33160063 else 33540923) else 33529463))))
  else (if n < 501 then (if n < 495 then (if n < 492 then (if n < 491 then (if n < 490 then
  33504495 else 33454559) else 33505007) else (if n < 494 then (if n < 493 then 33455583 else
  33356735) else 33540987)) else (if n < 498 then (if n < 497 then (if n < 496 then 33542011 else
  33529591) else 33504751) else (if n < 500 then (if n < 499 then 33455071 else 33540347) else
  33541371))) else (if n < 507 then (if n < 504 then (if n < 503 then (if n < 502 then 33528311
  else 33504239) else 33540603) else (if n < 506 then (if n < 505 then 33528823 else 33505263)
  else 33456095)) else (if n < 510 then (if n < 509 then (if n < 508 then 33357759 else 33161087)
  else 32767743) else (if n < 511 then 31981055 else 30407679))))) else (if n < 535 then (if n <
  524 then (if n < 518 then (if n < 515 then (if n < 514 then (if n < 513 then 33540103 else
  33541127) else 33527823) else (if n < 517 then (if n < 516 then 33503263 else 33454143) else
  33355903)) else (if n < 521 then (if n < 520 then (if n < 519 then 33159423 else 32766463) else
  31980543) else (if n < 523 then (if n < 522 then 30408703 else 27262975) else 0))) else (if n <
  530 then (if n < 527 then (if n < 526 then (if n < 525 then 33542143 else 0) else 0) else (if n
  < 529 then (if n < 528 then 0 else 0) else 0)) else (if n < 533 then (if n < 532 then (if n <
  531 then 0 else 0) else 0) else (if n < 534 then 33554431 else 33554431)))) else (if n < 547
  then (if n < 541 then (if n < 538 then (if n < 537 then (if n < 536 then 33554431 else 33554431)
  else 33554431) else (if n < 540 then (if n < 539 then 33554431 else 33554431) else 33550847))
  else (if n < 544 then (if n < 543 then (if n < 542 then 33546749 else 33554431) else 33554431)
  else (if n < 546 then (if n < 545 then 33554431 else 33554431) else 33554431))) else (if n < 553
  then (if n < 550 then (if n < 549 then (if n < 548 then 33554431 else 33554431) else 33554431)
  else (if n < 552 then (if n < 551 then 33554431 else 33554431) else 33554431)) else (if n < 556
  then (if n < 555 then (if n < 554 then 33554431 else 33554431) else 33554431) else (if n < 557
  then 33551359 else 33547261))))))) else (if n < 651 then (if n < 605 then (if n < 582 then (if n
  < 570 then (if n < 564 then (if n < 561 then (if n < 560 then (if n < 559 then 33554431 else
  33554431) else 33554431) else (if n < 563 then (if n < 562 then 33554431 else 33554431) else
  33554431)) else (if n < 567 then (if n < 566 then (if n < 565 then 33554431 else 33550335) else
  33554431) else (if n < 569 then (if n < 568 then 33550335 else 33554431) else 33540863))) else
  (if n < 576 then (if n < 573 then (if n < 572 then (if n < 571 then 33529343 else 33528247) else
  33504111) else (if n < 575 then (if n < 574 then 33540315 else 33541627) else 33527815)) else
  (if n < 579 then (if n < 578 then (if n < 577 then 33503247 else 33540387) else 33528391) else
  (if n < 581 then (if n < 580 then 33540283 else 33528183) else 33503983)))) else (if n < 594
  then (if n < 588 then (if n < 585 then (if n < 584 then (if n < 583 then 33541115 else 33529847)
  else 33528471) else (if n < 587 then (if n < 586 then 33504559 else 33540603) else 33528631))
  else (if n < 591 then (if n < 590 then (if n < 589 then 33504879 else 33541627) else 33528823)
  else (if n < 593 then (if n < 592 then 33505263 else 33528087) else 33503791))) else (if n < 600
  then (if n < 597 then (if n < 596 then (if n < 595 then 33541115 else 33529847) else 33528823)
  else (if n < 599 then (if n < 598 then 33505263 else 33528823) else 33505263)) else (if n < 603
  then (if n < 602 then (if n < 601 then 33540603 else 33541587) else 33528743) else (if n < 604
  then 33505103 else 33540573))))) else (if n < 628 then (if n < 617 then (if n < 611 then (if n <
  608 then (if n < 607 then (if n < 606 then 33528763 else 33528379) else 33504375) else (if n <
  610 then (if n < 609 then 33540607 else 33528799) else 33505215)) else (if n < 614 then (if n <
  613 then (if n < 612 then 33528455 else 33504527) else 33528443) else (if n < 616 then (if n <
  615 then 33504503 else 33541039) else 33529695))) else (if n < 623 then (if n < 620 then (if n <
  619 then (if n < 618 then 33540607 else 33527963) else 33503543) else (if n < 622 then (if n <
  621 then 33528831 else 33505279) else 33528551)) else (if n < 626 then (if n < 625 then (if n <
  624 then 33504719 else 33540673) else 33528963) else (if n < 627 then 33541345 else 33528259))))
  else (if n < 640 then (if n < 634 then (if n < 631 then (if n < 630 then (if n < 629 then
  33504135 else 33540321) else 33528131) else (if n < 633 then (if n < 632 then 33503879 else 0)
  else 0)) else (if n < 637 then (if n < 636 then (if n < 635 then 33525759 else 0) else 0) else
  (if n < 639 then (if n < 638 then 33540225 else 33542143) else 33528067))) else (if n < 646 then
  (if n < 643 then (if n < 642 then (if n < 641 then 0 else 0) else 33523711) else (if n < 645
  then (if n < 644 then 33492991 else 0) else 0)) else (if n < 649 then (if n < 648 then (if n <
  647 then 33527807 else 33540605) else 33554431) else (if n < 650 then 33528707 else
  33541119)))))) else (if n < 698 then (if n < 675 then (if n < 663 then (if n < 657 then (if n <
  654 then (if n < 653 then (if n < 652 then 33529855 else 33505031) else 33541631) else (if n <
  656 then (if n < 655 then 33528611 else 33504839) else 33541631)) else (if n < 660 then (if n <
  659 then (if n < 658 then 33528219 else 33504055) else 33541617) else (if n < 662 then (if n <
  661 then 33527875 else 33503367) else 33528483))) else (if n < 669 then (if n < 666 then (if n <
  665 then (if n < 664 then 33504583 else 33541101) else 33529819) else (if n < 668 then (if n <
  667 then 33540605 else 33541629) else 33528827)) else (if n < 672 then (if n < 671 then (if n <
  670 then 33505271 else 33527827) else 33503271) else (if n < 674 then (if n < 673 then 33541627
  else 33528675) else 33504967)))) else (if n < 687 then (if n < 681 then (if n < 678 then (if n <
  677 then (if n < 676 then 33528791 else 33505199) else 33541565) else (if n < 680 then (if n <
  679 then 33528699 else 33505015) else 33540607)) else (if n < 684 then (if n < 683 then (if n <
  682 then 33528739 else 33505095) else 33541117) else (if n < 686 then (if n < 685 then 33529851
  else 33528759) else 33542139))) else (if n < 693 then (if n < 690 then (if n < 689 then (if n <
  688 then 33528759 else 33528823) else 33542143) else (if n < 692 then (if n < 691 then 33528799
  else 33528807) else 33540607)) else (if n < 696 then (if n < 695 then (if n < 694 then 33541601
  else 33528451) else 33527971) else (if n < 697 then 33528183 else 33541501))))) else (if n < 721
  then (if n < 710 then (if n < 704 then (if n < 701 then (if n < 700 then (if n < 699 then
  33528571 else 33541119) else 33529855) else (if n < 703 then (if n < 702 then 33542143 else
  33529855) else 33542075)) else (if n < 707 then (if n < 706 then (if n < 705 then 33529415 else
  33542139) else 33527911) else (if n < 709 then (if n < 708 then 33529531 else 33541631) else
  33528475))) else (if n < 716 then (if n < 713 then (if n < 712 then (if n < 711 then 0 else 0)
  else 33541119) else (if n < 715 then (if n < 714 then 33541629 else 33528707) else 33527867))
  else (if n < 719 then (if n < 718 then (if n < 717 then 33528339 else 33540859) else 33529335)
  else (if n < 720 then 33529847 else 33529847)))) else (if n < 733 then (if n < 727 then (if n <
  724 then (if n < 723 then (if n < 722 then 33528123 else 33528831) else 33541119) else (if n <
  726 then (if n < 725 then 33528731 else 33541565) else 33528699)) else (if n < 730 then (if n <
  729 then (if n < 728 then 33540913 else 33529443) else 33528695) else (if n < 732 then (if n <
  731 then 33528823 else 33540603) else 33528035))) else (if n < 739 then (if n < 736 then (if n <
  735 then (if n < 734 then 33540705 else 33529027) else 33528187) else (if n < 738 then (if n <
  737 then 33540605 else 33528771) else 33528059)) else (if n < 742 then (if n < 741 then (if n <
  740 then 33528643 else 33540593) else 33528803) else (if n < 743 then 33541631 else
  33527907)))))))))
def m0 (q : Fin 744) : Nat := m0Nat q.val
def m1 (q : Fin 744) : Nat := m1Nat q.val

def refTrans0 (n : Nat) : Option (Fin 2 × Dir × Fin 744) :=
  (if n < 372 then (if n < 186 then (if n < 93 then (if n < 46 then (if n < 23 then (if n < 11
  then (if n < 5 then (if n < 2 then (if n < 1 then some (0, .right, 523) else some (0, .left, 3))
  else (if n < 3 then some (0, .right, 1) else (if n < 4 then some (1, .left, 566) else some (0,
  .left, 6)))) else (if n < 8 then (if n < 6 then some (0, .right, 4) else (if n < 7 then some (0,
  .left, 7) else some (0, .left, 567))) else (if n < 9 then some (1, .left, 7) else (if n < 10
  then some (1, .left, 10) else some (0, .left, 14))))) else (if n < 17 then (if n < 14 then (if n
  < 12 then some (1, .left, 14) else (if n < 13 then some (0, .left, 0) else some (1, .left, 0)))
  else (if n < 15 then some (0, .left, 16) else (if n < 16 then some (1, .left, 16) else some (0,
  .left, 18)))) else (if n < 20 then (if n < 18 then some (1, .left, 18) else (if n < 19 then some
  (0, .left, 20) else some (1, .left, 20))) else (if n < 21 then some (0, .left, 22) else (if n <
  22 then some (1, .left, 22) else some (0, .left, 24)))))) else (if n < 34 then (if n < 28 then
  (if n < 25 then (if n < 24 then some (1, .left, 24) else some (0, .left, 26)) else (if n < 26
  then some (1, .left, 26) else (if n < 27 then some (0, .left, 28) else some (1, .left, 28))))
  else (if n < 31 then (if n < 29 then some (0, .left, 12) else (if n < 30 then some (1, .left,
  12) else some (0, .left, 565))) else (if n < 32 then some (1, .right, 30) else (if n < 33 then
  some (0, .right, 33) else some (0, .right, 34))))) else (if n < 40 then (if n < 37 then (if n <
  35 then some (1, .left, 566) else (if n < 36 then some (0, .right, 34) else some (0, .left,
  37))) else (if n < 38 then some (1, .left, 38) else (if n < 39 then some (1, .left, 177) else
  some (0, .left, 40)))) else (if n < 43 then (if n < 41 then some (0, .left, 41) else (if n < 42
  then some (1, .left, 42) else some (0, .left, 43))) else (if n < 44 then some (0, .left, 59)
  else (if n < 45 then some (0, .left, 45) else some (0, .left, 46))))))) else (if n < 69 then (if
  n < 57 then (if n < 51 then (if n < 48 then (if n < 47 then some (0, .left, 47) else some (1,
  .left, 172)) else (if n < 49 then some (0, .left, 49) else (if n < 50 then some (0, .left, 50)
  else some (0, .left, 51)))) else (if n < 54 then (if n < 52 then some (1, .left, 52) else (if n
  < 53 then some (1, .left, 53) else some (0, .left, 121))) else (if n < 55 then some (0, .left,
  55) else (if n < 56 then some (0, .left, 56) else some (0, .left, 57))))) else (if n < 63 then
  (if n < 60 then (if n < 58 then some (0, .left, 58) else (if n < 59 then some (1, .left, 59)
  else some (1, .left, 60))) else (if n < 61 then some (1, .left, 23) else (if n < 62 then some
  (0, .left, 62) else some (0, .left, 63)))) else (if n < 66 then (if n < 64 then some (1, .left,
  57) else (if n < 65 then some (0, .left, 65) else some (1, .left, 66))) else (if n < 67 then
  some (0, .left, 67) else (if n < 68 then some (1, .left, 68) else some (1, .left, 69)))))) else
  (if n < 81 then (if n < 75 then (if n < 72 then (if n < 70 then some (1, .left, 70) else (if n <
  71 then some (1, .left, 71) else some (1, .left, 72))) else (if n < 73 then some (0, .left, 26)
  else (if n < 74 then some (0, .left, 74) else some (1, .left, 46)))) else (if n < 78 then (if n
  < 76 then some (0, .left, 76) else (if n < 77 then some (0, .left, 77) else some (0, .left,
  78))) else (if n < 79 then some (0, .left, 79) else (if n < 80 then some (0, .left, 120) else
  some (0, .left, 81))))) else (if n < 87 then (if n < 84 then (if n < 82 then some (1, .left, 82)
  else (if n < 83 then some (0, .left, 83) else some (0, .left, 84))) else (if n < 85 then some
  (0, .left, 19) else (if n < 86 then some (0, .left, 86) else some (0, .left, 87)))) else (if n <
  90 then (if n < 88 then some (0, .left, 88) else (if n < 89 then some (1, .left, 79) else some
  (0, .left, 90))) else (if n < 91 then some (1, .left, 93) else (if n < 92 then some (0, .left,
  92) else some (0, .left, 0)))))))) else (if n < 139 then (if n < 116 then (if n < 104 then (if n
  < 98 then (if n < 95 then (if n < 94 then some (0, .left, 94) else some (1, .left, 95)) else (if
  n < 96 then some (0, .left, 96) else (if n < 97 then some (1, .left, 97) else some (0, .left,
  98)))) else (if n < 101 then (if n < 99 then some (0, .left, 99) else (if n < 100 then some (0,
  .left, 100) else some (0, .left, 91))) else (if n < 102 then some (0, .left, 102) else (if n <
  103 then some (1, .left, 103) else some (0, .left, 104))))) else (if n < 110 then (if n < 107
  then (if n < 105 then some (1, .left, 84) else (if n < 106 then some (0, .left, 106) else some
  (0, .left, 109))) else (if n < 108 then some (0, .left, 108) else (if n < 109 then some (1,
  .left, 109) else some (0, .left, 113)))) else (if n < 113 then (if n < 111 then some (0, .left,
  111) else (if n < 112 then some (0, .left, 112) else some (1, .left, 113))) else (if n < 114
  then some (0, .left, 114) else (if n < 115 then some (1, .left, 19) else some (0, .left,
  116)))))) else (if n < 127 then (if n < 121 then (if n < 118 then (if n < 117 then some (0,
  .left, 117) else some (0, .left, 118)) else (if n < 119 then some (1, .left, 119) else (if n <
  120 then some (1, .left, 120) else some (1, .left, 121)))) else (if n < 124 then (if n < 122
  then some (0, .left, 22) else (if n < 123 then some (0, .left, 123) else some (1, .left, 124)))
  else (if n < 125 then some (0, .left, 125) else (if n < 126 then some (1, .left, 114) else some
  (0, .left, 127))))) else (if n < 133 then (if n < 130 then (if n < 128 then some (1, .left, 128)
  else (if n < 129 then some (0, .left, 129) else some (1, .left, 130))) else (if n < 131 then
  some (1, .left, 131) else (if n < 132 then some (1, .left, 132) else some (0, .left, 145))))
  else (if n < 136 then (if n < 134 then some (0, .left, 134) else (if n < 135 then some (0,
  .left, 135) else some (0, .left, 136))) else (if n < 137 then some (1, .left, 137) else (if n <
  138 then some (0, .left, 173) else some (0, .left, 139))))))) else (if n < 162 then (if n < 150
  then (if n < 144 then (if n < 141 then (if n < 140 then some (0, .left, 140) else some (0,
  .left, 141)) else (if n < 142 then some (1, .left, 142) else (if n < 143 then some (1, .left,
  143) else some (0, .left, 144)))) else (if n < 147 then (if n < 145 then some (1, .left, 145)
  else (if n < 146 then some (0, .left, 72) else some (0, .left, 147))) else (if n < 148 then some
  (1, .left, 135) else (if n < 149 then some (0, .left, 149) else some (0, .left, 150))))) else
  (if n < 156 then (if n < 153 then (if n < 151 then some (0, .left, 151) else (if n < 152 then
  some (1, .left, 152) else some (0, .left, 153))) else (if n < 154 then some (1, .left, 154) else
  (if n < 155 then some (1, .left, 155) else some (0, .left, 24)))) else (if n < 159 then (if n <
  157 then some (0, .left, 157) else (if n < 158 then some (0, .left, 165) else some (0, .left,
  159))) else (if n < 160 then some (0, .left, 160) else (if n < 161 then some (0, .left, 161)
  else some (1, .left, 162)))))) else (if n < 174 then (if n < 168 then (if n < 165 then (if n <
  163 then some (1, .left, 153) else (if n < 164 then some (0, .left, 164) else some (1, .left,
  165))) else (if n < 166 then some (1, .left, 15) else (if n < 167 then some (0, .left, 167) else
  some (0, .left, 176)))) else (if n < 171 then (if n < 169 then some (0, .left, 169) else (if n <
  170 then some (0, .left, 170) else some (0, .left, 171))) else (if n < 172 then some (0, .left,
  172) else (if n < 173 then some (1, .left, 173) else some (0, .left, 20))))) else (if n < 180
  then (if n < 177 then (if n < 175 then some (0, .left, 175) else (if n < 176 then some (1,
  .left, 176) else some (0, .left, 177))) else (if n < 178 then some (0, .left, 17) else (if n <
  179 then some (0, .left, 179) else some (1, .left, 180)))) else (if n < 183 then (if n < 181
  then some (0, .left, 181) else (if n < 182 then some (0, .left, 182) else some (0, .left, 183)))
  else (if n < 184 then some (0, .left, 70) else (if n < 185 then some (0, .right, 32) else some
  (0, .right, 184))))))))) else (if n < 279 then (if n < 232 then (if n < 209 then (if n < 197
  then (if n < 191 then (if n < 188 then (if n < 187 then some (0, .right, 185) else some (0,
  .right, 186)) else (if n < 189 then some (0, .right, 551) else (if n < 190 then some (0, .right,
  188) else some (0, .right, 639)))) else (if n < 194 then (if n < 192 then some (0, .right, 190)
  else (if n < 193 then some (0, .right, 187) else some (0, .right, 714))) else (if n < 195 then
  some (0, .right, 694) else (if n < 196 then some (0, .right, 193) else some (0, .right, 714)))))
  else (if n < 203 then (if n < 200 then (if n < 198 then some (0, .right, 652) else (if n < 199
  then some (0, .right, 195) else some (0, .right, 192))) else (if n < 201 then some (0, .right,
  741) else (if n < 202 then some (0, .right, 661) else some (0, .right, 547)))) else (if n < 206
  then (if n < 204 then some (0, .right, 546) else (if n < 205 then some (0, .right, 202) else
  some (0, .right, 739))) else (if n < 207 then some (0, .right, 631) else (if n < 208 then some
  (0, .right, 201) else some (0, .right, 115)))))) else (if n < 220 then (if n < 214 then (if n <
  211 then (if n < 210 then some (0, .right, 48) else some (0, .right, 208)) else (if n < 212 then
  some (0, .right, 210) else (if n < 213 then some (0, .right, 545) else some (0, .right, 212))))
  else (if n < 217 then (if n < 215 then some (0, .right, 213) else (if n < 216 then some (0,
  .right, 211) else some (0, .right, 168))) else (if n < 218 then some (0, .right, 156) else (if n
  < 219 then some (0, .right, 216) else some (0, .right, 737))))) else (if n < 226 then (if n <
  223 then (if n < 221 then some (0, .right, 628) else (if n < 222 then some (0, .right, 215) else
  some (0, .right, 207))) else (if n < 224 then some (0, .right, 199) else (if n < 225 then some
  (0, .right, 174) else some (0, .right, 542)))) else (if n < 229 then (if n < 227 then some (0,
  .right, 224) else (if n < 228 then some (0, .right, 226) else some (0, .right, 54))) else (if n
  < 230 then some (0, .right, 228) else (if n < 231 then some (0, .right, 229) else some (0,
  .right, 227))))))) else (if n < 255 then (if n < 243 then (if n < 237 then (if n < 234 then (if
  n < 233 then some (0, .right, 229) else some (0, .right, 232)) else (if n < 235 then some (0,
  .right, 231) else (if n < 236 then some (0, .right, 695) else some (0, .right, 235)))) else (if
  n < 240 then (if n < 238 then some (0, .right, 200) else (if n < 239 then some (0, .right, 236)
  else some (0, .right, 234))) else (if n < 241 then some (0, .right, 546) else (if n < 242 then
  some (0, .right, 547) else some (0, .right, 240))))) else (if n < 249 then (if n < 246 then (if
  n < 244 then some (0, .right, 743) else (if n < 245 then some (0, .right, 133) else some (0,
  .right, 148))) else (if n < 247 then some (0, .right, 244) else (if n < 248 then some (0,
  .right, 246) else some (0, .right, 243)))) else (if n < 252 then (if n < 250 then some (0,
  .right, 545) else (if n < 251 then some (0, .right, 249) else some (0, .right, 250))) else (if n
  < 253 then some (0, .right, 251) else (if n < 254 then some (0, .right, 248) else some (0,
  .right, 75)))))) else (if n < 267 then (if n < 261 then (if n < 258 then (if n < 256 then some
  (0, .right, 156) else (if n < 257 then some (0, .right, 254) else some (0, .right, 732))) else
  (if n < 259 then some (0, .right, 80) else (if n < 260 then some (0, .right, 543) else some (0,
  .right, 258)))) else (if n < 264 then (if n < 262 then some (0, .right, 260) else (if n < 263
  then some (0, .right, 257) else some (0, .right, 166))) else (if n < 265 then some (0, .right,
  263) else (if n < 266 then some (0, .right, 264) else some (0, .right, 551))))) else (if n < 273
  then (if n < 270 then (if n < 268 then some (0, .right, 266) else (if n < 269 then some (0,
  .right, 267) else some (0, .right, 265))) else (if n < 271 then some (0, .right, 262) else (if n
  < 272 then some (0, .right, 253) else some (0, .right, 239)))) else (if n < 276 then (if n < 274
  then some (0, .right, 223) else (if n < 275 then some (0, .right, 542) else some (0, .right,
  274))) else (if n < 277 then some (0, .right, 716) else (if n < 278 then some (0, .right, 671)
  else some (0, .right, 275)))))))) else (if n < 325 then (if n < 302 then (if n < 290 then (if n
  < 284 then (if n < 281 then (if n < 280 then some (0, .right, 278) else some (0, .right, 277))
  else (if n < 282 then some (0, .right, 279) else (if n < 283 then some (0, .right, 280) else
  some (0, .right, 281)))) else (if n < 287 then (if n < 285 then some (0, .right, 282) else (if n
  < 286 then some (0, .right, 283) else some (0, .right, 284))) else (if n < 288 then some (0,
  .right, 273) else (if n < 289 then some (0, .right, 285) else some (0, .right, 684))))) else (if
  n < 296 then (if n < 293 then (if n < 291 then some (0, .right, 278) else (if n < 292 then some
  (0, .right, 552) else some (0, .right, 291))) else (if n < 294 then some (0, .right, 605) else
  (if n < 295 then some (0, .right, 553) else some (0, .right, 294)))) else (if n < 299 then (if n
  < 297 then some (0, .right, 616) else (if n < 298 then some (0, .right, 293) else some (0,
  .right, 290))) else (if n < 300 then some (0, .right, 709) else (if n < 301 then some (0,
  .right, 619) else some (0, .right, 543)))))) else (if n < 313 then (if n < 307 then (if n < 304
  then (if n < 303 then some (0, .right, 542) else some (0, .right, 301)) else (if n < 305 then
  some (0, .right, 724) else (if n < 306 then some (0, .right, 658) else some (0, .right, 300))))
  else (if n < 310 then (if n < 308 then some (0, .right, 298) else (if n < 309 then some (0,
  .right, 158) else some (0, .right, 75))) else (if n < 311 then some (0, .right, 308) else (if n
  < 312 then some (0, .right, 310) else some (0, .right, 39))))) else (if n < 319 then (if n < 316
  then (if n < 314 then some (0, .right, 312) else (if n < 315 then some (0, .right, 313) else
  some (0, .right, 311))) else (if n < 317 then some (0, .right, 542) else (if n < 318 then some
  (0, .right, 316) else some (0, .right, 726)))) else (if n < 322 then (if n < 320 then some (0,
  .right, 669) else (if n < 321 then some (0, .right, 315) else some (0, .right, 115))) else (if n
  < 323 then some (0, .right, 321) else (if n < 324 then some (0, .right, 722) else some (0,
  .right, 621))))))) else (if n < 348 then (if n < 336 then (if n < 330 then (if n < 327 then (if
  n < 326 then some (0, .right, 690) else some (0, .right, 610)) else (if n < 328 then some (0,
  .right, 324) else (if n < 329 then some (0, .right, 320) else some (0, .right, 307)))) else (if
  n < 333 then (if n < 331 then some (0, .right, 715) else (if n < 332 then some (0, .right, 330)
  else some (0, .right, 542))) else (if n < 334 then some (0, .right, 332) else (if n < 335 then
  some (0, .right, 721) else some (0, .right, 334))))) else (if n < 342 then (if n < 339 then (if
  n < 337 then some (0, .right, 331) else (if n < 338 then some (0, .right, 85) else some (0,
  .right, 337))) else (if n < 340 then some (0, .right, 722) else (if n < 341 then some (0,
  .right, 605) else some (0, .right, 339)))) else (if n < 345 then (if n < 343 then some (0,
  .right, 553) else (if n < 344 then some (0, .right, 342) else some (0, .right, 343))) else (if n
  < 346 then some (0, .right, 344) else (if n < 347 then some (0, .right, 341) else some (0,
  .right, 336)))))) else (if n < 360 then (if n < 354 then (if n < 351 then (if n < 349 then some
  (0, .right, 726) else (if n < 350 then some (0, .right, 348) else some (0, .right, 546))) else
  (if n < 352 then some (0, .right, 350) else (if n < 353 then some (0, .right, 735) else some (0,
  .right, 352)))) else (if n < 357 then (if n < 355 then some (0, .right, 349) else (if n < 356
  then some (0, .right, 738) else some (0, .right, 545))) else (if n < 358 then some (0, .right,
  543) else (if n < 359 then some (0, .right, 356) else some (0, .right, 698))))) else (if n < 366
  then (if n < 363 then (if n < 361 then some (0, .right, 355) else (if n < 362 then some (0,
  .right, 44) else some (0, .right, 361))) else (if n < 364 then some (0, .right, 362) else (if n
  < 365 then some (0, .right, 702) else some (0, .right, 363)))) else (if n < 369 then (if n < 367
  then some (0, .right, 360) else (if n < 368 then some (0, .right, 354) else some (0, .right,
  347))) else (if n < 370 then some (0, .right, 329) else (if n < 371 then some (0, .right, 288)
  else some (0, .right, 287)))))))))) else (if n < 558 then (if n < 465 then (if n < 418 then (if
  n < 395 then (if n < 383 then (if n < 377 then (if n < 374 then (if n < 373 then some (0,
  .right, 545) else some (0, .right, 372)) else (if n < 375 then some (0, .right, 685) else (if n
  < 376 then some (0, .right, 576) else some (0, .right, 209)))) else (if n < 380 then (if n < 378
  then some (0, .right, 685) else (if n < 379 then some (0, .right, 572) else some (0, .right,
  375))) else (if n < 381 then some (0, .right, 570) else (if n < 382 then some (0, .right, 380)
  else some (0, .right, 690))))) else (if n < 389 then (if n < 386 then (if n < 384 then some (0,
  .right, 382) else (if n < 385 then some (0, .right, 381) else some (0, .right, 379))) else (if n
  < 387 then some (0, .right, 245) else (if n < 388 then some (0, .right, 690) else some (0,
  .right, 578)))) else (if n < 392 then (if n < 390 then some (0, .right, 387) else (if n < 391
  then some (0, .right, 583) else some (0, .right, 557))) else (if n < 393 then some (0, .right,
  391) else (if n < 394 then some (0, .right, 392) else some (0, .right, 390)))))) else (if n <
  406 then (if n < 400 then (if n < 397 then (if n < 396 then some (0, .right, 389) else some (0,
  .right, 295)) else (if n < 398 then some (0, .right, 396) else (if n < 399 then some (0, .right,
  722) else some (0, .right, 398)))) else (if n < 403 then (if n < 401 then some (0, .right, 397)
  else (if n < 402 then some (0, .right, 395) else some (0, .right, 385))) else (if n < 404 then
  some (0, .right, 543) else (if n < 405 then some (0, .right, 356) else some (0, .right, 696)))))
  else (if n < 412 then (if n < 409 then (if n < 407 then some (0, .right, 133) else (if n < 408
  then some (0, .right, 105) else some (0, .right, 406))) else (if n < 410 then some (0, .right,
  408) else (if n < 411 then some (0, .right, 405) else some (0, .right, 61)))) else (if n < 415
  then (if n < 413 then some (0, .right, 411) else (if n < 414 then some (0, .right, 412) else
  some (0, .right, 413))) else (if n < 416 then some (0, .right, 410) else (if n < 417 then some
  (0, .right, 543) else some (0, .right, 416))))))) else (if n < 441 then (if n < 429 then (if n <
  423 then (if n < 420 then (if n < 419 then some (0, .right, 687) else some (0, .right, 418))
  else (if n < 421 then some (0, .right, 133) else (if n < 422 then some (0, .right, 420) else
  some (0, .right, 691)))) else (if n < 426 then (if n < 424 then some (0, .right, 422) else (if n
  < 425 then some (0, .right, 419) else some (0, .right, 415))) else (if n < 427 then some (0,
  .right, 706) else (if n < 428 then some (0, .right, 719) else some (0, .right, 426))))) else (if
  n < 435 then (if n < 432 then (if n < 430 then some (0, .right, 543) else (if n < 431 then some
  (0, .right, 429) else some (0, .right, 688))) else (if n < 433 then some (0, .right, 597) else
  (if n < 434 then some (0, .right, 428) else some (0, .right, 691)))) else (if n < 438 then (if n
  < 436 then some (0, .right, 623) else (if n < 437 then some (0, .right, 595) else some (0,
  .right, 553))) else (if n < 439 then some (0, .right, 437) else (if n < 440 then some (0,
  .right, 438) else some (0, .right, 436)))))) else (if n < 453 then (if n < 447 then (if n < 444
  then (if n < 442 then some (0, .right, 435) else (if n < 443 then some (0, .right, 433) else
  some (0, .right, 425))) else (if n < 445 then some (0, .right, 402) else (if n < 446 then some
  (0, .right, 543) else some (0, .right, 445)))) else (if n < 450 then (if n < 448 then some (0,
  .right, 687) else (if n < 449 then some (0, .right, 588) else some (0, .right, 687))) else (if n
  < 451 then some (0, .right, 593) else (if n < 452 then some (0, .right, 448) else some (0,
  .right, 583))))) else (if n < 459 then (if n < 456 then (if n < 454 then some (0, .right, 452)
  else (if n < 455 then some (0, .right, 730) else some (0, .right, 454))) else (if n < 457 then
  some (0, .right, 453) else (if n < 458 then some (0, .right, 451) else some (0, .right, 148))))
  else (if n < 462 then (if n < 460 then some (0, .right, 101) else (if n < 461 then some (0,
  .right, 458) else some (0, .right, 730))) else (if n < 463 then some (0, .right, 461) else (if n
  < 464 then some (0, .right, 146) else some (0, .right, 463)))))))) else (if n < 511 then (if n <
  488 then (if n < 476 then (if n < 470 then (if n < 467 then (if n < 466 then some (0, .right,
  696) else some (0, .right, 465)) else (if n < 468 then some (0, .right, 462) else (if n < 469
  then some (0, .right, 543) else some (0, .right, 468)))) else (if n < 473 then (if n < 471 then
  some (0, .right, 688) else (if n < 472 then some (0, .right, 597) else some (0, .right, 688)))
  else (if n < 474 then some (0, .right, 599) else (if n < 475 then some (0, .right, 471) else
  some (0, .right, 467))))) else (if n < 482 then (if n < 479 then (if n < 477 then some (0,
  .right, 457) else (if n < 478 then some (0, .right, 436) else some (0, .right, 688))) else (if n
  < 480 then some (0, .right, 478) else (if n < 481 then some (0, .right, 477) else some (0,
  .right, 688)))) else (if n < 485 then (if n < 483 then some (0, .right, 481) else (if n < 484
  then some (0, .right, 685) else some (0, .right, 572))) else (if n < 486 then some (0, .right,
  482) else (if n < 487 then some (0, .right, 480) else some (0, .right, 158)))))) else (if n <
  499 then (if n < 493 then (if n < 490 then (if n < 489 then some (0, .right, 487) else some (0,
  .right, 688)) else (if n < 491 then some (0, .right, 599) else (if n < 492 then some (0, .right,
  729) else some (0, .right, 581)))) else (if n < 496 then (if n < 494 then some (0, .right, 490)
  else (if n < 495 then some (0, .right, 115) else some (0, .right, 156))) else (if n < 497 then
  some (0, .right, 494) else (if n < 498 then some (0, .right, 730) else some (0, .right, 591)))))
  else (if n < 505 then (if n < 502 then (if n < 500 then some (0, .right, 174) else (if n < 501
  then some (0, .right, 545) else some (0, .right, 499))) else (if n < 503 then some (0, .right,
  501) else (if n < 504 then some (0, .right, 36) else some (0, .right, 503)))) else (if n < 508
  then (if n < 506 then some (0, .right, 504) else (if n < 507 then some (0, .right, 502) else
  some (0, .right, 498))) else (if n < 509 then some (0, .right, 493) else (if n < 510 then some
  (0, .right, 486) else some (0, .right, 476))))))) else (if n < 534 then (if n < 522 then (if n <
  516 then (if n < 513 then (if n < 512 then some (0, .right, 444) else some (0, .right, 89)) else
  (if n < 514 then some (0, .right, 89) else (if n < 515 then some (0, .right, 512) else some (0,
  .right, 514)))) else (if n < 519 then (if n < 517 then some (0, .right, 515) else (if n < 518
  then some (0, .right, 516) else some (0, .right, 517))) else (if n < 520 then some (0, .right,
  518) else (if n < 521 then some (0, .right, 519) else some (0, .right, 520))))) else (if n < 528
  then (if n < 525 then (if n < 523 then some (0, .right, 511) else (if n < 524 then some (0,
  .right, 371) else some (0, .left, 11))) else (if n < 526 then some (0, .left, 9) else (if n <
  527 then some (0, .left, 15) else some (0, .left, 17)))) else (if n < 531 then (if n < 529 then
  some (0, .left, 19) else (if n < 530 then some (0, .left, 21) else some (0, .left, 23))) else
  (if n < 532 then some (0, .left, 25) else (if n < 533 then some (0, .left, 27) else some (0,
  .right, 2)))))) else (if n < 546 then (if n < 540 then (if n < 537 then (if n < 535 then some
  (0, .right, 533) else (if n < 536 then some (0, .right, 534) else some (0, .right, 549))) else
  (if n < 538 then some (0, .right, 536) else (if n < 539 then some (0, .right, 537) else some (0,
  .right, 538)))) else (if n < 543 then (if n < 541 then some (0, .right, 539) else (if n < 542
  then some (0, .right, 540) else some (0, .right, 535))) else (if n < 544 then some (0, .right,
  542) else (if n < 545 then some (0, .right, 543) else some (0, .right, 544))))) else (if n < 552
  then (if n < 549 then (if n < 547 then some (0, .right, 545) else (if n < 548 then some (0,
  .right, 546) else some (0, .right, 547))) else (if n < 550 then some (0, .right, 548) else (if n
  < 551 then some (0, .right, 31) else some (0, .right, 550)))) else (if n < 555 then (if n < 553
  then some (0, .right, 564) else (if n < 554 then some (0, .right, 552) else some (0, .right,
  553))) else (if n < 556 then some (0, .right, 554) else (if n < 557 then some (0, .right, 555)
  else some (0, .right, 556))))))))) else (if n < 651 then (if n < 604 then (if n < 581 then (if n
  < 569 then (if n < 563 then (if n < 560 then (if n < 559 then some (0, .right, 188) else some
  (0, .right, 648)) else (if n < 561 then some (0, .right, 559) else (if n < 562 then some (0,
  .right, 560) else some (0, .right, 561)))) else (if n < 566 then (if n < 564 then some (0,
  .right, 562) else (if n < 565 then some (0, .right, 563) else some (0, .left, 9))) else (if n <
  567 then some (0, .left, 565) else (if n < 568 then some (0, .left, 524) else some (0, .left,
  567))))) else (if n < 575 then (if n < 572 then (if n < 570 then some (0, .right, 538) else (if
  n < 571 then some (0, .right, 569) else some (0, .right, 573))) else (if n < 573 then some (0,
  .right, 571) else (if n < 574 then some (0, .right, 538) else some (0, .right, 560)))) else (if
  n < 578 then (if n < 576 then some (0, .right, 573) else (if n < 577 then some (0, .right, 575)
  else some (0, .right, 539))) else (if n < 579 then some (0, .right, 577) else (if n < 580 then
  some (0, .right, 539) else some (0, .right, 579)))))) else (if n < 592 then (if n < 586 then (if
  n < 583 then (if n < 582 then some (0, .right, 580) else some (0, .right, 540)) else (if n < 584
  then some (0, .right, 582) else (if n < 585 then some (0, .right, 586) else some (0, .right,
  584)))) else (if n < 589 then (if n < 587 then some (0, .right, 540) else (if n < 588 then some
  (0, .right, 586) else some (0, .right, 587))) else (if n < 590 then some (0, .right, 648) else
  (if n < 591 then some (0, .right, 586) else some (0, .right, 590))))) else (if n < 598 then (if
  n < 595 then (if n < 593 then some (0, .right, 586) else (if n < 594 then some (0, .right, 592)
  else some (0, .right, 541))) else (if n < 596 then some (0, .right, 594) else (if n < 597 then
  some (0, .right, 600) else some (0, .right, 596)))) else (if n < 601 then (if n < 599 then some
  (0, .right, 600) else (if n < 600 then some (0, .right, 598) else some (0, .right, 541))) else
  (if n < 602 then some (0, .right, 560) else (if n < 603 then some (0, .right, 600) else some (0,
  .right, 602))))))) else (if n < 627 then (if n < 615 then (if n < 609 then (if n < 606 then (if
  n < 605 then some (0, .right, 536) else some (0, .right, 604)) else (if n < 607 then some (0,
  .right, 608) else (if n < 608 then some (0, .right, 606) else some (0, .right, 536)))) else (if
  n < 612 then (if n < 610 then some (0, .right, 608) else (if n < 611 then some (0, .right, 609)
  else some (0, .right, 608))) else (if n < 613 then some (0, .right, 611) else (if n < 614 then
  some (0, .right, 608) else some (0, .right, 613))))) else (if n < 621 then (if n < 618 then (if
  n < 616 then some (0, .right, 537) else (if n < 617 then some (0, .right, 615) else some (0,
  .right, 537))) else (if n < 619 then some (0, .right, 617) else (if n < 620 then some (0,
  .right, 618) else some (0, .right, 617)))) else (if n < 624 then (if n < 622 then some (0,
  .right, 620) else (if n < 623 then some (0, .right, 617) else some (0, .right, 622))) else (if n
  < 625 then some (0, .right, 544) else (if n < 626 then some (0, .right, 624) else some (0,
  .right, 648)))))) else (if n < 639 then (if n < 633 then (if n < 630 then (if n < 628 then some
  (0, .right, 629) else (if n < 629 then some (0, .right, 627) else some (0, .right, 544))) else
  (if n < 631 then some (0, .right, 629) else (if n < 632 then some (0, .right, 630) else some (0,
  .left, 633)))) else (if n < 636 then (if n < 634 then some (0, .left, 634) else (if n < 635 then
  some (0, .left, 14) else some (0, .left, 636))) else (if n < 637 then some (1, .left, 11) else
  (if n < 638 then some (0, .right, 534) else some (0, .right, 632))))) else (if n < 645 then (if
  n < 642 then (if n < 640 then some (0, .right, 637) else (if n < 641 then some (0, .left, 641)
  else some (0, .left, 642))) else (if n < 643 then some (0, .left, 643) else (if n < 644 then
  some (0, .left, 16) else some (0, .left, 645)))) else (if n < 648 then (if n < 646 then some (1,
  .left, 646) else (if n < 647 then some (0, .left, 15) else some (0, .right, 534))) else (if n <
  649 then some (0, .right, 558) else (if n < 650 then some (0, .right, 647) else some (0, .right,
  640)))))))) else (if n < 697 then (if n < 674 then (if n < 662 then (if n < 656 then (if n < 653
  then (if n < 652 then some (0, .right, 650) else some (0, .right, 649)) else (if n < 654 then
  some (0, .right, 648) else (if n < 655 then some (0, .right, 647) else some (0, .right, 654))))
  else (if n < 659 then (if n < 657 then some (0, .right, 648) else (if n < 658 then some (0,
  .right, 647) else some (0, .right, 657))) else (if n < 660 then some (0, .right, 561) else (if n
  < 661 then some (0, .right, 647) else some (0, .right, 660))))) else (if n < 668 then (if n <
  665 then (if n < 663 then some (0, .right, 647) else (if n < 664 then some (0, .right, 662) else
  some (0, .right, 549))) else (if n < 666 then some (0, .right, 664) else (if n < 667 then some
  (0, .right, 549) else some (0, .right, 558)))) else (if n < 671 then (if n < 669 then some (0,
  .right, 666) else (if n < 670 then some (0, .right, 668) else some (0, .right, 680))) else (if n
  < 672 then some (0, .right, 670) else (if n < 673 then some (0, .right, 558) else some (0,
  .right, 680)))))) else (if n < 685 then (if n < 679 then (if n < 676 then (if n < 675 then some
  (0, .right, 673) else some (0, .right, 680)) else (if n < 677 then some (0, .right, 675) else
  (if n < 678 then some (0, .right, 560) else some (0, .right, 680)))) else (if n < 682 then (if n
  < 680 then some (0, .right, 678) else (if n < 681 then some (0, .right, 535) else some (0,
  .right, 680))) else (if n < 683 then some (0, .right, 681) else (if n < 684 then some (0,
  .right, 542) else some (0, .right, 683))))) else (if n < 691 then (if n < 688 then (if n < 686
  then some (0, .right, 692) else (if n < 687 then some (0, .right, 556) else some (0, .right,
  692))) else (if n < 689 then some (0, .right, 692) else (if n < 690 then some (0, .right, 552)
  else some (0, .right, 692)))) else (if n < 694 then (if n < 692 then some (0, .right, 692) else
  (if n < 693 then some (0, .right, 542) else some (0, .right, 559))) else (if n < 695 then some
  (0, .right, 692) else (if n < 696 then some (0, .right, 692) else some (0, .right, 692)))))))
  else (if n < 720 then (if n < 708 then (if n < 702 then (if n < 699 then (if n < 698 then some
  (0, .right, 648) else some (0, .right, 692)) else (if n < 700 then some (0, .right, 543) else
  (if n < 701 then some (0, .right, 699) else some (0, .right, 554)))) else (if n < 705 then (if n
  < 703 then some (0, .right, 712) else (if n < 704 then some (0, .right, 555) else some (0,
  .right, 712))) else (if n < 706 then some (0, .right, 557) else (if n < 707 then some (0,
  .right, 712) else some (0, .right, 712))))) else (if n < 714 then (if n < 711 then (if n < 709
  then some (0, .right, 553) else (if n < 710 then some (0, .right, 712) else some (0, .left,
  711))) else (if n < 712 then some (0, .left, 646) else (if n < 713 then some (0, .right, 543)
  else some (0, .right, 551)))) else (if n < 717 then (if n < 715 then some (0, .right, 712) else
  (if n < 716 then some (0, .right, 712) else some (0, .right, 712))) else (if n < 718 then some
  (0, .right, 545) else (if n < 719 then some (0, .right, 717) else some (0, .right, 723))))))
  else (if n < 732 then (if n < 726 then (if n < 723 then (if n < 721 then some (0, .right, 723)
  else (if n < 722 then some (0, .right, 723) else some (0, .right, 723))) else (if n < 724 then
  some (0, .right, 545) else (if n < 725 then some (0, .right, 723) else some (0, .right, 564))))
  else (if n < 729 then (if n < 727 then some (0, .right, 723) else (if n < 728 then some (0,
  .right, 546) else some (0, .right, 727))) else (if n < 730 then some (0, .right, 731) else (if n
  < 731 then some (0, .right, 731) else some (0, .right, 546))))) else (if n < 738 then (if n <
  735 then (if n < 733 then some (0, .right, 731) else (if n < 734 then some (0, .right, 547) else
  some (0, .right, 733))) else (if n < 736 then some (0, .right, 736) else (if n < 737 then some
  (0, .right, 547) else some (0, .right, 736)))) else (if n < 741 then (if n < 739 then some (0,
  .right, 736) else (if n < 740 then some (0, .right, 740) else some (0, .right, 548))) else (if n
  < 742 then some (0, .right, 740) else (if n < 743 then some (0, .right, 188) else some (0,
  .right, 740)))))))))))
def refTrans1 (n : Nat) : Option (Fin 2 × Dir × Fin 744) :=
  (if n < 372 then (if n < 186 then (if n < 93 then (if n < 46 then (if n < 23 then (if n < 11
  then (if n < 5 then (if n < 2 then (if n < 1 then some (1, .right, 523) else some (1, .right,
  5)) else (if n < 3 then some (0, .right, 1) else (if n < 4 then some (1, .left, 566) else some
  (1, .right, 5)))) else (if n < 8 then (if n < 6 then some (1, .right, 5) else (if n < 7 then
  some (1, .left, 7) else some (0, .left, 8))) else (if n < 9 then some (1, .left, 8) else (if n <
  10 then some (0, .left, 11) else some (1, .left, 14))))) else (if n < 17 then (if n < 14 then
  (if n < 12 then some (0, .left, 15) else (if n < 13 then some (1, .left, 0) else some (0, .left,
  0))) else (if n < 15 then some (1, .left, 16) else (if n < 16 then some (0, .left, 17) else some
  (1, .left, 18)))) else (if n < 20 then (if n < 18 then some (0, .left, 19) else (if n < 19 then
  some (1, .left, 20) else some (0, .left, 21))) else (if n < 21 then some (1, .left, 22) else (if
  n < 22 then some (0, .left, 23) else some (1, .left, 24)))))) else (if n < 34 then (if n < 28
  then (if n < 25 then (if n < 24 then some (0, .left, 25) else some (1, .left, 26)) else (if n <
  26 then some (0, .left, 27) else (if n < 27 then some (1, .left, 28) else some (0, .left, 29))))
  else (if n < 31 then (if n < 29 then some (1, .left, 12) else (if n < 30 then some (0, .left,
  13) else some (0, .right, 31))) else (if n < 32 then some (1, .right, 31) else (if n < 33 then
  some (1, .right, 33) else some (1, .right, 34))))) else (if n < 40 then (if n < 37 then (if n <
  35 then some (1, .right, 35) else (if n < 36 then some (1, .right, 35) else some (1, .left,
  37))) else (if n < 38 then some (1, .left, 38) else (if n < 39 then some (1, .left, 177) else
  some (1, .left, 40)))) else (if n < 43 then (if n < 41 then some (0, .left, 41) else (if n < 42
  then some (1, .left, 42) else some (0, .left, 43))) else (if n < 44 then some (0, .left, 59)
  else (if n < 45 then some (1, .left, 45) else some (0, .left, 46))))))) else (if n < 69 then (if
  n < 57 then (if n < 51 then (if n < 48 then (if n < 47 then some (0, .left, 47) else some (1,
  .left, 172)) else (if n < 49 then some (1, .left, 49) else (if n < 50 then some (0, .left, 50)
  else some (0, .left, 51)))) else (if n < 54 then (if n < 52 then some (1, .left, 52) else (if n
  < 53 then some (1, .left, 53) else some (0, .left, 121))) else (if n < 55 then some (1, .left,
  55) else (if n < 56 then some (0, .left, 56) else some (0, .left, 57))))) else (if n < 63 then
  (if n < 60 then (if n < 58 then some (0, .left, 58) else (if n < 59 then some (1, .left, 59)
  else some (1, .left, 60))) else (if n < 61 then some (1, .left, 23) else (if n < 62 then some
  (1, .left, 62) else some (0, .left, 63)))) else (if n < 66 then (if n < 64 then some (1, .left,
  57) else (if n < 65 then some (1, .left, 65) else some (1, .left, 66))) else (if n < 67 then
  some (0, .left, 67) else (if n < 68 then some (1, .left, 68) else some (1, .left, 69)))))) else
  (if n < 81 then (if n < 75 then (if n < 72 then (if n < 70 then some (1, .left, 70) else (if n <
  71 then some (1, .left, 71) else some (1, .left, 72))) else (if n < 73 then some (0, .left, 26)
  else (if n < 74 then some (1, .left, 74) else some (1, .left, 46)))) else (if n < 78 then (if n
  < 76 then some (1, .left, 76) else (if n < 77 then some (0, .left, 77) else some (0, .left,
  78))) else (if n < 79 then some (0, .left, 79) else (if n < 80 then some (0, .left, 120) else
  some (1, .left, 81))))) else (if n < 87 then (if n < 84 then (if n < 82 then some (1, .left, 82)
  else (if n < 83 then some (0, .left, 83) else some (0, .left, 84))) else (if n < 85 then some
  (0, .left, 19) else (if n < 86 then some (1, .left, 86) else some (0, .left, 87)))) else (if n <
  90 then (if n < 88 then some (0, .left, 88) else (if n < 89 then some (1, .left, 79) else some
  (1, .left, 90))) else (if n < 91 then some (1, .left, 93) else (if n < 92 then some (0, .left,
  92) else some (0, .left, 0)))))))) else (if n < 139 then (if n < 116 then (if n < 104 then (if n
  < 98 then (if n < 95 then (if n < 94 then some (0, .left, 94) else some (1, .left, 95)) else (if
  n < 96 then some (0, .left, 96) else (if n < 97 then some (1, .left, 97) else some (0, .left,
  98)))) else (if n < 101 then (if n < 99 then some (0, .left, 99) else (if n < 100 then some (0,
  .left, 100) else some (0, .left, 91))) else (if n < 102 then some (1, .left, 102) else (if n <
  103 then some (1, .left, 103) else some (0, .left, 104))))) else (if n < 110 then (if n < 107
  then (if n < 105 then some (1, .left, 84) else (if n < 106 then some (1, .left, 106) else some
  (0, .left, 109))) else (if n < 108 then some (1, .left, 108) else (if n < 109 then some (1,
  .left, 109) else some (0, .left, 113)))) else (if n < 113 then (if n < 111 then some (1, .left,
  111) else (if n < 112 then some (0, .left, 112) else some (1, .left, 113))) else (if n < 114
  then some (0, .left, 114) else (if n < 115 then some (1, .left, 19) else some (1, .left,
  116)))))) else (if n < 127 then (if n < 121 then (if n < 118 then (if n < 117 then some (0,
  .left, 117) else some (0, .left, 118)) else (if n < 119 then some (1, .left, 119) else (if n <
  120 then some (1, .left, 120) else some (1, .left, 121)))) else (if n < 124 then (if n < 122
  then some (0, .left, 22) else (if n < 123 then some (1, .left, 123) else some (1, .left, 124)))
  else (if n < 125 then some (0, .left, 125) else (if n < 126 then some (1, .left, 114) else some
  (1, .left, 127))))) else (if n < 133 then (if n < 130 then (if n < 128 then some (1, .left, 128)
  else (if n < 129 then some (0, .left, 129) else some (1, .left, 130))) else (if n < 131 then
  some (1, .left, 131) else (if n < 132 then some (1, .left, 132) else some (0, .left, 145))))
  else (if n < 136 then (if n < 134 then some (1, .left, 134) else (if n < 135 then some (0,
  .left, 135) else some (0, .left, 136))) else (if n < 137 then some (1, .left, 137) else (if n <
  138 then some (0, .left, 173) else some (1, .left, 139))))))) else (if n < 162 then (if n < 150
  then (if n < 144 then (if n < 141 then (if n < 140 then some (0, .left, 140) else some (0,
  .left, 141)) else (if n < 142 then some (1, .left, 142) else (if n < 143 then some (1, .left,
  143) else some (0, .left, 144)))) else (if n < 147 then (if n < 145 then some (1, .left, 145)
  else (if n < 146 then some (0, .left, 72) else some (1, .left, 147))) else (if n < 148 then some
  (1, .left, 135) else (if n < 149 then some (1, .left, 149) else some (0, .left, 150))))) else
  (if n < 156 then (if n < 153 then (if n < 151 then some (0, .left, 151) else (if n < 152 then
  some (1, .left, 152) else some (0, .left, 153))) else (if n < 154 then some (1, .left, 154) else
  (if n < 155 then some (1, .left, 155) else some (0, .left, 24)))) else (if n < 159 then (if n <
  157 then some (1, .left, 157) else (if n < 158 then some (0, .left, 165) else some (1, .left,
  159))) else (if n < 160 then some (0, .left, 160) else (if n < 161 then some (0, .left, 161)
  else some (1, .left, 162)))))) else (if n < 174 then (if n < 168 then (if n < 165 then (if n <
  163 then some (1, .left, 153) else (if n < 164 then some (1, .left, 164) else some (1, .left,
  165))) else (if n < 166 then some (1, .left, 15) else (if n < 167 then some (1, .left, 167) else
  some (0, .left, 176)))) else (if n < 171 then (if n < 169 then some (1, .left, 169) else (if n <
  170 then some (0, .left, 170) else some (0, .left, 171))) else (if n < 172 then some (0, .left,
  172) else (if n < 173 then some (1, .left, 173) else some (0, .left, 20))))) else (if n < 180
  then (if n < 177 then (if n < 175 then some (1, .left, 175) else (if n < 176 then some (1,
  .left, 176) else some (0, .left, 177))) else (if n < 178 then some (0, .left, 17) else (if n <
  179 then some (1, .left, 179) else some (1, .left, 180)))) else (if n < 183 then (if n < 181
  then some (0, .left, 181) else (if n < 182 then some (0, .left, 182) else some (0, .left, 183)))
  else (if n < 184 then some (0, .left, 70) else (if n < 185 then some (1, .right, 32) else some
  (1, .right, 184))))))))) else (if n < 279 then (if n < 232 then (if n < 209 then (if n < 197
  then (if n < 191 then (if n < 188 then (if n < 187 then some (1, .right, 185) else some (1,
  .right, 186)) else (if n < 189 then some (1, .right, 188) else (if n < 190 then some (1, .right,
  524) else some (1, .right, 189)))) else (if n < 194 then (if n < 192 then some (1, .right, 652)
  else (if n < 193 then some (1, .right, 191) else some (1, .right, 625))) else (if n < 195 then
  some (1, .right, 526) else (if n < 196 then some (1, .right, 194) else some (1, .right, 526)))))
  else (if n < 203 then (if n < 200 then (if n < 198 then some (1, .right, 196) else (if n < 199
  then some (1, .right, 197) else some (1, .right, 198))) else (if n < 201 then some (1, .right,
  526) else (if n < 202 then some (1, .right, 200) else some (1, .right, 644)))) else (if n < 206
  then (if n < 204 then some (1, .right, 163) else (if n < 205 then some (1, .right, 203) else
  some (1, .right, 204))) else (if n < 207 then some (1, .right, 205) else (if n < 208 then some
  (1, .right, 206) else some (1, .right, 560)))))) else (if n < 220 then (if n < 214 then (if n <
  211 then (if n < 210 then some (1, .right, 525) else some (1, .right, 209)) else (if n < 212
  then some (1, .right, 734) else (if n < 213 then some (1, .right, 64) else some (1, .right,
  524)))) else (if n < 217 then (if n < 215 then some (1, .right, 526) else (if n < 216 then some
  (1, .right, 214) else some (1, .right, 543))) else (if n < 218 then some (1, .right, 542) else
  (if n < 219 then some (1, .right, 217) else some (1, .right, 218))))) else (if n < 226 then (if
  n < 223 then (if n < 221 then some (1, .right, 219) else (if n < 222 then some (1, .right, 220)
  else some (1, .right, 221))) else (if n < 224 then some (1, .right, 222) else (if n < 225 then
  some (1, .right, 64) else some (1, .right, 80)))) else (if n < 229 then (if n < 227 then some
  (1, .right, 225) else (if n < 228 then some (1, .right, 684) else some (1, .right, 525))) else
  (if n < 230 then some (1, .right, 524) else (if n < 231 then some (1, .right, 700) else some (1,
  .right, 230))))))) else (if n < 255 then (if n < 243 then (if n < 237 then (if n < 234 then (if
  n < 233 then some (1, .right, 526) else some (1, .right, 655)) else (if n < 235 then some (1,
  .right, 233) else (if n < 236 then some (1, .right, 526) else some (1, .right, 663)))) else (if
  n < 240 then (if n < 238 then some (1, .right, 682) else (if n < 239 then some (1, .right, 237)
  else some (1, .right, 238))) else (if n < 241 then some (1, .right, 644) else (if n < 242 then
  some (1, .right, 163) else some (1, .right, 241))))) else (if n < 249 then (if n < 246 then (if
  n < 244 then some (1, .right, 242) else (if n < 245 then some (1, .right, 560) else some (1,
  .right, 525))) else (if n < 247 then some (1, .right, 245) else (if n < 248 then some (1,
  .right, 728) else some (1, .right, 247)))) else (if n < 252 then (if n < 250 then some (1,
  .right, 101) else (if n < 251 then some (1, .right, 524) else some (1, .right, 526))) else (if n
  < 253 then some (1, .right, 674) else (if n < 254 then some (1, .right, 252) else some (1,
  .right, 542)))))) else (if n < 267 then (if n < 261 then (if n < 258 then (if n < 256 then some
  (1, .right, 543) else (if n < 257 then some (1, .right, 255) else some (1, .right, 256))) else
  (if n < 259 then some (1, .right, 146) else (if n < 260 then some (1, .right, 110) else some (1,
  .right, 259)))) else (if n < 264 then (if n < 262 then some (1, .right, 700) else (if n < 263
  then some (1, .right, 261) else some (1, .right, 525))) else (if n < 265 then some (1, .right,
  524) else (if n < 266 then some (1, .right, 684) else some (1, .right, 138))))) else (if n < 273
  then (if n < 270 then (if n < 268 then some (1, .right, 524) else (if n < 269 then some (1,
  .right, 526) else some (1, .right, 268))) else (if n < 271 then some (1, .right, 269) else (if n
  < 272 then some (1, .right, 270) else some (1, .right, 271)))) else (if n < 276 then (if n < 274
  then some (1, .right, 272) else (if n < 275 then some (1, .right, 89) else some (1, .right,
  274))) else (if n < 277 then some (1, .right, 275) else (if n < 278 then some (1, .right, 276)
  else some (1, .right, 275)))))))) else (if n < 325 then (if n < 302 then (if n < 290 then (if n
  < 284 then (if n < 281 then (if n < 280 then some (1, .right, 278) else some (1, .right, 279))
  else (if n < 282 then some (1, .right, 279) else (if n < 283 then some (1, .right, 281) else
  some (1, .right, 281)))) else (if n < 287 then (if n < 285 then some (1, .right, 283) else (if n
  < 286 then some (1, .right, 283) else some (1, .right, 285))) else (if n < 288 then some (1,
  .right, 286) else (if n < 289 then some (1, .right, 285) else some (1, .right, 665))))) else (if
  n < 296 then (if n < 293 then (if n < 291 then some (1, .right, 289) else (if n < 292 then some
  (1, .right, 525) else some (1, .right, 524))) else (if n < 294 then some (1, .right, 292) else
  (if n < 295 then some (1, .right, 525) else some (1, .right, 524)))) else (if n < 299 then (if n
  < 297 then some (1, .right, 295) else (if n < 298 then some (1, .right, 296) else some (1,
  .right, 297))) else (if n < 300 then some (1, .right, 526) else (if n < 301 then some (1,
  .right, 299) else some (1, .right, 644)))))) else (if n < 313 then (if n < 307 then (if n < 304
  then (if n < 303 then some (1, .right, 107) else some (1, .right, 302)) else (if n < 305 then
  some (1, .right, 303) else (if n < 306 then some (1, .right, 304) else some (1, .right, 305))))
  else (if n < 310 then (if n < 308 then some (1, .right, 306) else (if n < 309 then some (1,
  .right, 542) else some (1, .right, 525))) else (if n < 311 then some (1, .right, 309) else (if n
  < 312 then some (1, .right, 684) else some (1, .right, 525))))) else (if n < 319 then (if n <
  316 then (if n < 314 then some (1, .right, 524) else (if n < 315 then some (1, .right, 700) else
  some (1, .right, 314))) else (if n < 317 then some (1, .right, 122) else (if n < 318 then some
  (1, .right, 524) else some (1, .right, 317)))) else (if n < 322 then (if n < 320 then some (1,
  .right, 318) else (if n < 321 then some (1, .right, 319) else some (1, .right, 525))) else (if n
  < 323 then some (1, .right, 524) else (if n < 324 then some (1, .right, 322) else some (1,
  .right, 323))))))) else (if n < 348 then (if n < 336 then (if n < 330 then (if n < 327 then (if
  n < 326 then some (1, .right, 665) else some (1, .right, 325)) else (if n < 328 then some (1,
  .right, 326) else (if n < 329 then some (1, .right, 327) else some (1, .right, 328)))) else (if
  n < 333 then (if n < 331 then some (1, .right, 526) else (if n < 332 then some (1, .right, 607)
  else some (1, .right, 101))) else (if n < 334 then some (1, .right, 524) else (if n < 335 then
  some (1, .right, 333) else some (1, .right, 621))))) else (if n < 342 then (if n < 339 then (if
  n < 337 then some (1, .right, 335) else (if n < 338 then some (1, .right, 525) else some (1,
  .right, 524))) else (if n < 340 then some (1, .right, 338) else (if n < 341 then some (1,
  .right, 707) else some (1, .right, 340)))) else (if n < 345 then (if n < 343 then some (1,
  .right, 126) else (if n < 344 then some (1, .right, 524) else some (1, .right, 526))) else (if n
  < 346 then some (1, .right, 669) else (if n < 347 then some (1, .right, 345) else some (1,
  .right, 346)))))) else (if n < 360 then (if n < 354 then (if n < 351 then (if n < 349 then some
  (1, .right, 526) else (if n < 350 then some (1, .right, 614) else some (1, .right, 101))) else
  (if n < 352 then some (1, .right, 524) else (if n < 353 then some (1, .right, 351) else some (1,
  .right, 679)))) else (if n < 357 then (if n < 355 then some (1, .right, 353) else (if n < 356
  then some (1, .right, 338) else some (1, .right, 644))) else (if n < 358 then some (1, .right,
  525) else (if n < 359 then some (1, .right, 357) else some (1, .right, 358))))) else (if n < 366
  then (if n < 363 then (if n < 361 then some (1, .right, 359) else (if n < 362 then some (1,
  .right, 525) else some (1, .right, 524))) else (if n < 364 then some (1, .right, 570) else (if n
  < 365 then some (1, .right, 526) else some (1, .right, 364)))) else (if n < 369 then (if n < 367
  then some (1, .right, 365) else (if n < 368 then some (1, .right, 366) else some (1, .right,
  367))) else (if n < 370 then some (1, .right, 368) else (if n < 371 then some (1, .right, 369)
  else some (1, .right, 370)))))))))) else (if n < 558 then (if n < 465 then (if n < 418 then (if
  n < 395 then (if n < 383 then (if n < 377 then (if n < 374 then (if n < 373 then some (1,
  .right, 126) else some (1, .right, 524)) else (if n < 375 then some (1, .right, 373) else (if n
  < 376 then some (1, .right, 374) else some (1, .right, 524)))) else (if n < 380 then (if n < 378
  then some (1, .right, 376) else (if n < 379 then some (1, .right, 377) else some (1, .right,
  378))) else (if n < 381 then some (1, .right, 702) else (if n < 382 then some (1, .right, 612)
  else some (1, .right, 250))))) else (if n < 389 then (if n < 386 then (if n < 384 then some (1,
  .right, 610) else (if n < 385 then some (1, .right, 383) else some (1, .right, 384))) else (if n
  < 387 then some (1, .right, 524) else (if n < 388 then some (1, .right, 386) else some (1,
  .right, 704)))) else (if n < 392 then (if n < 390 then some (1, .right, 388) else (if n < 391
  then some (1, .right, 595) else some (1, .right, 525))) else (if n < 393 then some (1, .right,
  524) else (if n < 394 then some (1, .right, 616) else some (1, .right, 393)))))) else (if n <
  406 then (if n < 400 then (if n < 397 then (if n < 396 then some (1, .right, 394) else some (1,
  .right, 526)) else (if n < 398 then some (1, .right, 621) else (if n < 399 then some (1, .right,
  526) else some (1, .right, 676)))) else (if n < 403 then (if n < 401 then some (1, .right, 399)
  else (if n < 402 then some (1, .right, 400) else some (1, .right, 401))) else (if n < 404 then
  some (1, .right, 80) else (if n < 405 then some (1, .right, 403) else some (1, .right, 404)))))
  else (if n < 412 then (if n < 409 then (if n < 407 then some (1, .right, 543) else (if n < 408
  then some (1, .right, 525) else some (1, .right, 407))) else (if n < 410 then some (1, .right,
  700) else (if n < 411 then some (1, .right, 409) else some (1, .right, 525)))) else (if n < 415
  then (if n < 413 then some (1, .right, 524) else (if n < 414 then some (1, .right, 718) else
  some (1, .right, 588))) else (if n < 416 then some (1, .right, 414) else (if n < 417 then some
  (1, .right, 101) else some (1, .right, 524))))))) else (if n < 441 then (if n < 429 then (if n <
  423 then (if n < 420 then (if n < 419 then some (1, .right, 417) else some (1, .right, 623))
  else (if n < 421 then some (1, .right, 525) else (if n < 422 then some (1, .right, 524) else
  some (1, .right, 421)))) else (if n < 426 then (if n < 424 then some (1, .right, 603) else (if n
  < 425 then some (1, .right, 423) else some (1, .right, 424))) else (if n < 427 then some (1,
  .right, 583) else (if n < 428 then some (1, .right, 526) else some (1, .right, 427))))) else (if
  n < 435 then (if n < 432 then (if n < 430 then some (1, .right, 122) else (if n < 431 then some
  (1, .right, 524) else some (1, .right, 430))) else (if n < 433 then some (1, .right, 431) else
  (if n < 434 then some (1, .right, 432) else some (1, .right, 322)))) else (if n < 438 then (if n
  < 436 then some (1, .right, 434) else (if n < 437 then some (1, .right, 720) else some (1,
  .right, 178))) else (if n < 439 then some (1, .right, 524) else (if n < 440 then some (1,
  .right, 526) else some (1, .right, 439)))))) else (if n < 453 then (if n < 447 then (if n < 444
  then (if n < 442 then some (1, .right, 440) else (if n < 443 then some (1, .right, 441) else
  some (1, .right, 442))) else (if n < 445 then some (1, .right, 443) else (if n < 446 then some
  (1, .right, 126) else some (1, .right, 524)))) else (if n < 450 then (if n < 448 then some (1,
  .right, 446) else (if n < 449 then some (1, .right, 447) else some (1, .right, 376))) else (if n
  < 451 then some (1, .right, 449) else (if n < 452 then some (1, .right, 450) else some (1,
  .right, 719))))) else (if n < 459 then (if n < 456 then (if n < 454 then some (1, .right, 585)
  else (if n < 455 then some (1, .right, 333) else some (1, .right, 591))) else (if n < 457 then
  some (1, .right, 455) else (if n < 458 then some (1, .right, 456) else some (1, .right, 543))))
  else (if n < 462 then (if n < 460 then some (1, .right, 525) else (if n < 461 then some (1,
  .right, 459) else some (1, .right, 460))) else (if n < 463 then some (1, .right, 676) else (if n
  < 464 then some (1, .right, 525) else some (1, .right, 524)))))))) else (if n < 511 then (if n <
  488 then (if n < 476 then (if n < 470 then (if n < 467 then (if n < 466 then some (1, .right,
  464) else some (1, .right, 452)) else (if n < 468 then some (1, .right, 466) else (if n < 469
  then some (1, .right, 64) else some (1, .right, 524)))) else (if n < 473 then (if n < 471 then
  some (1, .right, 469) else (if n < 472 then some (1, .right, 470) else some (1, .right, 362)))
  else (if n < 474 then some (1, .right, 472) else (if n < 475 then some (1, .right, 473) else
  some (1, .right, 474))))) else (if n < 482 then (if n < 479 then (if n < 477 then some (1,
  .right, 475) else (if n < 478 then some (1, .right, 597) else some (1, .right, 417))) else (if n
  < 480 then some (1, .right, 599) else (if n < 481 then some (1, .right, 479) else some (1,
  .right, 338)))) else (if n < 485 then (if n < 483 then some (1, .right, 436) else (if n < 484
  then some (1, .right, 430) else some (1, .right, 483))) else (if n < 486 then some (1, .right,
  484) else (if n < 487 then some (1, .right, 485) else some (1, .right, 525)))))) else (if n <
  499 then (if n < 493 then (if n < 490 then (if n < 489 then some (1, .right, 524) else some (1,
  .right, 488)) else (if n < 491 then some (1, .right, 489) else (if n < 492 then some (1, .right,
  317) else some (1, .right, 491)))) else (if n < 496 then (if n < 494 then some (1, .right, 492)
  else (if n < 495 then some (1, .right, 543) else some (1, .right, 545))) else (if n < 497 then
  some (1, .right, 495) else (if n < 498 then some (1, .right, 496) else some (1, .right, 497)))))
  else (if n < 505 then (if n < 502 then (if n < 500 then some (1, .right, 73) else (if n < 501
  then some (1, .right, 89) else some (1, .right, 500))) else (if n < 503 then some (1, .right,
  718) else (if n < 504 then some (1, .right, 525) else some (1, .right, 524)))) else (if n < 508
  then (if n < 506 then some (1, .right, 700) else (if n < 507 then some (1, .right, 505) else
  some (1, .right, 506))) else (if n < 509 then some (1, .right, 507) else (if n < 510 then some
  (1, .right, 508) else some (1, .right, 509))))))) else (if n < 534 then (if n < 522 then (if n <
  516 then (if n < 513 then (if n < 512 then some (1, .right, 510) else some (1, .right, 635))
  else (if n < 514 then none else (if n < 515 then some (1, .right, 513) else some (1, .right,
  526)))) else (if n < 519 then (if n < 517 then some (1, .right, 527) else (if n < 518 then some
  (1, .right, 528) else some (1, .right, 529))) else (if n < 520 then some (1, .right, 530) else
  (if n < 521 then some (1, .right, 531) else some (1, .right, 532))))) else (if n < 528 then (if
  n < 525 then (if n < 523 then some (1, .right, 521) else (if n < 524 then some (1, .right, 522)
  else some (1, .left, 11))) else (if n < 526 then some (1, .left, 9) else (if n < 527 then some
  (1, .left, 15) else some (1, .left, 17)))) else (if n < 531 then (if n < 529 then some (1,
  .left, 19) else (if n < 530 then some (1, .left, 21) else some (1, .left, 23))) else (if n < 532
  then some (1, .left, 25) else (if n < 533 then some (1, .left, 27) else some (1, .right,
  533)))))) else (if n < 546 then (if n < 540 then (if n < 537 then (if n < 535 then some (1,
  .right, 534) else (if n < 536 then some (1, .right, 535) else some (1, .right, 536))) else (if n
  < 538 then some (1, .right, 537) else (if n < 539 then some (1, .right, 538) else some (1,
  .right, 539)))) else (if n < 543 then (if n < 541 then some (1, .right, 540) else (if n < 542
  then some (1, .right, 541) else some (1, .right, 542))) else (if n < 544 then some (1, .right,
  543) else (if n < 545 then some (1, .right, 544) else some (1, .right, 545))))) else (if n < 552
  then (if n < 549 then (if n < 547 then some (1, .right, 546) else (if n < 548 then some (1,
  .right, 547) else some (1, .right, 548))) else (if n < 550 then some (1, .right, 549) else (if n
  < 551 then some (1, .right, 550) else some (1, .right, 551)))) else (if n < 555 then (if n < 553
  then some (1, .right, 552) else (if n < 554 then some (1, .right, 553) else some (1, .right,
  554))) else (if n < 556 then some (1, .right, 555) else (if n < 557 then some (1, .right, 556)
  else some (1, .right, 557))))))))) else (if n < 651 then (if n < 604 then (if n < 581 then (if n
  < 569 then (if n < 563 then (if n < 560 then (if n < 559 then some (1, .right, 558) else some
  (1, .right, 559)) else (if n < 561 then some (1, .right, 560) else (if n < 562 then some (1,
  .right, 561) else some (1, .right, 562)))) else (if n < 566 then (if n < 564 then some (1,
  .right, 563) else (if n < 565 then some (1, .right, 564) else some (1, .left, 566))) else (if n
  < 567 then some (1, .left, 566) else (if n < 568 then some (1, .left, 568) else some (1, .left,
  568))))) else (if n < 575 then (if n < 572 then (if n < 570 then some (1, .right, 635) else (if
  n < 571 then some (1, .right, 638) else some (1, .right, 653))) else (if n < 573 then some (1,
  .right, 651) else (if n < 574 then some (1, .right, 644) else some (1, .right, 558)))) else (if
  n < 578 then (if n < 576 then some (1, .right, 574) else (if n < 577 then some (1, .right, 651)
  else some (1, .right, 635))) else (if n < 579 then some (1, .right, 638) else (if n < 580 then
  some (1, .right, 644) else some (1, .right, 672)))))) else (if n < 592 then (if n < 586 then (if
  n < 583 then (if n < 582 then some (1, .right, 651) else some (1, .right, 635)) else (if n < 584
  then some (1, .right, 638) else (if n < 585 then some (1, .right, 672) else some (1, .right,
  651)))) else (if n < 589 then (if n < 587 then some (1, .right, 644) else (if n < 588 then some
  (1, .right, 653) else some (1, .right, 651))) else (if n < 590 then some (1, .right, 561) else
  (if n < 591 then some (1, .right, 589) else some (1, .right, 651))))) else (if n < 598 then (if
  n < 595 then (if n < 593 then some (1, .right, 574) else (if n < 594 then some (1, .right, 651)
  else some (1, .right, 635))) else (if n < 596 then some (1, .right, 638) else (if n < 597 then
  some (1, .right, 653) else some (1, .right, 651)))) else (if n < 601 then (if n < 599 then some
  (1, .right, 574) else (if n < 600 then some (1, .right, 651) else some (1, .right, 644))) else
  (if n < 602 then some (1, .right, 648) else (if n < 603 then some (1, .right, 601) else some (1,
  .right, 651))))))) else (if n < 627 then (if n < 615 then (if n < 609 then (if n < 606 then (if
  n < 605 then some (1, .right, 635) else some (1, .right, 638)) else (if n < 607 then some (1,
  .right, 667) else (if n < 608 then some (1, .right, 651) else some (1, .right, 644)))) else (if
  n < 612 then (if n < 610 then some (1, .right, 653) else (if n < 611 then some (1, .right, 651)
  else some (1, .right, 574))) else (if n < 613 then some (1, .right, 651) else (if n < 614 then
  some (1, .right, 562) else some (1, .right, 651))))) else (if n < 621 then (if n < 618 then (if
  n < 616 then some (1, .right, 635) else (if n < 617 then some (1, .right, 638) else some (1,
  .right, 644))) else (if n < 619 then some (1, .right, 648) else (if n < 620 then some (1,
  .right, 651) else some (1, .right, 656)))) else (if n < 624 then (if n < 622 then some (1,
  .right, 651) else (if n < 623 then some (1, .right, 574) else some (1, .right, 651))) else (if n
  < 625 then some (1, .right, 635) else (if n < 626 then some (1, .right, 638) else some (1,
  .right, 562)))))) else (if n < 639 then (if n < 633 then (if n < 630 then (if n < 628 then some
  (1, .right, 626) else (if n < 629 then some (1, .right, 651) else some (1, .right, 644))) else
  (if n < 631 then some (1, .right, 563) else (if n < 632 then some (1, .right, 651) else some (1,
  .left, 633)))) else (if n < 636 then (if n < 634 then some (0, .left, 634) else (if n < 635 then
  some (0, .left, 14) else some (1, .left, 636))) else (if n < 637 then some (1, .left, 11) else
  (if n < 638 then some (1, .right, 635) else some (1, .right, 525))))) else (if n < 645 then (if
  n < 642 then (if n < 640 then some (1, .right, 638) else (if n < 641 then some (1, .left, 641)
  else some (0, .left, 642))) else (if n < 643 then some (0, .left, 643) else (if n < 644 then
  some (0, .left, 16) else some (1, .left, 645)))) else (if n < 648 then (if n < 646 then some (1,
  .left, 646) else (if n < 647 then some (0, .left, 15) else some (1, .right, 644))) else (if n <
  649 then some (1, .right, 648) else (if n < 650 then some (1, .right, 648) else some (1, .right,
  525)))))))) else (if n < 697 then (if n < 674 then (if n < 662 then (if n < 656 then (if n < 653
  then (if n < 652 then some (1, .right, 524) else some (1, .right, 651)) else (if n < 654 then
  some (1, .right, 558) else (if n < 655 then some (1, .right, 653) else some (1, .right, 651))))
  else (if n < 659 then (if n < 657 then some (1, .right, 560) else (if n < 658 then some (1,
  .right, 656) else some (1, .right, 651))) else (if n < 660 then some (1, .right, 563) else (if n
  < 661 then some (1, .right, 659) else some (1, .right, 651))))) else (if n < 668 then (if n <
  665 then (if n < 663 then some (1, .right, 563) else (if n < 664 then some (1, .right, 651) else
  some (1, .right, 635))) else (if n < 666 then some (1, .right, 638) else (if n < 667 then some
  (1, .right, 644) else some (1, .right, 560)))) else (if n < 671 then (if n < 669 then some (1,
  .right, 667) else (if n < 670 then some (1, .right, 651) else some (1, .right, 648))) else (if n
  < 672 then some (1, .right, 651) else (if n < 673 then some (1, .right, 561) else some (1,
  .right, 672)))))) else (if n < 685 then (if n < 679 then (if n < 676 then (if n < 675 then some
  (1, .right, 651) else some (1, .right, 574)) else (if n < 677 then some (1, .right, 651) else
  (if n < 678 then some (1, .right, 562) else some (1, .right, 677)))) else (if n < 682 then (if n
  < 680 then some (1, .right, 651) else (if n < 681 then some (1, .right, 644) else some (1,
  .right, 659))) else (if n < 683 then some (1, .right, 651) else (if n < 684 then some (1,
  .right, 635) else some (1, .right, 638))))) else (if n < 691 then (if n < 688 then (if n < 686
  then some (1, .right, 701) else (if n < 687 then some (1, .right, 632) else some (1, .right,
  686))) else (if n < 689 then some (1, .right, 705) else (if n < 690 then some (1, .right, 632)
  else some (1, .right, 689)))) else (if n < 694 then (if n < 692 then some (1, .right, 708) else
  (if n < 693 then some (1, .right, 710) else some (1, .right, 632))) else (if n < 695 then some
  (1, .right, 693) else (if n < 696 then some (1, .right, 713) else some (1, .right, 742)))))))
  else (if n < 720 then (if n < 708 then (if n < 702 then (if n < 699 then (if n < 698 then some
  (1, .right, 632) else some (1, .right, 697)) else (if n < 700 then some (1, .right, 635) else
  (if n < 701 then some (1, .right, 638) else some (1, .right, 632)))) else (if n < 705 then (if n
  < 703 then some (1, .right, 701) else (if n < 704 then some (1, .right, 632) else some (1,
  .right, 703))) else (if n < 706 then some (1, .right, 632) else (if n < 707 then some (1,
  .right, 705) else some (1, .right, 689))))) else (if n < 714 then (if n < 711 then (if n < 709
  then some (1, .right, 632) else (if n < 710 then some (1, .right, 708) else some (1, .left,
  711))) else (if n < 712 then some (0, .left, 646) else (if n < 713 then some (1, .right, 710)
  else some (1, .right, 632)))) else (if n < 717 then (if n < 715 then some (1, .right, 713) else
  (if n < 716 then some (1, .right, 725) else some (1, .right, 742))) else (if n < 718 then some
  (1, .right, 635) else (if n < 719 then some (1, .right, 638) else some (1, .right, 686))))))
  else (if n < 732 then (if n < 726 then (if n < 723 then (if n < 721 then some (1, .right, 705)
  else (if n < 722 then some (1, .right, 689) else some (1, .right, 708))) else (if n < 724 then
  some (1, .right, 710) else (if n < 725 then some (1, .right, 713) else some (1, .right, 632))))
  else (if n < 729 then (if n < 727 then some (1, .right, 725) else (if n < 728 then some (1,
  .right, 635) else some (1, .right, 638))) else (if n < 730 then some (1, .right, 703) else (if n
  < 731 then some (1, .right, 686) else some (1, .right, 710))))) else (if n < 738 then (if n <
  735 then (if n < 733 then some (1, .right, 742) else (if n < 734 then some (1, .right, 635) else
  some (1, .right, 638))) else (if n < 736 then some (1, .right, 689) else (if n < 737 then some
  (1, .right, 710) else some (1, .right, 693)))) else (if n < 741 then (if n < 739 then some (1,
  .right, 742) else (if n < 740 then some (1, .right, 693) else some (1, .right, 710))) else (if n
  < 742 then some (1, .right, 713) else (if n < 743 then some (1, .right, 632) else some (1,
  .right, 742)))))))))))
def refTrans (q : Fin 744) (b : Fin 2) : Option (Fin 2 × Dir × Fin 744) :=
  if b == 0 then refTrans0 q.val else refTrans1 q.val

def candTrans0 (n : Nat) : Option (Fin 2 × Dir × Fin 543) :=
  (if n < 272 then (if n < 136 then (if n < 68 then (if n < 34 then (if n < 17 then (if n < 9 then
  (if n < 5 then (if n < 3 then (if n < 2 then (if n < 1 then some (0, .right, 235) else some (0,
  .left, 31)) else some (0, .right, 1)) else (if n < 4 then some (0, .left, 5) else some (0,
  .right, 3))) else (if n < 7 then (if n < 6 then some (0, .left, 6) else some (0, .left, 385))
  else (if n < 8 then some (1, .left, 6) else some (1, .left, 9)))) else (if n < 13 then (if n <
  11 then (if n < 10 then some (0, .left, 12) else some (1, .left, 12)) else (if n < 12 then some
  (1, .right, 353) else some (0, .left, 14))) else (if n < 15 then (if n < 14 then some (1, .left,
  14) else some (0, .left, 16)) else (if n < 16 then some (1, .left, 16) else some (0, .left,
  18))))) else (if n < 26 then (if n < 22 then (if n < 20 then (if n < 19 then (if n < 18 then
  some (1, .left, 18) else some (0, .left, 20)) else some (1, .left, 20)) else (if n < 21 then
  some (0, .left, 22) else some (1, .left, 22))) else (if n < 24 then (if n < 23 then some (0,
  .left, 24) else some (1, .left, 24)) else (if n < 25 then some (0, .left, 26) else some (1,
  .left, 26)))) else (if n < 30 then (if n < 28 then (if n < 27 then some (0, .left, 0) else some
  (1, .left, 0)) else (if n < 29 then some (0, .left, 383) else some (1, .right, 28))) else (if n
  < 32 then (if n < 31 then some (0, .right, 32) else some (1, .left, 384)) else (if n < 33 then
  some (0, .right, 31) else some (0, .left, 34)))))) else (if n < 51 then (if n < 43 then (if n <
  39 then (if n < 37 then (if n < 36 then (if n < 35 then some (1, .left, 38) else some (0, .left,
  36)) else some (0, .left, 37)) else (if n < 38 then some (1, .left, 38) else some (1, .left,
  39))) else (if n < 41 then (if n < 40 then some (1, .left, 21) else some (1, .left, 33)) else
  (if n < 42 then some (0, .left, 42) else some (1, .left, 43)))) else (if n < 47 then (if n < 45
  then (if n < 44 then some (0, .left, 17) else some (0, .left, 96)) else (if n < 46 then some (0,
  .left, 66) else some (0, .left, 15))) else (if n < 49 then (if n < 48 then some (0, .left, 46)
  else some (0, .left, 49)) else (if n < 50 then some (0, .right, 235) else some (0, .left,
  51))))) else (if n < 60 then (if n < 56 then (if n < 54 then (if n < 53 then (if n < 52 then
  some (1, .left, 52) else some (0, .left, 53)) else some (1, .left, 54)) else (if n < 55 then
  some (0, .left, 55) else some (0, .left, 56))) else (if n < 58 then (if n < 57 then some (0,
  .left, 57) else some (0, .left, 48)) else (if n < 59 then some (0, .left, 59) else some (1,
  .left, 59)))) else (if n < 64 then (if n < 62 then (if n < 61 then some (0, .left, 13) else some
  (0, .left, 43)) else (if n < 63 then some (1, .left, 66) else some (0, .left, 33))) else (if n <
  66 then (if n < 65 then some (1, .left, 65) else some (1, .left, 3)) else (if n < 67 then some
  (1, .left, 67) else some (1, .left, 68))))))) else (if n < 102 then (if n < 85 then (if n < 77
  then (if n < 73 then (if n < 71 then (if n < 70 then (if n < 69 then some (1, .left, 33) else
  some (0, .left, 70)) else some (1, .left, 62)) else (if n < 72 then some (0, .right, 30) else
  some (0, .right, 71))) else (if n < 75 then (if n < 74 then some (0, .right, 72) else some (0,
  .right, 73)) else (if n < 76 then some (0, .right, 371) else some (0, .right, 75)))) else (if n
  < 81 then (if n < 79 then (if n < 78 then some (0, .right, 453) else some (0, .right, 77)) else
  (if n < 80 then some (0, .right, 74) else some (0, .right, 513))) else (if n < 83 then (if n <
  82 then some (0, .right, 499) else some (0, .right, 80)) else (if n < 84 then some (0, .right,
  513) else some (0, .right, 458))))) else (if n < 94 then (if n < 90 then (if n < 88 then (if n <
  87 then (if n < 86 then some (0, .right, 82) else some (0, .right, 79)) else some (0, .right,
  540)) else (if n < 89 then some (0, .right, 467) else some (0, .right, 367))) else (if n < 92
  then (if n < 91 then some (0, .right, 366) else some (0, .right, 89)) else (if n < 93 then some
  (0, .right, 538) else some (0, .right, 449)))) else (if n < 98 then (if n < 96 then (if n < 95
  then some (0, .right, 88) else some (0, .left, 69)) else (if n < 97 then some (0, .left, 40)
  else some (0, .right, 95))) else (if n < 100 then (if n < 99 then some (0, .right, 97) else some
  (0, .right, 365)) else (if n < 101 then some (0, .right, 99) else some (0, .right, 100))))))
  else (if n < 119 then (if n < 111 then (if n < 107 then (if n < 105 then (if n < 104 then (if n
  < 103 then some (0, .right, 98) else some (0, .left, 69)) else some (0, .left, 69)) else (if n <
  106 then some (0, .right, 103) else some (0, .right, 536))) else (if n < 109 then (if n < 108
  then some (0, .right, 446) else some (0, .right, 102)) else (if n < 110 then some (0, .right,
  94) else some (0, .right, 86)))) else (if n < 115 then (if n < 113 then (if n < 112 then some
  (1, .left, 47) else some (0, .right, 362)) else (if n < 114 then some (0, .right, 111) else some
  (0, .right, 113))) else (if n < 117 then (if n < 116 then some (0, .left, 35) else some (0,
  .right, 115)) else (if n < 118 then some (0, .right, 116) else some (0, .right, 114))))) else
  (if n < 128 then (if n < 124 then (if n < 122 then (if n < 121 then (if n < 120 then some (0,
  .right, 116) else some (0, .right, 119)) else some (0, .right, 118)) else (if n < 123 then some
  (0, .right, 500) else some (0, .right, 122))) else (if n < 126 then (if n < 125 then some (0,
  .right, 87) else some (0, .right, 123)) else (if n < 127 then some (0, .right, 121) else some
  (0, .right, 90)))) else (if n < 132 then (if n < 130 then (if n < 129 then some (0, .right, 542)
  else some (0, .right, 97)) else (if n < 131 then some (0, .right, 128) else some (0, .right,
  101))) else (if n < 134 then (if n < 133 then some (0, .right, 130) else some (0, .right, 104))
  else (if n < 135 then some (0, .right, 531) else some (0, .right, 363)))))))) else (if n < 204
  then (if n < 170 then (if n < 153 then (if n < 145 then (if n < 141 then (if n < 139 then (if n
  < 138 then (if n < 137 then some (0, .right, 111) else some (0, .right, 136)) else some (0,
  .right, 134)) else (if n < 140 then some (0, .left, 47) else some (0, .right, 139))) else (if n
  < 143 then (if n < 142 then some (0, .right, 140) else some (0, .right, 371)) else (if n < 144
  then some (0, .right, 142) else some (0, .right, 143)))) else (if n < 149 then (if n < 147 then
  (if n < 146 then some (0, .right, 141) else some (0, .right, 138)) else (if n < 148 then some
  (0, .right, 132) else some (0, .right, 126))) else (if n < 151 then (if n < 150 then some (0,
  .right, 110) else some (0, .right, 362)) else (if n < 152 then some (0, .right, 150) else some
  (0, .right, 515))))) else (if n < 162 then (if n < 158 then (if n < 156 then (if n < 155 then
  (if n < 154 then some (0, .right, 477) else some (0, .right, 151)) else some (0, .right, 154))
  else (if n < 157 then some (0, .right, 153) else some (0, .right, 155))) else (if n < 160 then
  (if n < 159 then some (0, .right, 156) else some (0, .right, 157)) else (if n < 161 then some
  (0, .right, 158) else some (0, .right, 159)))) else (if n < 166 then (if n < 164 then (if n <
  163 then some (0, .right, 160) else some (0, .right, 149)) else (if n < 165 then some (0,
  .right, 161) else some (0, .right, 490))) else (if n < 168 then (if n < 167 then some (0,
  .right, 154) else some (0, .right, 372)) else (if n < 169 then some (0, .right, 167) else some
  (0, .right, 423)))))) else (if n < 187 then (if n < 179 then (if n < 175 then (if n < 173 then
  (if n < 172 then (if n < 171 then some (0, .right, 373) else some (0, .right, 170)) else some
  (0, .right, 434)) else (if n < 174 then some (0, .right, 169) else some (0, .right, 166))) else
  (if n < 177 then (if n < 176 then some (0, .right, 512) else some (0, .right, 437)) else (if n <
  178 then some (0, .right, 363) else some (0, .right, 177)))) else (if n < 183 then (if n < 181
  then (if n < 180 then some (0, .right, 523) else some (0, .right, 464)) else (if n < 182 then
  some (0, .right, 176) else some (0, .right, 174))) else (if n < 185 then (if n < 184 then some
  (0, .right, 104) else some (0, .right, 183)) else (if n < 186 then some (0, .right, 96) else
  some (0, .right, 185))))) else (if n < 196 then (if n < 192 then (if n < 190 then (if n < 189
  then (if n < 188 then some (0, .right, 184) else some (0, .right, 112)) else some (0, .right,
  525)) else (if n < 191 then some (0, .right, 475) else some (0, .right, 187))) else (if n < 194
  then (if n < 193 then some (0, .right, 521) else some (0, .right, 439)) else (if n < 195 then
  some (0, .right, 495) else some (0, .right, 428)))) else (if n < 200 then (if n < 198 then (if n
  < 197 then some (0, .right, 193) else some (0, .right, 191)) else (if n < 199 then some (0,
  .right, 182) else some (0, .right, 514))) else (if n < 202 then (if n < 201 then some (0,
  .right, 199) else some (0, .right, 520)) else (if n < 203 then some (0, .right, 201) else some
  (0, .right, 200))))))) else (if n < 238 then (if n < 221 then (if n < 213 then (if n < 209 then
  (if n < 207 then (if n < 206 then (if n < 205 then some (0, .right, 423) else some (0, .right,
  192)) else some (0, .right, 373)) else (if n < 208 then some (0, .right, 206) else some (0,
  .right, 207))) else (if n < 211 then (if n < 210 then some (0, .right, 208) else some (0,
  .right, 205)) else (if n < 212 then some (0, .right, 203) else some (0, .right, 525)))) else (if
  n < 217 then (if n < 215 then (if n < 214 then some (0, .right, 212) else some (0, .right, 366))
  else (if n < 216 then some (0, .right, 214) else some (0, .right, 534))) else (if n < 219 then
  (if n < 218 then some (0, .right, 216) else some (0, .right, 213)) else (if n < 220 then some
  (0, .right, 537) else some (0, .right, 365))))) else (if n < 230 then (if n < 226 then (if n <
  224 then (if n < 223 then (if n < 222 then some (0, .right, 363) else some (0, .right, 220))
  else some (0, .right, 503)) else (if n < 225 then some (0, .right, 219) else some (0, .left,
  69))) else (if n < 228 then (if n < 227 then some (0, .right, 225) else some (0, .right, 226))
  else (if n < 229 then some (0, .right, 507) else some (0, .right, 227)))) else (if n < 234 then
  (if n < 232 then (if n < 231 then some (0, .right, 224) else some (0, .right, 218)) else (if n <
  233 then some (0, .right, 211) else some (0, .right, 198))) else (if n < 236 then (if n < 235
  then some (0, .right, 164) else some (0, .right, 163)) else (if n < 237 then some (0, .right,
  491) else some (0, .right, 394)))))) else (if n < 255 then (if n < 247 then (if n < 243 then (if
  n < 241 then (if n < 240 then (if n < 239 then some (0, .right, 491) else some (0, .right, 390))
  else some (0, .right, 237)) else (if n < 242 then some (0, .right, 388) else some (0, .right,
  241))) else (if n < 245 then (if n < 244 then some (0, .right, 495) else some (0, .right, 243))
  else (if n < 246 then some (0, .right, 242) else some (0, .right, 240)))) else (if n < 251 then
  (if n < 249 then (if n < 248 then some (0, .right, 495) else some (0, .right, 396)) else (if n <
  250 then some (0, .right, 247) else some (0, .right, 401))) else (if n < 253 then (if n < 252
  then some (0, .right, 492) else some (0, .right, 251)) else (if n < 254 then some (0, .right,
  252) else some (0, .right, 250))))) else (if n < 264 then (if n < 260 then (if n < 258 then (if
  n < 257 then (if n < 256 then some (0, .right, 249) else some (0, .right, 171)) else some (0,
  .right, 256)) else (if n < 259 then some (0, .right, 521) else some (0, .right, 258))) else (if
  n < 262 then (if n < 261 then some (0, .right, 257) else some (0, .right, 255)) else (if n < 263
  then some (0, .right, 246) else some (0, .right, 363)))) else (if n < 268 then (if n < 266 then
  (if n < 265 then some (0, .right, 220) else some (0, .right, 501)) else (if n < 267 then some
  (0, .right, 103) else some (0, .right, 266))) else (if n < 270 then (if n < 269 then some (0,
  .right, 265) else some (0, .right, 185)) else (if n < 271 then some (0, .right, 269) else some
  (0, .right, 268))))))))) else (if n < 408 then (if n < 340 then (if n < 306 then (if n < 289
  then (if n < 281 then (if n < 277 then (if n < 275 then (if n < 274 then (if n < 273 then some
  (0, .right, 263) else some (0, .right, 493)) else some (0, .right, 273)) else (if n < 276 then
  some (0, .right, 496) else some (0, .right, 275))) else (if n < 279 then (if n < 278 then some
  (0, .right, 274) else some (0, .right, 271)) else (if n < 280 then some (0, .right, 510) else
  some (0, .right, 518)))) else (if n < 285 then (if n < 283 then (if n < 282 then some (0,
  .right, 279) else some (0, .right, 494)) else (if n < 284 then some (0, .right, 415) else some
  (0, .right, 281))) else (if n < 287 then (if n < 286 then some (0, .right, 441) else some (0,
  .right, 413)) else (if n < 288 then some (0, .right, 373) else some (0, .right, 287))))) else
  (if n < 298 then (if n < 294 then (if n < 292 then (if n < 291 then (if n < 290 then some (0,
  .right, 288) else some (0, .right, 286)) else some (0, .right, 285)) else (if n < 293 then some
  (0, .right, 284) else some (0, .right, 278))) else (if n < 296 then (if n < 295 then some (0,
  .right, 262) else some (0, .right, 406)) else (if n < 297 then some (0, .right, 493) else some
  (0, .right, 411)))) else (if n < 302 then (if n < 300 then (if n < 299 then some (0, .right,
  295) else some (0, .right, 401)) else (if n < 301 then some (0, .right, 299) else some (0,
  .right, 529))) else (if n < 304 then (if n < 303 then some (0, .right, 301) else some (0,
  .right, 300)) else (if n < 305 then some (0, .right, 298) else some (0, .left, 47)))))) else (if
  n < 323 then (if n < 315 then (if n < 311 then (if n < 309 then (if n < 308 then (if n < 307
  then some (1, .left, 47) else some (0, .right, 305)) else some (0, .right, 529)) else (if n <
  310 then some (0, .right, 308) else some (0, .right, 306))) else (if n < 313 then (if n < 312
  then some (0, .right, 501) else some (0, .right, 311)) else (if n < 314 then some (0, .right,
  309) else some (0, .right, 494)))) else (if n < 319 then (if n < 317 then (if n < 316 then some
  (0, .right, 417) else some (0, .right, 283)) else (if n < 318 then some (0, .right, 313) else
  some (0, .right, 304))) else (if n < 321 then (if n < 320 then some (0, .right, 286) else some
  (0, .right, 282)) else (if n < 322 then some (0, .right, 319) else some (0, .right, 314)))))
  else (if n < 332 then (if n < 328 then (if n < 326 then (if n < 325 then (if n < 324 then some
  (0, .right, 491) else some (0, .right, 390)) else some (0, .right, 322)) else (if n < 327 then
  some (0, .right, 321) else some (0, .right, 528))) else (if n < 330 then (if n < 329 then some
  (0, .right, 399) else some (0, .right, 315)) else (if n < 331 then some (0, .left, 69) else some
  (0, .right, 305)))) else (if n < 336 then (if n < 334 then (if n < 333 then some (0, .right,
  529) else some (0, .right, 409)) else (if n < 335 then some (0, .right, 365) else some (0,
  .right, 111))) else (if n < 338 then (if n < 337 then some (0, .right, 335) else some (0,
  .right, 336)) else (if n < 339 then some (0, .right, 333) else some (0, .right, 329))))))) else
  (if n < 374 then (if n < 357 then (if n < 349 then (if n < 345 then (if n < 343 then (if n < 342
  then (if n < 341 then some (0, .right, 326) else some (0, .right, 318)) else some (0, .right,
  294)) else (if n < 344 then some (1, .left, 50) else some (1, .left, 50))) else (if n < 347 then
  (if n < 346 then some (0, .right, 343) else some (0, .right, 345)) else (if n < 348 then some
  (0, .right, 346) else some (0, .right, 347)))) else (if n < 353 then (if n < 351 then (if n <
  350 then some (0, .right, 348) else some (0, .right, 349)) else (if n < 352 then some (0,
  .right, 350) else some (0, .right, 351))) else (if n < 355 then (if n < 354 then some (0,
  .right, 342) else some (0, .left, 10)) else (if n < 356 then some (0, .right, 2) else some (0,
  .right, 355))))) else (if n < 366 then (if n < 362 then (if n < 360 then (if n < 359 then (if n
  < 358 then some (0, .right, 356) else some (0, .right, 369)) else some (0, .right, 358)) else
  (if n < 361 then some (0, .right, 359) else some (0, .right, 360))) else (if n < 364 then (if n
  < 363 then some (0, .right, 357) else some (0, .right, 362)) else (if n < 365 then some (0,
  .right, 363) else some (0, .right, 364)))) else (if n < 370 then (if n < 368 then (if n < 367
  then some (0, .right, 365) else some (0, .right, 366)) else (if n < 369 then some (0, .right,
  367) else some (0, .right, 368))) else (if n < 372 then (if n < 371 then some (0, .right, 29)
  else some (0, .right, 370)) else (if n < 373 then some (0, .right, 382) else some (0, .right,
  372)))))) else (if n < 391 then (if n < 383 then (if n < 379 then (if n < 377 then (if n < 376
  then (if n < 375 then some (0, .right, 373) else some (0, .right, 374)) else some (0, .right,
  75)) else (if n < 378 then some (0, .right, 456) else some (0, .right, 377))) else (if n < 381
  then (if n < 380 then some (0, .right, 378) else some (0, .right, 379)) else (if n < 382 then
  some (0, .right, 380) else some (0, .right, 381)))) else (if n < 387 then (if n < 385 then (if n
  < 384 then some (0, .left, 8) else some (0, .left, 383)) else (if n < 386 then some (0, .left,
  354) else some (0, .left, 385))) else (if n < 389 then (if n < 388 then some (0, .right, 360)
  else some (0, .right, 387)) else (if n < 390 then some (0, .right, 391) else some (0, .right,
  389))))) else (if n < 400 then (if n < 396 then (if n < 394 then (if n < 393 then (if n < 392
  then some (0, .right, 360) else some (0, .right, 378)) else some (0, .right, 391)) else (if n <
  395 then some (0, .right, 393) else some (0, .right, 361))) else (if n < 398 then (if n < 397
  then some (0, .right, 395) else some (0, .right, 361)) else (if n < 399 then some (0, .right,
  397) else some (0, .right, 398)))) else (if n < 404 then (if n < 402 then (if n < 401 then some
  (0, .right, 395) else some (0, .right, 400)) else (if n < 403 then some (0, .right, 404) else
  some (0, .right, 402))) else (if n < 406 then (if n < 405 then some (0, .right, 395) else some
  (0, .right, 404)) else (if n < 407 then some (0, .right, 405) else some (0, .right, 456))))))))
  else (if n < 476 then (if n < 442 then (if n < 425 then (if n < 417 then (if n < 413 then (if n
  < 411 then (if n < 410 then (if n < 409 then some (0, .right, 404) else some (0, .right, 408))
  else some (0, .right, 404)) else (if n < 412 then some (0, .right, 410) else some (0, .right,
  400))) else (if n < 415 then (if n < 414 then some (0, .right, 412) else some (0, .right, 418))
  else (if n < 416 then some (0, .right, 414) else some (0, .right, 418)))) else (if n < 421 then
  (if n < 419 then (if n < 418 then some (0, .right, 416) else some (0, .right, 400)) else (if n <
  420 then some (0, .right, 378) else some (0, .right, 418))) else (if n < 423 then (if n < 422
  then some (0, .right, 420) else some (0, .right, 358)) else (if n < 424 then some (0, .right,
  422) else some (0, .right, 426))))) else (if n < 434 then (if n < 430 then (if n < 428 then (if
  n < 427 then (if n < 426 then some (0, .right, 424) else some (0, .right, 358)) else some (0,
  .right, 426)) else (if n < 429 then some (0, .right, 427) else some (0, .right, 426))) else (if
  n < 432 then (if n < 431 then some (0, .right, 429) else some (0, .right, 426)) else (if n < 433
  then some (0, .right, 431) else some (0, .right, 359)))) else (if n < 438 then (if n < 436 then
  (if n < 435 then some (0, .right, 433) else some (0, .right, 359)) else (if n < 437 then some
  (0, .right, 435) else some (0, .right, 436))) else (if n < 440 then (if n < 439 then some (0,
  .right, 435) else some (0, .right, 438)) else (if n < 441 then some (0, .right, 435) else some
  (0, .right, 440)))))) else (if n < 459 then (if n < 451 then (if n < 447 then (if n < 445 then
  (if n < 444 then (if n < 443 then some (0, .right, 364) else some (0, .right, 442)) else some
  (0, .right, 456)) else (if n < 446 then some (0, .right, 447) else some (0, .right, 445))) else
  (if n < 449 then (if n < 448 then some (0, .right, 364) else some (0, .right, 447)) else (if n <
  450 then some (0, .right, 448) else some (1, .left, 12)))) else (if n < 455 then (if n < 453
  then (if n < 452 then some (0, .right, 356) else some (0, .left, 450)) else (if n < 454 then
  some (0, .right, 451) else some (0, .left, 13))) else (if n < 457 then (if n < 456 then some (0,
  .right, 356) else some (0, .right, 376)) else (if n < 458 then some (0, .right, 455) else some
  (0, .right, 457))))) else (if n < 468 then (if n < 464 then (if n < 462 then (if n < 461 then
  (if n < 460 then some (0, .right, 456) else some (0, .right, 455)) else some (0, .right, 460))
  else (if n < 463 then some (0, .right, 456) else some (0, .right, 455))) else (if n < 466 then
  (if n < 465 then some (0, .right, 463) else some (0, .right, 379)) else (if n < 467 then some
  (0, .right, 455) else some (0, .right, 466)))) else (if n < 472 then (if n < 470 then (if n <
  469 then some (0, .right, 455) else some (0, .right, 468)) else (if n < 471 then some (0,
  .right, 369) else some (0, .right, 470))) else (if n < 474 then (if n < 473 then some (0,
  .right, 369) else some (0, .right, 376)) else (if n < 475 then some (0, .right, 472) else some
  (0, .right, 474))))))) else (if n < 510 then (if n < 493 then (if n < 485 then (if n < 481 then
  (if n < 479 then (if n < 478 then (if n < 477 then some (0, .right, 486) else some (0, .right,
  476)) else some (0, .right, 376)) else (if n < 480 then some (0, .right, 486) else some (0,
  .right, 479))) else (if n < 483 then (if n < 482 then some (0, .right, 486) else some (0,
  .right, 481)) else (if n < 484 then some (0, .right, 378) else some (0, .right, 486)))) else (if
  n < 489 then (if n < 487 then (if n < 486 then some (0, .right, 484) else some (0, .right, 357))
  else (if n < 488 then some (0, .right, 486) else some (0, .right, 487))) else (if n < 491 then
  (if n < 490 then some (0, .right, 362) else some (0, .right, 489)) else (if n < 492 then some
  (0, .right, 497) else some (0, .right, 508))))) else (if n < 502 then (if n < 498 then (if n <
  496 then (if n < 495 then (if n < 494 then some (0, .right, 497) else some (0, .right, 497))
  else some (0, .right, 497)) else (if n < 497 then some (0, .right, 497) else some (0, .right,
  362))) else (if n < 500 then (if n < 499 then some (0, .right, 377) else some (0, .right, 497))
  else (if n < 501 then some (0, .right, 497) else some (0, .right, 497)))) else (if n < 506 then
  (if n < 504 then (if n < 503 then some (0, .right, 456) else some (0, .right, 497)) else (if n <
  505 then some (0, .right, 363) else some (0, .right, 504))) else (if n < 508 then (if n < 507
  then some (0, .right, 374) else some (0, .right, 135)) else (if n < 509 then some (0, .right,
  375) else some (0, .right, 135)))))) else (if n < 527 then (if n < 519 then (if n < 515 then (if
  n < 513 then (if n < 512 then (if n < 511 then some (0, .right, 135) else some (0, .right, 135))
  else some (0, .right, 135)) else (if n < 514 then some (0, .right, 135) else some (0, .right,
  135))) else (if n < 517 then (if n < 516 then some (0, .right, 135) else some (0, .right, 365))
  else (if n < 518 then some (0, .right, 516) else some (0, .right, 522)))) else (if n < 523 then
  (if n < 521 then (if n < 520 then some (0, .right, 522) else some (0, .right, 522)) else (if n <
  522 then some (0, .right, 522) else some (0, .right, 365))) else (if n < 525 then (if n < 524
  then some (0, .right, 522) else some (0, .right, 382)) else (if n < 526 then some (0, .right,
  522) else some (0, .right, 366))))) else (if n < 535 then (if n < 531 then (if n < 529 then (if
  n < 528 then some (0, .right, 526) else some (0, .right, 530)) else (if n < 530 then some (0,
  .right, 530) else some (0, .right, 366))) else (if n < 533 then (if n < 532 then some (0,
  .right, 530) else some (0, .right, 367)) else (if n < 534 then some (0, .right, 532) else some
  (0, .right, 535)))) else (if n < 539 then (if n < 537 then (if n < 536 then some (0, .right,
  367) else some (0, .right, 535)) else (if n < 538 then some (0, .right, 535) else some (0,
  .right, 539))) else (if n < 541 then (if n < 540 then some (0, .right, 368) else some (0,
  .right, 539)) else (if n < 542 then some (0, .right, 75) else some (0, .right, 539))))))))))
def candTrans1 (n : Nat) : Option (Fin 2 × Dir × Fin 543) :=
  (if n < 272 then (if n < 136 then (if n < 68 then (if n < 34 then (if n < 17 then (if n < 9 then
  (if n < 5 then (if n < 3 then (if n < 2 then (if n < 1 then some (1, .right, 353) else some (1,
  .right, 4)) else some (0, .right, 1)) else (if n < 4 then some (1, .right, 4) else some (1,
  .right, 4))) else (if n < 7 then (if n < 6 then some (0, .left, 20) else some (0, .left, 7))
  else (if n < 8 then some (1, .left, 7) else some (0, .left, 10)))) else (if n < 13 then (if n <
  11 then (if n < 10 then some (1, .left, 12) else some (0, .left, 13)) else (if n < 12 then some
  (0, .right, 235) else some (1, .left, 14))) else (if n < 15 then (if n < 14 then some (0, .left,
  15) else some (1, .left, 16)) else (if n < 16 then some (0, .left, 17) else some (1, .left,
  18))))) else (if n < 26 then (if n < 22 then (if n < 20 then (if n < 19 then (if n < 18 then
  some (0, .left, 19) else some (1, .left, 20)) else some (0, .left, 21)) else (if n < 21 then
  some (1, .left, 22) else some (0, .left, 23))) else (if n < 24 then (if n < 23 then some (1,
  .left, 24) else some (0, .left, 25)) else (if n < 25 then some (1, .left, 26) else some (0,
  .left, 27)))) else (if n < 30 then (if n < 28 then (if n < 27 then some (1, .left, 0) else some
  (0, .left, 11)) else (if n < 29 then some (0, .right, 29) else some (1, .right, 29))) else (if n
  < 32 then (if n < 31 then some (0, .left, 63) else some (1, .right, 32)) else (if n < 33 then
  some (1, .right, 32) else some (0, .left, 24)))))) else (if n < 51 then (if n < 43 then (if n <
  39 then (if n < 37 then (if n < 36 then (if n < 35 then some (0, .left, 38) else some (0, .left,
  61)) else some (0, .left, 14)) else (if n < 38 then some (1, .left, 38) else some (1, .left,
  39))) else (if n < 41 then (if n < 40 then none else some (0, .left, 64)) else (if n < 42 then
  some (0, .left, 61) else some (1, .left, 43)))) else (if n < 47 then (if n < 45 then (if n < 44
  then some (1, .left, 17) else some (1, .left, 33)) else (if n < 46 then some (1, .left, 66) else
  some (1, .left, 45))) else (if n < 49 then (if n < 48 then some (0, .left, 42) else some (0,
  .left, 49)) else (if n < 50 then some (0, .right, 235) else some (0, .left, 51))))) else (if n <
  60 then (if n < 56 then (if n < 54 then (if n < 53 then (if n < 52 then some (1, .left, 52) else
  some (0, .left, 53)) else some (1, .left, 54)) else (if n < 55 then some (0, .left, 55) else
  some (0, .left, 56))) else (if n < 58 then (if n < 57 then some (0, .left, 57) else some (0,
  .left, 48)) else (if n < 59 then some (0, .left, 12) else some (1, .left, 30)))) else (if n < 64
  then (if n < 62 then (if n < 61 then some (1, .left, 61) else some (0, .left, 43)) else (if n <
  63 then some (0, .left, 16) else some (1, .left, 55))) else (if n < 66 then (if n < 65 then some
  (0, .left, 287) else some (0, .left, 66)) else (if n < 67 then some (0, .left, 18) else some (0,
  .left, 20))))))) else (if n < 102 then (if n < 85 then (if n < 77 then (if n < 73 then (if n <
  71 then (if n < 70 then (if n < 69 then some (0, .left, 22) else some (1, .left, 13)) else some
  (0, .left, 45)) else (if n < 72 then some (1, .right, 30) else some (1, .right, 71))) else (if n
  < 75 then (if n < 74 then some (1, .right, 72) else some (1, .right, 73)) else (if n < 76 then
  some (1, .right, 75) else some (0, .left, 13)))) else (if n < 81 then (if n < 79 then (if n < 78
  then some (1, .right, 76) else some (1, .right, 458)) else (if n < 80 then some (1, .right, 78)
  else some (1, .right, 443))) else (if n < 83 then (if n < 82 then some (0, .left, 15) else some
  (1, .right, 81)) else (if n < 84 then some (0, .left, 15) else some (1, .right, 83))))) else (if
  n < 94 then (if n < 90 then (if n < 88 then (if n < 87 then (if n < 86 then some (1, .right, 84)
  else some (1, .right, 85)) else some (0, .left, 15)) else (if n < 89 then some (1, .right, 87)
  else some (1, .left, 454))) else (if n < 92 then (if n < 91 then some (1, .left, 454) else some
  (1, .right, 90)) else (if n < 93 then some (1, .right, 91) else some (1, .right, 92)))) else (if
  n < 98 then (if n < 96 then (if n < 95 then some (1, .right, 93) else some (1, .right, 378))
  else (if n < 97 then some (0, .left, 10) else some (1, .right, 96))) else (if n < 100 then (if n
  < 99 then some (1, .right, 533) else some (1, .left, 41)) else (if n < 101 then some (0, .left,
  13) else some (0, .left, 15)))))) else (if n < 119 then (if n < 111 then (if n < 107 then (if n
  < 105 then (if n < 104 then (if n < 103 then some (1, .right, 101) else some (1, .right, 363))
  else some (1, .right, 362)) else (if n < 106 then some (1, .right, 104) else some (1, .right,
  105))) else (if n < 109 then (if n < 108 then some (1, .right, 106) else some (1, .right, 107))
  else (if n < 110 then some (1, .right, 108) else some (1, .right, 109)))) else (if n < 115 then
  (if n < 113 then (if n < 112 then some (1, .left, 69) else some (1, .left, 41)) else (if n < 114
  then some (1, .right, 112) else some (1, .right, 490))) else (if n < 117 then (if n < 116 then
  some (0, .left, 10) else some (0, .left, 13)) else (if n < 118 then some (1, .right, 505) else
  some (1, .right, 117))))) else (if n < 128 then (if n < 124 then (if n < 122 then (if n < 121
  then (if n < 120 then some (0, .left, 15) else some (1, .right, 461)) else some (1, .right,
  120)) else (if n < 123 then some (0, .left, 15) else some (1, .right, 469))) else (if n < 126
  then (if n < 125 then some (1, .right, 488) else some (1, .right, 124)) else (if n < 127 then
  some (1, .right, 125) else some (1, .right, 89)))) else (if n < 132 then (if n < 130 then (if n
  < 129 then some (1, .right, 127) else some (1, .right, 527)) else (if n < 131 then some (1,
  .right, 129) else some (1, .right, 480))) else (if n < 134 then (if n < 133 then some (1,
  .right, 131) else some (1, .right, 103)) else (if n < 135 then some (1, .right, 133) else some
  (0, .left, 60)))))))) else (if n < 204 then (if n < 170 then (if n < 153 then (if n < 145 then
  (if n < 141 then (if n < 139 then (if n < 138 then (if n < 137 then some (1, .right, 135) else
  some (1, .right, 505)) else some (1, .right, 137)) else (if n < 140 then some (0, .left, 10)
  else some (0, .left, 13))) else (if n < 143 then (if n < 142 then some (1, .right, 490) else
  some (0, .left, 58)) else (if n < 144 then some (0, .left, 13) else some (0, .left, 15)))) else
  (if n < 149 then (if n < 147 then (if n < 146 then some (1, .right, 144) else some (1, .right,
  145)) else (if n < 148 then some (1, .right, 146) else some (1, .right, 147))) else (if n < 151
  then (if n < 150 then some (1, .right, 148) else some (1, .left, 50)) else (if n < 152 then some
  (1, .right, 150) else some (1, .right, 151))))) else (if n < 162 then (if n < 158 then (if n <
  156 then (if n < 155 then (if n < 154 then some (1, .right, 152) else some (1, .right, 151))
  else some (1, .right, 154)) else (if n < 157 then some (1, .right, 155) else some (1, .right,
  155))) else (if n < 160 then (if n < 159 then some (1, .right, 157) else some (1, .right, 157))
  else (if n < 161 then some (1, .right, 159) else some (1, .right, 159)))) else (if n < 166 then
  (if n < 164 then (if n < 163 then some (1, .right, 161) else some (1, .right, 162)) else (if n <
  165 then some (1, .right, 161) else some (1, .right, 471))) else (if n < 168 then (if n < 167
  then some (1, .right, 165) else some (0, .left, 450)) else (if n < 169 then some (0, .left, 13)
  else some (1, .right, 168)))))) else (if n < 187 then (if n < 179 then (if n < 175 then (if n <
  173 then (if n < 172 then (if n < 171 then some (0, .left, 450) else some (0, .left, 13)) else
  some (1, .right, 171)) else (if n < 174 then some (1, .right, 172) else some (1, .right, 173)))
  else (if n < 177 then (if n < 176 then some (0, .left, 15) else some (1, .right, 175)) else (if
  n < 178 then some (1, .left, 454) else some (1, .right, 112)))) else (if n < 183 then (if n <
  181 then (if n < 180 then some (1, .right, 178) else some (1, .right, 179)) else (if n < 182
  then some (1, .right, 180) else some (1, .right, 181))) else (if n < 185 then (if n < 184 then
  some (1, .right, 115) else some (1, .right, 490)) else (if n < 186 then some (0, .left, 13) else
  some (1, .right, 505))))) else (if n < 196 then (if n < 192 then (if n < 190 then (if n < 189
  then (if n < 188 then some (1, .right, 186) else some (0, .left, 13)) else some (1, .right,
  188)) else (if n < 191 then some (1, .right, 189) else some (1, .right, 190))) else (if n < 194
  then (if n < 193 then some (1, .right, 140) else some (1, .right, 192)) else (if n < 195 then
  some (1, .right, 471) else some (1, .right, 194)))) else (if n < 200 then (if n < 198 then (if n
  < 197 then some (1, .right, 195) else some (1, .right, 196)) else (if n < 199 then some (1,
  .right, 197) else some (0, .left, 15))) else (if n < 202 then (if n < 201 then some (1, .right,
  425) else some (1, .right, 188)) else (if n < 203 then some (1, .right, 439) else some (1,
  .right, 202))))))) else (if n < 238 then (if n < 221 then (if n < 213 then (if n < 209 then (if
  n < 207 then (if n < 206 then (if n < 205 then some (1, .right, 511) else some (1, .right, 204))
  else some (1, .left, 58)) else (if n < 208 then some (0, .left, 13) else some (0, .left, 15)))
  else (if n < 211 then (if n < 210 then some (1, .right, 475) else some (1, .right, 209)) else
  (if n < 212 then some (1, .right, 210) else some (0, .left, 15)))) else (if n < 217 then (if n <
  215 then (if n < 214 then some (1, .right, 432) else some (1, .left, 41)) else (if n < 216 then
  some (0, .left, 13) else some (1, .right, 215))) else (if n < 219 then (if n < 218 then some (1,
  .right, 485) else some (1, .right, 217)) else (if n < 220 then some (1, .right, 140) else some
  (1, .left, 454))))) else (if n < 230 then (if n < 226 then (if n < 224 then (if n < 223 then (if
  n < 222 then some (0, .left, 10) else some (1, .right, 221)) else some (1, .right, 222)) else
  (if n < 225 then some (1, .right, 223) else some (0, .left, 10))) else (if n < 228 then (if n <
  227 then some (0, .left, 13) else some (1, .right, 388)) else (if n < 229 then some (0, .left,
  15) else some (1, .right, 228)))) else (if n < 234 then (if n < 232 then (if n < 231 then some
  (1, .right, 229) else some (1, .right, 230)) else (if n < 233 then some (1, .right, 231) else
  some (1, .right, 232))) else (if n < 236 then (if n < 235 then some (1, .right, 233) else some
  (1, .right, 234)) else (if n < 237 then some (1, .right, 100) else some (1, .right, 236))))))
  else (if n < 255 then (if n < 247 then (if n < 243 then (if n < 241 then (if n < 240 then (if n
  < 239 then some (1, .right, 140) else some (1, .right, 238)) else some (1, .right, 239)) else
  (if n < 242 then some (1, .right, 507) else some (1, .right, 430))) else (if n < 245 then (if n
  < 244 then some (1, .right, 100) else some (1, .right, 428)) else (if n < 246 then some (1,
  .right, 244) else some (1, .right, 245)))) else (if n < 251 then (if n < 249 then (if n < 248
  then some (1, .right, 140) else some (1, .right, 509)) else (if n < 250 then some (1, .right,
  248) else some (1, .right, 413))) else (if n < 253 then (if n < 252 then some (0, .left, 450)
  else some (0, .left, 13)) else (if n < 254 then some (1, .right, 434) else some (1, .right,
  253))))) else (if n < 264 then (if n < 260 then (if n < 258 then (if n < 257 then (if n < 256
  then some (1, .right, 254) else some (0, .left, 15)) else some (1, .right, 439)) else (if n <
  259 then some (0, .left, 15) else some (1, .right, 482))) else (if n < 262 then (if n < 261 then
  some (1, .right, 259) else some (1, .right, 260)) else (if n < 263 then some (1, .right, 261)
  else some (1, .left, 41)))) else (if n < 268 then (if n < 266 then (if n < 265 then some (1,
  .right, 263) else some (1, .right, 264)) else (if n < 267 then some (1, .right, 115) else some
  (1, .right, 505))) else (if n < 270 then (if n < 269 then some (1, .right, 267) else some (1,
  .right, 517)) else (if n < 271 then some (1, .right, 406) else some (1, .right, 270)))))))))
  else (if n < 408 then (if n < 340 then (if n < 306 then (if n < 289 then (if n < 281 then (if n
  < 277 then (if n < 275 then (if n < 274 then (if n < 273 then some (0, .left, 13) else some (1,
  .right, 272)) else some (1, .right, 441)) else (if n < 276 then some (1, .right, 140) else some
  (1, .right, 421))) else (if n < 279 then (if n < 278 then some (1, .right, 276) else some (1,
  .right, 277)) else (if n < 280 then some (1, .right, 401) else some (0, .left, 15)))) else (if n
  < 285 then (if n < 283 then (if n < 282 then some (1, .right, 280) else some (1, .right, 272))
  else (if n < 284 then some (1, .right, 282) else some (1, .right, 283))) else (if n < 287 then
  (if n < 286 then some (1, .right, 275) else some (1, .right, 519)) else (if n < 288 then some
  (1, .left, 44) else some (0, .left, 13))))) else (if n < 298 then (if n < 294 then (if n < 292
  then (if n < 291 then (if n < 290 then some (0, .left, 15) else some (1, .right, 289)) else some
  (1, .right, 290)) else (if n < 293 then some (1, .right, 291) else some (1, .right, 292))) else
  (if n < 296 then (if n < 295 then some (1, .right, 293) else some (1, .right, 273)) else (if n <
  297 then some (1, .right, 140) else some (1, .right, 296)))) else (if n < 302 then (if n < 300
  then (if n < 299 then some (1, .right, 297) else some (1, .right, 518)) else (if n < 301 then
  some (1, .right, 403) else some (1, .right, 188))) else (if n < 304 then (if n < 303 then some
  (1, .right, 409) else some (1, .right, 302)) else (if n < 305 then some (1, .right, 303) else
  some (1, .right, 363)))))) else (if n < 323 then (if n < 315 then (if n < 311 then (if n < 309
  then (if n < 308 then (if n < 307 then some (0, .left, 10) else some (1, .right, 306)) else some
  (1, .right, 307)) else (if n < 310 then some (1, .right, 482) else some (0, .left, 13))) else
  (if n < 313 then (if n < 312 then some (1, .right, 310) else some (1, .right, 299)) else (if n <
  314 then some (1, .right, 312) else some (1, .right, 140)))) else (if n < 319 then (if n < 317
  then (if n < 316 then some (1, .right, 314) else some (1, .right, 315)) else (if n < 318 then
  some (1, .right, 316) else some (1, .right, 317))) else (if n < 321 then (if n < 320 then some
  (1, .right, 415) else some (1, .right, 417)) else (if n < 322 then some (1, .right, 320) else
  some (1, .right, 286))))) else (if n < 332 then (if n < 328 then (if n < 326 then (if n < 325
  then (if n < 324 then some (1, .right, 272) else some (1, .right, 323)) else some (1, .right,
  324)) else (if n < 327 then some (1, .right, 325) else some (1, .right, 188))) else (if n < 330
  then (if n < 329 then some (1, .right, 327) else some (1, .right, 328)) else (if n < 331 then
  some (1, .right, 365) else some (1, .right, 330)))) else (if n < 336 then (if n < 334 then (if n
  < 333 then some (1, .right, 331) else some (1, .right, 332)) else (if n < 335 then some (1,
  .left, 50) else some (1, .right, 334))) else (if n < 338 then (if n < 337 then some (1, .right,
  517) else some (1, .right, 117)) else (if n < 339 then some (1, .right, 337) else some (1,
  .right, 338))))))) else (if n < 374 then (if n < 357 then (if n < 349 then (if n < 345 then (if
  n < 343 then (if n < 342 then (if n < 341 then some (1, .right, 339) else some (1, .right, 340))
  else some (1, .right, 341)) else (if n < 344 then some (1, .left, 10) else none)) else (if n <
  347 then (if n < 346 then some (1, .right, 344) else some (0, .left, 15)) else (if n < 348 then
  some (0, .left, 17) else some (0, .left, 19)))) else (if n < 353 then (if n < 351 then (if n <
  350 then some (0, .left, 21) else some (0, .left, 23)) else (if n < 352 then some (0, .left, 25)
  else some (0, .left, 27))) else (if n < 355 then (if n < 354 then some (1, .right, 352) else
  some (1, .left, 10)) else (if n < 356 then some (1, .right, 355) else some (1, .right, 356)))))
  else (if n < 366 then (if n < 362 then (if n < 360 then (if n < 359 then (if n < 358 then some
  (1, .right, 357) else some (1, .right, 358)) else some (1, .right, 359)) else (if n < 361 then
  some (1, .right, 360) else some (1, .right, 361))) else (if n < 364 then (if n < 363 then some
  (1, .right, 362) else some (1, .right, 363)) else (if n < 365 then some (1, .right, 364) else
  some (1, .right, 365)))) else (if n < 370 then (if n < 368 then (if n < 367 then some (1,
  .right, 366) else some (1, .right, 367)) else (if n < 369 then some (1, .right, 368) else some
  (1, .right, 369))) else (if n < 372 then (if n < 371 then some (1, .right, 370) else some (1,
  .right, 371)) else (if n < 373 then some (1, .right, 372) else some (1, .right, 373)))))) else
  (if n < 391 then (if n < 383 then (if n < 379 then (if n < 377 then (if n < 376 then (if n < 375
  then some (1, .right, 374) else some (1, .right, 375)) else some (1, .right, 376)) else (if n <
  378 then some (1, .right, 377) else some (1, .right, 378))) else (if n < 381 then (if n < 380
  then some (1, .right, 379) else some (1, .right, 380)) else (if n < 382 then some (1, .right,
  381) else some (1, .right, 382)))) else (if n < 387 then (if n < 385 then (if n < 384 then some
  (1, .left, 384) else some (1, .left, 384)) else (if n < 386 then some (1, .left, 386) else some
  (1, .left, 386))) else (if n < 389 then (if n < 388 then some (1, .left, 10) else some (1,
  .right, 452)) else (if n < 390 then some (1, .right, 459) else some (1, .right, 116))))) else
  (if n < 400 then (if n < 396 then (if n < 394 then (if n < 393 then (if n < 392 then some (1,
  .left, 454) else some (1, .right, 376)) else some (1, .right, 392)) else (if n < 395 then some
  (1, .right, 116) else some (1, .left, 10))) else (if n < 398 then (if n < 397 then some (1,
  .right, 452) else some (1, .left, 454)) else (if n < 399 then some (1, .right, 478) else some
  (1, .right, 116)))) else (if n < 404 then (if n < 402 then (if n < 401 then some (1, .left, 10)
  else some (1, .right, 452)) else (if n < 403 then some (1, .right, 478) else some (1, .right,
  116))) else (if n < 406 then (if n < 405 then some (1, .left, 454) else some (1, .right, 459))
  else (if n < 407 then some (1, .right, 116) else some (1, .right, 379)))))))) else (if n < 476
  then (if n < 442 then (if n < 425 then (if n < 417 then (if n < 413 then (if n < 411 then (if n
  < 410 then (if n < 409 then some (1, .right, 407) else some (1, .right, 116)) else some (1,
  .right, 392)) else (if n < 412 then some (1, .right, 116) else some (1, .left, 10))) else (if n
  < 415 then (if n < 414 then some (1, .right, 452) else some (1, .right, 459)) else (if n < 416
  then some (1, .right, 116) else some (1, .right, 392)))) else (if n < 421 then (if n < 419 then
  (if n < 418 then some (1, .right, 116) else some (1, .left, 454)) else (if n < 420 then some (1,
  .right, 456) else some (1, .right, 419))) else (if n < 423 then (if n < 422 then some (1,
  .right, 116) else some (1, .left, 10)) else (if n < 424 then some (1, .right, 452) else some (1,
  .right, 473))))) else (if n < 434 then (if n < 430 then (if n < 428 then (if n < 427 then (if n
  < 426 then some (1, .right, 116) else some (1, .left, 454)) else some (1, .right, 459)) else (if
  n < 429 then some (1, .right, 116) else some (1, .right, 392))) else (if n < 432 then (if n <
  431 then some (1, .right, 116) else some (1, .right, 380)) else (if n < 433 then some (1,
  .right, 116) else some (1, .left, 10)))) else (if n < 438 then (if n < 436 then (if n < 435 then
  some (1, .right, 452) else some (1, .left, 454)) else (if n < 437 then some (1, .right, 456)
  else some (1, .right, 116))) else (if n < 440 then (if n < 439 then some (1, .right, 462) else
  some (1, .right, 116)) else (if n < 441 then some (1, .right, 392) else some (1, .right,
  116)))))) else (if n < 459 then (if n < 451 then (if n < 447 then (if n < 445 then (if n < 444
  then (if n < 443 then some (1, .left, 10) else some (1, .right, 452)) else some (1, .right,
  380)) else (if n < 446 then some (1, .right, 444) else some (1, .right, 116))) else (if n < 449
  then (if n < 448 then some (1, .left, 454) else some (1, .right, 381)) else (if n < 450 then
  some (1, .right, 116) else some (0, .left, 12)))) else (if n < 455 then (if n < 453 then (if n <
  452 then some (1, .left, 10) else some (0, .left, 10)) else (if n < 454 then some (1, .right,
  452) else some (1, .left, 13))) else (if n < 457 then (if n < 456 then some (1, .left, 454) else
  some (1, .right, 456)) else (if n < 458 then some (1, .right, 456) else some (1, .right,
  116))))) else (if n < 468 then (if n < 464 then (if n < 462 then (if n < 461 then (if n < 460
  then some (1, .right, 376) else some (1, .right, 459)) else some (1, .right, 116)) else (if n <
  463 then some (1, .right, 378) else some (1, .right, 462))) else (if n < 466 then (if n < 465
  then some (1, .right, 116) else some (1, .right, 381)) else (if n < 467 then some (1, .right,
  465) else some (1, .right, 116)))) else (if n < 472 then (if n < 470 then (if n < 469 then some
  (1, .right, 381) else some (1, .right, 116)) else (if n < 471 then some (1, .left, 10) else some
  (1, .right, 452))) else (if n < 474 then (if n < 473 then some (1, .left, 454) else some (1,
  .right, 378)) else (if n < 475 then some (1, .right, 473) else some (1, .right, 116))))))) else
  (if n < 510 then (if n < 493 then (if n < 485 then (if n < 481 then (if n < 479 then (if n < 478
  then (if n < 477 then some (1, .right, 456) else some (1, .right, 116)) else some (1, .right,
  379)) else (if n < 480 then some (1, .right, 478) else some (1, .right, 116))) else (if n < 483
  then (if n < 482 then some (1, .right, 392) else some (1, .right, 116)) else (if n < 484 then
  some (1, .right, 380) else some (1, .right, 483)))) else (if n < 489 then (if n < 487 then (if n
  < 486 then some (1, .right, 116) else some (1, .left, 454)) else (if n < 488 then some (1,
  .right, 465) else some (1, .right, 116))) else (if n < 491 then (if n < 490 then some (1, .left,
  10) else some (1, .right, 452)) else (if n < 492 then some (1, .right, 506) else some (0, .left,
  450))))) else (if n < 502 then (if n < 498 then (if n < 496 then (if n < 495 then (if n < 494
  then some (1, .right, 492) else some (1, .right, 251)) else some (1, .right, 167)) else (if n <
  497 then some (1, .right, 170) else some (0, .left, 454))) else (if n < 500 then (if n < 499
  then some (0, .left, 450) else some (1, .right, 498)) else (if n < 501 then some (1, .right,
  142) else some (1, .right, 541)))) else (if n < 506 then (if n < 504 then (if n < 503 then some
  (0, .left, 450) else some (1, .right, 502)) else (if n < 505 then some (1, .left, 10) else some
  (1, .right, 452))) else (if n < 508 then (if n < 507 then some (0, .left, 450) else some (1,
  .right, 506)) else (if n < 509 then some (0, .left, 450) else some (1, .right, 508)))))) else
  (if n < 527 then (if n < 519 then (if n < 515 then (if n < 513 then (if n < 512 then (if n < 511
  then some (1, .right, 251) else some (1, .right, 167)) else some (1, .right, 170)) else (if n <
  514 then some (1, .right, 142) else some (1, .right, 524))) else (if n < 517 then (if n < 516
  then some (1, .right, 541) else some (1, .left, 10)) else (if n < 518 then some (1, .right, 452)
  else some (1, .right, 492)))) else (if n < 523 then (if n < 521 then (if n < 520 then some (1,
  .right, 251) else some (1, .right, 167)) else (if n < 522 then some (1, .right, 170) else some
  (0, .left, 454))) else (if n < 525 then (if n < 524 then some (1, .right, 142) else some (0,
  .left, 450)) else (if n < 526 then some (1, .right, 524) else some (1, .left, 10))))) else (if n
  < 535 then (if n < 531 then (if n < 529 then (if n < 528 then some (1, .right, 452) else some
  (1, .right, 508)) else (if n < 530 then some (1, .right, 492) else some (0, .left, 454))) else
  (if n < 533 then (if n < 532 then some (1, .right, 541) else some (1, .left, 10)) else (if n <
  534 then some (1, .right, 452) else some (1, .right, 167)))) else (if n < 539 then (if n < 537
  then (if n < 536 then some (0, .left, 454) else some (1, .right, 498)) else (if n < 538 then
  some (1, .right, 541) else some (1, .right, 498))) else (if n < 541 then (if n < 540 then some
  (0, .left, 454) else some (1, .right, 142)) else (if n < 542 then some (0, .left, 450) else some
  (1, .right, 541))))))))))
def candTrans (q : Fin 543) (b : Fin 2) : Option (Fin 2 × Dir × Fin 543) :=
  if b == 0 then candTrans0 q.val else candTrans1 q.val

def isBounce0 (n : Nat) : Bool :=
  (if n < 372 then (if n < 186 then (if n < 93 then (if n < 46 then (if n < 23 then (if n < 11
  then (if n < 5 then (if n < 2 then (if n < 1 then false else false) else (if n < 3 then false
  else (if n < 4 then false else false))) else (if n < 8 then (if n < 6 then false else (if n < 7
  then false else false)) else (if n < 9 then false else (if n < 10 then false else false)))) else
  (if n < 17 then (if n < 14 then (if n < 12 then false else (if n < 13 then true else true)) else
  (if n < 15 then false else (if n < 16 then false else false))) else (if n < 20 then (if n < 18
  then false else (if n < 19 then false else false)) else (if n < 21 then false else (if n < 22
  then false else false))))) else (if n < 34 then (if n < 28 then (if n < 25 then (if n < 24 then
  false else false) else (if n < 26 then false else (if n < 27 then false else false))) else (if n
  < 31 then (if n < 29 then false else (if n < 30 then false else false)) else (if n < 32 then
  false else (if n < 33 then false else false)))) else (if n < 40 then (if n < 37 then (if n < 35
  then false else (if n < 36 then false else false)) else (if n < 38 then false else (if n < 39
  then false else false))) else (if n < 43 then (if n < 41 then false else (if n < 42 then false
  else false)) else (if n < 44 then false else (if n < 45 then false else false)))))) else (if n <
  69 then (if n < 57 then (if n < 51 then (if n < 48 then (if n < 47 then false else false) else
  (if n < 49 then false else (if n < 50 then false else false))) else (if n < 54 then (if n < 52
  then false else (if n < 53 then false else false)) else (if n < 55 then false else (if n < 56
  then false else false)))) else (if n < 63 then (if n < 60 then (if n < 58 then false else (if n
  < 59 then false else false)) else (if n < 61 then false else (if n < 62 then false else false)))
  else (if n < 66 then (if n < 64 then false else (if n < 65 then false else false)) else (if n <
  67 then false else (if n < 68 then false else false))))) else (if n < 81 then (if n < 75 then
  (if n < 72 then (if n < 70 then false else (if n < 71 then false else false)) else (if n < 73
  then false else (if n < 74 then false else false))) else (if n < 78 then (if n < 76 then false
  else (if n < 77 then false else false)) else (if n < 79 then false else (if n < 80 then false
  else false)))) else (if n < 87 then (if n < 84 then (if n < 82 then false else (if n < 83 then
  false else false)) else (if n < 85 then false else (if n < 86 then false else false))) else (if
  n < 90 then (if n < 88 then false else (if n < 89 then false else false)) else (if n < 91 then
  false else (if n < 92 then false else true))))))) else (if n < 139 then (if n < 116 then (if n <
  104 then (if n < 98 then (if n < 95 then (if n < 94 then false else false) else (if n < 96 then
  false else (if n < 97 then false else false))) else (if n < 101 then (if n < 99 then false else
  (if n < 100 then false else false)) else (if n < 102 then false else (if n < 103 then false else
  false)))) else (if n < 110 then (if n < 107 then (if n < 105 then false else (if n < 106 then
  false else false)) else (if n < 108 then false else (if n < 109 then false else false))) else
  (if n < 113 then (if n < 111 then false else (if n < 112 then false else false)) else (if n <
  114 then false else (if n < 115 then false else false))))) else (if n < 127 then (if n < 121
  then (if n < 118 then (if n < 117 then false else false) else (if n < 119 then false else (if n
  < 120 then false else false))) else (if n < 124 then (if n < 122 then false else (if n < 123
  then false else false)) else (if n < 125 then false else (if n < 126 then false else false))))
  else (if n < 133 then (if n < 130 then (if n < 128 then false else (if n < 129 then false else
  false)) else (if n < 131 then false else (if n < 132 then false else false))) else (if n < 136
  then (if n < 134 then false else (if n < 135 then false else false)) else (if n < 137 then false
  else (if n < 138 then false else false)))))) else (if n < 162 then (if n < 150 then (if n < 144
  then (if n < 141 then (if n < 140 then false else false) else (if n < 142 then false else (if n
  < 143 then false else false))) else (if n < 147 then (if n < 145 then false else (if n < 146
  then false else false)) else (if n < 148 then false else (if n < 149 then false else false))))
  else (if n < 156 then (if n < 153 then (if n < 151 then false else (if n < 152 then false else
  false)) else (if n < 154 then false else (if n < 155 then false else false))) else (if n < 159
  then (if n < 157 then false else (if n < 158 then false else false)) else (if n < 160 then false
  else (if n < 161 then false else false))))) else (if n < 174 then (if n < 168 then (if n < 165
  then (if n < 163 then false else (if n < 164 then false else false)) else (if n < 166 then false
  else (if n < 167 then false else false))) else (if n < 171 then (if n < 169 then false else (if
  n < 170 then false else false)) else (if n < 172 then false else (if n < 173 then false else
  false)))) else (if n < 180 then (if n < 177 then (if n < 175 then false else (if n < 176 then
  false else false)) else (if n < 178 then false else (if n < 179 then false else false))) else
  (if n < 183 then (if n < 181 then false else (if n < 182 then false else false)) else (if n <
  184 then false else (if n < 185 then false else false)))))))) else (if n < 279 then (if n < 232
  then (if n < 209 then (if n < 197 then (if n < 191 then (if n < 188 then (if n < 187 then false
  else false) else (if n < 189 then false else (if n < 190 then false else false))) else (if n <
  194 then (if n < 192 then false else (if n < 193 then false else false)) else (if n < 195 then
  false else (if n < 196 then false else false)))) else (if n < 203 then (if n < 200 then (if n <
  198 then false else (if n < 199 then false else false)) else (if n < 201 then false else (if n <
  202 then false else false))) else (if n < 206 then (if n < 204 then false else (if n < 205 then
  false else false)) else (if n < 207 then false else (if n < 208 then false else true))))) else
  (if n < 220 then (if n < 214 then (if n < 211 then (if n < 210 then true else false) else (if n
  < 212 then false else (if n < 213 then false else false))) else (if n < 217 then (if n < 215
  then false else (if n < 216 then false else true)) else (if n < 218 then true else (if n < 219
  then false else false)))) else (if n < 226 then (if n < 223 then (if n < 221 then false else (if
  n < 222 then false else false)) else (if n < 224 then false else (if n < 225 then true else
  false))) else (if n < 229 then (if n < 227 then false else (if n < 228 then false else true))
  else (if n < 230 then false else (if n < 231 then false else false)))))) else (if n < 255 then
  (if n < 243 then (if n < 237 then (if n < 234 then (if n < 233 then false else false) else (if n
  < 235 then false else (if n < 236 then false else false))) else (if n < 240 then (if n < 238
  then false else (if n < 239 then false else false)) else (if n < 241 then false else (if n < 242
  then false else false)))) else (if n < 249 then (if n < 246 then (if n < 244 then false else (if
  n < 245 then true else true)) else (if n < 247 then false else (if n < 248 then false else
  false))) else (if n < 252 then (if n < 250 then false else (if n < 251 then false else false))
  else (if n < 253 then false else (if n < 254 then false else true))))) else (if n < 267 then (if
  n < 261 then (if n < 258 then (if n < 256 then true else (if n < 257 then false else false))
  else (if n < 259 then true else (if n < 260 then false else false))) else (if n < 264 then (if n
  < 262 then false else (if n < 263 then false else true)) else (if n < 265 then false else (if n
  < 266 then false else false)))) else (if n < 273 then (if n < 270 then (if n < 268 then false
  else (if n < 269 then false else false)) else (if n < 271 then false else (if n < 272 then false
  else false))) else (if n < 276 then (if n < 274 then false else (if n < 275 then false else
  false)) else (if n < 277 then false else (if n < 278 then false else false))))))) else (if n <
  325 then (if n < 302 then (if n < 290 then (if n < 284 then (if n < 281 then (if n < 280 then
  false else false) else (if n < 282 then false else (if n < 283 then false else false))) else (if
  n < 287 then (if n < 285 then false else (if n < 286 then false else false)) else (if n < 288
  then false else (if n < 289 then false else false)))) else (if n < 296 then (if n < 293 then (if
  n < 291 then false else (if n < 292 then false else false)) else (if n < 294 then false else (if
  n < 295 then false else false))) else (if n < 299 then (if n < 297 then false else (if n < 298
  then false else false)) else (if n < 300 then false else (if n < 301 then false else false)))))
  else (if n < 313 then (if n < 307 then (if n < 304 then (if n < 303 then false else false) else
  (if n < 305 then false else (if n < 306 then false else false))) else (if n < 310 then (if n <
  308 then false else (if n < 309 then true else true)) else (if n < 311 then false else (if n <
  312 then false else true)))) else (if n < 319 then (if n < 316 then (if n < 314 then false else
  (if n < 315 then false else false)) else (if n < 317 then false else (if n < 318 then false else
  false))) else (if n < 322 then (if n < 320 then false else (if n < 321 then false else true))
  else (if n < 323 then false else (if n < 324 then false else false)))))) else (if n < 348 then
  (if n < 336 then (if n < 330 then (if n < 327 then (if n < 326 then false else false) else (if n
  < 328 then false else (if n < 329 then false else false))) else (if n < 333 then (if n < 331
  then false else (if n < 332 then false else false)) else (if n < 334 then false else (if n < 335
  then false else false)))) else (if n < 342 then (if n < 339 then (if n < 337 then false else (if
  n < 338 then true else false)) else (if n < 340 then false else (if n < 341 then false else
  false))) else (if n < 345 then (if n < 343 then false else (if n < 344 then false else false))
  else (if n < 346 then false else (if n < 347 then false else false))))) else (if n < 360 then
  (if n < 354 then (if n < 351 then (if n < 349 then false else (if n < 350 then false else
  false)) else (if n < 352 then false else (if n < 353 then false else false))) else (if n < 357
  then (if n < 355 then false else (if n < 356 then false else false)) else (if n < 358 then false
  else (if n < 359 then false else false)))) else (if n < 366 then (if n < 363 then (if n < 361
  then false else (if n < 362 then true else false)) else (if n < 364 then false else (if n < 365
  then false else false))) else (if n < 369 then (if n < 367 then false else (if n < 368 then
  false else false)) else (if n < 370 then false else (if n < 371 then false else false)))))))))
  else (if n < 558 then (if n < 465 then (if n < 418 then (if n < 395 then (if n < 383 then (if n
  < 377 then (if n < 374 then (if n < 373 then false else false) else (if n < 375 then false else
  (if n < 376 then false else false))) else (if n < 380 then (if n < 378 then false else (if n <
  379 then false else false)) else (if n < 381 then false else (if n < 382 then false else
  false)))) else (if n < 389 then (if n < 386 then (if n < 384 then false else (if n < 385 then
  false else false)) else (if n < 387 then false else (if n < 388 then false else false))) else
  (if n < 392 then (if n < 390 then false else (if n < 391 then false else false)) else (if n <
  393 then false else (if n < 394 then false else false))))) else (if n < 406 then (if n < 400
  then (if n < 397 then (if n < 396 then false else false) else (if n < 398 then false else (if n
  < 399 then false else false))) else (if n < 403 then (if n < 401 then false else (if n < 402
  then false else false)) else (if n < 404 then false else (if n < 405 then false else false))))
  else (if n < 412 then (if n < 409 then (if n < 407 then true else (if n < 408 then true else
  false)) else (if n < 410 then false else (if n < 411 then false else true))) else (if n < 415
  then (if n < 413 then false else (if n < 414 then false else false)) else (if n < 416 then false
  else (if n < 417 then false else false)))))) else (if n < 441 then (if n < 429 then (if n < 423
  then (if n < 420 then (if n < 419 then false else false) else (if n < 421 then true else (if n <
  422 then false else false))) else (if n < 426 then (if n < 424 then false else (if n < 425 then
  false else false)) else (if n < 427 then false else (if n < 428 then false else false)))) else
  (if n < 435 then (if n < 432 then (if n < 430 then false else (if n < 431 then false else
  false)) else (if n < 433 then false else (if n < 434 then false else false))) else (if n < 438
  then (if n < 436 then false else (if n < 437 then false else false)) else (if n < 439 then false
  else (if n < 440 then false else false))))) else (if n < 453 then (if n < 447 then (if n < 444
  then (if n < 442 then false else (if n < 443 then false else false)) else (if n < 445 then false
  else (if n < 446 then false else false))) else (if n < 450 then (if n < 448 then false else (if
  n < 449 then false else false)) else (if n < 451 then false else (if n < 452 then false else
  false)))) else (if n < 459 then (if n < 456 then (if n < 454 then false else (if n < 455 then
  false else false)) else (if n < 457 then false else (if n < 458 then false else true))) else (if
  n < 462 then (if n < 460 then true else (if n < 461 then false else false)) else (if n < 463
  then false else (if n < 464 then true else false))))))) else (if n < 511 then (if n < 488 then
  (if n < 476 then (if n < 470 then (if n < 467 then (if n < 466 then false else false) else (if n
  < 468 then false else (if n < 469 then false else false))) else (if n < 473 then (if n < 471
  then false else (if n < 472 then false else false)) else (if n < 474 then false else (if n < 475
  then false else false)))) else (if n < 482 then (if n < 479 then (if n < 477 then false else (if
  n < 478 then false else false)) else (if n < 480 then false else (if n < 481 then false else
  false))) else (if n < 485 then (if n < 483 then false else (if n < 484 then false else false))
  else (if n < 486 then false else (if n < 487 then false else true))))) else (if n < 499 then (if
  n < 493 then (if n < 490 then (if n < 489 then false else false) else (if n < 491 then false
  else (if n < 492 then false else false))) else (if n < 496 then (if n < 494 then false else (if
  n < 495 then true else true)) else (if n < 497 then false else (if n < 498 then false else
  false)))) else (if n < 505 then (if n < 502 then (if n < 500 then true else (if n < 501 then
  false else false)) else (if n < 503 then false else (if n < 504 then true else false))) else (if
  n < 508 then (if n < 506 then false else (if n < 507 then false else false)) else (if n < 509
  then false else (if n < 510 then false else false)))))) else (if n < 534 then (if n < 522 then
  (if n < 516 then (if n < 513 then (if n < 512 then false else true) else (if n < 514 then true
  else (if n < 515 then false else false))) else (if n < 519 then (if n < 517 then false else (if
  n < 518 then false else false)) else (if n < 520 then false else (if n < 521 then false else
  false)))) else (if n < 528 then (if n < 525 then (if n < 523 then false else (if n < 524 then
  false else false)) else (if n < 526 then false else (if n < 527 then false else false))) else
  (if n < 531 then (if n < 529 then false else (if n < 530 then false else false)) else (if n <
  532 then false else (if n < 533 then false else false))))) else (if n < 546 then (if n < 540
  then (if n < 537 then (if n < 535 then false else (if n < 536 then false else false)) else (if n
  < 538 then false else (if n < 539 then false else false))) else (if n < 543 then (if n < 541
  then false else (if n < 542 then false else false)) else (if n < 544 then false else (if n < 545
  then false else false)))) else (if n < 552 then (if n < 549 then (if n < 547 then false else (if
  n < 548 then false else false)) else (if n < 550 then false else (if n < 551 then false else
  false))) else (if n < 555 then (if n < 553 then false else (if n < 554 then false else false))
  else (if n < 556 then false else (if n < 557 then false else false)))))))) else (if n < 651 then
  (if n < 604 then (if n < 581 then (if n < 569 then (if n < 563 then (if n < 560 then (if n < 559
  then false else false) else (if n < 561 then false else (if n < 562 then false else false)))
  else (if n < 566 then (if n < 564 then false else (if n < 565 then false else false)) else (if n
  < 567 then false else (if n < 568 then false else false)))) else (if n < 575 then (if n < 572
  then (if n < 570 then false else (if n < 571 then false else false)) else (if n < 573 then false
  else (if n < 574 then false else false))) else (if n < 578 then (if n < 576 then false else (if
  n < 577 then false else false)) else (if n < 579 then false else (if n < 580 then false else
  false))))) else (if n < 592 then (if n < 586 then (if n < 583 then (if n < 582 then false else
  false) else (if n < 584 then false else (if n < 585 then false else false))) else (if n < 589
  then (if n < 587 then false else (if n < 588 then false else false)) else (if n < 590 then false
  else (if n < 591 then false else false)))) else (if n < 598 then (if n < 595 then (if n < 593
  then false else (if n < 594 then false else false)) else (if n < 596 then false else (if n < 597
  then false else false))) else (if n < 601 then (if n < 599 then false else (if n < 600 then
  false else false)) else (if n < 602 then false else (if n < 603 then false else false)))))) else
  (if n < 627 then (if n < 615 then (if n < 609 then (if n < 606 then (if n < 605 then false else
  false) else (if n < 607 then false else (if n < 608 then false else false))) else (if n < 612
  then (if n < 610 then false else (if n < 611 then false else false)) else (if n < 613 then false
  else (if n < 614 then false else false)))) else (if n < 621 then (if n < 618 then (if n < 616
  then false else (if n < 617 then false else false)) else (if n < 619 then false else (if n < 620
  then false else false))) else (if n < 624 then (if n < 622 then false else (if n < 623 then
  false else false)) else (if n < 625 then false else (if n < 626 then false else false))))) else
  (if n < 639 then (if n < 633 then (if n < 630 then (if n < 628 then false else (if n < 629 then
  false else false)) else (if n < 631 then false else (if n < 632 then false else false))) else
  (if n < 636 then (if n < 634 then false else (if n < 635 then false else false)) else (if n <
  637 then false else (if n < 638 then false else true)))) else (if n < 645 then (if n < 642 then
  (if n < 640 then false else (if n < 641 then false else false)) else (if n < 643 then false else
  (if n < 644 then false else false))) else (if n < 648 then (if n < 646 then false else (if n <
  647 then false else false)) else (if n < 649 then false else (if n < 650 then false else
  true))))))) else (if n < 697 then (if n < 674 then (if n < 662 then (if n < 656 then (if n < 653
  then (if n < 652 then false else false) else (if n < 654 then false else (if n < 655 then false
  else false))) else (if n < 659 then (if n < 657 then false else (if n < 658 then false else
  false)) else (if n < 660 then false else (if n < 661 then false else false)))) else (if n < 668
  then (if n < 665 then (if n < 663 then false else (if n < 664 then false else false)) else (if n
  < 666 then false else (if n < 667 then false else false))) else (if n < 671 then (if n < 669
  then false else (if n < 670 then false else false)) else (if n < 672 then false else (if n < 673
  then false else false))))) else (if n < 685 then (if n < 679 then (if n < 676 then (if n < 675
  then false else false) else (if n < 677 then false else (if n < 678 then false else false)))
  else (if n < 682 then (if n < 680 then false else (if n < 681 then false else false)) else (if n
  < 683 then false else (if n < 684 then false else false)))) else (if n < 691 then (if n < 688
  then (if n < 686 then false else (if n < 687 then false else false)) else (if n < 689 then false
  else (if n < 690 then false else false))) else (if n < 694 then (if n < 692 then false else (if
  n < 693 then false else false)) else (if n < 695 then false else (if n < 696 then false else
  false)))))) else (if n < 720 then (if n < 708 then (if n < 702 then (if n < 699 then (if n < 698
  then false else false) else (if n < 700 then false else (if n < 701 then false else false)))
  else (if n < 705 then (if n < 703 then false else (if n < 704 then false else false)) else (if n
  < 706 then false else (if n < 707 then false else false)))) else (if n < 714 then (if n < 711
  then (if n < 709 then false else (if n < 710 then false else false)) else (if n < 712 then false
  else (if n < 713 then false else false))) else (if n < 717 then (if n < 715 then false else (if
  n < 716 then false else false)) else (if n < 718 then false else (if n < 719 then false else
  false))))) else (if n < 732 then (if n < 726 then (if n < 723 then (if n < 721 then false else
  (if n < 722 then false else false)) else (if n < 724 then false else (if n < 725 then false else
  false))) else (if n < 729 then (if n < 727 then false else (if n < 728 then false else false))
  else (if n < 730 then false else (if n < 731 then false else false)))) else (if n < 738 then (if
  n < 735 then (if n < 733 then false else (if n < 734 then false else false)) else (if n < 736
  then false else (if n < 737 then false else false))) else (if n < 741 then (if n < 739 then
  false else (if n < 740 then false else false)) else (if n < 742 then false else (if n < 743 then
  false else false))))))))))
def isBounce1 (n : Nat) : Bool :=
  (if n < 372 then (if n < 186 then (if n < 93 then (if n < 46 then (if n < 23 then (if n < 11
  then (if n < 5 then (if n < 2 then (if n < 1 then false else false) else (if n < 3 then false
  else (if n < 4 then false else false))) else (if n < 8 then (if n < 6 then false else (if n < 7
  then false else false)) else (if n < 9 then false else (if n < 10 then false else false)))) else
  (if n < 17 then (if n < 14 then (if n < 12 then false else (if n < 13 then true else true)) else
  (if n < 15 then false else (if n < 16 then false else false))) else (if n < 20 then (if n < 18
  then false else (if n < 19 then false else false)) else (if n < 21 then false else (if n < 22
  then false else false))))) else (if n < 34 then (if n < 28 then (if n < 25 then (if n < 24 then
  false else false) else (if n < 26 then false else (if n < 27 then false else false))) else (if n
  < 31 then (if n < 29 then false else (if n < 30 then false else false)) else (if n < 32 then
  false else (if n < 33 then false else false)))) else (if n < 40 then (if n < 37 then (if n < 35
  then false else (if n < 36 then false else false)) else (if n < 38 then false else (if n < 39
  then false else false))) else (if n < 43 then (if n < 41 then false else (if n < 42 then false
  else false)) else (if n < 44 then false else (if n < 45 then false else false)))))) else (if n <
  69 then (if n < 57 then (if n < 51 then (if n < 48 then (if n < 47 then false else false) else
  (if n < 49 then false else (if n < 50 then false else false))) else (if n < 54 then (if n < 52
  then false else (if n < 53 then false else false)) else (if n < 55 then false else (if n < 56
  then false else false)))) else (if n < 63 then (if n < 60 then (if n < 58 then false else (if n
  < 59 then false else false)) else (if n < 61 then false else (if n < 62 then false else false)))
  else (if n < 66 then (if n < 64 then false else (if n < 65 then false else false)) else (if n <
  67 then false else (if n < 68 then false else false))))) else (if n < 81 then (if n < 75 then
  (if n < 72 then (if n < 70 then false else (if n < 71 then false else false)) else (if n < 73
  then false else (if n < 74 then false else false))) else (if n < 78 then (if n < 76 then false
  else (if n < 77 then false else false)) else (if n < 79 then false else (if n < 80 then false
  else false)))) else (if n < 87 then (if n < 84 then (if n < 82 then false else (if n < 83 then
  false else false)) else (if n < 85 then false else (if n < 86 then false else false))) else (if
  n < 90 then (if n < 88 then false else (if n < 89 then false else false)) else (if n < 91 then
  false else (if n < 92 then false else true))))))) else (if n < 139 then (if n < 116 then (if n <
  104 then (if n < 98 then (if n < 95 then (if n < 94 then false else false) else (if n < 96 then
  false else (if n < 97 then false else false))) else (if n < 101 then (if n < 99 then false else
  (if n < 100 then false else false)) else (if n < 102 then false else (if n < 103 then false else
  false)))) else (if n < 110 then (if n < 107 then (if n < 105 then false else (if n < 106 then
  false else false)) else (if n < 108 then false else (if n < 109 then false else false))) else
  (if n < 113 then (if n < 111 then false else (if n < 112 then false else false)) else (if n <
  114 then false else (if n < 115 then false else false))))) else (if n < 127 then (if n < 121
  then (if n < 118 then (if n < 117 then false else false) else (if n < 119 then false else (if n
  < 120 then false else false))) else (if n < 124 then (if n < 122 then false else (if n < 123
  then false else false)) else (if n < 125 then false else (if n < 126 then false else false))))
  else (if n < 133 then (if n < 130 then (if n < 128 then false else (if n < 129 then false else
  false)) else (if n < 131 then false else (if n < 132 then false else false))) else (if n < 136
  then (if n < 134 then false else (if n < 135 then false else false)) else (if n < 137 then false
  else (if n < 138 then false else false)))))) else (if n < 162 then (if n < 150 then (if n < 144
  then (if n < 141 then (if n < 140 then false else false) else (if n < 142 then false else (if n
  < 143 then false else false))) else (if n < 147 then (if n < 145 then false else (if n < 146
  then false else false)) else (if n < 148 then false else (if n < 149 then false else false))))
  else (if n < 156 then (if n < 153 then (if n < 151 then false else (if n < 152 then false else
  false)) else (if n < 154 then false else (if n < 155 then false else false))) else (if n < 159
  then (if n < 157 then false else (if n < 158 then false else false)) else (if n < 160 then false
  else (if n < 161 then false else false))))) else (if n < 174 then (if n < 168 then (if n < 165
  then (if n < 163 then false else (if n < 164 then false else false)) else (if n < 166 then false
  else (if n < 167 then false else false))) else (if n < 171 then (if n < 169 then false else (if
  n < 170 then false else false)) else (if n < 172 then false else (if n < 173 then false else
  false)))) else (if n < 180 then (if n < 177 then (if n < 175 then false else (if n < 176 then
  false else false)) else (if n < 178 then false else (if n < 179 then false else false))) else
  (if n < 183 then (if n < 181 then false else (if n < 182 then false else false)) else (if n <
  184 then false else (if n < 185 then false else false)))))))) else (if n < 279 then (if n < 232
  then (if n < 209 then (if n < 197 then (if n < 191 then (if n < 188 then (if n < 187 then false
  else false) else (if n < 189 then false else (if n < 190 then true else false))) else (if n <
  194 then (if n < 192 then false else (if n < 193 then false else false)) else (if n < 195 then
  true else (if n < 196 then false else true)))) else (if n < 203 then (if n < 200 then (if n <
  198 then false else (if n < 199 then false else false)) else (if n < 201 then true else (if n <
  202 then false else true))) else (if n < 206 then (if n < 204 then true else (if n < 205 then
  false else false)) else (if n < 207 then false else (if n < 208 then false else false))))) else
  (if n < 220 then (if n < 214 then (if n < 211 then (if n < 210 then true else false) else (if n
  < 212 then false else (if n < 213 then true else true))) else (if n < 217 then (if n < 215 then
  true else (if n < 216 then false else false)) else (if n < 218 then false else (if n < 219 then
  false else false)))) else (if n < 226 then (if n < 223 then (if n < 221 then false else (if n <
  222 then false else false)) else (if n < 224 then false else (if n < 225 then true else true)))
  else (if n < 229 then (if n < 227 then false else (if n < 228 then false else true)) else (if n
  < 230 then true else (if n < 231 then false else false)))))) else (if n < 255 then (if n < 243
  then (if n < 237 then (if n < 234 then (if n < 233 then true else false) else (if n < 235 then
  false else (if n < 236 then true else false))) else (if n < 240 then (if n < 238 then false else
  (if n < 239 then false else false)) else (if n < 241 then true else (if n < 242 then true else
  false)))) else (if n < 249 then (if n < 246 then (if n < 244 then false else (if n < 245 then
  false else true)) else (if n < 247 then false else (if n < 248 then false else false))) else (if
  n < 252 then (if n < 250 then true else (if n < 251 then true else true)) else (if n < 253 then
  false else (if n < 254 then false else false))))) else (if n < 267 then (if n < 261 then (if n <
  258 then (if n < 256 then false else (if n < 257 then false else false)) else (if n < 259 then
  true else (if n < 260 then true else false))) else (if n < 264 then (if n < 262 then false else
  (if n < 263 then false else true)) else (if n < 265 then true else (if n < 266 then false else
  true)))) else (if n < 273 then (if n < 270 then (if n < 268 then true else (if n < 269 then true
  else false)) else (if n < 271 then false else (if n < 272 then false else false))) else (if n <
  276 then (if n < 274 then false else (if n < 275 then true else false)) else (if n < 277 then
  false else (if n < 278 then false else false))))))) else (if n < 325 then (if n < 302 then (if n
  < 290 then (if n < 284 then (if n < 281 then (if n < 280 then false else false) else (if n < 282
  then false else (if n < 283 then false else false))) else (if n < 287 then (if n < 285 then
  false else (if n < 286 then false else false)) else (if n < 288 then false else (if n < 289 then
  false else false)))) else (if n < 296 then (if n < 293 then (if n < 291 then false else (if n <
  292 then true else true)) else (if n < 294 then false else (if n < 295 then true else true)))
  else (if n < 299 then (if n < 297 then false else (if n < 298 then false else false)) else (if n
  < 300 then true else (if n < 301 then false else true))))) else (if n < 313 then (if n < 307
  then (if n < 304 then (if n < 303 then true else false) else (if n < 305 then false else (if n <
  306 then false else false))) else (if n < 310 then (if n < 308 then false else (if n < 309 then
  false else true)) else (if n < 311 then false else (if n < 312 then false else true)))) else (if
  n < 319 then (if n < 316 then (if n < 314 then true else (if n < 315 then false else false))
  else (if n < 317 then true else (if n < 318 then true else false))) else (if n < 322 then (if n
  < 320 then false else (if n < 321 then false else true)) else (if n < 323 then true else (if n <
  324 then false else false)))))) else (if n < 348 then (if n < 336 then (if n < 330 then (if n <
  327 then (if n < 326 then false else false) else (if n < 328 then false else (if n < 329 then
  false else false))) else (if n < 333 then (if n < 331 then true else (if n < 332 then false else
  true)) else (if n < 334 then true else (if n < 335 then false else false)))) else (if n < 342
  then (if n < 339 then (if n < 337 then false else (if n < 338 then true else true)) else (if n <
  340 then false else (if n < 341 then false else false))) else (if n < 345 then (if n < 343 then
  true else (if n < 344 then true else true)) else (if n < 346 then false else (if n < 347 then
  false else false))))) else (if n < 360 then (if n < 354 then (if n < 351 then (if n < 349 then
  true else (if n < 350 then false else true)) else (if n < 352 then true else (if n < 353 then
  false else false))) else (if n < 357 then (if n < 355 then false else (if n < 356 then false
  else true)) else (if n < 358 then true else (if n < 359 then false else false)))) else (if n <
  366 then (if n < 363 then (if n < 361 then false else (if n < 362 then true else true)) else (if
  n < 364 then false else (if n < 365 then true else false))) else (if n < 369 then (if n < 367
  then false else (if n < 368 then false else false)) else (if n < 370 then false else (if n < 371
  then false else false))))))))) else (if n < 558 then (if n < 465 then (if n < 418 then (if n <
  395 then (if n < 383 then (if n < 377 then (if n < 374 then (if n < 373 then true else true)
  else (if n < 375 then false else (if n < 376 then false else true))) else (if n < 380 then (if n
  < 378 then false else (if n < 379 then false else false)) else (if n < 381 then false else (if n
  < 382 then false else false)))) else (if n < 389 then (if n < 386 then (if n < 384 then false
  else (if n < 385 then false else false)) else (if n < 387 then true else (if n < 388 then false
  else false))) else (if n < 392 then (if n < 390 then false else (if n < 391 then false else
  true)) else (if n < 393 then true else (if n < 394 then false else false))))) else (if n < 406
  then (if n < 400 then (if n < 397 then (if n < 396 then false else true) else (if n < 398 then
  false else (if n < 399 then true else false))) else (if n < 403 then (if n < 401 then false else
  (if n < 402 then false else false)) else (if n < 404 then true else (if n < 405 then false else
  false)))) else (if n < 412 then (if n < 409 then (if n < 407 then false else (if n < 408 then
  true else false)) else (if n < 410 then false else (if n < 411 then false else true))) else (if
  n < 415 then (if n < 413 then true else (if n < 414 then false else false)) else (if n < 416
  then false else (if n < 417 then true else true)))))) else (if n < 441 then (if n < 429 then (if
  n < 423 then (if n < 420 then (if n < 419 then false else false) else (if n < 421 then true else
  (if n < 422 then true else false))) else (if n < 426 then (if n < 424 then false else (if n <
  425 then false else false)) else (if n < 427 then false else (if n < 428 then true else
  false)))) else (if n < 435 then (if n < 432 then (if n < 430 then true else (if n < 431 then
  true else false)) else (if n < 433 then false else (if n < 434 then false else false))) else (if
  n < 438 then (if n < 436 then false else (if n < 437 then false else true)) else (if n < 439
  then true else (if n < 440 then true else false))))) else (if n < 453 then (if n < 447 then (if
  n < 444 then (if n < 442 then false else (if n < 443 then false else false)) else (if n < 445
  then false else (if n < 446 then true else true))) else (if n < 450 then (if n < 448 then false
  else (if n < 449 then false else false)) else (if n < 451 then false else (if n < 452 then false
  else false)))) else (if n < 459 then (if n < 456 then (if n < 454 then false else (if n < 455
  then false else false)) else (if n < 457 then false else (if n < 458 then false else false)))
  else (if n < 462 then (if n < 460 then true else (if n < 461 then false else false)) else (if n
  < 463 then false else (if n < 464 then true else true))))))) else (if n < 511 then (if n < 488
  then (if n < 476 then (if n < 470 then (if n < 467 then (if n < 466 then false else false) else
  (if n < 468 then false else (if n < 469 then true else true))) else (if n < 473 then (if n < 471
  then false else (if n < 472 then false else false)) else (if n < 474 then false else (if n < 475
  then false else false)))) else (if n < 482 then (if n < 479 then (if n < 477 then false else (if
  n < 478 then false else false)) else (if n < 480 then false else (if n < 481 then false else
  false))) else (if n < 485 then (if n < 483 then false else (if n < 484 then false else false))
  else (if n < 486 then false else (if n < 487 then false else true))))) else (if n < 499 then (if
  n < 493 then (if n < 490 then (if n < 489 then true else false) else (if n < 491 then false else
  (if n < 492 then false else false))) else (if n < 496 then (if n < 494 then false else (if n <
  495 then false else false)) else (if n < 497 then false else (if n < 498 then false else
  false)))) else (if n < 505 then (if n < 502 then (if n < 500 then true else (if n < 501 then
  true else false)) else (if n < 503 then false else (if n < 504 then true else true))) else (if n
  < 508 then (if n < 506 then false else (if n < 507 then false else false)) else (if n < 509 then
  false else (if n < 510 then false else false)))))) else (if n < 534 then (if n < 522 then (if n
  < 516 then (if n < 513 then (if n < 512 then false else true) else (if n < 514 then false else
  (if n < 515 then false else true))) else (if n < 519 then (if n < 517 then true else (if n < 518
  then true else true)) else (if n < 520 then true else (if n < 521 then true else true)))) else
  (if n < 528 then (if n < 525 then (if n < 523 then false else (if n < 524 then false else
  false)) else (if n < 526 then false else (if n < 527 then false else false))) else (if n < 531
  then (if n < 529 then false else (if n < 530 then false else false)) else (if n < 532 then false
  else (if n < 533 then false else false))))) else (if n < 546 then (if n < 540 then (if n < 537
  then (if n < 535 then false else (if n < 536 then false else false)) else (if n < 538 then false
  else (if n < 539 then false else false))) else (if n < 543 then (if n < 541 then false else (if
  n < 542 then false else false)) else (if n < 544 then false else (if n < 545 then false else
  false)))) else (if n < 552 then (if n < 549 then (if n < 547 then false else (if n < 548 then
  false else false)) else (if n < 550 then false else (if n < 551 then false else false))) else
  (if n < 555 then (if n < 553 then false else (if n < 554 then false else false)) else (if n <
  556 then false else (if n < 557 then false else false)))))))) else (if n < 651 then (if n < 604
  then (if n < 581 then (if n < 569 then (if n < 563 then (if n < 560 then (if n < 559 then false
  else false) else (if n < 561 then false else (if n < 562 then false else false))) else (if n <
  566 then (if n < 564 then false else (if n < 565 then false else false)) else (if n < 567 then
  false else (if n < 568 then false else false)))) else (if n < 575 then (if n < 572 then (if n <
  570 then true else (if n < 571 then false else false)) else (if n < 573 then false else (if n <
  574 then true else false))) else (if n < 578 then (if n < 576 then false else (if n < 577 then
  false else true)) else (if n < 579 then false else (if n < 580 then true else false))))) else
  (if n < 592 then (if n < 586 then (if n < 583 then (if n < 582 then false else true) else (if n
  < 584 then false else (if n < 585 then false else false))) else (if n < 589 then (if n < 587
  then true else (if n < 588 then false else false)) else (if n < 590 then false else (if n < 591
  then false else false)))) else (if n < 598 then (if n < 595 then (if n < 593 then false else (if
  n < 594 then false else true)) else (if n < 596 then false else (if n < 597 then false else
  false))) else (if n < 601 then (if n < 599 then false else (if n < 600 then false else true))
  else (if n < 602 then false else (if n < 603 then false else false)))))) else (if n < 627 then
  (if n < 615 then (if n < 609 then (if n < 606 then (if n < 605 then true else false) else (if n
  < 607 then false else (if n < 608 then false else true))) else (if n < 612 then (if n < 610 then
  false else (if n < 611 then false else false)) else (if n < 613 then false else (if n < 614 then
  false else false)))) else (if n < 621 then (if n < 618 then (if n < 616 then true else (if n <
  617 then false else true)) else (if n < 619 then false else (if n < 620 then false else false)))
  else (if n < 624 then (if n < 622 then false else (if n < 623 then false else false)) else (if n
  < 625 then true else (if n < 626 then false else false))))) else (if n < 639 then (if n < 633
  then (if n < 630 then (if n < 628 then false else (if n < 629 then false else true)) else (if n
  < 631 then false else (if n < 632 then false else false))) else (if n < 636 then (if n < 634
  then false else (if n < 635 then false else false)) else (if n < 637 then false else (if n < 638
  then true else true)))) else (if n < 645 then (if n < 642 then (if n < 640 then false else (if n
  < 641 then false else false)) else (if n < 643 then false else (if n < 644 then false else
  false))) else (if n < 648 then (if n < 646 then false else (if n < 647 then false else true))
  else (if n < 649 then false else (if n < 650 then false else true))))))) else (if n < 697 then
  (if n < 674 then (if n < 662 then (if n < 656 then (if n < 653 then (if n < 652 then true else
  false) else (if n < 654 then false else (if n < 655 then false else false))) else (if n < 659
  then (if n < 657 then false else (if n < 658 then false else false)) else (if n < 660 then false
  else (if n < 661 then false else false)))) else (if n < 668 then (if n < 665 then (if n < 663
  then false else (if n < 664 then false else true)) else (if n < 666 then false else (if n < 667
  then true else false))) else (if n < 671 then (if n < 669 then false else (if n < 670 then false
  else false)) else (if n < 672 then false else (if n < 673 then false else false))))) else (if n
  < 685 then (if n < 679 then (if n < 676 then (if n < 675 then false else false) else (if n < 677
  then false else (if n < 678 then false else false))) else (if n < 682 then (if n < 680 then
  false else (if n < 681 then true else false)) else (if n < 683 then false else (if n < 684 then
  true else false)))) else (if n < 691 then (if n < 688 then (if n < 686 then false else (if n <
  687 then true else false)) else (if n < 689 then false else (if n < 690 then true else false)))
  else (if n < 694 then (if n < 692 then false else (if n < 693 then true else true)) else (if n <
  695 then false else (if n < 696 then false else false)))))) else (if n < 720 then (if n < 708
  then (if n < 702 then (if n < 699 then (if n < 698 then true else false) else (if n < 700 then
  true else (if n < 701 then false else true))) else (if n < 705 then (if n < 703 then false else
  (if n < 704 then true else false)) else (if n < 706 then true else (if n < 707 then false else
  false)))) else (if n < 714 then (if n < 711 then (if n < 709 then true else (if n < 710 then
  false else false)) else (if n < 712 then false else (if n < 713 then true else true))) else (if
  n < 717 then (if n < 715 then false else (if n < 716 then false else false)) else (if n < 718
  then true else (if n < 719 then false else false))))) else (if n < 732 then (if n < 726 then (if
  n < 723 then (if n < 721 then false else (if n < 722 then false else false)) else (if n < 724
  then true else (if n < 725 then false else true))) else (if n < 729 then (if n < 727 then false
  else (if n < 728 then true else false)) else (if n < 730 then false else (if n < 731 then false
  else true)))) else (if n < 738 then (if n < 735 then (if n < 733 then false else (if n < 734
  then true else false)) else (if n < 736 then false else (if n < 737 then true else false))) else
  (if n < 741 then (if n < 739 then false else (if n < 740 then false else true)) else (if n < 742
  then false else (if n < 743 then true else false))))))))))
def isBounce (q : Fin 744) (b : Fin 2) : Bool :=
  if b == 0 then isBounce0 q.val else isBounce1 q.val

def oppDir : Dir → Dir
  | .left => .right
  | .right => .left

def allowBit (v0 v1 : Nat) (k : Nat) (b : Fin 2) : Bool :=
  if b.val == 0 then v0.testBit k else v1.testBit k

def stepCellCheck (v0 v1 w0 w1 : Nat) (a : Fin 2) (d : Dir) (k : Fin 25) (b : Fin 2) : Bool :=
  let srcOk : Bool :=
    match d with
    | .left =>
      if k.val == 0 then true
      else if k.val == 12 then b == a
      else allowBit v0 v1 (k.val - 1) b
    | .right =>
      if k.val == 24 then true
      else if k.val == 10 then b == a
      else allowBit v0 v1 (k.val + 1) b
  !srcOk || allowBit w0 w1 k.val b

def checkAllCells (v0 v1 w0 w1 : Nat) (a : Fin 2) (d : Dir) : Bool :=
  (List.finRange 25).all fun k =>
    stepCellCheck v0 v1 w0 w1 a d k 0 && stepCellCheck v0 v1 w0 w1 a d k 1

def checkListIdx {α : Type} (P : Nat → α → Bool) (L : List α) (start : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun _ => true)
    (fun x _ ih i => P i x && ih (i + 1))
    L start

theorem checkListIdx_getD {α : Type} (P : Nat → α → Bool) (d : α) (L : List α) :
    ∀ (i k : Nat),
      k < L.length →
      checkListIdx P L i = true →
      P (i + k) (L.getD k d) = true := by
  induction L with
  | nil => intro i k hk _; cases hk
  | cons x xs ih =>
    intro i k hk h
    unfold checkListIdx at h
    dsimp only at h
    rw [Bool.and_eq_true] at h
    cases k with
    | zero => simpa [List.getD, Nat.add_zero] using h.1
    | succ k =>
      have hk' : k < xs.length := Nat.lt_of_succ_lt_succ hk
      have hrec := ih (i + 1) k hk' h.2
      have heq : i + 1 + k = i + (k + 1) := by omega
      rw [heq] at hrec
      simpa [List.getD] using hrec

def isSpecialNat (n : Nat) (b : Fin 2) : Bool :=
  (n == 503 && b.val == 0) || (n == 63 && b.val == 0) || (n == 203 && b.val == 1) ||
  (n == 208 && b.val == 0) || (n == 209 && b.val == 0) || (n == 212 && b.val == 1) ||
  (n == 216 && b.val == 0) || (n == 217 && b.val == 0) || (n == 224 && b.val == 1) ||
  (n == 225 && b.val == 1) || (n == 241 && b.val == 1) || (n == 244 && b.val == 0) ||
  (n == 245 && b.val == 0) || (n == 249 && b.val == 1) || (n == 251 && b.val == 0) ||
  (n == 254 && b.val == 0) || (n == 255 && b.val == 0) || (n == 258 && b.val == 1) ||
  (n == 266 && b.val == 1) || (n == 291 && b.val == 1) || (n == 294 && b.val == 1) ||
  (n == 302 && b.val == 1) || (n == 308 && b.val == 0) || (n == 309 && b.val == 0) ||
  (n == 316 && b.val == 1) || (n == 321 && b.val == 0) || (n == 332 && b.val == 1) ||
  (n == 337 && b.val == 0) || (n == 342 && b.val == 1) || (n == 350 && b.val == 1) ||
  (n == 361 && b.val == 0) || (n == 372 && b.val == 1) || (n == 376 && b.val == 0) ||
  (n == 386 && b.val == 0) || (n == 391 && b.val == 1) || (n == 403 && b.val == 1) ||
  (n == 406 && b.val == 0) || (n == 407 && b.val == 0) || (n == 416 && b.val == 1) ||
  (n == 420 && b.val == 0) || (n == 429 && b.val == 1) || (n == 445 && b.val == 1) ||
  (n == 458 && b.val == 0) || (n == 459 && b.val == 0) || (n == 463 && b.val == 0) ||
  (n == 468 && b.val == 1) || (n == 472 && b.val == 1) || (n == 487 && b.val == 0) ||
  (n == 494 && b.val == 0) || (n == 499 && b.val == 1) || (n == 712 && b.val == 1) ||
  (n == 713 && b.val == 1)

def checkEntryNat (n : Nat) (b : Fin 2) : Bool :=
  isSpecialNat n b || !allowBit (m0Nat n) (m1Nat n) 11 b ||
  match (if b == 0 then isBounce0 n else isBounce1 n) with
  | false =>
    match (if b == 0 then refTrans0 n else refTrans1 n) with
    | none => (if b == 0 then candTrans0 (fNat n).val else candTrans1 (fNat n).val).isNone
    | some (w, d, q') =>
      ((if b == 0 then candTrans0 (fNat n).val else candTrans1 (fNat n).val) == some (w, d, f q'))
        &&
      checkAllCells (m0Nat n) (m1Nat n) (m0 q') (m1 q') w d
  | true =>
    match (if b == 0 then refTrans0 n else refTrans1 n) with
    | none => false
    | some (w, d, p) =>
      match refTrans0 p.val, refTrans1 p.val with
      | some (w0, dp0, j1), some (w1, dp1, j1') =>
        (w0 == 0) && (w1 == 1) && (dp0 == (oppDir d)) && (dp1 == (oppDir d)) && (j1 == j1') &&
        match (refTrans j1 w) with
        | none => false
        | some (w2, d2, q2) =>
          ((if b == 0 then candTrans0 (fNat n).val else candTrans1 (fNat n).val) == some (w2, d2,
            f q2)) &&
          checkAllCells (m0Nat n) (m1Nat n) (m0 q2) (m1 q2) w2 d2
      | _, _ => false

def checkRefRow (i : Nat) (row : List (Option (Fin 2 × Dir × Fin 744))) : Bool :=
  (row.getD 0 none == refTrans0 i) &&
  (row.getD 1 none == refTrans1 i) &&
  checkEntryNat i 0 &&
  checkEntryNat i 1

def checkCandRow (i : Nat) (row : List (Option (Fin 2 × Dir × Fin 543))) : Bool :=
  (row.getD 0 none == candTrans0 i) &&
  (row.getD 1 none == candTrans1 i)

set_option maxHeartbeats 4000000 in
-- Exhaustive check over all 744 rows of the reference machine.
set_option maxRecDepth 200000 in
theorem refRows_valid : checkListIdx checkRefRow refRows 0 = true := by decide

set_option maxHeartbeats 4000000 in
-- Exhaustive check over all 543 rows of the candidate machine.
set_option maxRecDepth 200000 in
theorem candRows_valid : checkListIdx checkCandRow candRows 0 = true := by decide
set_option maxRecDepth 200000 in
theorem refRows_len : refRows.length = 744 := rfl
set_option maxRecDepth 200000 in
theorem candRows_len : candRows.length = 543 := rfl

theorem refTrans_eq (q : Fin 744) (b : Fin 2) : reference.transition q b = refTrans q b := by
  have h :=
    checkListIdx_getD checkRefRow [] refRows 0 q.val (by rw [refRows_len]; exact q.isLt)
      refRows_valid
  rw [Nat.zero_add] at h
  unfold checkRefRow at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have htr : reference.transition q b = (refRows.getD q.val []).getD b.val none := by
    rw [reference_eq]; rfl
  rw [htr]
  unfold refTrans
  rcases b with ⟨_ | _ | _, hlt⟩
  · exact h.1.1.1
  · exact h.1.1.2
  · omega

theorem candTrans_eq (q : Fin 543) (b : Fin 2) : candidate.transition q b = candTrans q b := by
  have h :=
    checkListIdx_getD checkCandRow [] candRows 0 q.val (by rw [candRows_len]; exact q.isLt)
      candRows_valid
  rw [Nat.zero_add] at h
  unfold checkCandRow at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have htr : candidate.transition q b = (candRows.getD q.val []).getD b.val none := by
    rw [candidate_eq]; rfl
  rw [htr]
  unfold candTrans
  rcases b with ⟨_ | _ | _, hlt⟩
  · exact h.1
  · exact h.2
  · omega

def checkEntry (q : Fin 744) (b : Fin 2) : Bool :=
  isSpecialNat q.val b || !allowBit (m0 q) (m1 q) 11 b ||
  match isBounce q b with
  | false =>
    match refTrans q b with
    | none => (candTrans (f q) b).isNone
    | some (w, d, q') =>
      (candTrans (f q) b == some (w, d, f q')) &&
      checkAllCells (m0 q) (m1 q) (m0 q') (m1 q') w d
  | true =>
    match refTrans q b with
    | none => false
    | some (w, d, p) =>
      match refTrans0 p.val, refTrans1 p.val with
      | some (w0, dp0, j1), some (w1, dp1, j1') =>
        (w0 == 0) && (w1 == 1) && (dp0 == (oppDir d)) && (dp1 == (oppDir d)) && (j1 == j1') &&
        match (refTrans j1 w) with
        | none => false
        | some (w2, d2, q2) =>
          (candTrans (f q) b == some (w2, d2, f q2)) &&
          checkAllCells (m0 q) (m1 q) (m0 q2) (m1 q2) w2 d2
      | _, _ => false

theorem table_valid (q : Fin 744) (b : Fin 2) : checkEntry q b = true := by
  have h :=
    checkListIdx_getD checkRefRow [] refRows 0 q.val (by rw [refRows_len]; exact q.isLt)
      refRows_valid
  rw [Nat.zero_add] at h
  unfold checkRefRow at h
  simp only [Bool.and_eq_true] at h
  unfold checkEntry m0 m1 f isBounce refTrans candTrans
  rcases b with ⟨_ | _ | _, hlt⟩
  · exact h.1.2
  · exact h.2
  · omega

def tapeAt (T : Tape (Fin 2)) (k : Fin 25) : Fin 2 :=
  T.nth ((k.val : ℤ) - 11)

def Inv (q : Fin 744) (T : Tape (Fin 2)) : Prop :=
  ∀ k : Fin 25, allowBit (m0 q) (m1 q) k.val (tapeAt T k) = true

theorem nth_init (i : ℤ) : (Tape.mk₁ ([] : List (Fin 2))).nth i = 0 := by
  rcases i with (_ | n) | n <;> rfl

theorem init_check (k : Fin 25) : allowBit (m0 371) (m1 371) k.val 0 = true := by
  revert k; decide

theorem inv_init : Inv 371 (Tape.mk₁ []) := by
  intro k
  rw [tapeAt, nth_init]
  exact init_check k

theorem inv_head {q : Fin 744} {T : Tape (Fin 2)} (h : Inv q T) :
    allowBit (m0 q) (m1 q) 11 T.head = true :=
  h ⟨11, by decide⟩

theorem offset_left_eq (k : Fin 25) (h0 : ¬(k.val == 0) = true) (h12 : ¬(k.val == 12) = true) :
    (k.val : ℤ) - 11 - 1 = (((k.val - 1 : ℕ) : ℤ) - 11) ∧ ((k.val : ℤ) - 11 - 1 ≠ 0) := by
  revert k h0 h12; decide

theorem offset_right_eq (k : Fin 25) (h24 : ¬(k.val == 24) = true) (h10 : ¬(k.val == 10) = true) :
    (k.val : ℤ) - 11 + 1 = (((k.val + 1 : ℕ) : ℤ) - 11) ∧ ((k.val : ℤ) - 11 + 1 ≠ 0) := by
  revert k h24 h10; decide

theorem k_pred_lt (k : Fin 25) : k.val - 1 < 25 := by
  revert k; decide

theorem k_succ_lt (k : Fin 25) (h24 : ¬(k.val == 24) = true) : k.val + 1 < 25 := by
  revert k h24; decide

theorem srcOk_holds {v0 v1 : Nat} {T : Tape (Fin 2)} (hInv : ∀ k : Fin 25, allowBit v0 v1 k.val
  (tapeAt T k) = true)
    (a : Fin 2) (d : Dir) (k : Fin 25) :
    (match d with
    | .left =>
      if k.val == 0 then true
      else if k.val == 12 then tapeAt ((T.write a).move d) k == a
      else allowBit v0 v1 (k.val - 1) (tapeAt ((T.write a).move d) k)
    | .right =>
      if k.val == 24 then true
      else if k.val == 10 then tapeAt ((T.write a).move d) k == a
      else allowBit v0 v1 (k.val + 1) (tapeAt ((T.write a).move d) k)) = true := by
  cases d with
  | left =>
    dsimp only
    by_cases h0 : (k.val == 0) = true
    · rw [ite_eq_left h0]
    · rw [ite_eq_right h0]
      by_cases h12 : (k.val == 12) = true
      · rw [ite_eq_left h12]
        have hk12 : (k.val : ℤ) - 11 - 1 = 0 := by revert k h12; decide
        rw [tapeAt, Tape.move_left_nth, hk12]
        exact beq_self_eq_true a
      · rw [ite_eq_right h12]
        obtain ⟨heq, hne⟩ := offset_left_eq k h0 h12
        have hnth : tapeAt ((T.write a).move .left) k = tapeAt T ⟨k.val - 1, k_pred_lt k⟩ := by
          rw [tapeAt, Tape.move_left_nth, Tape.write_nth, ite_eq_right hne, heq]
          rfl
        rw [hnth]
        exact hInv ⟨k.val - 1, k_pred_lt k⟩
  | right =>
    dsimp only
    by_cases h24 : (k.val == 24) = true
    · rw [ite_eq_left h24]
    · rw [ite_eq_right h24]
      by_cases h10 : (k.val == 10) = true
      · rw [ite_eq_left h10]
        have hk10 : (k.val : ℤ) - 11 + 1 = 0 := by revert k h10; decide
        rw [tapeAt, Tape.move_right_nth, hk10]
        exact beq_self_eq_true a
      · rw [ite_eq_right h10]
        obtain ⟨heq, hne⟩ := offset_right_eq k h24 h10
        have hnth : tapeAt ((T.write a).move .right) k = tapeAt T ⟨k.val + 1, k_succ_lt k h24⟩ := by
          rw [tapeAt, Tape.move_right_nth, Tape.write_nth, ite_eq_right hne, heq]
          rfl
        rw [hnth]
        exact hInv ⟨k.val + 1, k_succ_lt k h24⟩

theorem checkAllCells_sound {q q' : Fin 744} {T : Tape (Fin 2)} (hInv : Inv q T)
    (a : Fin 2) (d : Dir) (hall : checkAllCells (m0 q) (m1 q) (m0 q') (m1 q') a d = true) :
    Inv q' ((T.write a).move d) := by
  intro k
  unfold checkAllCells at hall
  rw [List.all_eq_true] at hall
  have hk := hall k (List.mem_finRange k)
  rw [Bool.and_eq_true] at hk
  have hcell : stepCellCheck (m0 q) (m1 q) (m0 q') (m1 q') a d k (tapeAt ((T.write a).move d) k) =
    true := by
    rcases tapeAt ((T.write a).move d) k with ⟨_ | _ | _, hlt⟩
    · exact hk.1
    · exact hk.2
    · omega
  dsimp only [stepCellCheck] at hcell
  have hsrc := srcOk_holds hInv a d k
  rw [hsrc, Bool.not_true, Bool.false_or] at hcell
  exact hcell

theorem move_opp (T : Tape (Fin 2)) (d : Dir) : (T.move d).move (oppDir d) = T := by
  cases d <;> simp [oppDir, Tape.move_left_right, Tape.move_right_left]

theorem ref_pass_step {p j1 : Fin 744} {d : Dir} (T : Tape (Fin 2))
    (hp0 : refTrans0 p.val = some (0, (oppDir d), j1))
    (hp1 : refTrans1 p.val = some (1, (oppDir d), j1)) :
    step reference ⟨p, T⟩ = some ⟨j1, T.move (oppDir d)⟩ := by
  have hp : reference.transition p T.head = some (T.head, (oppDir d), j1) := by
    rw [refTrans_eq]
    unfold refTrans
    rcases T.head with ⟨_ | _ | _, hlt⟩
    · exact hp0
    · exact hp1
    · omega
  simp [step, hp, Tape.write_self]

def WindowInv (v0 v1 : Nat) (T : Tape (Fin 2)) : Prop :=
  ∀ k : Fin 25, allowBit v0 v1 k.val (tapeAt T k) = true

theorem window_step_sound {v0 v1 w0 w1 : Nat} {T : Tape (Fin 2)} (hInv : WindowInv v0 v1 T)
    (a : Fin 2) (d : Dir) (hall : checkAllCells v0 v1 w0 w1 a d = true) :
    WindowInv w0 w1 ((T.write a).move d) := by
  intro k
  unfold checkAllCells at hall
  rw [List.all_eq_true] at hall
  have hk := hall k (List.mem_finRange k)
  rw [Bool.and_eq_true] at hk
  have hcell : stepCellCheck v0 v1 w0 w1 a d k (tapeAt ((T.write a).move d) k) = true := by
    rcases tapeAt ((T.write a).move d) k with ⟨_ | _ | _, hlt⟩
    · exact hk.1
    · exact hk.2
    · omega
  dsimp only [stepCellCheck] at hcell
  have hsrc := srcOk_holds hInv a d k
  rw [hsrc, Bool.not_true, Bool.false_or] at hcell
  exact hcell

def flipBit (b : Fin 2) : Fin 2 :=
  if b.val == 0 then 1 else 0

theorem force_bit_aux (b0 b1 : Bool) (b exp : Fin 2)
    (h_allow : (if b.val == 0 then b0 else b1) = true)
    (h_other : (if (flipBit exp).val == 0 then b0 else b1) = false) :
    b = exp := by
  revert b0 b1 b exp h_allow h_other; decide

theorem force_bit {v0 v1 : Nat} {b exp : Fin 2}
    (h_allow : allowBit v0 v1 11 b = true)
    (h_other : allowBit v0 v1 11 (flipBit exp) = false) :
    b = exp :=
  force_bit_aux (v0.testBit 11) (v1.testBit 11) b exp h_allow h_other

theorem halt_chain_end {v0 v1 : Nat}
    (h_head : allowBit v0 v1 11 0 = false)
    (h_tr : refTrans 513 1 = none) :
    ∀ T, WindowInv v0 v1 T → step reference ⟨513, T⟩ = none := by
  intro T hW
  have hb : T.head = 1 := force_bit (hW ⟨11, by decide⟩) h_head
  simp [step, refTrans_eq, hb, h_tr]

theorem halt_chain_last {q q' : Fin 744} {v0 v1 w0 w1 : Nat} {b a : Fin 2} {d : Dir}
    (h_head : allowBit v0 v1 11 (flipBit b) = false)
    (h_tr : refTrans q b = some (a, d, q'))
    (h_cells : checkAllCells v0 v1 w0 w1 a d = true)
    (h_end : ∀ T', WindowInv w0 w1 T' → step reference ⟨q', T'⟩ = none) :
    ∀ T, WindowInv v0 v1 T → ∃ ch, Reaches₁ (step reference) ⟨q, T⟩ ch ∧ step reference ch = none
      := by
  intro T hW
  have hb : T.head = b := force_bit (hW ⟨11, by decide⟩) h_head
  have hs : step reference ⟨q, T⟩ = some ⟨q', (T.write a).move d⟩ := by
    simp [step, refTrans_eq, hb, h_tr]
  have hW' := window_step_sound hW a d h_cells
  exact ⟨⟨q', (T.write a).move d⟩, Relation.TransGen.single hs, h_end _ hW'⟩

theorem halt_chain_step {q q' : Fin 744} {v0 v1 w0 w1 : Nat} {b a : Fin 2} {d : Dir}
    (h_head : allowBit v0 v1 11 (flipBit b) = false)
    (h_tr : refTrans q b = some (a, d, q'))
    (h_cells : checkAllCells v0 v1 w0 w1 a d = true)
    (h_next : ∀ T', WindowInv w0 w1 T' → ∃ ch, Reaches₁ (step reference) ⟨q', T'⟩ ch ∧ step
      reference ch = none) :
    ∀ T, WindowInv v0 v1 T → ∃ ch, Reaches₁ (step reference) ⟨q, T⟩ ch ∧ step reference ch = none
      := by
  intro T hW
  have hb : T.head = b := force_bit (hW ⟨11, by decide⟩) h_head
  have hs : step reference ⟨q, T⟩ = some ⟨q', (T.write a).move d⟩ := by
    simp [step, refTrans_eq, hb, h_tr]
  have hW' := window_step_sound hW a d h_cells
  obtain ⟨ch, hreach, hhalt⟩ := h_next _ hW'
  exact ⟨ch, Relation.TransGen.head hs hreach, hhalt⟩

theorem halt_chain_step_any {q q' : Fin 744} {v0 v1 w0 w1 : Nat} {d : Dir}
    (h_tr0 : refTrans q 0 = some (0, d, q'))
    (h_tr1 : refTrans q 1 = some (1, d, q'))
    (h_cells0 : checkAllCells v0 v1 w0 w1 0 d = true)
    (h_cells1 : checkAllCells v0 v1 w0 w1 1 d = true)
    (h_next : ∀ T', WindowInv w0 w1 T' → ∃ ch, Reaches₁ (step reference) ⟨q', T'⟩ ch ∧ step
      reference ch = none) :
    ∀ T, WindowInv v0 v1 T → ∃ ch, Reaches₁ (step reference) ⟨q, T⟩ ch ∧ step reference ch = none
      := by
  intro T hW
  rcases hb : T.head with ⟨_ | _ | _, _⟩
  · have hs : step reference ⟨q, T⟩ = some ⟨q', (T.write 0).move d⟩ := by
      simp [step, refTrans_eq, hb, h_tr0]
    have hW' := window_step_sound hW 0 d h_cells0
    obtain ⟨ch, hreach, hhalt⟩ := h_next _ hW'
    exact ⟨ch, Relation.TransGen.head hs hreach, hhalt⟩
  · have hs : step reference ⟨q, T⟩ = some ⟨q', (T.write 1).move d⟩ := by
      simp [step, refTrans_eq, hb, h_tr1]
    have hW' := window_step_sound hW 1 d h_cells1
    obtain ⟨ch, hreach, hhalt⟩ := h_next _ hW'
    exact ⟨ch, Relation.TransGen.head hs hreach, hhalt⟩
  · omega

theorem reaches_halt_177 (T : Tape (Fin 2)) (hW : WindowInv 33540119 33503215 T) :
    ∃ ch, Reaches₁ (step reference) ⟨177, T⟩ ch ∧ step reference ch = none := by
  have hc24 : ∀ T, WindowInv 33551353 33541127 T → step reference ⟨513, T⟩ = none :=
    halt_chain_end (by decide) (by decide)
  have hc23 : ∀ T, WindowInv 33548275 33527823 T → ∃ ch, Reaches₁ (step reference) ⟨514, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_last (b := 1) (a := 1) (d := .right) (by decide) (by decide) (by decide) hc24
  have hc22 : ∀ T, WindowInv 33542119 33501215 T → ∃ ch, Reaches₁ (step reference) ⟨515, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 0) (d := .right) (by decide) (by decide) (by decide) hc23
  have hc21 : ∀ T, WindowInv 33529807 33447999 T → ∃ ch, Reaches₁ (step reference) ⟨516, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 0) (d := .right) (by decide) (by decide) (by decide) hc22
  have hc20 : ∀ T, WindowInv 33505183 33341567 T → ∃ ch, Reaches₁ (step reference) ⟨517, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 0) (d := .right) (by decide) (by decide) (by decide) hc21
  have hc19 : ∀ T, WindowInv 33455935 33128703 T → ∃ ch, Reaches₁ (step reference) ⟨518, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 0) (d := .right) (by decide) (by decide) (by decide) hc20
  have hc18 : ∀ T, WindowInv 33357439 32702975 T → ∃ ch, Reaches₁ (step reference) ⟨519, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 0) (d := .right) (by decide) (by decide) (by decide) hc19
  have hc17 : ∀ T, WindowInv 33160447 31851519 T → ∃ ch, Reaches₁ (step reference) ⟨520, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 0) (d := .right) (by decide) (by decide) (by decide) hc18
  have hc16 : ∀ T, WindowInv 32766463 30148607 T → ∃ ch, Reaches₁ (step reference) ⟨521, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 0) (d := .right) (by decide) (by decide) (by decide) hc17
  have hc15 : ∀ T, WindowInv 31978495 26742783 T → ∃ ch, Reaches₁ (step reference) ⟨522, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 1) (d := .right) (by decide) (by decide) (by decide) hc16
  have hc14 : ∀ T, WindowInv 30402559 19931135 T → ∃ ch, Reaches₁ (step reference) ⟨523, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 1) (d := .right) (by decide) (by decide) (by decide) hc15
  have hc13 : ∀ T, WindowInv 27250687 6307839 T → ∃ ch, Reaches₁ (step reference) ⟨0, T⟩ ch ∧ step
    reference ch = none :=
    halt_chain_step_any (d := .right) (by decide) (by decide) (by decide) (by decide) hc14
  have hc12 : ∀ T, WindowInv 30402559 19931135 T → ∃ ch, Reaches₁ (step reference) ⟨12, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 1) (d := .left) (by decide) (by decide) (by decide) hc13
  have hc11 : ∀ T, WindowInv 31980543 26740735 T → ∃ ch, Reaches₁ (step reference) ⟨29, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 1) (d := .left) (by decide) (by decide) (by decide) hc12
  have hc10 : ∀ T, WindowInv 32765439 30149631 T → ∃ ch, Reaches₁ (step reference) ⟨27, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 0) (d := .left) (by decide) (by decide) (by decide) hc11
  have hc9 : ∀ T, WindowInv 33157887 31854079 T → ∃ ch, Reaches₁ (step reference) ⟨25, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 0) (d := .left) (by decide) (by decide) (by decide) hc10
  have hc8 : ∀ T, WindowInv 33354111 32706303 T → ∃ ch, Reaches₁ (step reference) ⟨23, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 0) (d := .left) (by decide) (by decide) (by decide) hc9
  have hc7 : ∀ T, WindowInv 33452223 33132415 T → ∃ ch, Reaches₁ (step reference) ⟨21, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 0) (d := .left) (by decide) (by decide) (by decide) hc8
  have hc6 : ∀ T, WindowInv 33501279 33345471 T → ∃ ch, Reaches₁ (step reference) ⟨19, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 0) (d := .left) (by decide) (by decide) (by decide) hc7
  have hc5 : ∀ T, WindowInv 33525807 33451999 T → ∃ ch, Reaches₁ (step reference) ⟨17, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 1) (a := 0) (d := .left) (by decide) (by decide) (by decide) hc6
  have hc4 : ∀ T, WindowInv 33540119 33503215 T → ∃ ch, Reaches₁ (step reference) ⟨177, T⟩ ch ∧
    step reference ch = none :=
    halt_chain_step (b := 0) (a := 0) (d := .left) (by decide) (by decide) (by decide) hc5
  exact hc4 T hW

theorem force_bit_k {v0 v1 k : Nat} {b exp : Fin 2}
    (h_allow : allowBit v0 v1 k b = true)
    (h_other : allowBit v0 v1 k (flipBit exp) = false) :
    b = exp :=
  force_bit_aux (v0.testBit k) (v1.testBit k) b exp h_allow h_other

theorem move_left_write_nth (U : Tape (Fin 2)) (w : Fin 2) (i : ℤ) (hi : i ≤ 0) :
    ((U.write w).move .left).nth i = U.nth (i - 1) := by
  have hne : i - 1 ≠ 0 := by omega
  rw [Tape.move_left_nth, Tape.write_nth, ite_eq_right hne]

def HaltCountdown (n : Nat) (c : Cfg 543 2) : Prop :=
  Nat.rec (motive := fun _ => Cfg 543 2 → Prop)
    (fun c => step candidate c = none)
    (fun _ ih c => ∃ c', step candidate c = some c' ∧ ih c')
    n c

def RefCountdown (n : Nat) (c : Cfg 744 2) : Prop :=
  Nat.rec (motive := fun _ => Cfg 744 2 → Prop)
    (fun c => step reference c = none)
    (fun _ ih c => ∃ c', Reaches₁ (step reference) c c' ∧ ih c')
    n c

def SyncCountdown (n : Nat) (c₂ : Cfg 543 2) (c₁ : Cfg 744 2) : Prop :=
  Nat.rec (motive := fun _ => Cfg 543 2 → Cfg 744 2 → Prop)
    (fun c₂ c₁ => Inv c₁.state c₁.tape ∧ c₂ = ⟨f c₁.state, c₁.tape⟩)
    (fun _ ih c₂ c₁ =>
      ∃ c₂' c₁', step candidate c₂ = some c₂' ∧
        Reaches₁ (step reference) c₁ c₁' ∧ ih c₂' c₁')
    n c₂ c₁

theorem halt_from_503 (T : Tape (Fin 2)) (hInv : Inv 503 T) (h0 : T.head = 0) :
    step reference ⟨503, T⟩ = some ⟨36, (T.write 0).move .right⟩ ∧
    RefCountdown 4 ⟨36, (T.write 0).move .right⟩ ∧
    step candidate ⟨f 503, T⟩ = some ⟨35, (T.write 0).move .left⟩ ∧
    HaltCountdown 4 ⟨35, (T.write 0).move .left⟩ := by
  have hs_ref1 : step reference ⟨503, T⟩ = some ⟨36, (T.write 0).move .right⟩ := by
    have htr : refTrans 503 0 = some (0, .right, 36) := by decide
    simp [step, refTrans_eq, h0, htr]
  have hW_503 : WindowInv 33553925 33538555 T := by
    intro k
    by_cases hk : k.val == 11
    · have hk11 : k = ⟨11, by decide⟩ := by revert k hk; decide
      subst hk11
      change allowBit 33553925 33538555 11 T.head = true
      rw [h0]; decide
    · have h_eq (b : Fin 2) :
          allowBit 33553925 33538555 k.val b = allowBit (m0 503) (m1 503) k.val b := by
        revert k hk b; decide
      change allowBit 33553925 33538555 k.val (tapeAt T k) = true
      rw [h_eq]
      exact hInv k
  let R1 := (T.write 0).move .right
  have hW1 : WindowInv 33554178 33546493 R1 := window_step_sound hW_503 0 .right (by decide)
  have hb1 : R1.head = 0 := force_bit (hW1 ⟨11, by decide⟩) (by decide)
  have hs_ref2 : step reference ⟨36, R1⟩ = some ⟨37, (R1.write 0).move .left⟩ := by
    have htr : refTrans 36 0 = some (0, .left, 37) := by decide
    simp [step, refTrans_eq, hb1, htr]
  let R2 := (R1.write 0).move .left
  have hW2 : WindowInv 33553925 33538555 R2 := window_step_sound hW1 0 .left (by decide)
  have hb2 : R2.head = 0 := force_bit (hW2 ⟨11, by decide⟩) (by decide)
  have hs_ref3 : step reference ⟨37, R2⟩ = some ⟨38, (R2.write 1).move .left⟩ := by
    have htr : refTrans 37 0 = some (1, .left, 38) := by decide
    simp [step, refTrans_eq, hb2, htr]
  let R3 := (R2.write 1).move .left
  have hW3 : WindowInv 33549323 33526775 R3 := window_step_sound hW2 1 .left (by decide)
  have hb3 : R3.head = 0 := force_bit (hW3 ⟨11, by decide⟩) (by decide)
  have hs_ref4 : step reference ⟨38, R3⟩ = some ⟨177, (R3.write 1).move .left⟩ := by
    have htr : refTrans 38 0 = some (1, .left, 177) := by decide
    simp [step, refTrans_eq, hb3, htr]
  let R4 := (R3.write 1).move .left
  have hW4 : WindowInv 33540119 33503215 R4 := window_step_sound hW3 1 .left (by decide)
  obtain ⟨ch, hreach177, hhalt177⟩ := reaches_halt_177 R4 hW4
  have h_ref_cd : RefCountdown 4 ⟨36, R1⟩ :=
    ⟨⟨37, R2⟩, Relation.TransGen.single hs_ref2,
     ⟨38, R3⟩, Relation.TransGen.single hs_ref3,
     ⟨177, R4⟩, Relation.TransGen.single hs_ref4,
     ch, hreach177, hhalt177⟩
  have hs_c1 : step candidate ⟨f 503, T⟩ = some ⟨35, (T.write 0).move .left⟩ := by
    have htr : candTrans (f 503) 0 = some (0, .left, 35) := by decide
    simp [step, candTrans_eq, h0, htr]
  let T1 := (T.write 0).move .left
  let T2 := (T1.write 0).move .left
  let T3 := (T2.write 0).move .left
  let T4 := (T3.write 1).move .left
  let T5 := (T4.write 1).move .left
  have hn1 : tapeAt T ⟨10, by decide⟩ = 0 := force_bit_k (hInv ⟨10, by decide⟩) (by decide)
  have hn2 : tapeAt T ⟨9, by decide⟩ = 0 := force_bit_k (hInv ⟨9, by decide⟩) (by decide)
  have hn3 : tapeAt T ⟨8, by decide⟩ = 1 := force_bit_k (hInv ⟨8, by decide⟩) (by decide)
  have hn4 : tapeAt T ⟨7, by decide⟩ = 1 := force_bit_k (hInv ⟨7, by decide⟩) (by decide)
  have hn5 : tapeAt T ⟨6, by decide⟩ = 1 := force_bit_k (hInv ⟨6, by decide⟩) (by decide)
  have ht1 : T1.head = 0 := by
    change ((T.write 0).move .left).nth 0 = 0
    rw [move_left_write_nth T 0 0 (by decide)]; exact hn1
  have ht2 : T2.head = 0 := by
    change ((T1.write 0).move .left).nth 0 = 0
    rw [move_left_write_nth T1 0 0 (by decide), move_left_write_nth T 0 (0 - 1) (by decide)]
    exact hn2
  have ht3 : T3.head = 1 := by
    change ((T2.write 0).move .left).nth 0 = 1
    rw [move_left_write_nth T2 0 0 (by decide), move_left_write_nth T1 0 (0 - 1) (by decide),
      move_left_write_nth T 0 (0 - 1 - 1) (by decide)]
    exact hn3
  have ht4 : T4.head = 1 := by
    change ((T3.write 1).move .left).nth 0 = 1
    rw [move_left_write_nth T3 1 0 (by decide), move_left_write_nth T2 0 (0 - 1) (by decide),
      move_left_write_nth T1 0 (0 - 1 - 1) (by decide),
      move_left_write_nth T 0 (0 - 1 - 1 - 1) (by decide)]
    exact hn4
  have ht5 : T5.head = 1 := by
    change ((T4.write 1).move .left).nth 0 = 1
    rw [move_left_write_nth T4 1 0 (by decide), move_left_write_nth T3 1 (0 - 1) (by decide),
      move_left_write_nth T2 0 (0 - 1 - 1) (by decide),
      move_left_write_nth T1 0 (0 - 1 - 1 - 1) (by decide),
      move_left_write_nth T 0 (0 - 1 - 1 - 1 - 1) (by decide)]
    exact hn5
  have hs_c2 : step candidate ⟨35, T1⟩ = some ⟨36, T2⟩ := by
    have htr : candTrans 35 0 = some (0, .left, 36) := by decide
    simp [step, candTrans_eq, ht1, htr]; rfl
  have hs_c3 : step candidate ⟨36, T2⟩ = some ⟨37, T3⟩ := by
    have htr : candTrans 36 0 = some (0, .left, 37) := by decide
    simp [step, candTrans_eq, ht2, htr]; rfl
  have hs_c4 : step candidate ⟨37, T3⟩ = some ⟨38, T4⟩ := by
    have htr : candTrans 37 1 = some (1, .left, 38) := by decide
    simp [step, candTrans_eq, ht3, htr]; rfl
  have hs_c5 : step candidate ⟨38, T4⟩ = some ⟨39, T5⟩ := by
    have htr : candTrans 38 1 = some (1, .left, 39) := by decide
    simp [step, candTrans_eq, ht4, htr]; rfl
  have hs_c6 : step candidate ⟨39, T5⟩ = none := by
    have htr : candTrans 39 1 = none := by decide
    simp [step, candTrans_eq, ht5, htr]
  have h_cand_cd : HaltCountdown 4 ⟨35, T1⟩ :=
    ⟨⟨36, T2⟩, hs_c2, ⟨37, T3⟩, hs_c3, ⟨38, T4⟩, hs_c4, ⟨39, T5⟩, hs_c5, hs_c6⟩
  exact ⟨hs_ref1, h_ref_cd, hs_c1, h_cand_cd⟩

def SyncEx (c₂ : Cfg 543 2) (c₁ : Cfg 744 2) : Prop :=
  ∃ n : Nat, SyncCountdown n c₂ c₁

theorem mk1_nil_move_right : ((Tape.mk₁ ([] : List (Fin 2))).write 0).move .right = Tape.mk₁ [] :=
  by
  have h_mk : Tape.mk₁ ([] : List (Fin 2)) = ⟨0, default, default⟩ := rfl
  have h_hd : (default : ListBlank (Fin 2)).head = 0 := rfl
  have h_tl : (default : ListBlank (Fin 2)).tail = default := rfl
  have h_cons : ListBlank.cons (0 : Fin 2) default = default := by
    have hc := ListBlank.cons_head_tail (default : ListBlank (Fin 2))
    rw [h_hd, h_tl] at hc
    exact hc
  rw [h_mk]
  dsimp [Tape.write, Tape.move]
  rw [h_hd, h_tl, h_cons]

def SimRel (c₂ : Cfg 543 2) (c₁ : Cfg 744 2) : Prop :=
  ((c₂ = init ∧ c₁ = init) ∨ (∃ n : Nat, HaltCountdown n c₂ ∧ RefCountdown n c₁)) ∨
  SyncEx c₂ c₁

theorem sync_base_ex {c_ref : Fin 744} :
    ∀ T, WindowInv (m0 c_ref) (m1 c_ref) T → SyncEx ⟨f c_ref, T⟩ ⟨c_ref, T⟩ :=
  fun _ hW => ⟨0, hW, rfl⟩

theorem sync_step_ex {c_cand next_cand : Fin 543} {c_ref next_ref : Fin 744}
    {v0 v1 w0 w1 : Nat} {b w : Fin 2} {d : Dir}
    (h_head : allowBit v0 v1 11 (flipBit b) = false)
    (h_cand : candTrans c_cand b = some (w, d, next_cand))
    (h_ref : refTrans c_ref b = some (w, d, next_ref))
    (h_cells : checkAllCells v0 v1 w0 w1 w d = true)
    (h_next : ∀ T', WindowInv w0 w1 T' → SyncEx ⟨next_cand, T'⟩ ⟨next_ref, T'⟩) :
    ∀ T, WindowInv v0 v1 T → SyncEx ⟨c_cand, T⟩ ⟨c_ref, T⟩ := by
  intro T hW
  have hb : T.head = b := force_bit (hW ⟨11, by decide⟩) h_head
  have hs_c : step candidate ⟨c_cand, T⟩ = some ⟨next_cand, (T.write w).move d⟩ := by
    simp [step, candTrans_eq, hb, h_cand]
  have hs_r : step reference ⟨c_ref, T⟩ = some ⟨next_ref, (T.write w).move d⟩ := by
    simp [step, refTrans_eq, hb, h_ref]
  have hW' := window_step_sound hW w d h_cells
  obtain ⟨m, h_m⟩ := h_next _ hW'
  exact ⟨m + 1, ⟨next_cand, (T.write w).move d⟩, ⟨next_ref, (T.write w).move d⟩,
    hs_c, Relation.TransGen.single hs_r, h_m⟩

theorem sync_step_bounce_ex {c_cand next_cand : Fin 543} {c_ref p j1 next_ref : Fin 744}
    {v0 v1 v0_n v1_n : Nat} {b w1_b w2 : Fin 2} {d1 d2 : Dir}
    (h_next : ∀ T', WindowInv v0_n v1_n T' → SyncEx ⟨next_cand, T'⟩ ⟨next_ref, T'⟩)
    (h_head : allowBit v0 v1 11 (flipBit b) = false)
    (h_cand : candTrans c_cand b = some (w2, d2, next_cand))
    (h_r1 : refTrans c_ref b = some (w1_b, d1, p))
    (hp0 : refTrans0 p.val = some (0, oppDir d1, j1))
    (hp1 : refTrans1 p.val = some (1, oppDir d1, j1))
    (h_r3 : refTrans j1 w1_b = some (w2, d2, next_ref))
    (h_cells : checkAllCells v0 v1 v0_n v1_n w2 d2 = true) :
    ∀ T, WindowInv v0 v1 T → SyncEx ⟨c_cand, T⟩ ⟨c_ref, T⟩ := by
  intro T hW
  have hb : T.head = b := force_bit (hW ⟨11, by decide⟩) h_head
  have hs_c : step candidate ⟨c_cand, T⟩ = some ⟨next_cand, (T.write w2).move d2⟩ := by
    simp [step, candTrans_eq, hb, h_cand]
  have hs1 : step reference ⟨c_ref, T⟩ = some ⟨p, (T.write w1_b).move d1⟩ := by
    simp [step, refTrans_eq, hb, h_r1]
  have hs2 : step reference ⟨p, (T.write w1_b).move d1⟩ = some ⟨j1, T.write w1_b⟩ := by
    rw [ref_pass_step ((T.write w1_b).move d1) hp0 hp1, move_opp]
  have hs3 : step reference ⟨j1, T.write w1_b⟩ = some ⟨next_ref, (T.write w2).move d2⟩ := by
    have hhead : (T.write w1_b).head = w1_b := rfl
    have hwrite : (T.write w1_b).write w2 = T.write w2 := rfl
    simp [step, refTrans_eq, hhead, h_r3, hwrite]
  have hW' := window_step_sound hW w2 d2 h_cells
  obtain ⟨m, h_m⟩ := h_next _ hW'
  exact ⟨m + 1, ⟨next_cand, (T.write w2).move d2⟩, ⟨next_ref, (T.write w2).move d2⟩,
    hs_c, Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2) hs3,
      h_m⟩

theorem restrict_window {v0 v1 r0 r1 : Nat} {b : Fin 2} {T : Tape (Fin 2)}
    (hW : WindowInv v0 v1 T) (hb : T.head = b)
    (h_head : allowBit r0 r1 11 b = true)
    (h_other : ∀ (k : Fin 25) (x : Fin 2), ¬(k.val == 11) = true → allowBit r0 r1 k.val x =
      allowBit v0 v1 k.val x) :
    WindowInv r0 r1 T := by
  intro k
  by_cases hk : k.val == 11
  · have hk11 : k = ⟨11, by decide⟩ := by revert k hk; decide
    subst hk11
    change allowBit r0 r1 11 T.head = true
    rw [hb]; exact h_head
  · rw [h_other k (tapeAt T k) hk]
    exact hW k

theorem sync_split_ex {c_cand : Fin 543} {c_ref : Fin 744}
    {v0 v1 r0_0 r1_0 r0_1 r1_1 : Nat}
    (h_head0 : allowBit r0_0 r1_0 11 0 = true)
    (h_other0 : ∀ (k : Fin 25) (x : Fin 2), ¬(k.val == 11) = true → allowBit r0_0 r1_0 k.val x =
      allowBit v0 v1 k.val x)
    (h_head1 : allowBit r0_1 r1_1 11 1 = true)
    (h_other1 : ∀ (k : Fin 25) (x : Fin 2), ¬(k.val == 11) = true → allowBit r0_1 r1_1 k.val x =
      allowBit v0 v1 k.val x)
    (h_branch0 : ∀ T, WindowInv r0_0 r1_0 T → SyncEx ⟨c_cand, T⟩ ⟨c_ref, T⟩)
    (h_branch1 : ∀ T, WindowInv r0_1 r1_1 T → SyncEx ⟨c_cand, T⟩ ⟨c_ref, T⟩) :
    ∀ T, WindowInv v0 v1 T → SyncEx ⟨c_cand, T⟩ ⟨c_ref, T⟩ := by
  intro T hW
  rcases hb : T.head with ⟨_ | _ | _, _⟩
  · exact h_branch0 T (restrict_window hW hb h_head0 h_other0)
  · exact h_branch1 T (restrict_window hW hb h_head1 h_other1)
  · omega

theorem sync_entry_1step_ex {q nrq : Fin 744} {ncq : Fin 543}
    {v0_n v1_n : Nat} {b w : Fin 2} {d : Dir}
    (h_next : ∀ T1, WindowInv v0_n v1_n T1 → SyncEx ⟨ncq, T1⟩ ⟨nrq, T1⟩)
    (h_cand : candTrans (f q) b = some (w, d, ncq))
    (h_ref : refTrans q b = some (w, d, nrq))
    (h_cells : checkAllCells (m0 q) (m1 q) v0_n v1_n w d = true)
    (T : Tape (Fin 2)) (hInv : Inv q T) (hb : T.head = b) :
    ∃ c₁, SimRel ⟨ncq, (T.write w).move d⟩ c₁ ∧
      Reaches₁ (step reference) ⟨q, T⟩ c₁ ∧
      step candidate ⟨f q, T⟩ = some ⟨ncq, (T.write w).move d⟩ := by
  have hs_c : step candidate ⟨f q, T⟩ = some ⟨ncq, (T.write w).move d⟩ := by
    simp [step, candTrans_eq, hb, h_cand]
  have hs_r : step reference ⟨q, T⟩ = some ⟨nrq, (T.write w).move d⟩ := by
    simp [step, refTrans_eq, hb, h_ref]
  have hW1 : WindowInv v0_n v1_n ((T.write w).move d) := window_step_sound hInv w d h_cells
  exact ⟨⟨nrq, (T.write w).move d⟩, Or.inr (h_next _ hW1), Relation.TransGen.single hs_r, hs_c⟩

theorem sync_entry_bounce_ex {q p j1 nrq : Fin 744} {ncq : Fin 543}
    {v0_n v1_n : Nat} {b w1 w2 : Fin 2} {d1 d2 : Dir}
    (h_next : ∀ T1, WindowInv v0_n v1_n T1 → SyncEx ⟨ncq, T1⟩ ⟨nrq, T1⟩)
    (h_cand : candTrans (f q) b = some (w2, d2, ncq))
    (h_r1 : refTrans q b = some (w1, d1, p))
    (hp0 : refTrans0 p.val = some (0, oppDir d1, j1))
    (hp1 : refTrans1 p.val = some (1, oppDir d1, j1))
    (h_r3 : refTrans j1 w1 = some (w2, d2, nrq))
    (h_cells : checkAllCells (m0 q) (m1 q) v0_n v1_n w2 d2 = true)
    (T : Tape (Fin 2)) (hInv : Inv q T) (hb : T.head = b) :
    ∃ c₁, SimRel ⟨ncq, (T.write w2).move d2⟩ c₁ ∧
      Reaches₁ (step reference) ⟨q, T⟩ c₁ ∧
      step candidate ⟨f q, T⟩ = some ⟨ncq, (T.write w2).move d2⟩ := by
  have hs_c : step candidate ⟨f q, T⟩ = some ⟨ncq, (T.write w2).move d2⟩ := by
    simp [step, candTrans_eq, hb, h_cand]
  have hs1 : step reference ⟨q, T⟩ = some ⟨p, (T.write w1).move d1⟩ := by
    simp [step, refTrans_eq, hb, h_r1]
  have hs2 : step reference ⟨p, (T.write w1).move d1⟩ = some ⟨j1, T.write w1⟩ := by
    rw [ref_pass_step ((T.write w1).move d1) hp0 hp1, move_opp]
  have hs3 : step reference ⟨j1, T.write w1⟩ = some ⟨nrq, (T.write w2).move d2⟩ := by
    have hhead : (T.write w1).head = w1 := rfl
    have hwrite : (T.write w1).write w2 = T.write w2 := rfl
    simp [step, refTrans_eq, hhead, h_r3, hwrite]
  have hW1 : WindowInv v0_n v1_n ((T.write w2).move d2) := window_step_sound hInv w2 d2 h_cells
  exact ⟨⟨nrq, (T.write w2).move d2⟩, Or.inr (h_next _ hW1),
    Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2) hs3, hs_c⟩


theorem sync_from_63_0 (T : Tape (Fin 2)) (hInv : Inv 63 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨33, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨63, T⟩ c₁ ∧
      step candidate ⟨f 63, T⟩ = some ⟨33, (T.write 1).move .left⟩ := by
  have hs_3 : ∀ T, WindowInv (m0 59) (m1 59) T → SyncEx ⟨f 59, T⟩ ⟨59, T⟩ := sync_base_ex
  have hs_2 : ∀ T, WindowInv 33545071 33432735 T → SyncEx ⟨34, T⟩ ⟨58, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33549751 33493583 T → SyncEx ⟨33, T⟩ ⟨57, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_1step_ex hs_1 (w := 1) (d := .left) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_203_1 (T : Tape (Fin 2)) (hInv : Inv 203 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨454, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨203, T⟩ c₁ ∧
      step candidate ⟨f 203, T⟩ = some ⟨454, (T.write 1).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 15) (m1 15) T → SyncEx ⟨f 15, T⟩ ⟨15, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33546431 33529667 T → SyncEx ⟨454, T⟩ ⟨165, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    163) (j1 := 164) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_208_0 (T : Tape (Fin 2)) (hInv : Inv 208 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨208, T⟩ c₁ ∧
      step candidate ⟨f 208, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 22) (m1 22) T → SyncEx ⟨f 22, T⟩ ⟨22, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33522687 33061951 T → SyncEx ⟨67, T⟩ ⟨121, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33540607 33306143 T → SyncEx ⟨66, T⟩ ⟨120, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33549567 33428239 T → SyncEx ⟨62, T⟩ ⟨119, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33554047 33489287 T → SyncEx ⟨70, T⟩ ⟨118, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33554239 33521859 T → SyncEx ⟨69, T⟩ ⟨117, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    115) (j1 := 116) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_209_0 (T : Tape (Fin 2)) (hInv : Inv 209 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨40, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨209, T⟩ c₁ ∧
      step candidate ⟨f 209, T⟩ = some ⟨40, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 22) (m1 22) T → SyncEx ⟨f 22, T⟩ ⟨22, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33526783 33057855 T → SyncEx ⟨5, T⟩ ⟨121, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33540607 33306143 T → SyncEx ⟨3, T⟩ ⟨53, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33549567 33428239 T → SyncEx ⟨65, T⟩ ⟨52, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33554047 33489287 T → SyncEx ⟨64, T⟩ ⟨51, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33552191 33523907 T → SyncEx ⟨40, T⟩ ⟨50, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    48) (j1 := 49) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_212_1 (T : Tape (Fin 2)) (hInv : Inv 212 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨212, T⟩ c₁ ∧
      step candidate ⟨f 212, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_8 : ∀ T, WindowInv (m0 26) (m1 26) T → SyncEx ⟨f 26, T⟩ ⟨26, T⟩ := sync_base_ex
  have hs_7 : ∀ T, WindowInv 33165311 31846655 T → SyncEx ⟨22, T⟩ ⟨72, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_8
  have hs_6 : ∀ T, WindowInv 33359871 32700543 T → SyncEx ⟨20, T⟩ ⟨71, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_7
  have hs_5 : ∀ T, WindowInv 33457151 33127487 T → SyncEx ⟨18, T⟩ ⟨70, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33507839 33338911 T → SyncEx ⟨17, T⟩ ⟨69, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33531135 33446671 T → SyncEx ⟨43, T⟩ ⟨68, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33544831 33498503 T → SyncEx ⟨42, T⟩ ⟨67, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33549631 33526467 T → SyncEx ⟨41, T⟩ ⟨66, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    64) (j1 := 65) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_216_0 (T : Tape (Fin 2)) (hInv : Inv 216 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨216, T⟩ c₁ ∧
      step candidate ⟨f 216, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_5 : ∀ T, WindowInv (m0 20) (m1 20) T → SyncEx ⟨f 20, T⟩ ⟨20, T⟩ := sync_base_ex
  have hs_4 : ∀ T, WindowInv 33546751 33299999 T → SyncEx ⟨66, T⟩ ⟨173, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33550591 33427215 T → SyncEx ⟨45, T⟩ ⟨172, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33550463 33492871 T → SyncEx ⟨70, T⟩ ⟨171, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33552447 33523651 T → SyncEx ⟨69, T⟩ ⟨170, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    168) (j1 := 169) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_217_0 (T : Tape (Fin 2)) (hInv : Inv 217 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨217, T⟩ c₁ ∧
      step candidate ⟨f 217, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 15) (m1 15) T → SyncEx ⟨f 15, T⟩ ⟨15, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33550399 33525699 T → SyncEx ⟨69, T⟩ ⟨165, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    156) (j1 := 157) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_224_1 (T : Tape (Fin 2)) (hInv : Inv 224 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨69, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨224, T⟩ c₁ ∧
      step candidate ⟨f 224, T⟩ = some ⟨69, (T.write 1).move .left⟩ := by
  have hs_7 : ∀ T, WindowInv (m0 72) (m1 72) T → SyncEx ⟨f 72, T⟩ ⟨72, T⟩ := sync_base_ex
  have hs_6 : ∀ T, WindowInv 33360895 32699519 T → SyncEx ⟨68, T⟩ ⟨71, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_7
  have hs_5 : ∀ T, WindowInv 33459711 33124927 T → SyncEx ⟨67, T⟩ ⟨70, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33509119 33337631 T → SyncEx ⟨66, T⟩ ⟨69, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33533823 33443983 T → SyncEx ⟨62, T⟩ ⟨68, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33546175 33497159 T → SyncEx ⟨70, T⟩ ⟨67, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33550303 33525795 T → SyncEx ⟨69, T⟩ ⟨66, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    64) (j1 := 65) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_225_1 (T : Tape (Fin 2)) (hInv : Inv 225 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨225, T⟩ c₁ ∧
      step candidate ⟨f 225, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 19) (m1 19) T → SyncEx ⟨f 19, T⟩ ⟨19, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33537919 33439887 T → SyncEx ⟨43, T⟩ ⟨84, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33546175 33497159 T → SyncEx ⟨61, T⟩ ⟨83, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548255 33527843 T → SyncEx ⟨41, T⟩ ⟨82, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    80) (j1 := 81) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_241_1 (T : Tape (Fin 2)) (hInv : Inv 241 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨454, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨241, T⟩ c₁ ∧
      step candidate ⟨f 241, T⟩ = some ⟨454, (T.write 1).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 15) (m1 15) T → SyncEx ⟨f 15, T⟩ ⟨15, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33547167 33528931 T → SyncEx ⟨454, T⟩ ⟨165, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    163) (j1 := 164) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_244_0 (T : Tape (Fin 2)) (hInv : Inv 244 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨244, T⟩ c₁ ∧
      step candidate ⟨f 244, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 173) (m1 173) T → SyncEx ⟨f 173, T⟩ ⟨173, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33547903 33429903 T → SyncEx ⟨62, T⟩ ⟨137, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33553215 33490119 T → SyncEx ⟨70, T⟩ ⟨136, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33553823 33522275 T → SyncEx ⟨69, T⟩ ⟨135, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    133) (j1 := 134) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_245_0 (T : Tape (Fin 2)) (hInv : Inv 245 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨40, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨245, T⟩ c₁ ∧
      step candidate ⟨f 245, T⟩ = some ⟨40, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 151) (m1 151) T → SyncEx ⟨f 151, T⟩ ⟨151, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33551775 33524323 T → SyncEx ⟨40, T⟩ ⟨150, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    148) (j1 := 149) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_249_1 (T : Tape (Fin 2)) (hInv : Inv 249 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨249, T⟩ c₁ ∧
      step candidate ⟨f 249, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 19) (m1 19) T → SyncEx ⟨f 19, T⟩ ⟨19, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33532399 33445407 T → SyncEx ⟨43, T⟩ ⟨84, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33543415 33499919 T → SyncEx ⟨42, T⟩ ⟨104, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548923 33527175 T → SyncEx ⟨41, T⟩ ⟨103, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    101) (j1 := 102) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_254_0 (T : Tape (Fin 2)) (hInv : Inv 254 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨254, T⟩ c₁ ∧
      step candidate ⟨f 254, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 22) (m1 22) T → SyncEx ⟨f 22, T⟩ ⟨22, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33546751 33037887 T → SyncEx ⟨67, T⟩ ⟨121, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33552639 33294111 T → SyncEx ⟨66, T⟩ ⟨120, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33553535 33424271 T → SyncEx ⟨45, T⟩ ⟨79, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33551935 33491399 T → SyncEx ⟨70, T⟩ ⟨78, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33553183 33522915 T → SyncEx ⟨69, T⟩ ⟨77, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    75) (j1 := 76) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_255_0 (T : Tape (Fin 2)) (hInv : Inv 255 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨255, T⟩ c₁ ∧
      step candidate ⟨f 255, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 15) (m1 15) T → SyncEx ⟨f 15, T⟩ ⟨15, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33551135 33524963 T → SyncEx ⟨69, T⟩ ⟨165, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    156) (j1 := 157) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_258_1 (T : Tape (Fin 2)) (hInv : Inv 258 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨69, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨258, T⟩ c₁ ∧
      step candidate ⟨f 258, T⟩ = some ⟨69, (T.write 1).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 173) (m1 173) T → SyncEx ⟨f 173, T⟩ ⟨173, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33531007 33446799 T → SyncEx ⟨62, T⟩ ⟨137, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33544767 33498567 T → SyncEx ⟨70, T⟩ ⟨136, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33549599 33526499 T → SyncEx ⟨69, T⟩ ⟨135, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    146) (j1 := 147) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_266_1 (T : Tape (Fin 2)) (hInv : Inv 266 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨58, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨266, T⟩ c₁ ∧
      step candidate ⟨f 266, T⟩ = some ⟨58, (T.write 0).move .left⟩ := by
  have hs_11 : ∀ T, WindowInv (m0 371) (m1 371) T → SyncEx ⟨f 371, T⟩ ⟨371, T⟩ := sync_base_ex
  have hs_10 : ∀ T, WindowInv 32702463 17631231 T → SyncEx ⟨49, T⟩ ⟨12, T⟩ :=
    sync_step_bounce_ex hs_11 (p := 0) (j1 := 523) (b := 0) (w1_b := 0) (w2 := 0) (d1 := .left)
      (d2 := .right) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have hs_9 : ∀ T, WindowInv 33128447 25592831 T → SyncEx ⟨48, T⟩ ⟨28, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hs_10
  have hs_8 : ∀ T, WindowInv 33341439 29573631 T → SyncEx ⟨57, T⟩ ⟨26, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_9
  have hs_7 : ∀ T, WindowInv 33445887 31566079 T → SyncEx ⟨56, T⟩ ⟨72, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_8
  have hs_6 : ∀ T, WindowInv 33498111 32562303 T → SyncEx ⟨55, T⟩ ⟨145, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_7
  have hs_5 : ∀ T, WindowInv 33526271 33058367 T → SyncEx ⟨63, T⟩ ⟨144, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33538303 33308447 T → SyncEx ⟨30, T⟩ ⟨143, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33546367 33431439 T → SyncEx ⟨59, T⟩ ⟨142, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33552447 33490887 T → SyncEx ⟨59, T⟩ ⟨141, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33553439 33522659 T → SyncEx ⟨58, T⟩ ⟨140, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    138) (j1 := 139) (w1 := 1) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_291_1 (T : Tape (Fin 2)) (hInv : Inv 291 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨450, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨291, T⟩ c₁ ∧
      step candidate ⟨f 291, T⟩ = some ⟨450, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 14) (m1 14) T → SyncEx ⟨f 14, T⟩ ⟨14, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33553127 33522971 T → SyncEx ⟨450, T⟩ ⟨11, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    525) (j1 := 9) (w1 := 1) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_294_1 (T : Tape (Fin 2)) (hInv : Inv 294 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨450, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨294, T⟩ c₁ ∧
      step candidate ⟨f 294, T⟩ = some ⟨450, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 14) (m1 14) T → SyncEx ⟨f 14, T⟩ ⟨14, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33554431 33523679 T → SyncEx ⟨450, T⟩ ⟨11, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    525) (j1 := 9) (w1 := 1) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_302_1 (T : Tape (Fin 2)) (hInv : Inv 302 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨302, T⟩ c₁ ∧
      step candidate ⟨f 302, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 113) (m1 113) T → SyncEx ⟨f 113, T⟩ ⟨113, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33546343 33529755 T → SyncEx ⟨41, T⟩ ⟨109, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    107) (j1 := 108) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_308_0 (T : Tape (Fin 2)) (hInv : Inv 308 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨308, T⟩ c₁ ∧
      step candidate ⟨f 308, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 155) (m1 155) T → SyncEx ⟨f 155, T⟩ ⟨155, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33524351 33060287 T → SyncEx ⟨67, T⟩ ⟨154, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33541439 33305311 T → SyncEx ⟨66, T⟩ ⟨153, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33549983 33427823 T → SyncEx ⟨62, T⟩ ⟨162, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33554255 33489079 T → SyncEx ⟨70, T⟩ ⟨161, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33554343 33521755 T → SyncEx ⟨69, T⟩ ⟨160, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    158) (j1 := 159) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_309_0 (T : Tape (Fin 2)) (hInv : Inv 309 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨35, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨309, T⟩ c₁ ∧
      step candidate ⟨f 309, T⟩ = some ⟨35, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 22) (m1 22) T → SyncEx ⟨f 22, T⟩ ⟨22, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33548927 33035711 T → SyncEx ⟨18, T⟩ ⟨121, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33553727 33293023 T → SyncEx ⟨17, T⟩ ⟨120, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33554079 33423727 T → SyncEx ⟨43, T⟩ ⟨79, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33554255 33489079 T → SyncEx ⟨61, T⟩ ⟨78, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33552295 33523803 T → SyncEx ⟨35, T⟩ ⟨77, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    75) (j1 := 76) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_316_1 (T : Tape (Fin 2)) (hInv : Inv 316 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨316, T⟩ c₁ ∧
      step candidate ⟨f 316, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_5 : ∀ T, WindowInv (m0 21) (m1 21) T → SyncEx ⟨f 21, T⟩ ⟨21, T⟩ := sync_base_ex
  have hs_4 : ∀ T, WindowInv 33506687 33340415 T → SyncEx ⟨17, T⟩ ⟨19, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33530559 33447423 T → SyncEx ⟨43, T⟩ ⟨114, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33542495 33500927 T → SyncEx ⟨42, T⟩ ⟨125, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548463 33527679 T → SyncEx ⟨41, T⟩ ⟨124, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    122) (j1 := 123) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_321_0 (T : Tape (Fin 2)) (hInv : Inv 321 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨47, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨321, T⟩ c₁ ∧
      step candidate ⟨f 321, T⟩ = some ⟨47, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 22) (m1 22) T → SyncEx ⟨f 22, T⟩ ⟨22, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33522687 33062911 T → SyncEx ⟨67, T⟩ ⟨121, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33540607 33306623 T → SyncEx ⟨66, T⟩ ⟨120, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33547519 33430527 T → SyncEx ⟨45, T⟩ ⟨119, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33550975 33492479 T → SyncEx ⟨46, T⟩ ⟨118, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33552703 33523455 T → SyncEx ⟨47, T⟩ ⟨117, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    115) (j1 := 116) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_332_1 (T : Tape (Fin 2)) (hInv : Inv 332 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨332, T⟩ c₁ ∧
      step candidate ⟨f 332, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 19) (m1 19) T → SyncEx ⟨f 19, T⟩ ⟨19, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33532863 33445631 T → SyncEx ⟨43, T⟩ ⟨84, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33543647 33500031 T → SyncEx ⟨42, T⟩ ⟨104, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33549039 33527231 T → SyncEx ⟨41, T⟩ ⟨103, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    101) (j1 := 102) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_337_0 (T : Tape (Fin 2)) (hInv : Inv 337 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨47, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨337, T⟩ c₁ ∧
      step candidate ⟨f 337, T⟩ = some ⟨47, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 22) (m1 22) T → SyncEx ⟨f 22, T⟩ ⟨22, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33531135 33054719 T → SyncEx ⟨67, T⟩ ⟨121, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33544831 33302527 T → SyncEx ⟨66, T⟩ ⟨120, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33549631 33428479 T → SyncEx ⟨45, T⟩ ⟨79, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33552031 33491455 T → SyncEx ⟨46, T⟩ ⟨88, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33553231 33522943 T → SyncEx ⟨47, T⟩ ⟨87, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    85) (j1 := 86) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_342_1 (T : Tape (Fin 2)) (hInv : Inv 342 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨58, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨342, T⟩ c₁ ∧
      step candidate ⟨f 342, T⟩ = some ⟨58, (T.write 1).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 145) (m1 145) T → SyncEx ⟨f 145, T⟩ ⟨145, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33457279 33127359 T → SyncEx ⟨30, T⟩ ⟨132, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33505855 33340895 T → SyncEx ⟨59, T⟩ ⟨131, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33532191 33445615 T → SyncEx ⟨59, T⟩ ⟨130, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33545359 33497975 T → SyncEx ⟨59, T⟩ ⟨129, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33549895 33526203 T → SyncEx ⟨58, T⟩ ⟨128, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    126) (j1 := 127) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_350_1 (T : Tape (Fin 2)) (hInv : Inv 350 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨350, T⟩ c₁ ∧
      step candidate ⟨f 350, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 19) (m1 19) T → SyncEx ⟨f 19, T⟩ ⟨19, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33532447 33445359 T → SyncEx ⟨43, T⟩ ⟨84, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33543439 33499895 T → SyncEx ⟨42, T⟩ ⟨104, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548935 33527163 T → SyncEx ⟨41, T⟩ ⟨103, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    101) (j1 := 102) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_361_0 (T : Tape (Fin 2)) (hInv : Inv 361 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨361, T⟩ c₁ ∧
      step candidate ⟨f 361, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_5 : ∀ T, WindowInv (m0 20) (m1 20) T → SyncEx ⟨f 20, T⟩ ⟨20, T⟩ := sync_base_ex
  have hs_4 : ∀ T, WindowInv 33538111 33308639 T → SyncEx ⟨66, T⟩ ⟨173, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33548319 33429487 T → SyncEx ⟨62, T⟩ ⟨172, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33553423 33489911 T → SyncEx ⟨70, T⟩ ⟨47, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33553927 33522171 T → SyncEx ⟨69, T⟩ ⟨46, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    44) (j1 := 45) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_372_1 (T : Tape (Fin 2)) (hInv : Inv 372 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨372, T⟩ c₁ ∧
      step candidate ⟨f 372, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_8 : ∀ T, WindowInv (m0 26) (m1 26) T → SyncEx ⟨f 26, T⟩ ⟨26, T⟩ := sync_base_ex
  have hs_7 : ∀ T, WindowInv 33177343 31834623 T → SyncEx ⟨22, T⟩ ⟨72, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_8
  have hs_6 : ∀ T, WindowInv 33365887 32694527 T → SyncEx ⟨20, T⟩ ⟨145, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_7
  have hs_5 : ∀ T, WindowInv 33460159 33124479 T → SyncEx ⟨18, T⟩ ⟨132, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33509343 33337407 T → SyncEx ⟨17, T⟩ ⟨131, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33531887 33445919 T → SyncEx ⟨43, T⟩ ⟨130, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33543159 33500175 T → SyncEx ⟨42, T⟩ ⟨129, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548795 33527303 T → SyncEx ⟨41, T⟩ ⟨128, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    126) (j1 := 127) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_391_1 (T : Tape (Fin 2)) (hInv : Inv 391 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨450, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨391, T⟩ c₁ ∧
      step candidate ⟨f 391, T⟩ = some ⟨450, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 14) (m1 14) T → SyncEx ⟨f 14, T⟩ ⟨14, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33553595 33522503 T → SyncEx ⟨450, T⟩ ⟨11, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    525) (j1 := 9) (w1 := 1) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_403_1 (T : Tape (Fin 2)) (hInv : Inv 403 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨403, T⟩ c₁ ∧
      step candidate ⟨f 403, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 19) (m1 19) T → SyncEx ⟨f 19, T⟩ ⟨19, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33537903 33439903 T → SyncEx ⟨43, T⟩ ⟨84, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33544119 33499215 T → SyncEx ⟨61, T⟩ ⟨83, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33547227 33528871 T → SyncEx ⟨41, T⟩ ⟨82, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    80) (j1 := 81) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_406_0 (T : Tape (Fin 2)) (hInv : Inv 406 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨69, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨406, T⟩ c₁ ∧
      step candidate ⟨f 406, T⟩ = some ⟨69, (T.write 0).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 173) (m1 173) T → SyncEx ⟨f 173, T⟩ ⟨173, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33548143 33429663 T → SyncEx ⟨62, T⟩ ⟨137, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33553335 33489999 T → SyncEx ⟨70, T⟩ ⟨136, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33553883 33522215 T → SyncEx ⟨69, T⟩ ⟨135, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    133) (j1 := 134) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_407_0 (T : Tape (Fin 2)) (hInv : Inv 407 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨35, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨407, T⟩ c₁ ∧
      step candidate ⟨f 407, T⟩ = some ⟨35, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 113) (m1 113) T → SyncEx ⟨f 113, T⟩ ⟨113, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33551835 33524263 T → SyncEx ⟨35, T⟩ ⟨109, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    105) (j1 := 106) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_416_1 (T : Tape (Fin 2)) (hInv : Inv 416 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨416, T⟩ c₁ ∧
      step candidate ⟨f 416, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 19) (m1 19) T → SyncEx ⟨f 19, T⟩ ⟨19, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33533807 33445599 T → SyncEx ⟨43, T⟩ ⟨84, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33544119 33500015 T → SyncEx ⟨42, T⟩ ⟨104, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33549275 33527223 T → SyncEx ⟨41, T⟩ ⟨103, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    101) (j1 := 102) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_420_0 (T : Tape (Fin 2)) (hInv : Inv 420 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨47, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨420, T⟩ c₁ ∧
      step candidate ⟨f 420, T⟩ = some ⟨47, (T.write 0).move .left⟩ := by
  have hs_5 : ∀ T, WindowInv (m0 20) (m1 20) T → SyncEx ⟨f 20, T⟩ ⟨20, T⟩ := sync_base_ex
  have hs_4 : ∀ T, WindowInv 33542879 33303871 T → SyncEx ⟨66, T⟩ ⟨173, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33548655 33429151 T → SyncEx ⟨45, T⟩ ⟨137, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33551543 33491791 T → SyncEx ⟨46, T⟩ ⟨136, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33552987 33523111 T → SyncEx ⟨47, T⟩ ⟨135, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    133) (j1 := 134) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_429_1 (T : Tape (Fin 2)) (hInv : Inv 429 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨429, T⟩ c₁ ∧
      step candidate ⟨f 429, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_5 : ∀ T, WindowInv (m0 21) (m1 21) T → SyncEx ⟨f 21, T⟩ ⟨21, T⟩ := sync_base_ex
  have hs_4 : ∀ T, WindowInv 33507039 33341375 T → SyncEx ⟨17, T⟩ ⟨19, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33530735 33447903 T → SyncEx ⟨43, T⟩ ⟨114, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33542583 33501167 T → SyncEx ⟨42, T⟩ ⟨125, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548507 33527799 T → SyncEx ⟨41, T⟩ ⟨124, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    122) (j1 := 123) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_445_1 (T : Tape (Fin 2)) (hInv : Inv 445 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨445, T⟩ c₁ ∧
      step candidate ⟨f 445, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_8 : ∀ T, WindowInv (m0 26) (m1 26) T → SyncEx ⟨f 26, T⟩ ⟨26, T⟩ := sync_base_ex
  have hs_7 : ∀ T, WindowInv 33176319 31835647 T → SyncEx ⟨22, T⟩ ⟨72, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_8
  have hs_6 : ∀ T, WindowInv 33365375 32695039 T → SyncEx ⟨20, T⟩ ⟨145, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_7
  have hs_5 : ∀ T, WindowInv 33459903 33124735 T → SyncEx ⟨18, T⟩ ⟨132, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33509215 33337535 T → SyncEx ⟨17, T⟩ ⟨131, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33531823 33445983 T → SyncEx ⟨43, T⟩ ⟨130, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33543127 33500207 T → SyncEx ⟨42, T⟩ ⟨129, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548779 33527319 T → SyncEx ⟨41, T⟩ ⟨128, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    126) (j1 := 127) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_458_0 (T : Tape (Fin 2)) (hInv : Inv 458 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨47, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨458, T⟩ c₁ ∧
      step candidate ⟨f 458, T⟩ = some ⟨47, (T.write 0).move .left⟩ := by
  have hs_7 : ∀ T, WindowInv (m0 24) (m1 24) T → SyncEx ⟨f 24, T⟩ ⟨24, T⟩ := sync_base_ex
  have hs_6 : ∀ T, WindowInv 33506687 32553727 T → SyncEx ⟨68, T⟩ ⟨155, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_7
  have hs_5 : ∀ T, WindowInv 33532607 33052031 T → SyncEx ⟨67, T⟩ ⟨154, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33545567 33301183 T → SyncEx ⟨66, T⟩ ⟨153, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33549999 33427807 T → SyncEx ⟨45, T⟩ ⟨152, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33552215 33491119 T → SyncEx ⟨46, T⟩ ⟨151, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33553323 33522775 T → SyncEx ⟨47, T⟩ ⟨150, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    148) (j1 := 149) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_459_0 (T : Tape (Fin 2)) (hInv : Inv 459 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨47, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨459, T⟩ c₁ ∧
      step candidate ⟨f 459, T⟩ = some ⟨47, (T.write 1).move .left⟩ := by
  have hs_4 : ∀ T, WindowInv (m0 19) (m1 19) T → SyncEx ⟨f 19, T⟩ ⟨19, T⟩ := sync_base_ex
  have hs_3 : ∀ T, WindowInv 33533615 33444191 T → SyncEx ⟨43, T⟩ ⟨84, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33544023 33499311 T → SyncEx ⟨42, T⟩ ⟨104, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33547179 33528919 T → SyncEx ⟨47, T⟩ ⟨103, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    101) (j1 := 102) (w1 := 0) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_463_0 (T : Tape (Fin 2)) (hInv : Inv 463 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨47, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨463, T⟩ c₁ ∧
      step candidate ⟨f 463, T⟩ = some ⟨47, (T.write 1).move .left⟩ := by
  have hs_5 : ∀ T, WindowInv (m0 20) (m1 20) T → SyncEx ⟨f 20, T⟩ ⟨20, T⟩ := sync_base_ex
  have hs_4 : ∀ T, WindowInv 33510751 33335999 T → SyncEx ⟨66, T⟩ ⟨173, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33532591 33445215 T → SyncEx ⟨45, T⟩ ⟨137, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33543511 33499823 T → SyncEx ⟨46, T⟩ ⟨136, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548971 33527127 T → SyncEx ⟨47, T⟩ ⟨135, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    146) (j1 := 147) (w1 := 0) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_468_1 (T : Tape (Fin 2)) (hInv : Inv 468 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨41, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨468, T⟩ c₁ ∧
      step candidate ⟨f 468, T⟩ = some ⟨41, (T.write 1).move .left⟩ := by
  have hs_8 : ∀ T, WindowInv (m0 26) (m1 26) T → SyncEx ⟨f 26, T⟩ ⟨26, T⟩ := sync_base_ex
  have hs_7 : ∀ T, WindowInv 33164031 31847935 T → SyncEx ⟨22, T⟩ ⟨72, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_8
  have hs_6 : ∀ T, WindowInv 33359231 32701183 T → SyncEx ⟨20, T⟩ ⟨71, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_7
  have hs_5 : ∀ T, WindowInv 33456831 33127807 T → SyncEx ⟨18, T⟩ ⟨70, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33507679 33339071 T → SyncEx ⟨17, T⟩ ⟨69, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33531055 33446751 T → SyncEx ⟨43, T⟩ ⟨68, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33542743 33500591 T → SyncEx ⟨42, T⟩ ⟨67, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33548587 33527511 T → SyncEx ⟨41, T⟩ ⟨66, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    64) (j1 := 65) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_487_0 (T : Tape (Fin 2)) (hInv : Inv 487 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨47, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨487, T⟩ c₁ ∧
      step candidate ⟨f 487, T⟩ = some ⟨47, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 155) (m1 155) T → SyncEx ⟨f 155, T⟩ ⟨155, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33523903 33060735 T → SyncEx ⟨67, T⟩ ⟨154, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33541215 33305535 T → SyncEx ⟨66, T⟩ ⟨153, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33547823 33429983 T → SyncEx ⟨45, T⟩ ⟨162, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33551127 33492207 T → SyncEx ⟨46, T⟩ ⟨161, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33552779 33523319 T → SyncEx ⟨47, T⟩ ⟨160, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    158) (j1 := 159) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_494_0 (T : Tape (Fin 2)) (hInv : Inv 494 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨47, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨494, T⟩ c₁ ∧
      step candidate ⟨f 494, T⟩ = some ⟨47, (T.write 0).move .left⟩ := by
  have hs_6 : ∀ T, WindowInv (m0 22) (m1 22) T → SyncEx ⟨f 22, T⟩ ⟨22, T⟩ := sync_base_ex
  have hs_5 : ∀ T, WindowInv 33521855 33062783 T → SyncEx ⟨67, T⟩ ⟨121, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_6
  have hs_4 : ∀ T, WindowInv 33540191 33306559 T → SyncEx ⟨66, T⟩ ⟨120, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33547311 33430495 T → SyncEx ⟨45, T⟩ ⟨119, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33550871 33492463 T → SyncEx ⟨46, T⟩ ⟨118, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33552651 33523447 T → SyncEx ⟨47, T⟩ ⟨117, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    115) (j1 := 116) (w1 := 0) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_499_1 (T : Tape (Fin 2)) (hInv : Inv 499 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨69, (T.write 1).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨499, T⟩ c₁ ∧
      step candidate ⟨f 499, T⟩ = some ⟨69, (T.write 1).move .left⟩ := by
  have hs_5 : ∀ T, WindowInv (m0 20) (m1 20) T → SyncEx ⟨f 20, T⟩ ⟨20, T⟩ := sync_base_ex
  have hs_4 : ∀ T, WindowInv 33505375 33341375 T → SyncEx ⟨66, T⟩ ⟨173, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_5
  have hs_3 : ∀ T, WindowInv 33531951 33445855 T → SyncEx ⟨62, T⟩ ⟨172, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_4
  have hs_2 : ∀ T, WindowInv 33545239 33498095 T → SyncEx ⟨70, T⟩ ⟨47, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_3
  have hs_1 : ∀ T, WindowInv 33549835 33526263 T → SyncEx ⟨69, T⟩ ⟨46, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    73) (j1 := 74) (w1 := 1) (w2 := 1) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_712_1 (T : Tape (Fin 2)) (hInv : Inv 712 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨60, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨712, T⟩ c₁ ∧
      step candidate ⟨f 712, T⟩ = some ⟨60, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 15) (m1 15) T → SyncEx ⟨f 15, T⟩ ⟨15, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33554431 33523711 T → SyncEx ⟨60, T⟩ ⟨646, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    710) (j1 := 711) (w1 := 1) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_713_1 (T : Tape (Fin 2)) (hInv : Inv 713 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨58, (T.write 0).move .left⟩ c₁ ∧
      Reaches₁ (step reference) ⟨713, T⟩ c₁ ∧
      step candidate ⟨f 713, T⟩ = some ⟨58, (T.write 0).move .left⟩ := by
  have hs_2 : ∀ T, WindowInv (m0 14) (m1 14) T → SyncEx ⟨f 14, T⟩ ⟨14, T⟩ := sync_base_ex
  have hs_1 : ∀ T, WindowInv 33552383 33524731 T → SyncEx ⟨58, T⟩ ⟨634, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide) hs_2
  exact sync_entry_bounce_ex hs_1 (p :=
    632) (j1 := 633) (w1 := 1) (w2 := 0) (d1 := .right) (d2 := .left) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_376_0 (T : Tape (Fin 2)) (hInv : Inv 376 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨139, (T.write 0).move .right⟩ c₁ ∧
      Reaches₁ (step reference) ⟨376, T⟩ c₁ ∧
      step candidate ⟨f 376, T⟩ = some ⟨139, (T.write 0).move .right⟩ := by
  have hb0_6 : ∀ T, WindowInv (m0 22) (m1 22) T → SyncEx ⟨f 22, T⟩ ⟨22, T⟩ := sync_base_ex
  have hb0_5 : ∀ T, WindowInv 33529791 33055103 T → SyncEx ⟨18, T⟩ ⟨121, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_6
  have hb0_4 : ∀ T, WindowInv 33540063 33306815 T → SyncEx ⟨66, T⟩ ⟨53, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_5
  have hb0_3 : ∀ T, WindowInv 33547247 33430623 T → SyncEx ⟨45, T⟩ ⟨52, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_4
  have hb0_2 : ∀ T, WindowInv 33550839 33492527 T → SyncEx ⟨46, T⟩ ⟨51, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_3
  have hb0_1 : ∀ T, WindowInv 33552635 33523479 T → SyncEx ⟨47, T⟩ ⟨50, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_2
  have hb0_0 : ∀ T, WindowInv 33553533 33538955 T → SyncEx ⟨139, T⟩ ⟨209, T⟩ :=
    sync_step_bounce_ex hb0_1 (p := 48) (j1 := 49) (b := 0) (w1_b := 0) (w2 := 0) (d1 := .right)
      (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have hb1_1 : ∀ T, WindowInv (m0 11) (m1 11) T → SyncEx ⟨f 11, T⟩ ⟨11, T⟩ := sync_base_ex
  have hb1_0 : ∀ T, WindowInv 33551485 33541003 T → SyncEx ⟨139, T⟩ ⟨209, T⟩ :=
    sync_step_bounce_ex hb1_1 (p := 525) (j1 := 9) (b := 1) (w1_b := 1) (w2 := 0) (d1 := .right)
      (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h_split : ∀ T, WindowInv 33553533 33541003 T → SyncEx ⟨139, T⟩ ⟨209, T⟩ :=
    sync_split_ex (by decide) (by decide) (by decide) (by decide) hb0_0 hb1_0
  exact sync_entry_1step_ex h_split (w :=
    0) (d := .right) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_386_0 (T : Tape (Fin 2)) (hInv : Inv 386 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨139, (T.write 0).move .right⟩ c₁ ∧
      Reaches₁ (step reference) ⟨386, T⟩ c₁ ∧
      step candidate ⟨f 386, T⟩ = some ⟨139, (T.write 0).move .right⟩ := by
  have hb0_7 : ∀ T, WindowInv (m0 24) (m1 24) T → SyncEx ⟨f 24, T⟩ ⟨24, T⟩ := sync_base_ex
  have hb0_6 : ∀ T, WindowInv 33507199 32553215 T → SyncEx ⟨68, T⟩ ⟨155, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_7
  have hb0_5 : ∀ T, WindowInv 33532863 33051775 T → SyncEx ⟨67, T⟩ ⟨154, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_6
  have hb0_4 : ∀ T, WindowInv 33545695 33301055 T → SyncEx ⟨66, T⟩ ⟨153, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_5
  have hb0_3 : ∀ T, WindowInv 33550063 33427743 T → SyncEx ⟨45, T⟩ ⟨152, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_4
  have hb0_2 : ∀ T, WindowInv 33552247 33491087 T → SyncEx ⟨46, T⟩ ⟨151, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_3
  have hb0_1 : ∀ T, WindowInv 33553339 33522759 T → SyncEx ⟨47, T⟩ ⟨150, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      hb0_2
  have hb0_0 : ∀ T, WindowInv 33553885 33538595 T → SyncEx ⟨139, T⟩ ⟨245, T⟩ :=
    sync_step_bounce_ex hb0_1 (p := 148) (j1 := 149) (b := 0) (w1_b := 0) (w2 := 0) (d1 := .right)
      (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have hb1_1 : ∀ T, WindowInv (m0 11) (m1 11) T → SyncEx ⟨f 11, T⟩ ⟨11, T⟩ := sync_base_ex
  have hb1_0 : ∀ T, WindowInv 33551837 33540643 T → SyncEx ⟨139, T⟩ ⟨245, T⟩ :=
    sync_step_bounce_ex hb1_1 (p := 525) (j1 := 9) (b := 1) (w1_b := 1) (w2 := 0) (d1 := .right)
      (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h_split : ∀ T, WindowInv 33553885 33540643 T → SyncEx ⟨139, T⟩ ⟨245, T⟩ :=
    sync_split_ex (by decide) (by decide) (by decide) (by decide) hb0_0 hb1_0
  exact sync_entry_1step_ex h_split (w :=
    0) (d := .right) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_472_1 (T : Tape (Fin 2)) (hInv : Inv 472 T) (hb : T.head = 1) :
    ∃ c₁, SimRel ⟨140, (T.write 1).move .right⟩ c₁ ∧
      Reaches₁ (step reference) ⟨472, T⟩ c₁ ∧
      step candidate ⟨f 472, T⟩ = some ⟨140, (T.write 1).move .right⟩ := by
  have h11_0_5 : ∀ T, WindowInv (m0 20) (m1 20) T → SyncEx ⟨f 20, T⟩ ⟨20, T⟩ := sync_base_ex
  have h11_0_4 : ∀ T, WindowInv 33538399 33308351 T → SyncEx ⟨66, T⟩ ⟨173, T⟩ :=
    sync_step_ex (b := 1) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      h11_0_5
  have h11_0_3 : ∀ T, WindowInv 33546415 33431391 T → SyncEx ⟨45, T⟩ ⟨172, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide)
      h11_0_4
  have h11_0_2 : ∀ T, WindowInv 33550423 33492911 T → SyncEx ⟨46, T⟩ ⟨47, T⟩ :=
    sync_step_ex (b := 1) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide)
      h11_0_3
  have h11_0_1 : ∀ T, WindowInv 33552427 33523671 T → SyncEx ⟨47, T⟩ ⟨46, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      h11_0_2
  have h11_0_0 : ∀ T, WindowInv 33553429 33539051 T → SyncEx ⟨139, T⟩ ⟨361, T⟩ :=
    sync_step_bounce_ex h11_0_1 (p := 44) (j1 := 45) (b := 0) (w1_b := 0) (w2 := 0) (d1 := .right)
      (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h11_1_1 : ∀ T, WindowInv (m0 11) (m1 11) T → SyncEx ⟨f 11, T⟩ ⟨11, T⟩ := sync_base_ex
  have h11_1_0 : ∀ T, WindowInv 33551381 33541099 T → SyncEx ⟨139, T⟩ ⟨361, T⟩ :=
    sync_step_bounce_ex h11_1_1 (p := 525) (j1 := 9) (b := 1) (w1_b := 1) (w2 := 0) (d1 := .right)
      (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  have h10_1_1 : ∀ T, WindowInv (m0 15) (m1 15) T → SyncEx ⟨f 15, T⟩ ⟨15, T⟩ := sync_base_ex
  have h10_1_0 : ∀ T, WindowInv 33550379 33529815 T → SyncEx ⟨140, T⟩ ⟨362, T⟩ :=
    sync_step_bounce_ex h10_1_1 (p := 524) (j1 := 11) (b := 1) (w1_b := 1) (w2 := 0) (d1 :=
      .right) (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h_split11 : ∀ T, WindowInv 33553429 33541099 T → SyncEx ⟨139, T⟩ ⟨361, T⟩ :=
    sync_split_ex (by decide) (by decide) (by decide) (by decide) h11_0_0 h11_1_0
  have h_10_0 : ∀ T, WindowInv 33552427 33527767 T → SyncEx ⟨140, T⟩ ⟨362, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .right) (by decide) (by decide) (by decide) (by decide)
      h_split11
  have h_split10 : ∀ T, WindowInv 33552427 33529815 T → SyncEx ⟨140, T⟩ ⟨362, T⟩ :=
    sync_split_ex (by decide) (by decide) (by decide) (by decide) h_10_0 h10_1_0
  exact sync_entry_1step_ex h_split10 (w :=
    1) (d := .right) (by decide) (by decide) (by decide) T hInv hb

theorem sync_from_251_0 (T : Tape (Fin 2)) (hInv : Inv 251 T) (hb : T.head = 0) :
    ∃ c₁, SimRel ⟨100, (T.write 0).move .right⟩ c₁ ∧
      Reaches₁ (step reference) ⟨251, T⟩ c₁ ∧
      step candidate ⟨f 251, T⟩ = some ⟨100, (T.write 0).move .right⟩ := by
  have h11_0_1 : ∀ T, WindowInv (m0 545) (m1 545) T → SyncEx ⟨f 545, T⟩ ⟨545, T⟩ := sync_base_ex
  have h11_0_0 : ∀ T, WindowInv 33554255 33538225 T → SyncEx ⟨99, T⟩ ⟨249, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .right) (by decide) (by decide) (by decide) (by decide)
      h11_0_1
  have h11_1_4 : ∀ T, WindowInv (m0 19) (m1 19) T → SyncEx ⟨f 19, T⟩ ⟨19, T⟩ := sync_base_ex
  have h11_1_3 : ∀ T, WindowInv 33532543 33445263 T → SyncEx ⟨43, T⟩ ⟨84, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      h11_1_4
  have h11_1_2 : ∀ T, WindowInv 33545535 33497799 T → SyncEx ⟨42, T⟩ ⟨104, T⟩ :=
    sync_step_ex (b := 0) (w := 1) (d := .left) (by decide) (by decide) (by decide) (by decide)
      h11_1_3
  have h11_1_1 : ∀ T, WindowInv 33549983 33526115 T → SyncEx ⟨41, T⟩ ⟨103, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .left) (by decide) (by decide) (by decide) (by decide)
      h11_1_2
  have h11_1_0 : ∀ T, WindowInv 33552207 33540273 T → SyncEx ⟨99, T⟩ ⟨249, T⟩ :=
    sync_step_bounce_ex h11_1_1 (p := 101) (j1 := 102) (b := 1) (w1_b := 1) (w2 := 1) (d1 :=
      .right) (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h10_1_1 : ∀ T, WindowInv (m0 15) (m1 15) T → SyncEx ⟨f 15, T⟩ ⟨15, T⟩ := sync_base_ex
  have h10_1_0 : ∀ T, WindowInv 33552031 33528163 T → SyncEx ⟨100, T⟩ ⟨250, T⟩ :=
    sync_step_bounce_ex h10_1_1 (p := 524) (j1 := 11) (b := 1) (w1_b := 1) (w2 := 0) (d1 :=
      .right) (d2 := .left) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h_split11 : ∀ T, WindowInv 33554255 33540273 T → SyncEx ⟨99, T⟩ ⟨249, T⟩ :=
    sync_split_ex (by decide) (by decide) (by decide) (by decide) h11_0_0 h11_1_0
  have h_10_0 : ∀ T, WindowInv 33554079 33526115 T → SyncEx ⟨100, T⟩ ⟨250, T⟩ :=
    sync_step_ex (b := 0) (w := 0) (d := .right) (by decide) (by decide) (by decide) (by decide)
      h_split11
  have h_split10 : ∀ T, WindowInv 33554079 33528163 T → SyncEx ⟨100, T⟩ ⟨250, T⟩ :=
    sync_split_ex (by decide) (by decide) (by decide) (by decide) h_10_0 h10_1_0
  exact sync_entry_1step_ex h_split10 (w :=
    0) (d := .right) (by decide) (by decide) (by decide) T hInv hb

theorem respects :
    Respects (step candidate) (step reference) SimRel := by
  intro c₂ c₁ hRel
  rcases hRel with (⟨hc2, hc1⟩ | ⟨_ | m, hcd2, hcd1⟩) | ⟨_ | m, hsync⟩
  · subst hc2 hc1
    have hhd : (Tape.mk₁ ([] : List (Fin 2))).head = 0 := rfl
    have hsc : step candidate (init : Cfg 543 2) = some ⟨235, Tape.mk₁ []⟩ := by
      have htr : candTrans 0 0 = some (0, .right, 235) := by decide
      simp [init, step, candTrans_eq, hhd, htr, mk1_nil_move_right]
    have hsr1 : step reference (init : Cfg 744 2) = some ⟨523, Tape.mk₁ []⟩ := by
      have htr : refTrans 0 0 = some (0, .right, 523) := by decide
      simp [init, step, refTrans_eq, hhd, htr, mk1_nil_move_right]
    have hsr2 : step reference ⟨523, Tape.mk₁ []⟩ = some ⟨371, Tape.mk₁ []⟩ := by
      have htr : refTrans 523 0 = some (0, .right, 371) := by decide
      simp [step, refTrans_eq, hhd, htr, mk1_nil_move_right]
    rw [hsc]
    exact ⟨⟨371, Tape.mk₁ []⟩, Or.inr ⟨0, inv_init, rfl⟩, Relation.TransGen.tail
      (Relation.TransGen.single hsr1) hsr2⟩
  · change step candidate c₂ = none at hcd2
    change step reference c₁ = none at hcd1
    rw [hcd2, hcd1]
  · rcases hcd2 with ⟨c₂', hc2s, hcd2'⟩
    rcases hcd1 with ⟨c₁', hc1r, hcd1'⟩
    rw [hc2s]
    exact ⟨c₁', Or.inl (Or.inr ⟨m, hcd2', hcd1'⟩), hc1r⟩
  · rcases hsync with ⟨hInv, hEq⟩
    subst hEq
    obtain ⟨q, T⟩ := c₁
    by_cases h_503_0 : (q.val == 503 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_503_0
      have hq : q = 503 := Fin.ext h_503_0.1
      have h0 : T.head = 0 := Fin.ext h_503_0.2
      subst hq
      obtain ⟨hs_ref, href_cd, hs_cand, hcand_cd⟩ := halt_from_503 T hInv h0
      rw [hs_cand]
      exact ⟨⟨36, (T.write 0).move .right⟩, Or.inl (Or.inr ⟨4, hcand_cd, href_cd⟩),
        Relation.TransGen.single hs_ref⟩
    by_cases h_63_0 : (q.val == 63 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_63_0
      have hq : q = 63 := Fin.ext h_63_0.1
      have hb : T.head = 0 := Fin.ext h_63_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_63_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_203_1 : (q.val == 203 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_203_1
      have hq : q = 203 := Fin.ext h_203_1.1
      have hb : T.head = 1 := Fin.ext h_203_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_203_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_208_0 : (q.val == 208 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_208_0
      have hq : q = 208 := Fin.ext h_208_0.1
      have hb : T.head = 0 := Fin.ext h_208_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_208_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_209_0 : (q.val == 209 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_209_0
      have hq : q = 209 := Fin.ext h_209_0.1
      have hb : T.head = 0 := Fin.ext h_209_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_209_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_212_1 : (q.val == 212 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_212_1
      have hq : q = 212 := Fin.ext h_212_1.1
      have hb : T.head = 1 := Fin.ext h_212_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_212_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_216_0 : (q.val == 216 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_216_0
      have hq : q = 216 := Fin.ext h_216_0.1
      have hb : T.head = 0 := Fin.ext h_216_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_216_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_217_0 : (q.val == 217 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_217_0
      have hq : q = 217 := Fin.ext h_217_0.1
      have hb : T.head = 0 := Fin.ext h_217_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_217_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_224_1 : (q.val == 224 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_224_1
      have hq : q = 224 := Fin.ext h_224_1.1
      have hb : T.head = 1 := Fin.ext h_224_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_224_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_225_1 : (q.val == 225 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_225_1
      have hq : q = 225 := Fin.ext h_225_1.1
      have hb : T.head = 1 := Fin.ext h_225_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_225_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_241_1 : (q.val == 241 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_241_1
      have hq : q = 241 := Fin.ext h_241_1.1
      have hb : T.head = 1 := Fin.ext h_241_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_241_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_244_0 : (q.val == 244 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_244_0
      have hq : q = 244 := Fin.ext h_244_0.1
      have hb : T.head = 0 := Fin.ext h_244_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_244_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_245_0 : (q.val == 245 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_245_0
      have hq : q = 245 := Fin.ext h_245_0.1
      have hb : T.head = 0 := Fin.ext h_245_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_245_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_249_1 : (q.val == 249 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_249_1
      have hq : q = 249 := Fin.ext h_249_1.1
      have hb : T.head = 1 := Fin.ext h_249_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_249_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_251_0 : (q.val == 251 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_251_0
      have hq : q = 251 := Fin.ext h_251_0.1
      have hb : T.head = 0 := Fin.ext h_251_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_251_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_254_0 : (q.val == 254 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_254_0
      have hq : q = 254 := Fin.ext h_254_0.1
      have hb : T.head = 0 := Fin.ext h_254_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_254_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_255_0 : (q.val == 255 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_255_0
      have hq : q = 255 := Fin.ext h_255_0.1
      have hb : T.head = 0 := Fin.ext h_255_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_255_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_258_1 : (q.val == 258 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_258_1
      have hq : q = 258 := Fin.ext h_258_1.1
      have hb : T.head = 1 := Fin.ext h_258_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_258_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_266_1 : (q.val == 266 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_266_1
      have hq : q = 266 := Fin.ext h_266_1.1
      have hb : T.head = 1 := Fin.ext h_266_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_266_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_291_1 : (q.val == 291 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_291_1
      have hq : q = 291 := Fin.ext h_291_1.1
      have hb : T.head = 1 := Fin.ext h_291_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_291_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_294_1 : (q.val == 294 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_294_1
      have hq : q = 294 := Fin.ext h_294_1.1
      have hb : T.head = 1 := Fin.ext h_294_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_294_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_302_1 : (q.val == 302 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_302_1
      have hq : q = 302 := Fin.ext h_302_1.1
      have hb : T.head = 1 := Fin.ext h_302_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_302_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_308_0 : (q.val == 308 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_308_0
      have hq : q = 308 := Fin.ext h_308_0.1
      have hb : T.head = 0 := Fin.ext h_308_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_308_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_309_0 : (q.val == 309 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_309_0
      have hq : q = 309 := Fin.ext h_309_0.1
      have hb : T.head = 0 := Fin.ext h_309_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_309_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_316_1 : (q.val == 316 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_316_1
      have hq : q = 316 := Fin.ext h_316_1.1
      have hb : T.head = 1 := Fin.ext h_316_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_316_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_321_0 : (q.val == 321 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_321_0
      have hq : q = 321 := Fin.ext h_321_0.1
      have hb : T.head = 0 := Fin.ext h_321_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_321_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_332_1 : (q.val == 332 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_332_1
      have hq : q = 332 := Fin.ext h_332_1.1
      have hb : T.head = 1 := Fin.ext h_332_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_332_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_337_0 : (q.val == 337 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_337_0
      have hq : q = 337 := Fin.ext h_337_0.1
      have hb : T.head = 0 := Fin.ext h_337_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_337_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_342_1 : (q.val == 342 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_342_1
      have hq : q = 342 := Fin.ext h_342_1.1
      have hb : T.head = 1 := Fin.ext h_342_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_342_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_350_1 : (q.val == 350 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_350_1
      have hq : q = 350 := Fin.ext h_350_1.1
      have hb : T.head = 1 := Fin.ext h_350_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_350_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_361_0 : (q.val == 361 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_361_0
      have hq : q = 361 := Fin.ext h_361_0.1
      have hb : T.head = 0 := Fin.ext h_361_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_361_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_372_1 : (q.val == 372 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_372_1
      have hq : q = 372 := Fin.ext h_372_1.1
      have hb : T.head = 1 := Fin.ext h_372_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_372_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_376_0 : (q.val == 376 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_376_0
      have hq : q = 376 := Fin.ext h_376_0.1
      have hb : T.head = 0 := Fin.ext h_376_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_376_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_386_0 : (q.val == 386 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_386_0
      have hq : q = 386 := Fin.ext h_386_0.1
      have hb : T.head = 0 := Fin.ext h_386_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_386_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_391_1 : (q.val == 391 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_391_1
      have hq : q = 391 := Fin.ext h_391_1.1
      have hb : T.head = 1 := Fin.ext h_391_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_391_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_403_1 : (q.val == 403 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_403_1
      have hq : q = 403 := Fin.ext h_403_1.1
      have hb : T.head = 1 := Fin.ext h_403_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_403_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_406_0 : (q.val == 406 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_406_0
      have hq : q = 406 := Fin.ext h_406_0.1
      have hb : T.head = 0 := Fin.ext h_406_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_406_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_407_0 : (q.val == 407 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_407_0
      have hq : q = 407 := Fin.ext h_407_0.1
      have hb : T.head = 0 := Fin.ext h_407_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_407_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_416_1 : (q.val == 416 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_416_1
      have hq : q = 416 := Fin.ext h_416_1.1
      have hb : T.head = 1 := Fin.ext h_416_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_416_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_420_0 : (q.val == 420 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_420_0
      have hq : q = 420 := Fin.ext h_420_0.1
      have hb : T.head = 0 := Fin.ext h_420_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_420_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_429_1 : (q.val == 429 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_429_1
      have hq : q = 429 := Fin.ext h_429_1.1
      have hb : T.head = 1 := Fin.ext h_429_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_429_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_445_1 : (q.val == 445 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_445_1
      have hq : q = 445 := Fin.ext h_445_1.1
      have hb : T.head = 1 := Fin.ext h_445_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_445_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_458_0 : (q.val == 458 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_458_0
      have hq : q = 458 := Fin.ext h_458_0.1
      have hb : T.head = 0 := Fin.ext h_458_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_458_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_459_0 : (q.val == 459 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_459_0
      have hq : q = 459 := Fin.ext h_459_0.1
      have hb : T.head = 0 := Fin.ext h_459_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_459_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_463_0 : (q.val == 463 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_463_0
      have hq : q = 463 := Fin.ext h_463_0.1
      have hb : T.head = 0 := Fin.ext h_463_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_463_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_468_1 : (q.val == 468 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_468_1
      have hq : q = 468 := Fin.ext h_468_1.1
      have hb : T.head = 1 := Fin.ext h_468_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_468_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_472_1 : (q.val == 472 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_472_1
      have hq : q = 472 := Fin.ext h_472_1.1
      have hb : T.head = 1 := Fin.ext h_472_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_472_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_487_0 : (q.val == 487 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_487_0
      have hq : q = 487 := Fin.ext h_487_0.1
      have hb : T.head = 0 := Fin.ext h_487_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_487_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_494_0 : (q.val == 494 && T.head.val == 0) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_494_0
      have hq : q = 494 := Fin.ext h_494_0.1
      have hb : T.head = 0 := Fin.ext h_494_0.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_494_0 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_499_1 : (q.val == 499 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_499_1
      have hq : q = 499 := Fin.ext h_499_1.1
      have hb : T.head = 1 := Fin.ext h_499_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_499_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_712_1 : (q.val == 712 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_712_1
      have hq : q = 712 := Fin.ext h_712_1.1
      have hb : T.head = 1 := Fin.ext h_712_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_712_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    by_cases h_713_1 : (q.val == 713 && T.head.val == 1) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at h_713_1
      have hq : q = 713 := Fin.ext h_713_1.1
      have hb : T.head = 1 := Fin.ext h_713_1.2
      subst hq
      obtain ⟨c₁, hrel, hreach, hsc⟩ := sync_from_713_1 T hInv hb
      rw [hsc]
      exact ⟨c₁, hrel, hreach⟩
    have hb_head := inv_head hInv
    have htab := table_valid q T.head
    unfold checkEntry at htab
    have hspec_f : isSpecialNat q.val T.head = false := by
      unfold isSpecialNat
      rw [Bool.eq_false_iff.mpr h_503_0, Bool.eq_false_iff.mpr h_63_0,
        Bool.eq_false_iff.mpr h_203_1, Bool.eq_false_iff.mpr h_208_0,
        Bool.eq_false_iff.mpr h_209_0, Bool.eq_false_iff.mpr h_212_1,
        Bool.eq_false_iff.mpr h_216_0, Bool.eq_false_iff.mpr h_217_0,
        Bool.eq_false_iff.mpr h_224_1, Bool.eq_false_iff.mpr h_225_1,
        Bool.eq_false_iff.mpr h_241_1, Bool.eq_false_iff.mpr h_244_0,
        Bool.eq_false_iff.mpr h_245_0, Bool.eq_false_iff.mpr h_249_1,
        Bool.eq_false_iff.mpr h_251_0, Bool.eq_false_iff.mpr h_254_0,
        Bool.eq_false_iff.mpr h_255_0, Bool.eq_false_iff.mpr h_258_1,
        Bool.eq_false_iff.mpr h_266_1, Bool.eq_false_iff.mpr h_291_1,
        Bool.eq_false_iff.mpr h_294_1, Bool.eq_false_iff.mpr h_302_1,
        Bool.eq_false_iff.mpr h_308_0, Bool.eq_false_iff.mpr h_309_0,
        Bool.eq_false_iff.mpr h_316_1, Bool.eq_false_iff.mpr h_321_0,
        Bool.eq_false_iff.mpr h_332_1, Bool.eq_false_iff.mpr h_337_0,
        Bool.eq_false_iff.mpr h_342_1, Bool.eq_false_iff.mpr h_350_1,
        Bool.eq_false_iff.mpr h_361_0, Bool.eq_false_iff.mpr h_372_1,
        Bool.eq_false_iff.mpr h_376_0, Bool.eq_false_iff.mpr h_386_0,
        Bool.eq_false_iff.mpr h_391_1, Bool.eq_false_iff.mpr h_403_1,
        Bool.eq_false_iff.mpr h_406_0, Bool.eq_false_iff.mpr h_407_0,
        Bool.eq_false_iff.mpr h_416_1, Bool.eq_false_iff.mpr h_420_0,
        Bool.eq_false_iff.mpr h_429_1, Bool.eq_false_iff.mpr h_445_1,
        Bool.eq_false_iff.mpr h_458_0, Bool.eq_false_iff.mpr h_459_0,
        Bool.eq_false_iff.mpr h_463_0, Bool.eq_false_iff.mpr h_468_1,
        Bool.eq_false_iff.mpr h_472_1, Bool.eq_false_iff.mpr h_487_0,
        Bool.eq_false_iff.mpr h_494_0, Bool.eq_false_iff.mpr h_499_1,
        Bool.eq_false_iff.mpr h_712_1, Bool.eq_false_iff.mpr h_713_1]
      rfl
    rw [hspec_f, Bool.false_or, hb_head, Bool.not_true, Bool.false_or] at htab
    rcases hb : isBounce q T.head with _ | _
    · rw [hb] at htab
      rcases h1 : refTrans q T.head with _ | ⟨w, d, q'⟩
      · rw [h1] at htab
        have hcand : candTrans (f q) T.head = none := Option.isNone_iff_eq_none.mp htab
        have hs_cand : step candidate ⟨f q, T⟩ = none := by simp [step, candTrans_eq, hcand]
        have hs_ref : step reference ⟨q, T⟩ = none := by simp [step, refTrans_eq, h1]
        rw [hs_cand, hs_ref]
      · rw [h1, Bool.and_eq_true, beq_iff_eq] at htab
        rcases htab with ⟨hcand, hall⟩
        have hs_cand : step candidate ⟨f q, T⟩ = some ⟨f q', (T.write w).move d⟩ := by
          simp [step, candTrans_eq, hcand]
        have hs_ref : step reference ⟨q, T⟩ = some ⟨q', (T.write w).move d⟩ := by
          simp [step, refTrans_eq, h1]
        rw [hs_cand]
        exact ⟨⟨q', (T.write w).move d⟩, Or.inr ⟨0, checkAllCells_sound hInv w d hall, rfl⟩,
          Relation.TransGen.single hs_ref⟩
    · rw [hb] at htab
      rcases h1 : refTrans q T.head with _ | ⟨w, d, p⟩
      · rw [h1] at htab; cases htab
      · rw [h1] at htab
        dsimp only at htab
        rcases hp0 : refTrans0 p.val with _ | ⟨w0, dp0, j1⟩
        · rw [hp0] at htab; cases htab
        · rcases hp1 : refTrans1 p.val with _ | ⟨w1, dp1, j1'⟩
          · rw [hp0, hp1] at htab; cases htab
          · rw [hp0, hp1] at htab
            simp only [Bool.and_eq_true, beq_iff_eq] at htab
            rcases htab with ⟨⟨⟨⟨⟨hw0, hw1⟩, hdp0⟩, hdp1⟩, hj1⟩, htab⟩
            subst hw0 hw1 hj1 hdp0 hdp1
            rcases hj : (refTrans j1 w) with _ | ⟨w2, d2, q2⟩
            · rw [hj] at htab; cases htab
            · rw [hj, Bool.and_eq_true, beq_iff_eq] at htab
              rcases htab with ⟨hcand, hall⟩
              have hstep_cand : step candidate ⟨f q, T⟩ = some ⟨f q2, (T.write w2).move d2⟩ := by
                simp [step, candTrans_eq, hcand]
              rw [hstep_cand]
              refine ⟨⟨q2, (T.write w2).move d2⟩, Or.inr ⟨0, checkAllCells_sound hInv w2 d2 hall,
                rfl⟩, ?_⟩
              have hs1 : step reference ⟨q, T⟩ = some ⟨p, (T.write w).move d⟩ := by
                simp [step, refTrans_eq, h1]
              have hs2 : step reference ⟨p, (T.write w).move d⟩ = some ⟨j1, T.write w⟩ := by
                rw [ref_pass_step ((T.write w).move d) hp0 hp1, move_opp]
              have hs3 : step reference ⟨j1, T.write w⟩ = some ⟨q2, (T.write w2).move d2⟩ := by
                have hhead_w : (T.write w).head = w := rfl
                have hwrite_w : (T.write w).write w2 = T.write w2 := rfl
                simp [step, refTrans_eq, hhead_w, hj, hwrite_w]
              exact Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hs1)
                hs2) hs3
  · rcases hsync with ⟨c₂', c₁', hc2s, hc1r, hsync'⟩
    rw [hc2s]
    exact ⟨c₁', Or.inr ⟨m, hsync'⟩, hc1r⟩

theorem init_rel : SimRel (init : Cfg 543 2) (init : Cfg 744 2) :=
  Or.inl (Or.inl ⟨rfl, rfl⟩)

theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  (StateTransition.tr_eval_dom respects init_rel).symm

end ConjectureMachines.Riemann543
