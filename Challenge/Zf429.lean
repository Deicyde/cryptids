/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cryptids.Machines
import Mathlib.SetTheory.ZFC.Basic

/-!
# Challenge.Zf429

429-state ZF Turing machine challenge specification.
-/

namespace ConjectureMachines.Zf429

/-- 432 states, 2 symbols,
SHA-256 `cb9ffd320f7360b5e0e49181a6201286b408d1f8c168d61fafc51d1ca8b86702`. -/
def reference : Machine 432 2 := Machine.ofRows [
  [some (1, .right, 1), some (1, .left, 2)],
  [some (0, .left, 0), some (0, .left, 3)],
  [some (1, .left, 0), some (1, .right, 60)],
  [some (1, .left, 1), some (1, .right, 4)],
  [some (0, .right, 3), some (0, .right, 1)],
  [some (1, .left, 92), some (1, .right, 6)],
  [some (0, .right, 5), some (1, .right, 7)],
  [some (0, .right, 60), some (1, .right, 59)],
  [some (0, .right, 9), none],
  [some (1, .right, 9), some (1, .left, 92)],
  [some (0, .right, 12), some (1, .right, 10)],
  [some (0, .right, 13), some (1, .right, 11)],
  [some (1, .left, 45), some (0, .right, 36)],
  [some (1, .right, 41), some (1, .right, 13)],
  [some (0, .right, 10), some (1, .right, 14)],
  [some (0, .right, 11), some (1, .right, 15)],
  [some (0, .right, 14), some (1, .right, 16)],
  [some (0, .right, 15), some (1, .right, 17)],
  [some (0, .right, 34), some (1, .right, 18)],
  [some (0, .right, 35), some (1, .right, 19)],
  [some (0, .right, 16), some (1, .right, 20)],
  [some (0, .right, 17), some (1, .right, 21)],
  [some (0, .right, 20), some (1, .right, 22)],
  [some (0, .right, 21), some (1, .right, 23)],
  [some (0, .right, 22), some (1, .right, 24)],
  [some (0, .right, 23), some (1, .right, 25)],
  [some (0, .right, 24), some (1, .right, 26)],
  [some (0, .right, 25), some (1, .right, 27)],
  [some (0, .right, 26), some (1, .right, 28)],
  [some (0, .right, 27), some (1, .right, 29)],
  [some (0, .right, 28), some (1, .right, 30)],
  [some (0, .right, 29), some (1, .right, 31)],
  [some (0, .right, 30), some (1, .right, 32)],
  [some (0, .right, 31), some (1, .right, 33)],
  [some (0, .right, 32), some (1, .right, 34)],
  [some (0, .right, 33), some (1, .right, 35)],
  [some (0, .left, 12), some (1, .right, 37)],
  [some (0, .right, 38), some (1, .right, 37)],
  [some (0, .left, 39), some (1, .right, 37)],
  [some (1, .left, 40), some (1, .left, 39)],
  [some (0, .left, 43), some (0, .left, 39)],
  [some (0, .left, 43), some (0, .right, 42)],
  [some (1, .right, 41), some (1, .right, 42)],
  [some (0, .left, 44), some (1, .left, 43)],
  [some (0, .left, 89), some (1, .left, 43)],
  [some (0, .left, 46), some (1, .left, 45)],
  [some (0, .left, 90), some (1, .left, 45)],
  [some (0, .right, 47), some (0, .right, 48)],
  [some (0, .left, 5), some (0, .right, 48)],
  [some (1, .right, 8), some (0, .right, 24)],
  [some (1, .right, 8), some (0, .right, 25)],
  [some (1, .right, 8), some (0, .right, 16)],
  [some (1, .right, 8), some (0, .right, 17)],
  [some (1, .right, 8), some (0, .right, 26)],
  [some (1, .right, 8), some (0, .right, 27)],
  [some (1, .right, 8), some (0, .right, 28)],
  [some (1, .right, 8), some (0, .right, 29)],
  [some (1, .right, 8), some (0, .right, 30)],
  [some (1, .right, 8), some (0, .right, 31)],
  [some (1, .right, 8), some (0, .right, 14)],
  [some (1, .right, 8), some (0, .right, 15)],
  [some (1, .right, 8), some (0, .right, 32)],
  [some (1, .right, 8), some (0, .right, 33)],
  [some (1, .right, 8), some (0, .right, 34)],
  [some (1, .right, 8), some (0, .right, 35)],
  [some (1, .right, 8), some (0, .right, 18)],
  [some (1, .right, 8), some (0, .right, 19)],
  [some (1, .right, 8), some (0, .right, 20)],
  [some (1, .right, 8), some (0, .right, 21)],
  [some (1, .right, 8), some (0, .right, 22)],
  [some (1, .right, 8), some (0, .right, 23)],
  [some (0, .left, 86), some (1, .left, 71)],
  [some (0, .left, 71), some (1, .left, 72)],
  [some (0, .left, 85), some (1, .left, 73)],
  [some (0, .left, 73), some (1, .left, 74)],
  [some (0, .left, 74), some (1, .left, 75)],
  [some (0, .left, 75), some (1, .left, 76)],
  [some (0, .left, 76), some (1, .left, 77)],
  [some (0, .left, 72), some (1, .left, 78)],
  [some (0, .left, 78), some (1, .left, 79)],
  [some (0, .left, 79), some (1, .left, 80)],
  [some (0, .left, 80), some (1, .left, 81)],
  [some (0, .left, 81), some (1, .left, 82)],
  [some (0, .left, 82), some (1, .left, 83)],
  [some (0, .left, 83), some (1, .left, 84)],
  [some (0, .left, 84), some (1, .left, 85)],
  [some (0, .right, 86), some (1, .right, 87)],
  [some (0, .right, 5), some (1, .right, 88)],
  [some (0, .right, 126), some (0, .right, 126)],
  [some (1, .right, 47), some (0, .left, 89)],
  [some (0, .left, 89), some (0, .left, 90)],
  [some (0, .left, 90), some (0, .left, 91)],
  [some (0, .left, 92), some (1, .left, 77)],
  [some (0, .left, 93), some (0, .left, 92)],
  [some (0, .left, 94), some (0, .left, 93)],
  [some (0, .left, 95), some (0, .left, 94)],
  [some (0, .right, 328), some (1, .right, 97)],
  [some (0, .right, 333), some (1, .right, 418)],
  [some (0, .right, 99), some (0, .left, 90)],
  [some (0, .right, 49), some (1, .right, 100)],
  [some (0, .right, 101), some (1, .right, 104)],
  [some (0, .right, 49), some (1, .right, 102)],
  [some (0, .right, 103), some (0, .left, 90)],
  [some (0, .right, 50), some (1, .right, 50)],
  [some (0, .right, 105), some (0, .left, 90)],
  [some (0, .right, 50), some (1, .right, 328)],
  [some (0, .right, 98), some (1, .right, 107)],
  [some (0, .right, 391), some (1, .right, 405)],
  [some (0, .right, 98), some (1, .right, 109)],
  [some (0, .right, 395), some (1, .right, 407)],
  [some (0, .right, 49), some (1, .right, 111)],
  [some (0, .right, 421), some (1, .right, 410)],
  [some (0, .right, 113), some (1, .right, 117)],
  [some (0, .right, 63), some (1, .right, 114)],
  [some (0, .right, 115), some (1, .right, 116)],
  [some (0, .right, 65), some (0, .left, 93)],
  [some (0, .right, 415), some (0, .left, 91)],
  [some (0, .right, 65), some (1, .right, 118)],
  [some (0, .right, 420), some (0, .left, 90)],
  [some (0, .right, 112), some (1, .right, 120)],
  [some (0, .right, 388), some (1, .right, 403)],
  [some (0, .right, 112), some (1, .right, 421)],
  [some (0, .right, 123), some (1, .right, 124)],
  [some (0, .right, 59), some (0, .left, 90)],
  [some (0, .right, 382), some (1, .right, 125)],
  [some (0, .right, 401), some (1, .right, 52)],
  [some (0, .right, 122), some (1, .right, 127)],
  [some (0, .right, 381), some (1, .right, 176)],
  [some (0, .right, 405), some (1, .right, 139)],
  [some (0, .right, 277), some (1, .right, 130)],
  [some (0, .right, 288), some (1, .right, 131)],
  [some (0, .right, 362), some (1, .right, 132)],
  [some (0, .right, 315), some (1, .right, 133)],
  [some (0, .right, 320), some (1, .right, 134)],
  [some (0, .right, 316), some (1, .right, 135)],
  [some (0, .right, 360), some (1, .right, 136)],
  [some (0, .right, 317), some (1, .right, 137)],
  [some (0, .right, 289), some (1, .right, 138)],
  [some (0, .right, 319), some (1, .right, 140)],
  [some (0, .right, 310), some (1, .right, 150)],
  [some (0, .right, 280), some (1, .right, 141)],
  [some (0, .right, 359), some (1, .right, 142)],
  [some (0, .right, 317), some (1, .right, 143)],
  [some (0, .right, 360), some (1, .right, 144)],
  [some (0, .right, 289), some (1, .right, 145)],
  [some (0, .right, 318), some (1, .right, 146)],
  [some (0, .right, 280), some (1, .right, 147)],
  [some (0, .right, 301), some (1, .right, 148)],
  [some (0, .right, 343), some (1, .right, 149)],
  [some (0, .right, 301), some (1, .right, 151)],
  [some (0, .right, 407), some (1, .right, 161)],
  [some (0, .right, 290), some (1, .right, 152)],
  [some (0, .right, 358), some (1, .right, 153)],
  [some (0, .right, 316), some (1, .right, 154)],
  [some (0, .right, 366), some (1, .right, 155)],
  [some (0, .right, 302), some (1, .right, 156)],
  [some (0, .right, 429), some (1, .right, 157)],
  [some (0, .right, 302), some (1, .right, 158)],
  [some (0, .right, 316), some (1, .right, 159)],
  [some (0, .right, 291), some (1, .right, 160)],
  [some (0, .right, 318), some (1, .right, 162)],
  [some (0, .right, 343), some (1, .right, 170)],
  [some (0, .right, 319), some (1, .right, 163)],
  [some (0, .right, 318), some (1, .right, 164)],
  [some (0, .right, 344), some (1, .right, 165)],
  [some (0, .right, 67), some (1, .right, 166)],
  [some (0, .right, 167), none],
  [some (0, .right, 67), some (1, .right, 168)],
  [some (0, .right, 169), some (0, .left, 90)],
  [some (0, .right, 68), some (1, .right, 68)],
  [some (0, .right, 108), some (1, .right, 171)],
  [some (0, .right, 106), some (1, .right, 172)],
  [some (0, .right, 341), some (1, .right, 173)],
  [some (0, .right, 312), some (1, .right, 174)],
  [some (0, .right, 427), some (1, .right, 175)],
  [some (0, .right, 394), some (1, .right, 177)],
  [some (0, .right, 385), some (1, .right, 187)],
  [some (0, .right, 405), some (1, .right, 178)],
  [some (0, .right, 119), some (1, .right, 179)],
  [some (0, .right, 344), some (1, .right, 180)],
  [some (0, .right, 108), some (1, .right, 181)],
  [some (0, .right, 296), some (1, .right, 182)],
  [some (0, .right, 306), some (1, .right, 183)],
  [some (0, .right, 429), some (1, .right, 184)],
  [some (0, .right, 339), some (1, .right, 185)],
  [some (0, .right, 311), some (1, .right, 186)],
  [some (0, .right, 337), some (1, .right, 188)],
  [some (0, .right, 391), some (1, .right, 198)],
  [some (0, .right, 311), some (1, .right, 189)],
  [some (0, .right, 295), some (1, .right, 190)],
  [some (0, .right, 431), some (1, .right, 191)],
  [some (0, .right, 312), some (1, .right, 192)],
  [some (0, .right, 337), some (1, .right, 193)],
  [some (0, .right, 294), some (1, .right, 194)],
  [some (0, .right, 431), some (1, .right, 195)],
  [some (0, .right, 339), some (1, .right, 196)],
  [some (0, .right, 287), some (1, .right, 197)],
  [some (0, .right, 311), some (1, .right, 199)],
  [some (0, .right, 395), some (1, .right, 209)],
  [some (0, .right, 364), some (1, .right, 200)],
  [some (0, .right, 321), some (1, .right, 201)],
  [some (0, .right, 364), some (1, .right, 202)],
  [some (0, .right, 296), some (1, .right, 203)],
  [some (0, .right, 429), some (1, .right, 204)],
  [some (0, .right, 429), some (1, .right, 205)],
  [some (0, .right, 272), some (1, .right, 206)],
  [some (0, .right, 264), some (1, .right, 207)],
  [some (0, .right, 339), some (1, .right, 208)],
  [some (0, .right, 368), some (1, .right, 210)],
  [some (0, .right, 310), some (1, .right, 220)],
  [some (0, .right, 313), some (1, .right, 211)],
  [some (0, .right, 297), some (1, .right, 212)],
  [some (0, .right, 341), some (1, .right, 213)],
  [some (0, .right, 297), some (1, .right, 214)],
  [some (0, .right, 313), some (1, .right, 215)],
  [some (0, .right, 362), some (1, .right, 216)],
  [some (0, .right, 386), some (1, .right, 217)],
  [some (0, .right, 403), some (1, .right, 218)],
  [some (0, .right, 298), some (1, .right, 219)],
  [some (0, .right, 392), some (1, .right, 221)],
  [some (0, .right, 399), some (1, .right, 231)],
  [some (0, .right, 405), some (1, .right, 222)],
  [some (0, .right, 298), some (1, .right, 223)],
  [some (0, .right, 272), some (1, .right, 224)],
  [some (0, .right, 286), some (1, .right, 225)],
  [some (0, .right, 315), some (1, .right, 226)],
  [some (0, .right, 339), some (1, .right, 227)],
  [some (0, .right, 286), some (1, .right, 228)],
  [some (0, .right, 368), some (1, .right, 229)],
  [some (0, .right, 370), some (1, .right, 230)],
  [some (0, .right, 283), some (1, .right, 232)],
  [some (0, .right, 310), some (1, .right, 242)],
  [some (0, .right, 368), some (1, .right, 233)],
  [some (0, .right, 324), some (1, .right, 234)],
  [some (0, .right, 322), some (1, .right, 235)],
  [some (0, .right, 264), some (1, .right, 236)],
  [some (0, .right, 366), some (1, .right, 237)],
  [some (0, .right, 341), some (1, .right, 238)],
  [some (0, .right, 339), some (1, .right, 239)],
  [some (0, .right, 366), some (1, .right, 240)],
  [some (0, .right, 305), some (1, .right, 241)],
  [some (0, .right, 359), some (1, .right, 243)],
  [some (0, .right, 403), some (1, .right, 253)],
  [some (0, .right, 314), some (1, .right, 244)],
  [some (0, .right, 366), some (1, .right, 245)],
  [some (0, .right, 288), some (1, .right, 246)],
  [some (0, .right, 304), some (1, .right, 247)],
  [some (0, .right, 314), some (1, .right, 248)],
  [some (0, .right, 291), some (1, .right, 249)],
  [some (0, .right, 343), some (1, .right, 250)],
  [some (0, .right, 300), some (1, .right, 251)],
  [some (0, .right, 344), some (1, .right, 252)],
  [some (0, .right, 360), some (1, .right, 254)],
  [some (0, .right, 310), some (1, .right, 128)],
  [some (0, .right, 316), some (1, .right, 255)],
  [some (0, .right, 308), some (1, .right, 256)],
  [some (0, .right, 359), some (1, .right, 257)],
  [some (0, .right, 300), some (1, .right, 258)],
  [some (0, .right, 315), some (1, .right, 259)],
  [some (0, .right, 364), some (1, .right, 260)],
  [some (0, .right, 358), some (1, .right, 261)],
  [some (0, .right, 290), some (1, .right, 262)],
  [some (0, .right, 277), some (1, .right, 263)],
  [some (0, .right, 429), some (1, .right, 129)],
  [some (0, .right, 429), some (1, .right, 265)],
  [some (0, .right, 283), some (1, .right, 266)],
  [some (0, .right, 366), some (1, .right, 267)],
  [some (0, .right, 324), some (1, .right, 268)],
  [some (0, .right, 366), some (1, .right, 269)],
  [some (0, .right, 287), some (1, .right, 270)],
  [some (0, .right, 368), some (1, .right, 271)],
  [some (0, .right, 341), some (1, .right, 337)],
  [some (0, .right, 306), some (1, .right, 273)],
  [some (0, .right, 325), some (1, .right, 274)],
  [some (0, .right, 364), some (1, .right, 275)],
  [some (0, .right, 339), some (1, .right, 276)],
  [some (0, .right, 296), some (1, .right, 364)],
  [some (0, .right, 360), some (1, .right, 278)],
  [some (0, .right, 307), some (1, .right, 279)],
  [some (0, .right, 308), some (1, .right, 318)],
  [some (0, .right, 288), some (1, .right, 281)],
  [some (0, .right, 315), some (1, .right, 282)],
  [some (0, .right, 344), some (1, .right, 358)],
  [some (0, .right, 306), some (1, .right, 284)],
  [some (0, .right, 368), some (1, .right, 285)],
  [some (0, .right, 337), some (1, .right, 341)],
  [some (0, .right, 294), some (1, .right, 339)],
  [some (0, .right, 295), some (1, .right, 339)],
  [some (0, .right, 304), some (1, .right, 429)],
  [some (0, .right, 366), some (1, .right, 307)],
  [some (0, .right, 359), some (1, .right, 304)],
  [some (0, .right, 366), some (1, .right, 292)],
  [some (0, .right, 429), some (1, .right, 293)],
  [some (0, .right, 362), some (1, .right, 364)],
  [some (0, .right, 320), some (1, .right, 326)],
  [some (0, .right, 305), some (1, .right, 337)],
  [some (0, .right, 337), some (1, .right, 325)],
  [some (0, .right, 321), some (1, .right, 366)],
  [some (0, .right, 397), some (1, .right, 299)],
  [some (0, .right, 403), some (1, .right, 121)],
  [some (0, .right, 358), some (1, .right, 322)],
  [some (0, .right, 343), some (1, .right, 323)],
  [some (0, .right, 358), some (1, .right, 303)],
  [some (0, .right, 343), some (1, .right, 368)],
  [some (0, .right, 359), some (1, .right, 323)],
  [some (0, .right, 429), some (1, .right, 320)],
  [some (0, .right, 344), some (1, .right, 321)],
  [some (0, .right, 360), some (1, .right, 327)],
  [some (0, .right, 358), some (1, .right, 309)],
  [some (0, .right, 337), some (1, .right, 364)],
  [some (0, .right, 352), some (1, .right, 416)],
  [some (0, .right, 341), some (1, .right, 429)],
  [some (0, .right, 337), some (1, .right, 429)],
  [some (0, .right, 364), some (1, .right, 429)],
  [some (0, .right, 359), some (1, .right, 343)],
  [some (0, .right, 364), some (1, .right, 370)],
  [some (0, .right, 358), some (1, .right, 359)],
  [some (0, .right, 360), some (1, .right, 359)],
  [some (0, .right, 362), some (1, .right, 370)],
  [some (0, .right, 429), some (1, .right, 364)],
  [some (0, .right, 429), some (1, .right, 344)],
  [some (0, .right, 337), some (1, .right, 339)],
  [some (0, .right, 368), some (1, .right, 429)],
  [some (0, .right, 358), some (1, .right, 366)],
  [some (0, .right, 339), some (1, .right, 341)],
  [some (0, .right, 341), some (1, .right, 364)],
  [some (0, .right, 337), some (1, .right, 337)],
  [some (0, .right, 343), some (1, .right, 366)],
  [some (0, .right, 353), some (1, .right, 419)],
  [some (0, .right, 422), some (1, .right, 330)],
  [some (0, .right, 69), some (1, .right, 331)],
  [some (0, .right, 332), some (0, .left, 94)],
  [some (0, .right, 62), some (1, .right, 428)],
  [some (0, .right, 412), some (1, .right, 334)],
  [some (0, .right, 67), some (1, .right, 335)],
  [some (0, .right, 336), some (0, .left, 94)],
  [some (0, .right, 64), some (1, .right, 425)],
  [some (0, .right, 343), some (1, .right, 338)],
  [some (0, .right, 387), some (1, .right, 403)],
  [some (0, .right, 343), some (1, .right, 340)],
  [some (0, .right, 393), some (1, .right, 405)],
  [some (0, .right, 343), some (1, .right, 342)],
  [some (0, .right, 396), some (1, .right, 407)],
  [some (0, .right, 329), some (1, .right, 411)],
  [some (0, .right, 425), some (1, .right, 345)],
  [some (0, .right, 354), some (1, .right, 346)],
  [some (0, .right, 419), some (1, .right, 347)],
  [some (0, .right, 110), some (1, .right, 398)],
  [some (0, .right, 63), some (0, .left, 94)],
  [some (0, .right, 62), some (1, .right, 350)],
  [some (0, .right, 348), some (1, .right, 351)],
  [some (0, .right, 409), some (0, .left, 95)],
  [some (0, .right, 59), some (1, .right, 349)],
  [some (0, .right, 69), some (1, .right, 349)],
  [some (0, .right, 69), some (1, .right, 355)],
  [some (0, .right, 68), some (1, .right, 356)],
  [some (0, .right, 348), some (1, .right, 357)],
  [some (0, .right, 427), some (0, .left, 95)],
  [some (0, .right, 343), some (1, .right, 68)],
  [some (0, .right, 358), some (1, .right, 68)],
  [some (0, .right, 359), some (1, .right, 68)],
  [some (0, .right, 360), some (1, .right, 68)],
  [some (0, .right, 431), some (1, .right, 363)],
  [some (0, .right, 429), some (1, .right, 431)],
  [some (0, .right, 96), some (1, .right, 365)],
  [some (0, .right, 361), some (1, .right, 96)],
  [some (0, .right, 96), some (1, .right, 367)],
  [some (0, .right, 358), some (1, .right, 96)],
  [some (0, .right, 96), some (1, .right, 369)],
  [some (0, .right, 343), some (1, .right, 96)],
  [some (0, .right, 431), some (1, .right, 371)],
  [some (0, .right, 364), some (1, .right, 431)],
  [some (0, .right, 64), some (0, .left, 93)],
  [some (0, .right, 374), some (0, .left, 93)],
  [some (0, .right, 62), some (1, .right, 64)],
  [some (0, .right, 68), some (0, .left, 93)],
  [some (0, .right, 377), some (0, .left, 93)],
  [some (0, .right, 68), some (1, .right, 62)],
  [some (0, .right, 70), some (0, .left, 93)],
  [some (0, .right, 380), some (0, .left, 93)],
  [some (0, .right, 62), some (1, .right, 66)],
  [some (0, .right, 49), some (0, .left, 92)],
  [some (0, .right, 51), some (1, .right, 383)],
  [some (0, .right, 384), some (0, .left, 93)],
  [some (0, .right, 62), some (1, .right, 60)],
  [some (0, .right, 53), some (0, .left, 92)],
  [some (0, .right, 53), some (1, .right, 373)],
  [some (0, .right, 53), some (1, .right, 376)],
  [some (0, .right, 53), some (1, .right, 389)],
  [some (0, .right, 390), some (0, .left, 93)],
  [some (0, .right, 62), some (1, .right, 68)],
  [some (0, .right, 55), some (0, .left, 92)],
  [some (0, .right, 55), some (1, .right, 373)],
  [some (0, .right, 55), some (1, .right, 376)],
  [some (0, .right, 55), some (1, .right, 379)],
  [some (0, .right, 57), some (0, .left, 92)],
  [some (0, .right, 57), some (1, .right, 376)],
  [some (0, .right, 57), some (1, .right, 379)],
  [some (0, .right, 61), some (0, .left, 92)],
  [some (0, .right, 61), some (1, .right, 400)],
  [some (0, .right, 50), some (0, .left, 93)],
  [some (0, .right, 61), some (1, .right, 402)],
  [some (0, .right, 52), some (0, .left, 93)],
  [some (0, .right, 61), some (1, .right, 404)],
  [some (0, .right, 54), some (0, .left, 93)],
  [some (0, .right, 61), some (1, .right, 406)],
  [some (0, .right, 56), some (0, .left, 93)],
  [some (0, .right, 61), some (1, .right, 408)],
  [some (0, .right, 58), some (0, .left, 93)],
  [some (0, .right, 61), some (1, .right, 372)],
  [some (0, .right, 61), some (1, .right, 375)],
  [some (0, .right, 61), some (1, .right, 378)],
  [some (0, .right, 61), some (1, .right, 413)],
  [some (0, .right, 414), some (0, .left, 93)],
  [some (0, .right, 68), some (1, .right, 64)],
  [some (0, .right, 63), some (0, .left, 92)],
  [some (0, .right, 63), some (1, .right, 417)],
  [some (0, .right, 60), some (0, .left, 93)],
  [some (0, .right, 63), some (1, .right, 375)],
  [some (0, .right, 63), some (1, .right, 378)],
  [some (0, .right, 65), some (0, .left, 92)],
  [some (0, .right, 67), some (0, .left, 92)],
  [some (0, .right, 67), some (1, .right, 423)],
  [some (0, .right, 424), some (0, .left, 93)],
  [some (0, .right, 70), some (1, .right, 62)],
  [some (0, .right, 67), some (1, .right, 426)],
  [some (0, .right, 62), some (0, .left, 93)],
  [some (0, .right, 67), some (1, .right, 372)],
  [some (0, .right, 69), some (1, .right, 375)],
  [some (0, .right, 96), some (1, .right, 430)],
  [some (0, .right, 359), some (1, .right, 96)],
  [some (0, .right, 360), some (1, .right, 96)]]

/-- 429 states, 2 symbols,
SHA-256 `041919e91a6a5cb2afee60ecdf97975a57811c0c8e0cff52c771d66501f7f730`. -/
def candidate : Machine 429 2 := Machine.ofRows [
  [some (1, .right, 1), some (1, .left, 2)],
  [some (0, .left, 0), some (0, .left, 3)],
  [some (1, .left, 0), some (1, .right, 59)],
  [some (1, .left, 1), some (1, .right, 4)],
  [some (0, .right, 3), some (0, .right, 1)],
  [some (1, .left, 90), some (1, .right, 6)],
  [some (0, .right, 5), some (1, .right, 7)],
  [some (0, .right, 59), some (1, .right, 58)],
  [some (0, .right, 9), none],
  [some (1, .right, 9), some (1, .left, 90)],
  [some (0, .right, 12), some (1, .right, 10)],
  [some (0, .right, 13), some (1, .right, 11)],
  [some (1, .left, 44), some (0, .right, 36)],
  [some (1, .right, 41), some (1, .right, 13)],
  [some (0, .right, 10), some (1, .right, 14)],
  [some (0, .right, 11), some (1, .right, 15)],
  [some (0, .right, 14), some (1, .right, 16)],
  [some (0, .right, 15), some (1, .right, 17)],
  [some (0, .right, 34), some (1, .right, 18)],
  [some (0, .right, 35), some (1, .right, 19)],
  [some (0, .right, 16), some (1, .right, 20)],
  [some (0, .right, 17), some (1, .right, 21)],
  [some (0, .right, 20), some (1, .right, 22)],
  [some (0, .right, 21), some (1, .right, 23)],
  [some (0, .right, 22), some (1, .right, 24)],
  [some (0, .right, 23), some (1, .right, 25)],
  [some (0, .right, 24), some (1, .right, 26)],
  [some (0, .right, 25), some (1, .right, 27)],
  [some (0, .right, 26), some (1, .right, 28)],
  [some (0, .right, 27), some (1, .right, 29)],
  [some (0, .right, 28), some (1, .right, 30)],
  [some (0, .right, 29), some (1, .right, 31)],
  [some (0, .right, 30), some (1, .right, 32)],
  [some (0, .right, 31), some (1, .right, 33)],
  [some (0, .right, 32), some (1, .right, 34)],
  [some (0, .right, 33), some (1, .right, 35)],
  [some (0, .left, 12), some (1, .right, 37)],
  [some (0, .right, 38), some (1, .right, 37)],
  [some (0, .left, 39), some (1, .right, 37)],
  [some (1, .left, 40), some (1, .left, 39)],
  [some (0, .left, 42), some (0, .left, 39)],
  [some (0, .left, 42), some (0, .right, 13)],
  [some (0, .left, 43), some (1, .left, 42)],
  [some (0, .left, 88), some (1, .left, 42)],
  [some (0, .left, 45), some (1, .left, 44)],
  [some (0, .left, 89), some (1, .left, 44)],
  [some (0, .right, 46), some (0, .right, 47)],
  [some (0, .left, 5), some (0, .right, 47)],
  [some (1, .right, 8), some (0, .right, 24)],
  [some (1, .right, 8), some (0, .right, 25)],
  [some (1, .right, 8), some (0, .right, 16)],
  [some (1, .right, 8), some (0, .right, 17)],
  [some (1, .right, 8), some (0, .right, 26)],
  [some (1, .right, 8), some (0, .right, 27)],
  [some (1, .right, 8), some (0, .right, 28)],
  [some (1, .right, 8), some (0, .right, 29)],
  [some (1, .right, 8), some (0, .right, 30)],
  [some (1, .right, 8), some (0, .right, 31)],
  [some (1, .right, 8), some (0, .right, 14)],
  [some (1, .right, 8), some (0, .right, 15)],
  [some (1, .right, 8), some (0, .right, 32)],
  [some (1, .right, 8), some (0, .right, 33)],
  [some (1, .right, 8), some (0, .right, 34)],
  [some (1, .right, 8), some (0, .right, 35)],
  [some (1, .right, 8), some (0, .right, 18)],
  [some (1, .right, 8), some (0, .right, 19)],
  [some (1, .right, 8), some (0, .right, 20)],
  [some (1, .right, 8), some (0, .right, 21)],
  [some (1, .right, 8), some (0, .right, 22)],
  [some (1, .right, 8), some (0, .right, 23)],
  [some (0, .left, 85), some (1, .left, 70)],
  [some (0, .left, 70), some (1, .left, 71)],
  [some (0, .left, 84), some (1, .left, 72)],
  [some (0, .left, 72), some (1, .left, 73)],
  [some (0, .left, 73), some (1, .left, 74)],
  [some (0, .left, 74), some (1, .left, 75)],
  [some (0, .left, 75), some (1, .left, 76)],
  [some (0, .left, 71), some (1, .left, 77)],
  [some (0, .left, 77), some (1, .left, 78)],
  [some (0, .left, 78), some (1, .left, 79)],
  [some (0, .left, 79), some (1, .left, 80)],
  [some (0, .left, 80), some (1, .left, 81)],
  [some (0, .left, 81), some (1, .left, 82)],
  [some (0, .left, 82), some (1, .left, 83)],
  [some (0, .left, 83), some (1, .left, 84)],
  [some (0, .right, 85), some (1, .right, 86)],
  [some (0, .right, 5), some (1, .right, 87)],
  [some (0, .right, 123), some (0, .right, 123)],
  [some (1, .right, 46), some (0, .left, 88)],
  [some (0, .left, 88), some (0, .left, 89)],
  [some (0, .left, 90), some (1, .left, 76)],
  [some (0, .left, 417), some (0, .left, 92)],
  [some (0, .left, 369), some (0, .left, 45)],
  [some (0, .right, 325), some (1, .right, 94)],
  [some (0, .right, 330), some (1, .right, 415)],
  [some (0, .right, 96), some (0, .left, 89)],
  [some (0, .right, 48), some (1, .right, 97)],
  [some (0, .right, 98), some (1, .right, 101)],
  [some (0, .right, 48), some (1, .right, 99)],
  [some (0, .right, 100), some (0, .left, 89)],
  [some (0, .right, 49), some (1, .right, 49)],
  [some (0, .right, 102), some (0, .left, 89)],
  [some (0, .right, 49), some (1, .right, 325)],
  [some (0, .right, 95), some (1, .right, 104)],
  [some (0, .right, 388), some (1, .right, 402)],
  [some (0, .right, 95), some (1, .right, 106)],
  [some (0, .right, 392), some (1, .right, 404)],
  [some (0, .right, 48), some (1, .right, 108)],
  [some (0, .right, 418), some (1, .right, 407)],
  [some (0, .right, 110), some (1, .right, 114)],
  [some (0, .right, 62), some (1, .right, 111)],
  [some (0, .right, 112), some (1, .right, 113)],
  [some (0, .right, 64), some (0, .left, 91)],
  [some (0, .right, 412), some (0, .left, 91)],
  [some (0, .right, 64), some (1, .right, 115)],
  [some (0, .right, 417), some (0, .left, 89)],
  [some (0, .right, 109), some (1, .right, 117)],
  [some (0, .right, 385), some (1, .right, 400)],
  [some (0, .right, 109), some (1, .right, 418)],
  [some (0, .right, 120), some (1, .right, 121)],
  [some (0, .right, 58), some (0, .left, 89)],
  [some (0, .right, 379), some (1, .right, 122)],
  [some (0, .right, 398), some (1, .right, 51)],
  [some (0, .right, 119), some (1, .right, 124)],
  [some (0, .right, 378), some (1, .right, 173)],
  [some (0, .right, 402), some (1, .right, 136)],
  [some (0, .right, 274), some (1, .right, 127)],
  [some (0, .right, 285), some (1, .right, 128)],
  [some (0, .right, 359), some (1, .right, 129)],
  [some (0, .right, 312), some (1, .right, 130)],
  [some (0, .right, 317), some (1, .right, 131)],
  [some (0, .right, 313), some (1, .right, 132)],
  [some (0, .right, 357), some (1, .right, 133)],
  [some (0, .right, 314), some (1, .right, 134)],
  [some (0, .right, 286), some (1, .right, 135)],
  [some (0, .right, 316), some (1, .right, 137)],
  [some (0, .right, 307), some (1, .right, 147)],
  [some (0, .right, 277), some (1, .right, 138)],
  [some (0, .right, 356), some (1, .right, 139)],
  [some (0, .right, 314), some (1, .right, 140)],
  [some (0, .right, 357), some (1, .right, 141)],
  [some (0, .right, 286), some (1, .right, 142)],
  [some (0, .right, 315), some (1, .right, 143)],
  [some (0, .right, 277), some (1, .right, 144)],
  [some (0, .right, 298), some (1, .right, 145)],
  [some (0, .right, 340), some (1, .right, 146)],
  [some (0, .right, 298), some (1, .right, 148)],
  [some (0, .right, 404), some (1, .right, 158)],
  [some (0, .right, 287), some (1, .right, 149)],
  [some (0, .right, 355), some (1, .right, 150)],
  [some (0, .right, 313), some (1, .right, 151)],
  [some (0, .right, 363), some (1, .right, 152)],
  [some (0, .right, 299), some (1, .right, 153)],
  [some (0, .right, 426), some (1, .right, 154)],
  [some (0, .right, 299), some (1, .right, 155)],
  [some (0, .right, 313), some (1, .right, 156)],
  [some (0, .right, 288), some (1, .right, 157)],
  [some (0, .right, 315), some (1, .right, 159)],
  [some (0, .right, 340), some (1, .right, 167)],
  [some (0, .right, 316), some (1, .right, 160)],
  [some (0, .right, 315), some (1, .right, 161)],
  [some (0, .right, 341), some (1, .right, 162)],
  [some (0, .right, 66), some (1, .right, 163)],
  [some (0, .right, 164), none],
  [some (0, .right, 66), some (1, .right, 165)],
  [some (0, .right, 166), some (0, .left, 89)],
  [some (0, .right, 67), some (1, .right, 67)],
  [some (0, .right, 105), some (1, .right, 168)],
  [some (0, .right, 103), some (1, .right, 169)],
  [some (0, .right, 338), some (1, .right, 170)],
  [some (0, .right, 309), some (1, .right, 171)],
  [some (0, .right, 424), some (1, .right, 172)],
  [some (0, .right, 391), some (1, .right, 174)],
  [some (0, .right, 382), some (1, .right, 184)],
  [some (0, .right, 402), some (1, .right, 175)],
  [some (0, .right, 116), some (1, .right, 176)],
  [some (0, .right, 341), some (1, .right, 177)],
  [some (0, .right, 105), some (1, .right, 178)],
  [some (0, .right, 293), some (1, .right, 179)],
  [some (0, .right, 303), some (1, .right, 180)],
  [some (0, .right, 426), some (1, .right, 181)],
  [some (0, .right, 336), some (1, .right, 182)],
  [some (0, .right, 308), some (1, .right, 183)],
  [some (0, .right, 334), some (1, .right, 185)],
  [some (0, .right, 388), some (1, .right, 195)],
  [some (0, .right, 308), some (1, .right, 186)],
  [some (0, .right, 292), some (1, .right, 187)],
  [some (0, .right, 428), some (1, .right, 188)],
  [some (0, .right, 309), some (1, .right, 189)],
  [some (0, .right, 334), some (1, .right, 190)],
  [some (0, .right, 291), some (1, .right, 191)],
  [some (0, .right, 428), some (1, .right, 192)],
  [some (0, .right, 336), some (1, .right, 193)],
  [some (0, .right, 284), some (1, .right, 194)],
  [some (0, .right, 308), some (1, .right, 196)],
  [some (0, .right, 392), some (1, .right, 206)],
  [some (0, .right, 361), some (1, .right, 197)],
  [some (0, .right, 318), some (1, .right, 198)],
  [some (0, .right, 361), some (1, .right, 199)],
  [some (0, .right, 293), some (1, .right, 200)],
  [some (0, .right, 426), some (1, .right, 201)],
  [some (0, .right, 426), some (1, .right, 202)],
  [some (0, .right, 269), some (1, .right, 203)],
  [some (0, .right, 261), some (1, .right, 204)],
  [some (0, .right, 336), some (1, .right, 205)],
  [some (0, .right, 365), some (1, .right, 207)],
  [some (0, .right, 307), some (1, .right, 217)],
  [some (0, .right, 310), some (1, .right, 208)],
  [some (0, .right, 294), some (1, .right, 209)],
  [some (0, .right, 338), some (1, .right, 210)],
  [some (0, .right, 294), some (1, .right, 211)],
  [some (0, .right, 310), some (1, .right, 212)],
  [some (0, .right, 359), some (1, .right, 213)],
  [some (0, .right, 383), some (1, .right, 214)],
  [some (0, .right, 400), some (1, .right, 215)],
  [some (0, .right, 295), some (1, .right, 216)],
  [some (0, .right, 389), some (1, .right, 218)],
  [some (0, .right, 396), some (1, .right, 228)],
  [some (0, .right, 402), some (1, .right, 219)],
  [some (0, .right, 295), some (1, .right, 220)],
  [some (0, .right, 269), some (1, .right, 221)],
  [some (0, .right, 283), some (1, .right, 222)],
  [some (0, .right, 312), some (1, .right, 223)],
  [some (0, .right, 336), some (1, .right, 224)],
  [some (0, .right, 283), some (1, .right, 225)],
  [some (0, .right, 365), some (1, .right, 226)],
  [some (0, .right, 367), some (1, .right, 227)],
  [some (0, .right, 280), some (1, .right, 229)],
  [some (0, .right, 307), some (1, .right, 239)],
  [some (0, .right, 365), some (1, .right, 230)],
  [some (0, .right, 321), some (1, .right, 231)],
  [some (0, .right, 319), some (1, .right, 232)],
  [some (0, .right, 261), some (1, .right, 233)],
  [some (0, .right, 363), some (1, .right, 234)],
  [some (0, .right, 338), some (1, .right, 235)],
  [some (0, .right, 336), some (1, .right, 236)],
  [some (0, .right, 363), some (1, .right, 237)],
  [some (0, .right, 302), some (1, .right, 238)],
  [some (0, .right, 356), some (1, .right, 240)],
  [some (0, .right, 400), some (1, .right, 250)],
  [some (0, .right, 311), some (1, .right, 241)],
  [some (0, .right, 363), some (1, .right, 242)],
  [some (0, .right, 285), some (1, .right, 243)],
  [some (0, .right, 301), some (1, .right, 244)],
  [some (0, .right, 311), some (1, .right, 245)],
  [some (0, .right, 288), some (1, .right, 246)],
  [some (0, .right, 340), some (1, .right, 247)],
  [some (0, .right, 297), some (1, .right, 248)],
  [some (0, .right, 341), some (1, .right, 249)],
  [some (0, .right, 357), some (1, .right, 251)],
  [some (0, .right, 307), some (1, .right, 125)],
  [some (0, .right, 313), some (1, .right, 252)],
  [some (0, .right, 305), some (1, .right, 253)],
  [some (0, .right, 356), some (1, .right, 254)],
  [some (0, .right, 297), some (1, .right, 255)],
  [some (0, .right, 312), some (1, .right, 256)],
  [some (0, .right, 361), some (1, .right, 257)],
  [some (0, .right, 355), some (1, .right, 258)],
  [some (0, .right, 287), some (1, .right, 259)],
  [some (0, .right, 274), some (1, .right, 260)],
  [some (0, .right, 426), some (1, .right, 126)],
  [some (0, .right, 426), some (1, .right, 262)],
  [some (0, .right, 280), some (1, .right, 263)],
  [some (0, .right, 363), some (1, .right, 264)],
  [some (0, .right, 321), some (1, .right, 265)],
  [some (0, .right, 363), some (1, .right, 266)],
  [some (0, .right, 284), some (1, .right, 267)],
  [some (0, .right, 365), some (1, .right, 268)],
  [some (0, .right, 338), some (1, .right, 334)],
  [some (0, .right, 303), some (1, .right, 270)],
  [some (0, .right, 322), some (1, .right, 271)],
  [some (0, .right, 361), some (1, .right, 272)],
  [some (0, .right, 336), some (1, .right, 273)],
  [some (0, .right, 293), some (1, .right, 361)],
  [some (0, .right, 357), some (1, .right, 275)],
  [some (0, .right, 304), some (1, .right, 276)],
  [some (0, .right, 305), some (1, .right, 315)],
  [some (0, .right, 285), some (1, .right, 278)],
  [some (0, .right, 312), some (1, .right, 279)],
  [some (0, .right, 341), some (1, .right, 355)],
  [some (0, .right, 303), some (1, .right, 281)],
  [some (0, .right, 365), some (1, .right, 282)],
  [some (0, .right, 334), some (1, .right, 338)],
  [some (0, .right, 291), some (1, .right, 336)],
  [some (0, .right, 292), some (1, .right, 336)],
  [some (0, .right, 301), some (1, .right, 426)],
  [some (0, .right, 363), some (1, .right, 304)],
  [some (0, .right, 356), some (1, .right, 301)],
  [some (0, .right, 363), some (1, .right, 289)],
  [some (0, .right, 426), some (1, .right, 290)],
  [some (0, .right, 359), some (1, .right, 361)],
  [some (0, .right, 317), some (1, .right, 323)],
  [some (0, .right, 302), some (1, .right, 334)],
  [some (0, .right, 334), some (1, .right, 322)],
  [some (0, .right, 318), some (1, .right, 363)],
  [some (0, .right, 394), some (1, .right, 296)],
  [some (0, .right, 400), some (1, .right, 118)],
  [some (0, .right, 355), some (1, .right, 319)],
  [some (0, .right, 340), some (1, .right, 320)],
  [some (0, .right, 355), some (1, .right, 300)],
  [some (0, .right, 340), some (1, .right, 365)],
  [some (0, .right, 356), some (1, .right, 320)],
  [some (0, .right, 426), some (1, .right, 317)],
  [some (0, .right, 341), some (1, .right, 318)],
  [some (0, .right, 357), some (1, .right, 324)],
  [some (0, .right, 355), some (1, .right, 306)],
  [some (0, .right, 334), some (1, .right, 361)],
  [some (0, .right, 349), some (1, .right, 413)],
  [some (0, .right, 338), some (1, .right, 426)],
  [some (0, .right, 334), some (1, .right, 426)],
  [some (0, .right, 361), some (1, .right, 426)],
  [some (0, .right, 356), some (1, .right, 340)],
  [some (0, .right, 361), some (1, .right, 367)],
  [some (0, .right, 355), some (1, .right, 356)],
  [some (0, .right, 357), some (1, .right, 356)],
  [some (0, .right, 359), some (1, .right, 367)],
  [some (0, .right, 426), some (1, .right, 361)],
  [some (0, .right, 426), some (1, .right, 341)],
  [some (0, .right, 334), some (1, .right, 336)],
  [some (0, .right, 365), some (1, .right, 426)],
  [some (0, .right, 355), some (1, .right, 363)],
  [some (0, .right, 336), some (1, .right, 338)],
  [some (0, .right, 338), some (1, .right, 361)],
  [some (0, .right, 334), some (1, .right, 334)],
  [some (0, .right, 340), some (1, .right, 363)],
  [some (0, .right, 350), some (1, .right, 416)],
  [some (0, .right, 419), some (1, .right, 327)],
  [some (0, .right, 68), some (1, .right, 328)],
  [some (0, .right, 329), some (0, .left, 369)],
  [some (0, .right, 61), some (1, .right, 425)],
  [some (0, .right, 409), some (1, .right, 331)],
  [some (0, .right, 66), some (1, .right, 332)],
  [some (0, .right, 333), some (0, .left, 369)],
  [some (0, .right, 63), some (1, .right, 422)],
  [some (0, .right, 340), some (1, .right, 335)],
  [some (0, .right, 384), some (1, .right, 400)],
  [some (0, .right, 340), some (1, .right, 337)],
  [some (0, .right, 390), some (1, .right, 402)],
  [some (0, .right, 340), some (1, .right, 339)],
  [some (0, .right, 393), some (1, .right, 404)],
  [some (0, .right, 326), some (1, .right, 408)],
  [some (0, .right, 422), some (1, .right, 342)],
  [some (0, .right, 351), some (1, .right, 343)],
  [some (0, .right, 416), some (1, .right, 344)],
  [some (0, .right, 107), some (1, .right, 395)],
  [some (0, .right, 62), some (0, .left, 92)],
  [some (0, .right, 61), some (1, .right, 347)],
  [some (0, .right, 345), some (1, .right, 348)],
  [some (0, .right, 406), some (0, .left, 328)],
  [some (0, .right, 58), some (1, .right, 346)],
  [some (0, .right, 68), some (1, .right, 346)],
  [some (0, .right, 68), some (1, .right, 352)],
  [some (0, .right, 67), some (1, .right, 353)],
  [some (0, .right, 345), some (1, .right, 354)],
  [some (0, .right, 424), some (0, .left, 328)],
  [some (0, .right, 340), some (1, .right, 67)],
  [some (0, .right, 355), some (1, .right, 67)],
  [some (0, .right, 356), some (1, .right, 67)],
  [some (0, .right, 357), some (1, .right, 67)],
  [some (0, .right, 428), some (1, .right, 360)],
  [some (0, .right, 426), some (1, .right, 428)],
  [some (0, .right, 93), some (1, .right, 362)],
  [some (0, .right, 358), some (1, .right, 93)],
  [some (0, .right, 93), some (1, .right, 364)],
  [some (0, .right, 355), some (1, .right, 93)],
  [some (0, .right, 93), some (1, .right, 366)],
  [some (0, .right, 340), some (1, .right, 93)],
  [some (0, .right, 428), some (1, .right, 368)],
  [some (0, .right, 361), some (1, .right, 428)],
  [some (0, .right, 63), some (0, .left, 417)],
  [some (0, .right, 371), some (0, .left, 417)],
  [some (0, .right, 61), some (1, .right, 63)],
  [some (0, .right, 67), some (0, .left, 417)],
  [some (0, .right, 374), some (0, .left, 417)],
  [some (0, .right, 67), some (1, .right, 61)],
  [some (0, .right, 69), some (0, .left, 417)],
  [some (0, .right, 377), some (0, .left, 417)],
  [some (0, .right, 61), some (1, .right, 65)],
  [some (0, .right, 48), some (0, .left, 90)],
  [some (0, .right, 50), some (1, .right, 380)],
  [some (0, .right, 381), some (0, .left, 417)],
  [some (0, .right, 61), some (1, .right, 59)],
  [some (0, .right, 52), some (0, .left, 90)],
  [some (0, .right, 52), some (1, .right, 370)],
  [some (0, .right, 52), some (1, .right, 373)],
  [some (0, .right, 52), some (1, .right, 386)],
  [some (0, .right, 387), some (0, .left, 417)],
  [some (0, .right, 61), some (1, .right, 67)],
  [some (0, .right, 54), some (0, .left, 90)],
  [some (0, .right, 54), some (1, .right, 370)],
  [some (0, .right, 54), some (1, .right, 373)],
  [some (0, .right, 54), some (1, .right, 376)],
  [some (0, .right, 56), some (0, .left, 90)],
  [some (0, .right, 56), some (1, .right, 373)],
  [some (0, .right, 56), some (1, .right, 376)],
  [some (0, .right, 60), some (0, .left, 90)],
  [some (0, .right, 60), some (1, .right, 397)],
  [some (0, .right, 49), some (0, .left, 417)],
  [some (0, .right, 60), some (1, .right, 399)],
  [some (0, .right, 51), some (0, .left, 417)],
  [some (0, .right, 60), some (1, .right, 401)],
  [some (0, .right, 53), some (0, .left, 417)],
  [some (0, .right, 60), some (1, .right, 403)],
  [some (0, .right, 55), some (0, .left, 417)],
  [some (0, .right, 60), some (1, .right, 405)],
  [some (0, .right, 57), some (0, .left, 417)],
  [some (0, .right, 60), some (1, .right, 369)],
  [some (0, .right, 60), some (1, .right, 372)],
  [some (0, .right, 60), some (1, .right, 375)],
  [some (0, .right, 60), some (1, .right, 410)],
  [some (0, .right, 411), some (0, .left, 417)],
  [some (0, .right, 67), some (1, .right, 63)],
  [some (0, .right, 62), some (0, .left, 90)],
  [some (0, .right, 62), some (1, .right, 414)],
  [some (0, .right, 59), some (0, .left, 417)],
  [some (0, .right, 62), some (1, .right, 372)],
  [some (0, .right, 62), some (1, .right, 375)],
  [some (0, .right, 64), some (0, .left, 90)],
  [some (0, .right, 66), some (0, .left, 90)],
  [some (0, .right, 66), some (1, .right, 420)],
  [some (0, .right, 421), some (0, .left, 417)],
  [some (0, .right, 69), some (1, .right, 61)],
  [some (0, .right, 66), some (1, .right, 423)],
  [some (0, .right, 61), some (0, .left, 417)],
  [some (0, .right, 66), some (1, .right, 369)],
  [some (0, .right, 68), some (1, .right, 372)],
  [some (0, .right, 93), some (1, .right, 427)],
  [some (0, .right, 356), some (1, .right, 93)],
  [some (0, .right, 357), some (1, .right, 93)]]

theorem candidate_equivalent : Halts candidate ↔ Halts reference := by
  sorry

end ConjectureMachines.Zf429

namespace ConjectureMachines.Semantics.Zf

/-- The Cantor pairing function $\operatorname{cantorPair}(x, y) = x + \frac{(x+y)(x+y+1)}{2}$
computed by `builtin_pair` in `zf2.nql`. -/
def cantorPair (x y : ℕ) : ℕ :=
  x + (x + y) * (x + y + 1) / 2

/-- Gödel number of the atomic equality formula $v_x = v_y$ (`weq` in `zf2.nql`). -/
def zfEq (x y : ℕ) : ℕ :=
  cantorPair (cantorPair x y) 0

/-- Gödel number of the atomic membership formula $v_x \in v_y$ (`wel` in `zf2.nql`). -/
def zfMem (x y : ℕ) : ℕ :=
  cantorPair (cantorPair x y) 1

/-- Gödel number of the implication formula $\varphi \to \psi$ (`wim` in `zf2.nql`). -/
def zfImp (φ ψ : ℕ) : ℕ :=
  cantorPair (cantorPair φ ψ) 2

/-- Gödel number of the negation formula $\neg \varphi$ (`wn` in `zf2.nql`). -/
def zfNot (φ : ℕ) : ℕ :=
  cantorPair φ 3

/-- Gödel number of the universal formula $\forall v_x\, \varphi$ (`wal` in `zf2.nql`). -/
def zfAll (x φ : ℕ) : ℕ :=
  cantorPair (cantorPair x φ) 4

/-- Gödel number of the existential abbreviation
$\exists v_x\, \varphi \equiv \neg \forall v_x \neg \varphi$ (`wex` in `zf2.nql`). -/
def zfEx (x φ : ℕ) : ℕ :=
  zfNot (zfAll x (zfNot φ))

/-- Gödel number of the conjunction abbreviation
$\varphi \land \psi \equiv \neg (\varphi \to \neg \psi)$ (`wa` in `zf2.nql`). -/
def zfAnd (φ ψ : ℕ) : ℕ :=
  zfNot (zfImp φ (zfNot ψ))

/-- Axiom scheme `B1` (`axiomcode = 3`):
$(\varphi \to \psi) \to ((\psi \to \chi) \to (\varphi \to \chi))$. -/
def axB1 (φ ψ χ : ℕ) : ℕ :=
  zfImp (zfImp φ ψ) (zfImp (zfImp ψ χ) (zfImp φ χ))

/-- Axiom scheme `B2` (`axiomcode = 4`): $(\neg \varphi \to \varphi) \to \varphi$. -/
def axB2 (φ : ℕ) : ℕ :=
  zfImp (zfImp (zfNot φ) φ) φ

/-- Axiom scheme `B3` (`axiomcode = 5`): $\varphi \to (\neg \varphi \to \psi)$. -/
def axB3 (φ ψ : ℕ) : ℕ :=
  zfImp φ (zfImp (zfNot φ) ψ)

/-- Axiom scheme `B4` (`axiomcode = 6`):
$\forall v_x (\varphi \to \psi) \to (\forall v_x \varphi \to \forall v_x \psi)$. -/
def axB4 (x φ ψ : ℕ) : ℕ :=
  zfImp (zfAll x (zfImp φ ψ)) (zfImp (zfAll x φ) (zfAll x ψ))

/-- Axiom scheme `B6a` (`axiomcode = 7`, subject to $x \ne z \land z \ne y$):
$(v_x = v_y \to \forall v_z\, v_x = v_y) \land (v_x \in v_y \to \forall v_z\, v_x \in v_y)$. -/
def axB6a (x y z : ℕ) : ℕ :=
  zfAnd (zfImp (zfEq x y) (zfAll z (zfEq x y))) (zfImp (zfMem x y) (zfAll z (zfMem x y)))

/-- Axiom scheme `B6b` (`axiomcode = 8`):
$\forall v_x \forall v_y \varphi \to \forall v_y \forall v_x \varphi$. -/
def axB6b (x y φ : ℕ) : ℕ :=
  zfImp (zfAll x (zfAll y φ)) (zfAll y (zfAll x φ))

/-- Axiom scheme `B6c` (`axiomcode = 9`): $\exists v_x \forall v_x \varphi \to \varphi$. -/
def axB6c (x φ : ℕ) : ℕ :=
  zfImp (zfEx x (zfAll x φ)) φ

/-- Axiom scheme `B7` (`axiomcode = 10`): $\exists v_x\, v_x = v_y$. -/
def axB7 (x y : ℕ) : ℕ :=
  zfEx x (zfEq x y)

/-- Axiom scheme `B8a` (`axiomcode = 11`): $v_x = v_y \to (v_x = v_z \to v_y = v_z)$. -/
def axB8a (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfEq x z) (zfEq y z))

/-- Axiom scheme `B8b` (`axiomcode = 12`): $v_x = v_y \to (v_x \in v_z \to v_y \in v_z)$. -/
def axB8b (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfMem x z) (zfMem y z))

/-- Axiom scheme `B8c` (`axiomcode = 13`): $v_x = v_y \to (v_z \in v_x \to v_z \in v_y)$. -/
def axB8c (x y z : ℕ) : ℕ :=
  zfImp (zfEq x y) (zfImp (zfMem z x) (zfMem z y))

/-- Axiom of Extensionality (`EXT`, `axiomcode = 14`):
$\forall v_2 ((v_2 \in v_0 \to v_2 \in v_1) \land (v_2 \in v_1 \to v_2 \in v_0)) \to v_0 = v_1$. -/
def axExt : ℕ :=
  zfImp
    (zfAll 2 (zfAnd (zfImp (zfMem 2 0) (zfMem 2 1)) (zfImp (zfMem 2 1) (zfMem 2 0))))
    (zfEq 0 1)

/-- Helper formula $\exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi)$ used in `axRep`. -/
def axRepRhs (φ : ℕ) : ℕ :=
  zfEx 3 (zfAnd (zfMem 3 0) (zfAll 1 φ))

/-- Axiom scheme of Replacement (`REP`, `axiomcode = 15`):
$\forall v_3 \exists v_1 \forall v_2 (\forall v_1 \varphi \to v_2 = v_1) \to
  \exists v_1 \forall v_2 ((v_2 \in v_1 \to \exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi))
    \land (\exists v_3 (v_3 \in v_0 \land \forall v_1 \varphi) \to v_2 \in v_1))$. -/
def axRep (φ : ℕ) : ℕ :=
  zfImp
    (zfAll 3 (zfEx 1 (zfAll 2 (zfImp (zfAll 1 φ) (zfEq 2 1)))))
    (zfEx 1 (zfAll 2
      (zfAnd (zfImp (zfMem 2 1) (axRepRhs φ)) (zfImp (axRepRhs φ) (zfMem 2 1)))))

/-- Axiom of Power Set (`POW`, `axiomcode = 16`):
$\exists v_1 \forall v_2 (\forall v_3 (v_3 \in v_2 \to v_3 \in v_0) \to v_2 \in v_1)$. -/
def axPow : ℕ :=
  zfEx 1 (zfAll 2 (zfImp (zfAll 3 (zfImp (zfMem 3 2) (zfMem 3 0))) (zfMem 2 1)))

/-- Axiom of Union (`UNI`, `axiomcode = 17`):
$\exists v_1 \forall v_2 (\exists v_3 (v_2 \in v_3 \land v_3 \in v_0) \to v_2 \in v_1)$. -/
def axUni : ℕ :=
  zfEx 1 (zfAll 2 (zfImp (zfEx 3 (zfAnd (zfMem 2 3) (zfMem 3 0))) (zfMem 2 1)))

/-- Helper singleton-characterization formula
$\forall v_1 ((v_1 \in v_2 \to v_1 = v_0) \land (v_1 = v_0 \to v_1 \in v_2))$ used in `axInf`. -/
def axInfSingleton : ℕ :=
  zfAll 1 (zfAnd (zfImp (zfMem 1 2) (zfEq 1 0)) (zfImp (zfEq 1 0) (zfMem 1 2)))

/-- Axiom of Infinity (`INF`, `axiomcode > 17`):
$\exists v_1 (v_0 \in v_1 \land \forall v_0 (v_0 \in v_1 \to
  \exists v_2 (v_2 \in v_1 \land \forall v_1 (v_1 \in v_2 \leftrightarrow v_1 = v_0))))$. -/
def axInf : ℕ :=
  zfEx 1
    (zfAnd (zfMem 0 1)
      (zfAll 0 (zfImp (zfMem 0 1) (zfEx 2 (zfAnd (zfMem 2 1) axInfSingleton)))))

/-- The inductive provability predicate `ZFProvable φ` of O'Rear's `zf2.nql` Hilbert system
for Zermelo–Fraenkel set theory. -/
inductive ZFProvable : ℕ → Prop where
  | moot : ZFProvable (zfEq 0 0)
  | mp {φ ψ : ℕ} : ZFProvable φ → ZFProvable (zfImp φ ψ) → ZFProvable ψ
  | gen (x : ℕ) {φ : ℕ} : ZFProvable φ → ZFProvable (zfAll x φ)
  | b1 (φ ψ χ : ℕ) : ZFProvable (axB1 φ ψ χ)
  | b2 (φ : ℕ) : ZFProvable (axB2 φ)
  | b3 (φ ψ : ℕ) : ZFProvable (axB3 φ ψ)
  | b4 (x φ ψ : ℕ) : ZFProvable (axB4 x φ ψ)
  | b6a (x y z : ℕ) (hxz : x ≠ z) (hzy : z ≠ y) : ZFProvable (axB6a x y z)
  | b6b (x y φ : ℕ) : ZFProvable (axB6b x y φ)
  | b6c (x φ : ℕ) : ZFProvable (axB6c x φ)
  | b7 (x y : ℕ) : ZFProvable (axB7 x y)
  | b8a (x y z : ℕ) : ZFProvable (axB8a x y z)
  | b8b (x y z : ℕ) : ZFProvable (axB8b x y z)
  | b8c (x y z : ℕ) : ZFProvable (axB8c x y z)
  | ext : ZFProvable axExt
  | rep (φ : ℕ) : ZFProvable (axRep φ)
  | pow : ZFProvable axPow
  | uni : ZFProvable axUni
  | inf : ZFProvable axInf

/-- ZF set theory is inconsistent if the contradiction formula $v_0 \in v_0$ (`zfMem 0 0 = 1`)
is provable in `ZFProvable`. -/
def ZFInconsistent : Prop :=
  ZFProvable (zfMem 0 0)

/-- Well-formed formulas of first-order set theory with variables indexed by `ℕ`. -/
inductive ZFFormula : Type where
  | eq (x y : ℕ) : ZFFormula
  | mem (x y : ℕ) : ZFFormula
  | imp (φ ψ : ZFFormula) : ZFFormula
  | not (φ : ZFFormula) : ZFFormula
  | all (x : ℕ) (φ : ZFFormula) : ZFFormula
  deriving DecidableEq, Repr

namespace ZFFormula

/-- Existential quantification abbreviation
$\exists v_x\, \varphi \equiv \neg \forall v_x \neg \varphi$. -/
def ex (x : ℕ) (φ : ZFFormula) : ZFFormula :=
  .not (.all x (.not φ))

/-- Conjunction abbreviation $\varphi \land \psi \equiv \neg (\varphi \to \neg \psi)$. -/
def and (φ ψ : ZFFormula) : ZFFormula :=
  .not (.imp φ (.not ψ))

/-- The Gödel number of a `ZFFormula`, matching `zf2.nql`. -/
def code : ZFFormula → ℕ
  | .eq x y => zfEq x y
  | .mem x y => zfMem x y
  | .imp φ ψ => zfImp φ.code ψ.code
  | .not φ => zfNot φ.code
  | .all x φ => zfAll x φ.code

/-- Tarski satisfaction of a `ZFFormula` in Mathlib's cumulative hierarchy `ZFSet.{u}`
under a variable assignment `v : ℕ → ZFSet.{u}`. -/
def Holds (v : ℕ → ZFSet.{u}) : ZFFormula → Prop
  | .eq x y => v x = v y
  | .mem x y => v x ∈ v y
  | .imp φ ψ => φ.Holds v → ψ.Holds v
  | .not φ => ¬ φ.Holds v
  | .all x φ => ∀ s : ZFSet.{u}, φ.Holds (Function.update v x s)

end ZFFormula

/-- Soundness of the `ZFProvable` Hilbert system with respect to Mathlib's `ZFSet.{0}`:
any provable well-formed formula holds under every variable assignment `v : ℕ → ZFSet.{0}`. -/
theorem zfProvable_sound_zfSet (φ : ZFFormula) (h : ZFProvable φ.code)
    (v : ℕ → ZFSet.{0}) : φ.Holds v := by
  sorry

/-- Relative consistency of `ZFProvable` from Mathlib's `ZFSet.{0}` model of ZFC:
`ZFInconsistent` is false assuming `zfProvable_sound_zfSet`. -/
theorem not_zfInconsistent : ¬ ZFInconsistent := by
  sorry

/-- Provability predicate of the exact 20-clause Hilbert system implemented by Andrew Wade's
`zf_432_wade.tm` (`zf2.py` prior to commit `10fcf152b3`). -/
inductive WadeZFProvable : ℕ → Prop where
  | moot : WadeZFProvable (zfEq 0 0)
  | mp {φ ψ : ℕ} : WadeZFProvable φ → WadeZFProvable (zfImp φ ψ) → WadeZFProvable ψ
  | gen (x : ℕ) {φ : ℕ} : WadeZFProvable φ → WadeZFProvable (zfAll x φ)
  | b1 (φ ψ χ : ℕ) : WadeZFProvable (axB1 φ ψ χ)
  | b2 (φ : ℕ) : WadeZFProvable (axB2 φ)
  | b3 (φ ψ : ℕ) : WadeZFProvable (axB3 φ ψ)
  | b4 (x φ ψ : ℕ) : WadeZFProvable (axB4 x φ ψ)
  | b6a_wade (x y z : ℕ) (hxz : x ≠ z) (hy : y ≠ 0) : WadeZFProvable (axB6a x y z)
  | b6b (x y φ : ℕ) : WadeZFProvable (axB6b x y φ)
  | b6c (x φ : ℕ) : WadeZFProvable (axB6c x φ)
  | b7 (x y : ℕ) : WadeZFProvable (axB7 x y)
  | b8a_zero (x y : ℕ) : WadeZFProvable (axB8a x y 0)
  | b8b (x y z : ℕ) : WadeZFProvable (axB8b x y z)
  | b8c_zero (x y : ℕ) : WadeZFProvable (axB8c x y 0)
  | ext : WadeZFProvable axExt
  | rep (φ : ℕ) : WadeZFProvable (axRep φ)
  | pow : WadeZFProvable axPow
  | uni : WadeZFProvable axUni
  | inf : WadeZFProvable axInf

/-- Inconsistency of the `WadeZFProvable` Hilbert system: $v_0 \in v_0$ (`zfMem 0 0 = 1`) is
provable. -/
def WadeZFInconsistent : Prop :=
  WadeZFProvable (zfMem 0 0)

/-- The 432-state baseline machine `zf_432` (`ConjectureMachines.Zf429.reference`) halts on the
blank tape if and only if `WadeZFProvable` proves `v_0 ∈ v_0` (`WadeZFInconsistent`). -/
theorem halts_reference_iff_wadeZFInconsistent :
    Halts ConjectureMachines.Zf429.reference ↔ WadeZFInconsistent := by
  sorry

/-- The 429-state reduced machine `zf_429` (`ConjectureMachines.Zf429.candidate`) halts on the
blank tape if and only if `WadeZFProvable` proves `v_0 ∈ v_0` (`WadeZFInconsistent`). -/
theorem halts_candidate_429_iff_wadeZFInconsistent :
    Halts ConjectureMachines.Zf429.candidate ↔ WadeZFInconsistent := by
  sorry

end ConjectureMachines.Semantics.Zf

