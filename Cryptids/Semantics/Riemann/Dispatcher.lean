/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann.Gadgets

/-!
# Layer 2: BDD Dispatcher & Abstract Register Machine Step for `riemann_744`

This module formalizes the binary decision diagram (BDD) instruction dispatcher
(`State 0 → 523 → …`) and jump/noop return chains (`States 36..183, 524..532, 9..29, 12, 13 → 0`)
of the 744-state Turing machine `reference` (`riemann_744`), connecting the Turing machine
configuration `entryCfgR`
to the 16-register abstract machine program `program : ℕ → Instr`.
-/

@[expose] public section

namespace ConjectureMachines.Riemann543.Semantics

open Turing StateTransition
open ConjectureMachines.Riemann543

abbrev refM : Machine 744 2 := Machines.riemann744

/-!
## 1. Multi-Step Execution and Canonical Tape Configurations
-/

export ConjectureMachines.Riemann543.Layer1
  (nSteps pcBits encodeReg encodeRegs regsTape entryCfg postPcCfg regIncrState regDecrState)

open ConjectureMachines.Riemann543.Layer1
  (nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq nSteps_reaches nSteps_reaches₁
   nSteps_eval_dom nSteps_of_halt mem_eval_iff_nSteps Tape.mkL)

/-- Canonical configuration at State `0` (`!ENTRY`) with arbitrary right register tape `R`:
the head is on the blank `0` immediately to the left of `pcBits 11 pc ++ [0, 0]`. -/
def entryCfgR (pc : ℕ) (R : ListBlank (Fin 2)) : Cfg 744 2 :=
  ⟨0, ⟨0, default, ListBlank.append (pcBits 11 pc ++ [0, 0]) R⟩⟩

theorem entryCfgR_eq_mkL (pc : ℕ) (R : ListBlank (Fin 2)) :
    entryCfgR pc R = ⟨0, Tape.mkL default (ListBlank.append (pcBits 11 pc ++ [0, 0]) R)⟩ := rfl

theorem entryCfgR_eq_mk' (pc : ℕ) (R : ListBlank (Fin 2)) :
    entryCfgR pc R = ⟨0, Tape.mk' default (ListBlank.append (0 :: pcBits 11 pc ++ [0, 0]) R)⟩ := by
  simp [entryCfgR, Tape.mk']

/-- Configuration at State `523` (`dispatchroot`, 1 step after `entryCfgR pc R`), where the head is
on the MSB (`bit 10`) of `pcBits 11 pc`. -/
def dispatchRootCfgR (pc : ℕ) (R : ListBlank (Fin 2)) : Cfg 744 2 :=
  ⟨523, Tape.mk' default (ListBlank.append (pcBits 11 pc ++ [0, 0]) R)⟩

/-- Configuration immediately after the 11-bit PC scan (at step 12 from `entryCfgR pc R`),
where the head is on the first `0` of the `[0, 0]` fence in leaf state `q`. -/
def postPcCfgR (q : Fin 744) (pc : ℕ) (R : ListBlank (Fin 2)) : Cfg 744 2 :=
  ⟨q, Tape.mk' (ListBlank.append (pcBits 11 pc).reverse default) (R.cons 0 |>.cons 0)⟩

/-!
## 2. Symbolic Bounded-Window Evaluator
-/

/-- A symbolic window state `(q, L, hd, R_pre)` representing the configuration
`⟨q, ⟨hd, ListBlank.append L default, ListBlank.append R_pre R⟩⟩` independently of `R`. -/
structure WinState where
  q : Fin 744
  L : List (Fin 2)
  hd : Fin 2
  R_pre : List (Fin 2)
  deriving DecidableEq, Repr

/-- Realization of a symbolic `WinState` as a concrete `Cfg 744 2` for an arbitrary tail `R`. -/
def winCfg (s : WinState) (R : ListBlank (Fin 2)) : Cfg 744 2 :=
  ⟨s.q, ⟨s.hd, ListBlank.append s.L default, ListBlank.append R_pre R⟩⟩
where
  R_pre := s.R_pre

/-- One symbolic step of `refM` inside the bounded window (returning `none` if the machine
halts or would step right past `R_pre`). -/
def winStep (s : WinState) : Option WinState :=
  match refTrans s.q s.hd with
  | none => none
  | some (w, .left, q') =>
    match s.L with
    | [] => some ⟨q', [], 0, w :: s.R_pre⟩
    | a :: L' => some ⟨q', L', a, w :: s.R_pre⟩
  | some (w, .right, q') =>
    match s.R_pre with
    | [] => none
    | a :: R_pre' => some ⟨q', w :: s.L, a, R_pre'⟩

/-- `n` symbolic steps of `winStep`. -/
def winNSteps : ℕ → WinState → Option WinState
  | 0, s => some s
  | n + 1, s => (winStep s).bind (winNSteps n)

/-- Symbolic execution until returning to State `0` (`!ENTRY`), bounded by `fuel` steps. -/
def winRunToEntry : ℕ → WinState → Option WinState
  | 0, _ => none
  | fuel + 1, s =>
    match winStep s with
    | none => none
    | some s' => if s'.q == 0 then some s' else winRunToEntry fuel s'

@[simp]
theorem default_head_fin2 : (default : ListBlank (Fin 2)).head = 0 := rfl

@[simp]
theorem default_tail_fin2 : (default : ListBlank (Fin 2)).tail = default := rfl

theorem winStep_sound {s s' : WinState} (h : winStep s = some s') (R : ListBlank (Fin 2)) :
    step refM (winCfg s R) = some (winCfg s' R) := by
  unfold winStep at h
  rcases htr : refTrans s.q s.hd with _ | ⟨w, d, q'⟩
  · rw [htr] at h; cases h
  · rw [htr] at h
    cases d with
    | left =>
      cases hL : s.L with
      | nil =>
        rw [hL] at h
        injection h with h'
        subst h'
        simp [winCfg, winCfg.R_pre, step, refTrans_eq, htr, hL, Tape.write, Tape.move]
      | cons a L' =>
        rw [hL] at h
        injection h with h'
        subst h'
        simp [winCfg, winCfg.R_pre, step, refTrans_eq, htr, hL, Tape.write, Tape.move]
    | right =>
      cases hR : s.R_pre with
      | nil =>
        rw [hR] at h; cases h
      | cons a R_pre' =>
        rw [hR] at h
        injection h with h'
        subst h'
        simp [winCfg, winCfg.R_pre, step, refTrans_eq, htr, hR, Tape.write, Tape.move]

theorem winNSteps_sound {n : ℕ} {s s' : WinState} (h : winNSteps n s = some s')
    (R : ListBlank (Fin 2)) :
    nSteps refM n (winCfg s R) = some (winCfg s' R) := by
  induction n generalizing s with
  | zero =>
    injection h with h'
    subst h'
    rfl
  | succ n ih =>
    unfold winNSteps at h
    rcases hs : winStep s with _ | s₁
    · rw [hs] at h; cases h
    · rw [hs, Option.bind_some] at h
      rw [nSteps_succ, winStep_sound hs R, Option.bind_some]
      exact ih h

theorem winRunToEntry_sound {fuel : ℕ} {s s' : WinState}
    (h : winRunToEntry fuel s = some s') (R : ListBlank (Fin 2)) :
    ∃ n, 1 ≤ n ∧ nSteps refM n (winCfg s R) = some (winCfg s' R) := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    unfold winRunToEntry at h
    rcases hs : winStep s with _ | s₁
    · rw [hs] at h; cases h
    · rw [hs] at h
      dsimp only at h
      split at h
      · injection h with h'
        subst h'
        exact ⟨1, le_refl 1, Layer1.step_one (winStep_sound hs R)⟩
      · obtain ⟨n, hn, hsteps⟩ := ih h
        refine ⟨n + 1, by omega, ?_⟩
        rw [nSteps_succ, winStep_sound hs R, Option.bind_some]
        exact hsteps

theorem winStep_halt {s : WinState} (h : (refTrans s.q s.hd).isNone = true)
    (R : ListBlank (Fin 2)) :
    step refM (winCfg s R) = none := by
  have hnone : refTrans s.q s.hd = none := Option.isNone_iff_eq_none.mp h
  simp [winCfg, step, refTrans_eq, hnone]

/-- Initial symbolic window state for `entryCfgR pc R`. -/
def initWin (pc : ℕ) : WinState :=
  ⟨0, [], 0, pcBits 11 pc ++ [0, 0]⟩

/-- Target symbolic window state after 12 steps for `postPcCfgR q pc R`. -/
def postPcWin (q : Fin 744) (pc : ℕ) : WinState :=
  ⟨q, (pcBits 11 pc).reverse ++ [0], 0, [0]⟩

@[simp]
theorem winCfg_initWin (pc : ℕ) (R : ListBlank (Fin 2)) :
    winCfg (initWin pc) R = entryCfgR pc R := rfl

@[simp]
theorem winCfg_postPcWin (q : Fin 744) (pc : ℕ) (R : ListBlank (Fin 2)) :
    winCfg (postPcWin q pc) R = postPcCfgR q pc R := by
  simp [winCfg, winCfg.R_pre, postPcWin, postPcCfgR, Tape.mk']

theorem step_entryCfgR (pc : ℕ) (R : ListBlank (Fin 2)) :
    step refM (entryCfgR pc R) = some (dispatchRootCfgR pc R) := by
  have htr : refTrans 0 0 = some (0, .right, 523) := by decide
  simp [entryCfgR, dispatchRootCfgR, step, refTrans_eq, htr, Tape.write, Tape.move, Tape.mk']

/-!
## 3. Abstract Register Machine Instructions and Program Table
-/

/-- The 5 primitive instruction types of the `riemann_744` register machine. -/
inductive Instr where
  | initReg
  | incr (k : Fin 16)
  | decr (k : Fin 16)
  | jump (target : ℕ)
  | halt
  deriving DecidableEq, Repr

/-- The decoded instruction table of `refM` (`riemann_744`) for all 11-bit program counters
`pc < 2048` (with active program `0 .. 1539` and `halt` at `pc = 1539`). -/
def _program_0 (pc : ℕ) : Instr :=
  (if pc < 24 then (if pc < 20 then (if pc < 18 then (if pc < 17 then .decr 0 else .jump 19) else
  (if pc < 19 then .jump 16 else .jump 20)) else (if pc < 22 then (if pc < 21 then .incr 0 else
  .incr 1) else (if pc < 23 then .jump 24 else .jump 25))) else (if pc < 28 then (if pc < 26 then
  (if pc < 25 then .decr 0 else .jump 29) else (if pc < 27 then .incr 2 else .incr 3)) else (if pc
  < 30 then (if pc < 29 then .jump 24 else .jump 30) else (if pc < 31 then .jump 32 else .jump
  33))))

def _program_1 (pc : ℕ) : Instr :=
  (if pc < 40 then (if pc < 36 then (if pc < 34 then (if pc < 33 then .decr 3 else .jump 36) else
  (if pc < 35 then .incr 0 else .jump 32)) else (if pc < 38 then (if pc < 37 then .decr 4 else
  .jump 39) else (if pc < 39 then .jump 36 else .jump 40))) else (if pc < 44 then (if pc < 42 then
  (if pc < 41 then .decr 2 else .jump 44) else (if pc < 43 then .incr 4 else .jump 40)) else (if
  pc < 46 then (if pc < 45 then .jump 48 else .jump 49) else (if pc < 47 then .jump 50 else .jump
  51))))

def _program_2 (pc : ℕ) : Instr :=
  (if pc < 56 then (if pc < 52 then (if pc < 50 then (if pc < 49 then .decr 0 else .jump 53) else
  (if pc < 51 then .incr 2 else .incr 3)) else (if pc < 54 then (if pc < 53 then .jump 48 else
  .jump 54) else (if pc < 55 then .jump 56 else .jump 57))) else (if pc < 60 then (if pc < 58 then
  (if pc < 57 then .decr 3 else .jump 60) else (if pc < 59 then .incr 0 else .jump 56)) else (if
  pc < 62 then (if pc < 61 then .jump 64 else .jump 65) else (if pc < 63 then .jump 66 else .jump
  67))))

def _program_3 (pc : ℕ) : Instr :=
  (if pc < 72 then (if pc < 68 then (if pc < 66 then (if pc < 65 then .decr 0 else .jump 69) else
  (if pc < 67 then .incr 6 else .incr 8)) else (if pc < 70 then (if pc < 69 then .jump 64 else
  .jump 70) else (if pc < 71 then .jump 72 else .jump 73))) else (if pc < 76 then (if pc < 74 then
  (if pc < 73 then .decr 8 else .jump 76) else (if pc < 75 then .incr 0 else .jump 72)) else (if
  pc < 78 then (if pc < 77 then .jump 80 else .jump 81) else (if pc < 79 then .jump 82 else .jump
  83))))

def _program_4 (pc : ℕ) : Instr :=
  (if pc < 88 then (if pc < 84 then (if pc < 82 then (if pc < 81 then .decr 4 else .jump 85) else
  (if pc < 83 then .incr 7 else .incr 8)) else (if pc < 86 then (if pc < 85 then .jump 80 else
  .jump 86) else (if pc < 87 then .jump 88 else .jump 89))) else (if pc < 92 then (if pc < 90 then
  (if pc < 89 then .decr 8 else .jump 92) else (if pc < 91 then .incr 4 else .jump 88)) else (if
  pc < 94 then (if pc < 93 then .decr 7 else .jump 97) else (if pc < 95 then .decr 6 else .jump
  99))))

def _program_5 (pc : ℕ) : Instr :=
  (if pc < 104 then (if pc < 100 then (if pc < 98 then (if pc < 97 then .jump 92 else .incr 5)
  else (if pc < 99 then .jump 76 else .jump 100)) else (if pc < 102 then (if pc < 101 then .decr 7
  else .jump 103) else (if pc < 103 then .jump 100 else .jump 104))) else (if pc < 108 then (if pc
  < 106 then (if pc < 105 then .decr 5 else .jump 125) else (if pc < 107 then .jump 108 else .jump
  109)) else (if pc < 110 then (if pc < 109 then .jump 112 else .jump 113) else (if pc < 111 then
  .jump 114 else .jump 115))))

def _program_6 (pc : ℕ) : Instr :=
  (if pc < 120 then (if pc < 116 then (if pc < 114 then (if pc < 113 then .decr 4 else .jump 117)
  else (if pc < 115 then .incr 3 else .incr 7)) else (if pc < 118 then (if pc < 117 then .jump 112
  else .jump 118) else (if pc < 119 then .jump 120 else .jump 121))) else (if pc < 124 then (if pc
  < 122 then (if pc < 121 then .decr 7 else .jump 124) else (if pc < 123 then .incr 4 else .jump
  120)) else (if pc < 126 then (if pc < 125 then .jump 104 else .decr 3) else (if pc < 127 then
  .jump 130 else .decr 2))))

def _program_7 (pc : ℕ) : Instr :=
  (if pc < 136 then (if pc < 132 then (if pc < 130 then (if pc < 129 then .jump 137 else .jump
  125) else (if pc < 131 then .decr 2 else .jump 145)) else (if pc < 134 then (if pc < 133 then
  .decr 2 else .jump 135) else (if pc < 135 then .jump 132 else .jump 136))) else (if pc < 140
  then (if pc < 138 then (if pc < 137 then .jump 248 else .jump 138) else (if pc < 139 then .jump
  140 else .jump 141)) else (if pc < 142 then (if pc < 141 then .decr 3 else .jump 143) else (if
  pc < 143 then .jump 140 else .jump 144))))

def _program_8 (pc : ℕ) : Instr :=
  (if pc < 152 then (if pc < 148 then (if pc < 146 then (if pc < 145 then .jump 248 else .jump
  146) else (if pc < 147 then .jump 148 else .jump 149)) else (if pc < 150 then (if pc < 149 then
  .jump 152 else .jump 153) else (if pc < 151 then .jump 154 else .jump 155))) else (if pc < 156
  then (if pc < 154 then (if pc < 153 then .decr 0 else .jump 157) else (if pc < 155 then .incr 3
  else .incr 2)) else (if pc < 158 then (if pc < 157 then .jump 152 else .jump 158) else (if pc <
  159 then .jump 160 else .jump 161))))

def _program_9 (pc : ℕ) : Instr :=
  (if pc < 168 then (if pc < 164 then (if pc < 162 then (if pc < 161 then .decr 2 else .jump 164)
  else (if pc < 163 then .incr 0 else .jump 160)) else (if pc < 166 then (if pc < 165 then .jump
  168 else .jump 169) else (if pc < 167 then .jump 170 else .jump 171))) else (if pc < 172 then
  (if pc < 170 then (if pc < 169 then .decr 0 else .jump 173) else (if pc < 171 then .incr 7 else
  .incr 8)) else (if pc < 174 then (if pc < 173 then .jump 168 else .jump 174) else (if pc < 175
  then .jump 176 else .jump 177))))

def _program_10 (pc : ℕ) : Instr :=
  (if pc < 184 then (if pc < 180 then (if pc < 178 then (if pc < 177 then .decr 8 else .jump 180)
  else (if pc < 179 then .incr 0 else .jump 176)) else (if pc < 182 then (if pc < 181 then .jump
  184 else .jump 185) else (if pc < 183 then .jump 186 else .jump 187))) else (if pc < 188 then
  (if pc < 186 then (if pc < 185 then .decr 1 else .jump 189) else (if pc < 187 then .incr 6 else
  .incr 8)) else (if pc < 190 then (if pc < 189 then .jump 184 else .jump 190) else (if pc < 191
  then .jump 192 else .jump 193))))

def _program_11 (pc : ℕ) : Instr :=
  (if pc < 200 then (if pc < 196 then (if pc < 194 then (if pc < 193 then .decr 8 else .jump 196)
  else (if pc < 195 then .incr 1 else .jump 192)) else (if pc < 198 then (if pc < 197 then .decr 6
  else .jump 201) else (if pc < 199 then .decr 7 else .jump 203))) else (if pc < 204 then (if pc <
  202 then (if pc < 201 then .jump 196 else .incr 5) else (if pc < 203 then .jump 180 else .jump
  204)) else (if pc < 206 then (if pc < 205 then .decr 6 else .jump 207) else (if pc < 207 then
  .jump 204 else .jump 208))))

def _program_12 (pc : ℕ) : Instr :=
  (if pc < 216 then (if pc < 212 then (if pc < 210 then (if pc < 209 then .decr 5 else .jump 229)
  else (if pc < 211 then .jump 212 else .jump 213)) else (if pc < 214 then (if pc < 213 then .jump
  216 else .jump 217) else (if pc < 215 then .jump 218 else .jump 219))) else (if pc < 220 then
  (if pc < 218 then (if pc < 217 then .decr 1 else .jump 221) else (if pc < 219 then .incr 2 else
  .incr 6)) else (if pc < 222 then (if pc < 221 then .jump 216 else .jump 222) else (if pc < 223
  then .jump 224 else .jump 225))))

def _program_13 (pc : ℕ) : Instr :=
  (if pc < 232 then (if pc < 228 then (if pc < 226 then (if pc < 225 then .decr 6 else .jump 228)
  else (if pc < 227 then .incr 1 else .jump 224)) else (if pc < 230 then (if pc < 229 then .jump
  208 else .decr 2) else (if pc < 231 then .jump 234 else .decr 3))) else (if pc < 236 then (if pc
  < 234 then (if pc < 233 then .jump 241 else .jump 229) else (if pc < 235 then .decr 3 else .jump
  250)) else (if pc < 238 then (if pc < 237 then .decr 3 else .jump 239) else (if pc < 239 then
  .jump 236 else .jump 240))))

def _program_14 (pc : ℕ) : Instr :=
  (if pc < 248 then (if pc < 244 then (if pc < 242 then (if pc < 241 then .jump 248 else .jump
  242) else (if pc < 243 then .jump 244 else .jump 245)) else (if pc < 246 then (if pc < 245 then
  .decr 2 else .jump 247) else (if pc < 247 then .jump 244 else .jump 248))) else (if pc < 252
  then (if pc < 250 then (if pc < 249 then .incr 0 else .jump 44) else (if pc < 251 then .jump 252
  else .jump 253)) else (if pc < 254 then (if pc < 253 then .jump 256 else .jump 257) else (if pc
  < 255 then .jump 258 else .jump 259))))

def _program_15 (pc : ℕ) : Instr :=
  (if pc < 264 then (if pc < 260 then (if pc < 258 then (if pc < 257 then .decr 1 else .jump 261)
  else (if pc < 259 then .incr 2 else .incr 3)) else (if pc < 262 then (if pc < 261 then .jump 256
  else .jump 262) else (if pc < 263 then .jump 264 else .jump 265))) else (if pc < 268 then (if pc
  < 266 then (if pc < 265 then .decr 3 else .jump 268) else (if pc < 267 then .incr 1 else .jump
  264)) else (if pc < 270 then (if pc < 269 then .decr 2 else .jump 21) else (if pc < 271 then
  .decr 2 else .jump 21))))

def _program_16 (pc : ℕ) : Instr :=
  (if pc < 280 then (if pc < 276 then (if pc < 274 then (if pc < 273 then .decr 2 else .jump 21)
  else (if pc < 275 then .decr 2 else .jump 21)) else (if pc < 278 then (if pc < 277 then .decr 2
  else .jump 21) else (if pc < 279 then .decr 2 else .jump 21))) else (if pc < 284 then (if pc <
  282 then (if pc < 281 then .decr 2 else .jump 21) else (if pc < 283 then .decr 2 else .jump 21))
  else (if pc < 286 then (if pc < 285 then .decr 2 else .jump 21) else (if pc < 287 then .decr 2
  else .jump 21))))

def _program_17 (pc : ℕ) : Instr :=
  (if pc < 296 then (if pc < 292 then (if pc < 290 then (if pc < 289 then .decr 2 else .jump 21)
  else (if pc < 291 then .decr 2 else .jump 21)) else (if pc < 294 then (if pc < 293 then .decr 2
  else .jump 21) else (if pc < 295 then .decr 2 else .jump 21))) else (if pc < 300 then (if pc <
  298 then (if pc < 297 then .decr 2 else .jump 21) else (if pc < 299 then .decr 2 else .jump 21))
  else (if pc < 302 then (if pc < 301 then .decr 2 else .jump 21) else (if pc < 303 then .decr 2
  else .jump 21))))

def _program_18 (pc : ℕ) : Instr :=
  (if pc < 312 then (if pc < 308 then (if pc < 306 then (if pc < 305 then .decr 2 else .jump 21)
  else (if pc < 307 then .decr 2 else .jump 21)) else (if pc < 310 then (if pc < 309 then .decr 2
  else .jump 21) else (if pc < 311 then .decr 2 else .jump 21))) else (if pc < 316 then (if pc <
  314 then (if pc < 313 then .decr 2 else .jump 21) else (if pc < 315 then .decr 2 else .jump 21))
  else (if pc < 318 then (if pc < 317 then .decr 2 else .jump 21) else (if pc < 319 then .decr 2
  else .jump 21))))

def _program_19 (pc : ℕ) : Instr :=
  (if pc < 328 then (if pc < 324 then (if pc < 322 then (if pc < 321 then .decr 2 else .jump 21)
  else (if pc < 323 then .decr 2 else .jump 21)) else (if pc < 326 then (if pc < 325 then .decr 2
  else .jump 21) else (if pc < 327 then .decr 2 else .jump 21))) else (if pc < 332 then (if pc <
  330 then (if pc < 329 then .decr 2 else .jump 21) else (if pc < 331 then .decr 2 else .jump 21))
  else (if pc < 334 then (if pc < 333 then .decr 2 else .jump 21) else (if pc < 335 then .decr 2
  else .jump 21))))

def _program_20 (pc : ℕ) : Instr :=
  (if pc < 344 then (if pc < 340 then (if pc < 338 then (if pc < 337 then .decr 2 else .jump 21)
  else (if pc < 339 then .decr 2 else .jump 21)) else (if pc < 342 then (if pc < 341 then .decr 2
  else .jump 21) else (if pc < 343 then .decr 2 else .jump 21))) else (if pc < 348 then (if pc <
  346 then (if pc < 345 then .decr 2 else .jump 21) else (if pc < 347 then .decr 2 else .jump 21))
  else (if pc < 350 then (if pc < 349 then .decr 2 else .jump 21) else (if pc < 351 then .decr 2
  else .jump 21))))

def _program_21 (pc : ℕ) : Instr :=
  (if pc < 360 then (if pc < 356 then (if pc < 354 then (if pc < 353 then .decr 2 else .jump 21)
  else (if pc < 355 then .decr 2 else .jump 21)) else (if pc < 358 then (if pc < 357 then .decr 2
  else .jump 21) else (if pc < 359 then .decr 2 else .jump 21))) else (if pc < 364 then (if pc <
  362 then (if pc < 361 then .decr 2 else .jump 21) else (if pc < 363 then .decr 2 else .jump 21))
  else (if pc < 366 then (if pc < 365 then .decr 2 else .jump 21) else (if pc < 367 then .decr 2
  else .jump 21))))

def _program_22 (pc : ℕ) : Instr :=
  (if pc < 376 then (if pc < 372 then (if pc < 370 then (if pc < 369 then .decr 2 else .jump 21)
  else (if pc < 371 then .decr 2 else .jump 21)) else (if pc < 374 then (if pc < 373 then .decr 2
  else .jump 21) else (if pc < 375 then .decr 2 else .jump 21))) else (if pc < 380 then (if pc <
  378 then (if pc < 377 then .decr 2 else .jump 21) else (if pc < 379 then .decr 2 else .jump 21))
  else (if pc < 382 then (if pc < 381 then .decr 2 else .jump 21) else (if pc < 383 then .decr 2
  else .jump 21))))

def _program_23 (pc : ℕ) : Instr :=
  (if pc < 392 then (if pc < 388 then (if pc < 386 then (if pc < 385 then .decr 2 else .jump 21)
  else (if pc < 387 then .decr 2 else .jump 21)) else (if pc < 390 then (if pc < 389 then .decr 2
  else .jump 21) else (if pc < 391 then .decr 2 else .jump 21))) else (if pc < 396 then (if pc <
  394 then (if pc < 393 then .decr 2 else .jump 21) else (if pc < 395 then .decr 2 else .jump 21))
  else (if pc < 398 then (if pc < 397 then .decr 2 else .jump 21) else (if pc < 399 then .decr 2
  else .jump 21))))

def _program_24 (pc : ℕ) : Instr :=
  (if pc < 408 then (if pc < 404 then (if pc < 402 then (if pc < 401 then .decr 2 else .jump 21)
  else (if pc < 403 then .decr 2 else .jump 21)) else (if pc < 406 then (if pc < 405 then .decr 2
  else .jump 21) else (if pc < 407 then .decr 2 else .jump 21))) else (if pc < 412 then (if pc <
  410 then (if pc < 409 then .decr 2 else .jump 21) else (if pc < 411 then .decr 2 else .jump 21))
  else (if pc < 414 then (if pc < 413 then .decr 2 else .jump 21) else (if pc < 415 then .decr 2
  else .jump 21))))

def _program_25 (pc : ℕ) : Instr :=
  (if pc < 424 then (if pc < 420 then (if pc < 418 then (if pc < 417 then .decr 2 else .jump 21)
  else (if pc < 419 then .decr 2 else .jump 21)) else (if pc < 422 then (if pc < 421 then .decr 2
  else .jump 21) else (if pc < 423 then .decr 2 else .jump 21))) else (if pc < 428 then (if pc <
  426 then (if pc < 425 then .decr 2 else .jump 21) else (if pc < 427 then .decr 2 else .jump 21))
  else (if pc < 430 then (if pc < 429 then .decr 2 else .jump 21) else (if pc < 431 then .decr 2
  else .jump 21))))

def _program_26 (pc : ℕ) : Instr :=
  (if pc < 440 then (if pc < 436 then (if pc < 434 then (if pc < 433 then .decr 2 else .jump 21)
  else (if pc < 435 then .decr 2 else .jump 21)) else (if pc < 438 then (if pc < 437 then .decr 2
  else .jump 21) else (if pc < 439 then .decr 2 else .jump 21))) else (if pc < 444 then (if pc <
  442 then (if pc < 441 then .decr 2 else .jump 21) else (if pc < 443 then .decr 2 else .jump 21))
  else (if pc < 446 then (if pc < 445 then .decr 2 else .jump 21) else (if pc < 447 then .decr 2
  else .jump 21))))

def _program_27 (pc : ℕ) : Instr :=
  (if pc < 456 then (if pc < 452 then (if pc < 450 then (if pc < 449 then .decr 2 else .jump 21)
  else (if pc < 451 then .decr 2 else .jump 21)) else (if pc < 454 then (if pc < 453 then .decr 2
  else .jump 21) else (if pc < 455 then .decr 2 else .jump 21))) else (if pc < 460 then (if pc <
  458 then (if pc < 457 then .decr 2 else .jump 21) else (if pc < 459 then .decr 2 else .jump 21))
  else (if pc < 462 then (if pc < 461 then .decr 2 else .jump 21) else (if pc < 463 then .decr 2
  else .jump 21))))

def _program_28 (pc : ℕ) : Instr :=
  (if pc < 472 then (if pc < 468 then (if pc < 466 then (if pc < 465 then .decr 2 else .jump 21)
  else (if pc < 467 then .decr 2 else .jump 21)) else (if pc < 470 then (if pc < 469 then .decr 2
  else .jump 21) else (if pc < 471 then .decr 2 else .jump 21))) else (if pc < 476 then (if pc <
  474 then (if pc < 473 then .decr 2 else .jump 21) else (if pc < 475 then .decr 2 else .jump 21))
  else (if pc < 478 then (if pc < 477 then .decr 2 else .jump 21) else (if pc < 479 then .decr 2
  else .jump 21))))

def _program_29 (pc : ℕ) : Instr :=
  (if pc < 488 then (if pc < 484 then (if pc < 482 then (if pc < 481 then .decr 2 else .jump 21)
  else (if pc < 483 then .decr 2 else .jump 21)) else (if pc < 486 then (if pc < 485 then .decr 2
  else .jump 21) else (if pc < 487 then .decr 2 else .jump 21))) else (if pc < 492 then (if pc <
  490 then (if pc < 489 then .decr 2 else .jump 21) else (if pc < 491 then .decr 2 else .jump 21))
  else (if pc < 494 then (if pc < 493 then .decr 2 else .jump 21) else (if pc < 495 then .decr 2
  else .jump 21))))

def _program_30 (pc : ℕ) : Instr :=
  (if pc < 504 then (if pc < 500 then (if pc < 498 then (if pc < 497 then .decr 2 else .jump 21)
  else (if pc < 499 then .decr 2 else .jump 21)) else (if pc < 502 then (if pc < 501 then .decr 2
  else .jump 21) else (if pc < 503 then .decr 2 else .jump 21))) else (if pc < 508 then (if pc <
  506 then (if pc < 505 then .decr 2 else .jump 21) else (if pc < 507 then .decr 2 else .jump 21))
  else (if pc < 510 then (if pc < 509 then .decr 2 else .jump 21) else (if pc < 511 then .decr 2
  else .jump 21))))

def _program_31 (pc : ℕ) : Instr :=
  (if pc < 128 then (if pc < 64 then (if pc < 32 then (if pc < 16 then .initReg else _program_0
  pc) else (if pc < 48 then _program_1 pc else _program_2 pc)) else (if pc < 96 then (if pc < 80
  then _program_3 pc else _program_4 pc) else (if pc < 112 then _program_5 pc else _program_6
  pc))) else (if pc < 192 then (if pc < 160 then (if pc < 144 then _program_7 pc else _program_8
  pc) else (if pc < 176 then _program_9 pc else _program_10 pc)) else (if pc < 224 then (if pc <
  208 then _program_11 pc else _program_12 pc) else (if pc < 240 then _program_13 pc else
  _program_14 pc))))

def _program_32 (pc : ℕ) : Instr :=
  (if pc < 384 then (if pc < 320 then (if pc < 288 then (if pc < 272 then _program_15 pc else
  _program_16 pc) else (if pc < 304 then _program_17 pc else _program_18 pc)) else (if pc < 352
  then (if pc < 336 then _program_19 pc else _program_20 pc) else (if pc < 368 then _program_21 pc
  else _program_22 pc))) else (if pc < 448 then (if pc < 416 then (if pc < 400 then _program_23 pc
  else _program_24 pc) else (if pc < 432 then _program_25 pc else _program_26 pc)) else (if pc <
  480 then (if pc < 464 then _program_27 pc else _program_28 pc) else (if pc < 496 then
  _program_29 pc else _program_30 pc))))

def _program_33 (pc : ℕ) : Instr :=
  (if pc < 520 then (if pc < 516 then (if pc < 514 then (if pc < 513 then .decr 2 else .jump 21)
  else (if pc < 515 then .decr 2 else .jump 21)) else (if pc < 518 then (if pc < 517 then .decr 2
  else .jump 21) else (if pc < 519 then .decr 2 else .jump 21))) else (if pc < 524 then (if pc <
  522 then (if pc < 521 then .decr 2 else .jump 21) else (if pc < 523 then .decr 2 else .jump 21))
  else (if pc < 526 then (if pc < 525 then .decr 2 else .jump 21) else (if pc < 527 then .decr 2
  else .jump 21))))

def _program_34 (pc : ℕ) : Instr :=
  (if pc < 536 then (if pc < 532 then (if pc < 530 then (if pc < 529 then .decr 2 else .jump 21)
  else (if pc < 531 then .decr 2 else .jump 21)) else (if pc < 534 then (if pc < 533 then .decr 2
  else .jump 21) else (if pc < 535 then .decr 2 else .jump 21))) else (if pc < 540 then (if pc <
  538 then (if pc < 537 then .decr 2 else .jump 21) else (if pc < 539 then .decr 2 else .jump 21))
  else (if pc < 542 then (if pc < 541 then .decr 2 else .jump 21) else (if pc < 543 then .decr 2
  else .jump 21))))

def _program_35 (pc : ℕ) : Instr :=
  (if pc < 552 then (if pc < 548 then (if pc < 546 then (if pc < 545 then .decr 2 else .jump 21)
  else (if pc < 547 then .decr 2 else .jump 21)) else (if pc < 550 then (if pc < 549 then .decr 2
  else .jump 21) else (if pc < 551 then .decr 2 else .jump 21))) else (if pc < 556 then (if pc <
  554 then (if pc < 553 then .decr 2 else .jump 21) else (if pc < 555 then .decr 2 else .jump 21))
  else (if pc < 558 then (if pc < 557 then .decr 2 else .jump 21) else (if pc < 559 then .decr 2
  else .jump 21))))

def _program_36 (pc : ℕ) : Instr :=
  (if pc < 568 then (if pc < 564 then (if pc < 562 then (if pc < 561 then .decr 2 else .jump 21)
  else (if pc < 563 then .decr 2 else .jump 21)) else (if pc < 566 then (if pc < 565 then .decr 2
  else .jump 21) else (if pc < 567 then .decr 2 else .jump 21))) else (if pc < 572 then (if pc <
  570 then (if pc < 569 then .decr 2 else .jump 21) else (if pc < 571 then .decr 2 else .jump 21))
  else (if pc < 574 then (if pc < 573 then .decr 2 else .jump 21) else (if pc < 575 then .decr 2
  else .jump 21))))

def _program_37 (pc : ℕ) : Instr :=
  (if pc < 584 then (if pc < 580 then (if pc < 578 then (if pc < 577 then .decr 2 else .jump 21)
  else (if pc < 579 then .decr 2 else .jump 21)) else (if pc < 582 then (if pc < 581 then .decr 2
  else .jump 21) else (if pc < 583 then .decr 2 else .jump 21))) else (if pc < 588 then (if pc <
  586 then (if pc < 585 then .decr 2 else .jump 21) else (if pc < 587 then .decr 2 else .jump 21))
  else (if pc < 590 then (if pc < 589 then .decr 2 else .jump 21) else (if pc < 591 then .decr 2
  else .jump 21))))

def _program_38 (pc : ℕ) : Instr :=
  (if pc < 600 then (if pc < 596 then (if pc < 594 then (if pc < 593 then .decr 2 else .jump 21)
  else (if pc < 595 then .decr 2 else .jump 21)) else (if pc < 598 then (if pc < 597 then .decr 2
  else .jump 21) else (if pc < 599 then .decr 2 else .jump 21))) else (if pc < 604 then (if pc <
  602 then (if pc < 601 then .decr 2 else .jump 21) else (if pc < 603 then .decr 2 else .jump 21))
  else (if pc < 606 then (if pc < 605 then .decr 2 else .jump 21) else (if pc < 607 then .decr 2
  else .jump 21))))

def _program_39 (pc : ℕ) : Instr :=
  (if pc < 616 then (if pc < 612 then (if pc < 610 then (if pc < 609 then .decr 2 else .jump 21)
  else (if pc < 611 then .decr 2 else .jump 21)) else (if pc < 614 then (if pc < 613 then .decr 2
  else .jump 21) else (if pc < 615 then .decr 2 else .jump 21))) else (if pc < 620 then (if pc <
  618 then (if pc < 617 then .decr 2 else .jump 21) else (if pc < 619 then .decr 2 else .jump 21))
  else (if pc < 622 then (if pc < 621 then .decr 2 else .jump 21) else (if pc < 623 then .decr 2
  else .jump 21))))

def _program_40 (pc : ℕ) : Instr :=
  (if pc < 632 then (if pc < 628 then (if pc < 626 then (if pc < 625 then .decr 2 else .jump 21)
  else (if pc < 627 then .decr 2 else .jump 21)) else (if pc < 630 then (if pc < 629 then .decr 2
  else .jump 21) else (if pc < 631 then .decr 2 else .jump 21))) else (if pc < 636 then (if pc <
  634 then (if pc < 633 then .decr 2 else .jump 21) else (if pc < 635 then .decr 2 else .jump 21))
  else (if pc < 638 then (if pc < 637 then .decr 2 else .jump 21) else (if pc < 639 then .decr 2
  else .jump 21))))

def _program_41 (pc : ℕ) : Instr :=
  (if pc < 648 then (if pc < 644 then (if pc < 642 then (if pc < 641 then .decr 2 else .jump 21)
  else (if pc < 643 then .decr 2 else .jump 21)) else (if pc < 646 then (if pc < 645 then .decr 2
  else .jump 21) else (if pc < 647 then .decr 2 else .jump 21))) else (if pc < 652 then (if pc <
  650 then (if pc < 649 then .decr 2 else .jump 21) else (if pc < 651 then .decr 2 else .jump 21))
  else (if pc < 654 then (if pc < 653 then .decr 2 else .jump 21) else (if pc < 655 then .decr 2
  else .jump 21))))

def _program_42 (pc : ℕ) : Instr :=
  (if pc < 664 then (if pc < 660 then (if pc < 658 then (if pc < 657 then .decr 2 else .jump 21)
  else (if pc < 659 then .decr 2 else .jump 21)) else (if pc < 662 then (if pc < 661 then .decr 2
  else .jump 21) else (if pc < 663 then .decr 2 else .jump 21))) else (if pc < 668 then (if pc <
  666 then (if pc < 665 then .decr 2 else .jump 21) else (if pc < 667 then .decr 2 else .jump 21))
  else (if pc < 670 then (if pc < 669 then .decr 2 else .jump 21) else (if pc < 671 then .decr 2
  else .jump 21))))

def _program_43 (pc : ℕ) : Instr :=
  (if pc < 680 then (if pc < 676 then (if pc < 674 then (if pc < 673 then .decr 2 else .jump 21)
  else (if pc < 675 then .decr 2 else .jump 21)) else (if pc < 678 then (if pc < 677 then .decr 2
  else .jump 21) else (if pc < 679 then .decr 2 else .jump 21))) else (if pc < 684 then (if pc <
  682 then (if pc < 681 then .decr 2 else .jump 21) else (if pc < 683 then .decr 2 else .jump 21))
  else (if pc < 686 then (if pc < 685 then .decr 2 else .jump 21) else (if pc < 687 then .decr 2
  else .jump 21))))

def _program_44 (pc : ℕ) : Instr :=
  (if pc < 696 then (if pc < 692 then (if pc < 690 then (if pc < 689 then .decr 2 else .jump 21)
  else (if pc < 691 then .decr 2 else .jump 21)) else (if pc < 694 then (if pc < 693 then .decr 2
  else .jump 21) else (if pc < 695 then .decr 2 else .jump 21))) else (if pc < 700 then (if pc <
  698 then (if pc < 697 then .decr 2 else .jump 21) else (if pc < 699 then .decr 2 else .jump 21))
  else (if pc < 702 then (if pc < 701 then .decr 2 else .jump 21) else (if pc < 703 then .decr 2
  else .jump 21))))

def _program_45 (pc : ℕ) : Instr :=
  (if pc < 712 then (if pc < 708 then (if pc < 706 then (if pc < 705 then .decr 2 else .jump 21)
  else (if pc < 707 then .decr 2 else .jump 21)) else (if pc < 710 then (if pc < 709 then .decr 2
  else .jump 21) else (if pc < 711 then .decr 2 else .jump 21))) else (if pc < 716 then (if pc <
  714 then (if pc < 713 then .decr 2 else .jump 21) else (if pc < 715 then .decr 2 else .jump 21))
  else (if pc < 718 then (if pc < 717 then .decr 2 else .jump 21) else (if pc < 719 then .decr 2
  else .jump 21))))

def _program_46 (pc : ℕ) : Instr :=
  (if pc < 728 then (if pc < 724 then (if pc < 722 then (if pc < 721 then .decr 2 else .jump 21)
  else (if pc < 723 then .decr 2 else .jump 21)) else (if pc < 726 then (if pc < 725 then .decr 2
  else .jump 21) else (if pc < 727 then .decr 2 else .jump 21))) else (if pc < 732 then (if pc <
  730 then (if pc < 729 then .decr 2 else .jump 21) else (if pc < 731 then .decr 2 else .jump 21))
  else (if pc < 734 then (if pc < 733 then .decr 2 else .jump 21) else (if pc < 735 then .decr 2
  else .jump 21))))

def _program_47 (pc : ℕ) : Instr :=
  (if pc < 744 then (if pc < 740 then (if pc < 738 then (if pc < 737 then .decr 2 else .jump 21)
  else (if pc < 739 then .decr 2 else .jump 21)) else (if pc < 742 then (if pc < 741 then .decr 2
  else .jump 21) else (if pc < 743 then .decr 2 else .jump 21))) else (if pc < 748 then (if pc <
  746 then (if pc < 745 then .decr 2 else .jump 21) else (if pc < 747 then .decr 2 else .jump 21))
  else (if pc < 750 then (if pc < 749 then .decr 2 else .jump 21) else (if pc < 751 then .decr 2
  else .jump 21))))

def _program_48 (pc : ℕ) : Instr :=
  (if pc < 760 then (if pc < 756 then (if pc < 754 then (if pc < 753 then .decr 2 else .jump 21)
  else (if pc < 755 then .decr 2 else .jump 21)) else (if pc < 758 then (if pc < 757 then .decr 2
  else .jump 21) else (if pc < 759 then .decr 2 else .jump 21))) else (if pc < 764 then (if pc <
  762 then (if pc < 761 then .decr 2 else .jump 21) else (if pc < 763 then .decr 2 else .jump 21))
  else (if pc < 766 then (if pc < 765 then .decr 2 else .jump 21) else (if pc < 767 then .decr 2
  else .jump 21))))

def _program_49 (pc : ℕ) : Instr :=
  (if pc < 776 then (if pc < 772 then (if pc < 770 then (if pc < 769 then .decr 2 else .jump 21)
  else (if pc < 771 then .decr 2 else .jump 21)) else (if pc < 774 then (if pc < 773 then .decr 2
  else .jump 21) else (if pc < 775 then .decr 2 else .jump 21))) else (if pc < 780 then (if pc <
  778 then (if pc < 777 then .decr 2 else .jump 779) else (if pc < 779 then .jump 776 else .jump
  780)) else (if pc < 782 then (if pc < 781 then .decr 9 else .jump 783) else (if pc < 783 then
  .jump 780 else .jump 784))))

def _program_50 (pc : ℕ) : Instr :=
  (if pc < 792 then (if pc < 788 then (if pc < 786 then (if pc < 785 then .decr 10 else .jump 787)
  else (if pc < 787 then .jump 784 else .jump 788)) else (if pc < 790 then (if pc < 789 then .incr
  10 else .jump 790) else (if pc < 791 then .jump 792 else .jump 793))) else (if pc < 796 then (if
  pc < 794 then (if pc < 793 then .decr 11 else .jump 795) else (if pc < 795 then .jump 792 else
  .jump 796)) else (if pc < 798 then (if pc < 797 then .incr 11 else .jump 798) else (if pc < 799
  then .jump 800 else .jump 801))))

def _program_51 (pc : ℕ) : Instr :=
  (if pc < 808 then (if pc < 804 then (if pc < 802 then (if pc < 801 then .decr 11 else .jump 805)
  else (if pc < 803 then .incr 2 else .incr 3)) else (if pc < 806 then (if pc < 805 then .jump 800
  else .jump 806) else (if pc < 807 then .jump 808 else .jump 809))) else (if pc < 812 then (if pc
  < 810 then (if pc < 809 then .decr 3 else .jump 812) else (if pc < 811 then .incr 11 else .jump
  808)) else (if pc < 814 then (if pc < 813 then .jump 816 else .jump 817) else (if pc < 815 then
  .jump 818 else .jump 819))))

def _program_52 (pc : ℕ) : Instr :=
  (if pc < 824 then (if pc < 820 then (if pc < 818 then (if pc < 817 then .decr 0 else .jump 821)
  else (if pc < 819 then .incr 3 else .incr 5)) else (if pc < 822 then (if pc < 821 then .jump 816
  else .jump 822) else (if pc < 823 then .jump 824 else .jump 825))) else (if pc < 828 then (if pc
  < 826 then (if pc < 825 then .decr 5 else .jump 828) else (if pc < 827 then .incr 0 else .jump
  824)) else (if pc < 830 then (if pc < 829 then .decr 3 else .jump 833) else (if pc < 831 then
  .decr 2 else .jump 841))))

def _program_53 (pc : ℕ) : Instr :=
  (if pc < 840 then (if pc < 836 then (if pc < 834 then (if pc < 833 then .jump 828 else .decr 2)
  else (if pc < 835 then .jump 848 else .jump 836)) else (if pc < 838 then (if pc < 837 then .decr
  2 else .jump 839) else (if pc < 839 then .jump 836 else .jump 840))) else (if pc < 844 then (if
  pc < 842 then (if pc < 841 then .jump 946 else .jump 842) else (if pc < 843 then .jump 844 else
  .jump 845)) else (if pc < 846 then (if pc < 845 then .decr 3 else .jump 847) else (if pc < 847
  then .jump 844 else .jump 848))))

def _program_54 (pc : ℕ) : Instr :=
  (if pc < 856 then (if pc < 852 then (if pc < 850 then (if pc < 849 then .decr 9 else .jump 853)
  else (if pc < 851 then .incr 2 else .incr 5)) else (if pc < 854 then (if pc < 853 then .jump 848
  else .jump 854) else (if pc < 855 then .jump 856 else .jump 857))) else (if pc < 860 then (if pc
  < 858 then (if pc < 857 then .decr 5 else .jump 860) else (if pc < 859 then .incr 9 else .jump
  856)) else (if pc < 862 then (if pc < 861 then .decr 2 else .jump 877) else (if pc < 863 then
  .jump 864 else .jump 865))))

def _program_55 (pc : ℕ) : Instr :=
  (if pc < 872 then (if pc < 868 then (if pc < 866 then (if pc < 865 then .decr 11 else .jump 869)
  else (if pc < 867 then .incr 3 else .incr 5)) else (if pc < 870 then (if pc < 869 then .jump 864
  else .jump 870) else (if pc < 871 then .jump 872 else .jump 873))) else (if pc < 876 then (if pc
  < 874 then (if pc < 873 then .decr 5 else .jump 876) else (if pc < 875 then .incr 11 else .jump
  872)) else (if pc < 878 then (if pc < 877 then .jump 860 else .jump 878) else (if pc < 879 then
  .jump 880 else .jump 881))))

def _program_56 (pc : ℕ) : Instr :=
  (if pc < 888 then (if pc < 884 then (if pc < 882 then (if pc < 881 then .decr 10 else .jump 885)
  else (if pc < 883 then .incr 3 else .incr 2)) else (if pc < 886 then (if pc < 885 then .jump 880
  else .jump 886) else (if pc < 887 then .jump 888 else .jump 889))) else (if pc < 892 then (if pc
  < 890 then (if pc < 889 then .decr 2 else .jump 892) else (if pc < 891 then .incr 10 else .jump
  888)) else (if pc < 894 then (if pc < 893 then .decr 9 else .jump 895) else (if pc < 895 then
  .jump 892 else .jump 896))))

def _program_57 (pc : ℕ) : Instr :=
  (if pc < 904 then (if pc < 900 then (if pc < 898 then (if pc < 897 then .decr 3 else .jump 900)
  else (if pc < 899 then .incr 9 else .jump 896)) else (if pc < 902 then (if pc < 901 then .jump
  904 else .jump 905) else (if pc < 903 then .jump 906 else .jump 907))) else (if pc < 908 then
  (if pc < 906 then (if pc < 905 then .decr 10 else .jump 909) else (if pc < 907 then .incr 2 else
  .incr 5)) else (if pc < 910 then (if pc < 909 then .jump 904 else .jump 910) else (if pc < 911
  then .jump 912 else .jump 913))))

def _program_58 (pc : ℕ) : Instr :=
  (if pc < 920 then (if pc < 916 then (if pc < 914 then (if pc < 913 then .decr 5 else .jump 916)
  else (if pc < 915 then .incr 10 else .jump 912)) else (if pc < 918 then (if pc < 917 then .decr
  2 else .jump 933) else (if pc < 919 then .jump 920 else .jump 921))) else (if pc < 924 then (if
  pc < 922 then (if pc < 921 then .decr 11 else .jump 925) else (if pc < 923 then .incr 3 else
  .incr 5)) else (if pc < 926 then (if pc < 925 then .jump 920 else .jump 926) else (if pc < 927
  then .jump 928 else .jump 929))))

def _program_59 (pc : ℕ) : Instr :=
  (if pc < 936 then (if pc < 932 then (if pc < 930 then (if pc < 929 then .decr 5 else .jump 932)
  else (if pc < 931 then .incr 11 else .jump 928)) else (if pc < 934 then (if pc < 933 then .jump
  916 else .jump 934) else (if pc < 935 then .jump 936 else .jump 937))) else (if pc < 940 then
  (if pc < 938 then (if pc < 937 then .decr 10 else .jump 939) else (if pc < 939 then .jump 936
  else .jump 940)) else (if pc < 942 then (if pc < 941 then .decr 3 else .jump 944) else (if pc <
  943 then .incr 10 else .jump 940))))

def _program_60 (pc : ℕ) : Instr :=
  (if pc < 952 then (if pc < 948 then (if pc < 946 then (if pc < 945 then .incr 11 else .jump 797)
  else (if pc < 947 then .jump 948 else .jump 949)) else (if pc < 950 then (if pc < 949 then .jump
  952 else .jump 953) else (if pc < 951 then .jump 954 else .jump 955))) else (if pc < 956 then
  (if pc < 954 then (if pc < 953 then .decr 9 else .jump 957) else (if pc < 955 then .incr 2 else
  .incr 5)) else (if pc < 958 then (if pc < 957 then .jump 952 else .jump 958) else (if pc < 959
  then .jump 960 else .jump 961))))

def _program_61 (pc : ℕ) : Instr :=
  (if pc < 968 then (if pc < 964 then (if pc < 962 then (if pc < 961 then .decr 5 else .jump 964)
  else (if pc < 963 then .incr 9 else .jump 960)) else (if pc < 966 then (if pc < 965 then .jump
  968 else .jump 969) else (if pc < 967 then .jump 970 else .jump 971))) else (if pc < 972 then
  (if pc < 970 then (if pc < 969 then .decr 10 else .jump 973) else (if pc < 971 then .incr 6 else
  .incr 7)) else (if pc < 974 then (if pc < 973 then .jump 968 else .jump 974) else (if pc < 975
  then .jump 976 else .jump 977))))

def _program_62 (pc : ℕ) : Instr :=
  (if pc < 984 then (if pc < 980 then (if pc < 978 then (if pc < 977 then .decr 7 else .jump 980)
  else (if pc < 979 then .incr 10 else .jump 976)) else (if pc < 982 then (if pc < 981 then .decr
  6 else .jump 997) else (if pc < 983 then .jump 984 else .jump 985))) else (if pc < 988 then (if
  pc < 986 then (if pc < 985 then .decr 1 else .jump 989) else (if pc < 987 then .incr 5 else
  .incr 7)) else (if pc < 990 then (if pc < 989 then .jump 984 else .jump 990) else (if pc < 991
  then .jump 992 else .jump 993))))

def _program_63 (pc : ℕ) : Instr :=
  (if pc < 1000 then (if pc < 996 then (if pc < 994 then (if pc < 993 then .decr 7 else .jump 996)
  else (if pc < 995 then .incr 1 else .jump 992)) else (if pc < 998 then (if pc < 997 then .jump
  980 else .jump 998) else (if pc < 999 then .jump 1000 else .jump 1001))) else (if pc < 1004 then
  (if pc < 1002 then (if pc < 1001 then .decr 2 else .jump 1004) else (if pc < 1003 then .incr 3
  else .jump 1000)) else (if pc < 1006 then (if pc < 1005 then .decr 5 else .jump 1009) else (if
  pc < 1007 then .decr 3 else .jump 1008))))

def _program_64 (pc : ℕ) : Instr :=
  (if pc < 1016 then (if pc < 1012 then (if pc < 1010 then (if pc < 1009 then .jump 1004 else
  .jump 1010) else (if pc < 1011 then .jump 1012 else .jump 1013)) else (if pc < 1014 then (if pc
  < 1013 then .decr 12 else .jump 1015) else (if pc < 1015 then .jump 1012 else .jump 1016))) else
  (if pc < 1020 then (if pc < 1018 then (if pc < 1017 then .decr 3 else .jump 1020) else (if pc <
  1019 then .incr 12 else .jump 1016)) else (if pc < 1022 then (if pc < 1021 then .jump 1024 else
  .jump 1025) else (if pc < 1023 then .jump 1026 else .jump 1027))))

def _program_65 (pc : ℕ) : Instr :=
  (if pc < 640 then (if pc < 576 then (if pc < 544 then (if pc < 528 then _program_33 pc else
  _program_34 pc) else (if pc < 560 then _program_35 pc else _program_36 pc)) else (if pc < 608
  then (if pc < 592 then _program_37 pc else _program_38 pc) else (if pc < 624 then _program_39 pc
  else _program_40 pc))) else (if pc < 704 then (if pc < 672 then (if pc < 656 then _program_41 pc
  else _program_42 pc) else (if pc < 688 then _program_43 pc else _program_44 pc)) else (if pc <
  736 then (if pc < 720 then _program_45 pc else _program_46 pc) else (if pc < 752 then
  _program_47 pc else _program_48 pc))))

def _program_66 (pc : ℕ) : Instr :=
  (if pc < 896 then (if pc < 832 then (if pc < 800 then (if pc < 784 then _program_49 pc else
  _program_50 pc) else (if pc < 816 then _program_51 pc else _program_52 pc)) else (if pc < 864
  then (if pc < 848 then _program_53 pc else _program_54 pc) else (if pc < 880 then _program_55 pc
  else _program_56 pc))) else (if pc < 960 then (if pc < 928 then (if pc < 912 then _program_57 pc
  else _program_58 pc) else (if pc < 944 then _program_59 pc else _program_60 pc)) else (if pc <
  992 then (if pc < 976 then _program_61 pc else _program_62 pc) else (if pc < 1008 then
  _program_63 pc else _program_64 pc))))

def _program_67 (pc : ℕ) : Instr :=
  (if pc < 1032 then (if pc < 1028 then (if pc < 1026 then (if pc < 1025 then .decr 12 else .jump
  1029) else (if pc < 1027 then .incr 5 else .incr 2)) else (if pc < 1030 then (if pc < 1029 then
  .jump 1024 else .jump 1030) else (if pc < 1031 then .jump 1032 else .jump 1033))) else (if pc <
  1036 then (if pc < 1034 then (if pc < 1033 then .decr 2 else .jump 1036) else (if pc < 1035 then
  .incr 12 else .jump 1032)) else (if pc < 1038 then (if pc < 1037 then .decr 5 else .jump 1053)
  else (if pc < 1039 then .jump 1040 else .jump 1041))))

def _program_68 (pc : ℕ) : Instr :=
  (if pc < 1048 then (if pc < 1044 then (if pc < 1042 then (if pc < 1041 then .decr 12 else .jump
  1045) else (if pc < 1043 then .incr 3 else .incr 2)) else (if pc < 1046 then (if pc < 1045 then
  .jump 1040 else .jump 1046) else (if pc < 1047 then .jump 1048 else .jump 1049))) else (if pc <
  1052 then (if pc < 1050 then (if pc < 1049 then .decr 2 else .jump 1052) else (if pc < 1051 then
  .incr 12 else .jump 1048)) else (if pc < 1054 then (if pc < 1053 then .jump 1036 else .jump
  1054) else (if pc < 1055 then .jump 1056 else .jump 1057))))

def _program_69 (pc : ℕ) : Instr :=
  (if pc < 1064 then (if pc < 1060 then (if pc < 1058 then (if pc < 1057 then .decr 12 else .jump
  1059) else (if pc < 1059 then .jump 1056 else .jump 1060)) else (if pc < 1062 then (if pc < 1061
  then .decr 3 else .jump 1064) else (if pc < 1063 then .incr 12 else .jump 1060))) else (if pc <
  1068 then (if pc < 1066 then (if pc < 1065 then .decr 10 else .jump 1069) else (if pc < 1067
  then .incr 5 else .incr 2)) else (if pc < 1070 then (if pc < 1069 then .jump 1064 else .jump
  1070) else (if pc < 1071 then .jump 1072 else .jump 1073))))

def _program_70 (pc : ℕ) : Instr :=
  (if pc < 1080 then (if pc < 1076 then (if pc < 1074 then (if pc < 1073 then .decr 2 else .jump
  1076) else (if pc < 1075 then .incr 10 else .jump 1072)) else (if pc < 1078 then (if pc < 1077
  then .decr 5 else .jump 1093) else (if pc < 1079 then .jump 1080 else .jump 1081))) else (if pc
  < 1084 then (if pc < 1082 then (if pc < 1081 then .decr 10 else .jump 1085) else (if pc < 1083
  then .incr 3 else .incr 2)) else (if pc < 1086 then (if pc < 1085 then .jump 1080 else .jump
  1086) else (if pc < 1087 then .jump 1088 else .jump 1089))))

def _program_71 (pc : ℕ) : Instr :=
  (if pc < 1096 then (if pc < 1092 then (if pc < 1090 then (if pc < 1089 then .decr 2 else .jump
  1092) else (if pc < 1091 then .incr 10 else .jump 1088)) else (if pc < 1094 then (if pc < 1093
  then .jump 1076 else .jump 1094) else (if pc < 1095 then .jump 1096 else .jump 1097))) else (if
  pc < 1100 then (if pc < 1098 then (if pc < 1097 then .decr 13 else .jump 1099) else (if pc <
  1099 then .jump 1096 else .jump 1100)) else (if pc < 1102 then (if pc < 1101 then .decr 3 else
  .jump 1104) else (if pc < 1103 then .incr 13 else .jump 1100))))

def _program_72 (pc : ℕ) : Instr :=
  (if pc < 1112 then (if pc < 1108 then (if pc < 1106 then (if pc < 1105 then .decr 14 else .jump
  1107) else (if pc < 1107 then .jump 1104 else .jump 1108)) else (if pc < 1110 then (if pc < 1109
  then .decr 15 else .jump 1111) else (if pc < 1111 then .jump 1108 else .jump 1112))) else (if pc
  < 1116 then (if pc < 1114 then (if pc < 1113 then .incr 15 else .jump 1114) else (if pc < 1115
  then .jump 1116 else .jump 1117)) else (if pc < 1118 then (if pc < 1117 then .decr 11 else .jump
  1119) else (if pc < 1119 then .jump 1116 else .jump 1120))))

def _program_73 (pc : ℕ) : Instr :=
  (if pc < 1128 then (if pc < 1124 then (if pc < 1122 then (if pc < 1121 then .incr 11 else .jump
  1122) else (if pc < 1123 then .jump 1124 else .jump 1125)) else (if pc < 1126 then (if pc < 1125
  then .jump 1128 else .jump 1129) else (if pc < 1127 then .jump 1130 else .jump 1131))) else (if
  pc < 1132 then (if pc < 1130 then (if pc < 1129 then .decr 11 else .jump 1133) else (if pc <
  1131 then .incr 3 else .incr 5)) else (if pc < 1134 then (if pc < 1133 then .jump 1128 else
  .jump 1134) else (if pc < 1135 then .jump 1136 else .jump 1137))))

def _program_74 (pc : ℕ) : Instr :=
  (if pc < 1144 then (if pc < 1140 then (if pc < 1138 then (if pc < 1137 then .decr 5 else .jump
  1140) else (if pc < 1139 then .incr 11 else .jump 1136)) else (if pc < 1142 then (if pc < 1141
  then .jump 1144 else .jump 1145) else (if pc < 1143 then .jump 1146 else .jump 1147))) else (if
  pc < 1148 then (if pc < 1146 then (if pc < 1145 then .decr 1 else .jump 1149) else (if pc < 1147
  then .incr 5 else .incr 2)) else (if pc < 1150 then (if pc < 1149 then .jump 1144 else .jump
  1150) else (if pc < 1151 then .jump 1152 else .jump 1153))))

def _program_75 (pc : ℕ) : Instr :=
  (if pc < 1160 then (if pc < 1156 then (if pc < 1154 then (if pc < 1153 then .decr 2 else .jump
  1156) else (if pc < 1155 then .incr 1 else .jump 1152)) else (if pc < 1158 then (if pc < 1157
  then .decr 5 else .jump 1161) else (if pc < 1159 then .decr 3 else .jump 1169))) else (if pc <
  1164 then (if pc < 1162 then (if pc < 1161 then .jump 1156 else .decr 3) else (if pc < 1163 then
  .jump 1176 else .jump 1164)) else (if pc < 1166 then (if pc < 1165 then .decr 3 else .jump 1167)
  else (if pc < 1167 then .jump 1164 else .jump 1168))))

def _program_76 (pc : ℕ) : Instr :=
  (if pc < 1176 then (if pc < 1172 then (if pc < 1170 then (if pc < 1169 then .jump 1274 else
  .jump 1170) else (if pc < 1171 then .jump 1172 else .jump 1173)) else (if pc < 1174 then (if pc
  < 1173 then .decr 5 else .jump 1175) else (if pc < 1175 then .jump 1172 else .jump 1176))) else
  (if pc < 1180 then (if pc < 1178 then (if pc < 1177 then .decr 14 else .jump 1181) else (if pc <
  1179 then .incr 3 else .incr 2)) else (if pc < 1182 then (if pc < 1181 then .jump 1176 else
  .jump 1182) else (if pc < 1183 then .jump 1184 else .jump 1185))))

def _program_77 (pc : ℕ) : Instr :=
  (if pc < 1192 then (if pc < 1188 then (if pc < 1186 then (if pc < 1185 then .decr 2 else .jump
  1188) else (if pc < 1187 then .incr 14 else .jump 1184)) else (if pc < 1190 then (if pc < 1189
  then .decr 3 else .jump 1205) else (if pc < 1191 then .jump 1192 else .jump 1193))) else (if pc
  < 1196 then (if pc < 1194 then (if pc < 1193 then .decr 11 else .jump 1197) else (if pc < 1195
  then .incr 5 else .incr 2)) else (if pc < 1198 then (if pc < 1197 then .jump 1192 else .jump
  1198) else (if pc < 1199 then .jump 1200 else .jump 1201))))

def _program_78 (pc : ℕ) : Instr :=
  (if pc < 1208 then (if pc < 1204 then (if pc < 1202 then (if pc < 1201 then .decr 2 else .jump
  1204) else (if pc < 1203 then .incr 11 else .jump 1200)) else (if pc < 1206 then (if pc < 1205
  then .jump 1188 else .jump 1206) else (if pc < 1207 then .jump 1208 else .jump 1209))) else (if
  pc < 1212 then (if pc < 1210 then (if pc < 1209 then .decr 15 else .jump 1213) else (if pc <
  1211 then .incr 5 else .incr 3)) else (if pc < 1214 then (if pc < 1213 then .jump 1208 else
  .jump 1214) else (if pc < 1215 then .jump 1216 else .jump 1217))))

def _program_79 (pc : ℕ) : Instr :=
  (if pc < 1224 then (if pc < 1220 then (if pc < 1218 then (if pc < 1217 then .decr 3 else .jump
  1220) else (if pc < 1219 then .incr 15 else .jump 1216)) else (if pc < 1222 then (if pc < 1221
  then .decr 14 else .jump 1223) else (if pc < 1223 then .jump 1220 else .jump 1224))) else (if pc
  < 1228 then (if pc < 1226 then (if pc < 1225 then .decr 5 else .jump 1228) else (if pc < 1227
  then .incr 14 else .jump 1224)) else (if pc < 1230 then (if pc < 1229 then .jump 1232 else .jump
  1233) else (if pc < 1231 then .jump 1234 else .jump 1235))))

def _program_80 (pc : ℕ) : Instr :=
  (if pc < 1240 then (if pc < 1236 then (if pc < 1234 then (if pc < 1233 then .decr 15 else .jump
  1237) else (if pc < 1235 then .incr 3 else .incr 2)) else (if pc < 1238 then (if pc < 1237 then
  .jump 1232 else .jump 1238) else (if pc < 1239 then .jump 1240 else .jump 1241))) else (if pc <
  1244 then (if pc < 1242 then (if pc < 1241 then .decr 2 else .jump 1244) else (if pc < 1243 then
  .incr 15 else .jump 1240)) else (if pc < 1246 then (if pc < 1245 then .decr 3 else .jump 1261)
  else (if pc < 1247 then .jump 1248 else .jump 1249))))

def _program_81 (pc : ℕ) : Instr :=
  (if pc < 1256 then (if pc < 1252 then (if pc < 1250 then (if pc < 1249 then .decr 11 else .jump
  1253) else (if pc < 1251 then .incr 5 else .incr 2)) else (if pc < 1254 then (if pc < 1253 then
  .jump 1248 else .jump 1254) else (if pc < 1255 then .jump 1256 else .jump 1257))) else (if pc <
  1260 then (if pc < 1258 then (if pc < 1257 then .decr 2 else .jump 1260) else (if pc < 1259 then
  .incr 11 else .jump 1256)) else (if pc < 1262 then (if pc < 1261 then .jump 1244 else .jump
  1262) else (if pc < 1263 then .jump 1264 else .jump 1265))))

def _program_82 (pc : ℕ) : Instr :=
  (if pc < 1272 then (if pc < 1268 then (if pc < 1266 then (if pc < 1265 then .decr 15 else .jump
  1267) else (if pc < 1267 then .jump 1264 else .jump 1268)) else (if pc < 1270 then (if pc < 1269
  then .decr 5 else .jump 1272) else (if pc < 1271 then .incr 15 else .jump 1268))) else (if pc <
  1276 then (if pc < 1274 then (if pc < 1273 then .incr 11 else .jump 1121) else (if pc < 1275
  then .jump 1276 else .jump 1277)) else (if pc < 1278 then (if pc < 1277 then .jump 1280 else
  .jump 1281) else (if pc < 1279 then .jump 1282 else .jump 1283))))

def _program_83 (pc : ℕ) : Instr :=
  (if pc < 1288 then (if pc < 1284 then (if pc < 1282 then (if pc < 1281 then .decr 14 else .jump
  1285) else (if pc < 1283 then .incr 3 else .incr 2)) else (if pc < 1286 then (if pc < 1285 then
  .jump 1280 else .jump 1286) else (if pc < 1287 then .jump 1288 else .jump 1289))) else (if pc <
  1292 then (if pc < 1290 then (if pc < 1289 then .decr 2 else .jump 1292) else (if pc < 1291 then
  .incr 14 else .jump 1288)) else (if pc < 1294 then (if pc < 1293 then .decr 3 else .jump 1309)
  else (if pc < 1295 then .jump 1296 else .jump 1297))))

def _program_84 (pc : ℕ) : Instr :=
  (if pc < 1304 then (if pc < 1300 then (if pc < 1298 then (if pc < 1297 then .decr 14 else .jump
  1301) else (if pc < 1299 then .incr 5 else .incr 2)) else (if pc < 1302 then (if pc < 1301 then
  .jump 1296 else .jump 1302) else (if pc < 1303 then .jump 1304 else .jump 1305))) else (if pc <
  1308 then (if pc < 1306 then (if pc < 1305 then .decr 2 else .jump 1308) else (if pc < 1307 then
  .incr 14 else .jump 1304)) else (if pc < 1310 then (if pc < 1309 then .jump 1292 else .jump
  1310) else (if pc < 1311 then .jump 1312 else .jump 1313))))

def _program_85 (pc : ℕ) : Instr :=
  (if pc < 1320 then (if pc < 1316 then (if pc < 1314 then (if pc < 1313 then .decr 14 else .jump
  1315) else (if pc < 1315 then .jump 1312 else .jump 1316)) else (if pc < 1318 then (if pc < 1317
  then .decr 5 else .jump 1320) else (if pc < 1319 then .incr 14 else .jump 1316))) else (if pc <
  1324 then (if pc < 1322 then (if pc < 1321 then .decr 14 else .jump 1325) else (if pc < 1323
  then .incr 2 else .incr 6)) else (if pc < 1326 then (if pc < 1325 then .jump 1320 else .jump
  1326) else (if pc < 1327 then .jump 1328 else .jump 1329))))

def _program_86 (pc : ℕ) : Instr :=
  (if pc < 1336 then (if pc < 1332 then (if pc < 1330 then (if pc < 1329 then .decr 6 else .jump
  1332) else (if pc < 1331 then .incr 14 else .jump 1328)) else (if pc < 1334 then (if pc < 1333
  then .decr 2 else .jump 1349) else (if pc < 1335 then .jump 1336 else .jump 1337))) else (if pc
  < 1340 then (if pc < 1338 then (if pc < 1337 then .decr 14 else .jump 1341) else (if pc < 1339
  then .incr 3 else .incr 6)) else (if pc < 1342 then (if pc < 1341 then .jump 1336 else .jump
  1342) else (if pc < 1343 then .jump 1344 else .jump 1345))))

def _program_87 (pc : ℕ) : Instr :=
  (if pc < 1352 then (if pc < 1348 then (if pc < 1346 then (if pc < 1345 then .decr 6 else .jump
  1348) else (if pc < 1347 then .incr 14 else .jump 1344)) else (if pc < 1350 then (if pc < 1349
  then .jump 1332 else .decr 3) else (if pc < 1351 then .jump 1365 else .jump 1352))) else (if pc
  < 1356 then (if pc < 1354 then (if pc < 1353 then .decr 1 else .jump 1357) else (if pc < 1355
  then .incr 5 else .incr 2)) else (if pc < 1358 then (if pc < 1357 then .jump 1352 else .jump
  1358) else (if pc < 1359 then .jump 1360 else .jump 1361))))

def _program_88 (pc : ℕ) : Instr :=
  (if pc < 1368 then (if pc < 1364 then (if pc < 1362 then (if pc < 1361 then .decr 2 else .jump
  1364) else (if pc < 1363 then .incr 1 else .jump 1360)) else (if pc < 1366 then (if pc < 1365
  then .jump 1349 else .jump 1366) else (if pc < 1367 then .jump 1368 else .jump 1369))) else (if
  pc < 1372 then (if pc < 1370 then (if pc < 1369 then .decr 14 else .jump 1371) else (if pc <
  1371 then .jump 1368 else .jump 1372)) else (if pc < 1374 then (if pc < 1373 then .decr 5 else
  .jump 1376) else (if pc < 1375 then .incr 14 else .jump 1372))))

def _program_89 (pc : ℕ) : Instr :=
  (if pc < 1384 then (if pc < 1380 then (if pc < 1378 then (if pc < 1377 then .decr 15 else .jump
  1381) else (if pc < 1379 then .incr 3 else .incr 2)) else (if pc < 1382 then (if pc < 1381 then
  .jump 1376 else .jump 1382) else (if pc < 1383 then .jump 1384 else .jump 1385))) else (if pc <
  1388 then (if pc < 1386 then (if pc < 1385 then .decr 2 else .jump 1388) else (if pc < 1387 then
  .incr 15 else .jump 1384)) else (if pc < 1390 then (if pc < 1389 then .decr 3 else .jump 1405)
  else (if pc < 1391 then .jump 1392 else .jump 1393))))

def _program_90 (pc : ℕ) : Instr :=
  (if pc < 1400 then (if pc < 1396 then (if pc < 1394 then (if pc < 1393 then .decr 15 else .jump
  1397) else (if pc < 1395 then .incr 5 else .incr 2)) else (if pc < 1398 then (if pc < 1397 then
  .jump 1392 else .jump 1398) else (if pc < 1399 then .jump 1400 else .jump 1401))) else (if pc <
  1404 then (if pc < 1402 then (if pc < 1401 then .decr 2 else .jump 1404) else (if pc < 1403 then
  .incr 15 else .jump 1400)) else (if pc < 1406 then (if pc < 1405 then .jump 1388 else .jump
  1406) else (if pc < 1407 then .jump 1408 else .jump 1409))))

def _program_91 (pc : ℕ) : Instr :=
  (if pc < 1416 then (if pc < 1412 then (if pc < 1410 then (if pc < 1409 then .decr 15 else .jump
  1411) else (if pc < 1411 then .jump 1408 else .jump 1412)) else (if pc < 1414 then (if pc < 1413
  then .decr 5 else .jump 1416) else (if pc < 1415 then .incr 15 else .jump 1412))) else (if pc <
  1420 then (if pc < 1418 then (if pc < 1417 then .decr 15 else .jump 1421) else (if pc < 1419
  then .incr 3 else .incr 2)) else (if pc < 1422 then (if pc < 1421 then .jump 1416 else .jump
  1422) else (if pc < 1423 then .jump 1424 else .jump 1425))))

def _program_92 (pc : ℕ) : Instr :=
  (if pc < 1432 then (if pc < 1428 then (if pc < 1426 then (if pc < 1425 then .decr 2 else .jump
  1428) else (if pc < 1427 then .incr 15 else .jump 1424)) else (if pc < 1430 then (if pc < 1429
  then .decr 3 else .jump 1445) else (if pc < 1431 then .jump 1432 else .jump 1433))) else (if pc
  < 1436 then (if pc < 1434 then (if pc < 1433 then .decr 15 else .jump 1437) else (if pc < 1435
  then .incr 5 else .incr 2)) else (if pc < 1438 then (if pc < 1437 then .jump 1432 else .jump
  1438) else (if pc < 1439 then .jump 1440 else .jump 1441))))

def _program_93 (pc : ℕ) : Instr :=
  (if pc < 1448 then (if pc < 1444 then (if pc < 1442 then (if pc < 1441 then .decr 2 else .jump
  1444) else (if pc < 1443 then .incr 15 else .jump 1440)) else (if pc < 1446 then (if pc < 1445
  then .jump 1428 else .jump 1446) else (if pc < 1447 then .jump 1448 else .jump 1449))) else (if
  pc < 1452 then (if pc < 1450 then (if pc < 1449 then .decr 15 else .jump 1451) else (if pc <
  1451 then .jump 1448 else .jump 1452)) else (if pc < 1454 then (if pc < 1453 then .decr 5 else
  .jump 1456) else (if pc < 1455 then .incr 15 else .jump 1452))))

def _program_94 (pc : ℕ) : Instr :=
  (if pc < 1464 then (if pc < 1460 then (if pc < 1458 then (if pc < 1457 then .decr 12 else .jump
  1461) else (if pc < 1459 then .incr 3 else .incr 2)) else (if pc < 1462 then (if pc < 1461 then
  .jump 1456 else .jump 1462) else (if pc < 1463 then .jump 1464 else .jump 1465))) else (if pc <
  1468 then (if pc < 1466 then (if pc < 1465 then .decr 2 else .jump 1468) else (if pc < 1467 then
  .incr 12 else .jump 1464)) else (if pc < 1470 then (if pc < 1469 then .decr 3 else .jump 1485)
  else (if pc < 1471 then .jump 1472 else .jump 1473))))

def _program_95 (pc : ℕ) : Instr :=
  (if pc < 1480 then (if pc < 1476 then (if pc < 1474 then (if pc < 1473 then .decr 15 else .jump
  1477) else (if pc < 1475 then .incr 5 else .incr 2)) else (if pc < 1478 then (if pc < 1477 then
  .jump 1472 else .jump 1478) else (if pc < 1479 then .jump 1480 else .jump 1481))) else (if pc <
  1484 then (if pc < 1482 then (if pc < 1481 then .decr 2 else .jump 1484) else (if pc < 1483 then
  .incr 15 else .jump 1480)) else (if pc < 1486 then (if pc < 1485 then .jump 1468 else .jump
  1486) else (if pc < 1487 then .jump 1488 else .jump 1489))))

def _program_96 (pc : ℕ) : Instr :=
  (if pc < 1496 then (if pc < 1492 then (if pc < 1490 then (if pc < 1489 then .decr 13 else .jump
  1493) else (if pc < 1491 then .incr 2 else .incr 6)) else (if pc < 1494 then (if pc < 1493 then
  .jump 1488 else .jump 1494) else (if pc < 1495 then .jump 1496 else .jump 1497))) else (if pc <
  1500 then (if pc < 1498 then (if pc < 1497 then .decr 6 else .jump 1500) else (if pc < 1499 then
  .incr 13 else .jump 1496)) else (if pc < 1502 then (if pc < 1501 then .decr 2 else .jump 1517)
  else (if pc < 1503 then .jump 1504 else .jump 1505))))

def _program_97 (pc : ℕ) : Instr :=
  (if pc < 1512 then (if pc < 1508 then (if pc < 1506 then (if pc < 1505 then .decr 14 else .jump
  1509) else (if pc < 1507 then .incr 3 else .incr 6)) else (if pc < 1510 then (if pc < 1509 then
  .jump 1504 else .jump 1510) else (if pc < 1511 then .jump 1512 else .jump 1513))) else (if pc <
  1516 then (if pc < 1514 then (if pc < 1513 then .decr 6 else .jump 1516) else (if pc < 1515 then
  .incr 14 else .jump 1512)) else (if pc < 1518 then (if pc < 1517 then .jump 1500 else .decr 3)
  else (if pc < 1519 then .jump 1522 else .decr 5))))

def _program_98 (pc : ℕ) : Instr :=
  (if pc < 1528 then (if pc < 1524 then (if pc < 1522 then (if pc < 1521 then .jump 1529 else
  .jump 1517) else (if pc < 1523 then .decr 5 else .jump 21)) else (if pc < 1526 then (if pc <
  1525 then .decr 5 else .jump 1527) else (if pc < 1527 then .jump 1524 else .jump 1528))) else
  (if pc < 1532 then (if pc < 1530 then (if pc < 1529 then .jump 1539 else .jump 1530) else (if pc
  < 1531 then .jump 1532 else .jump 1533)) else (if pc < 1534 then (if pc < 1533 then .decr 3 else
  .jump 1535) else (if pc < 1535 then .jump 1532 else .jump 1536))))

def _program_99 (pc : ℕ) : Instr :=
  (if pc < 1152 then (if pc < 1088 then (if pc < 1056 then (if pc < 1040 then _program_67 pc else
  _program_68 pc) else (if pc < 1072 then _program_69 pc else _program_70 pc)) else (if pc < 1120
  then (if pc < 1104 then _program_71 pc else _program_72 pc) else (if pc < 1136 then _program_73
  pc else _program_74 pc))) else (if pc < 1216 then (if pc < 1184 then (if pc < 1168 then
  _program_75 pc else _program_76 pc) else (if pc < 1200 then _program_77 pc else _program_78 pc))
  else (if pc < 1248 then (if pc < 1232 then _program_79 pc else _program_80 pc) else (if pc <
  1264 then _program_81 pc else _program_82 pc))))

def _program_100 (pc : ℕ) : Instr :=
  (if pc < 1408 then (if pc < 1344 then (if pc < 1312 then (if pc < 1296 then _program_83 pc else
  _program_84 pc) else (if pc < 1328 then _program_85 pc else _program_86 pc)) else (if pc < 1376
  then (if pc < 1360 then _program_87 pc else _program_88 pc) else (if pc < 1392 then _program_89
  pc else _program_90 pc))) else (if pc < 1472 then (if pc < 1440 then (if pc < 1424 then
  _program_91 pc else _program_92 pc) else (if pc < 1456 then _program_93 pc else _program_94 pc))
  else (if pc < 1504 then (if pc < 1488 then _program_95 pc else _program_96 pc) else (if pc <
  1520 then _program_97 pc else _program_98 pc))))

def _program_101 (pc : ℕ) : Instr :=
  (if pc < 1544 then (if pc < 1540 then (if pc < 1538 then (if pc < 1537 then .jump 21 else .jump
  1539) else (if pc < 1539 then .jump 21 else .halt)) else (if pc < 1542 then (if pc < 1541 then
  .jump 1544 else .jump 1545) else (if pc < 1543 then .jump 1546 else .jump 1547))) else (if pc <
  1548 then (if pc < 1546 then (if pc < 1545 then .jump 1552 else .jump 1553) else (if pc < 1547
  then .jump 1554 else .jump 1555)) else (if pc < 1550 then (if pc < 1549 then .jump 1556 else
  .jump 1557) else (if pc < 1551 then .jump 1558 else .jump 1559))))

def _program_102 (pc : ℕ) : Instr :=
  (if pc < 1560 then (if pc < 1556 then (if pc < 1554 then (if pc < 1553 then .jump 1568 else
  .jump 1569) else (if pc < 1555 then .jump 1570 else .jump 1571)) else (if pc < 1558 then (if pc
  < 1557 then .jump 1572 else .jump 1573) else (if pc < 1559 then .jump 1574 else .jump 1575)))
  else (if pc < 1564 then (if pc < 1562 then (if pc < 1561 then .jump 1576 else .jump 1577) else
  (if pc < 1563 then .jump 1578 else .jump 1579)) else (if pc < 1566 then (if pc < 1565 then .jump
  1580 else .jump 1581) else (if pc < 1567 then .jump 1582 else .jump 1583))))

def _program_103 (pc : ℕ) : Instr :=
  (if pc < 1576 then (if pc < 1572 then (if pc < 1570 then (if pc < 1569 then .jump 1600 else
  .jump 1601) else (if pc < 1571 then .jump 1602 else .jump 1603)) else (if pc < 1574 then (if pc
  < 1573 then .jump 1604 else .jump 1605) else (if pc < 1575 then .jump 1606 else .jump 1607)))
  else (if pc < 1580 then (if pc < 1578 then (if pc < 1577 then .jump 1608 else .jump 1609) else
  (if pc < 1579 then .jump 1610 else .jump 1611)) else (if pc < 1582 then (if pc < 1581 then .jump
  1612 else .jump 1613) else (if pc < 1583 then .jump 1614 else .jump 1615))))

def _program_104 (pc : ℕ) : Instr :=
  (if pc < 1592 then (if pc < 1588 then (if pc < 1586 then (if pc < 1585 then .jump 1616 else
  .jump 1617) else (if pc < 1587 then .jump 1618 else .jump 1619)) else (if pc < 1590 then (if pc
  < 1589 then .jump 1620 else .jump 1621) else (if pc < 1591 then .jump 1622 else .jump 1623)))
  else (if pc < 1596 then (if pc < 1594 then (if pc < 1593 then .jump 1624 else .jump 1625) else
  (if pc < 1595 then .jump 1626 else .jump 1627)) else (if pc < 1598 then (if pc < 1597 then .jump
  1628 else .jump 1629) else (if pc < 1599 then .jump 1630 else .jump 1631))))

def _program_105 (pc : ℕ) : Instr :=
  (if pc < 1608 then (if pc < 1604 then (if pc < 1602 then (if pc < 1601 then .jump 1664 else
  .jump 1665) else (if pc < 1603 then .jump 1666 else .jump 1667)) else (if pc < 1606 then (if pc
  < 1605 then .jump 1668 else .jump 1669) else (if pc < 1607 then .jump 1670 else .jump 1671)))
  else (if pc < 1612 then (if pc < 1610 then (if pc < 1609 then .jump 1672 else .jump 1673) else
  (if pc < 1611 then .jump 1674 else .jump 1675)) else (if pc < 1614 then (if pc < 1613 then .jump
  1676 else .jump 1677) else (if pc < 1615 then .jump 1678 else .jump 1679))))

def _program_106 (pc : ℕ) : Instr :=
  (if pc < 1624 then (if pc < 1620 then (if pc < 1618 then (if pc < 1617 then .jump 1680 else
  .jump 1681) else (if pc < 1619 then .jump 1682 else .jump 1683)) else (if pc < 1622 then (if pc
  < 1621 then .jump 1684 else .jump 1685) else (if pc < 1623 then .jump 1686 else .jump 1687)))
  else (if pc < 1628 then (if pc < 1626 then (if pc < 1625 then .jump 1688 else .jump 1689) else
  (if pc < 1627 then .jump 1690 else .jump 1691)) else (if pc < 1630 then (if pc < 1629 then .jump
  1692 else .jump 1693) else (if pc < 1631 then .jump 1694 else .jump 1695))))

def _program_107 (pc : ℕ) : Instr :=
  (if pc < 1640 then (if pc < 1636 then (if pc < 1634 then (if pc < 1633 then .jump 1696 else
  .jump 1697) else (if pc < 1635 then .jump 1698 else .jump 1699)) else (if pc < 1638 then (if pc
  < 1637 then .jump 1700 else .jump 1701) else (if pc < 1639 then .jump 1702 else .jump 1703)))
  else (if pc < 1644 then (if pc < 1642 then (if pc < 1641 then .jump 1704 else .jump 1705) else
  (if pc < 1643 then .jump 1706 else .jump 1707)) else (if pc < 1646 then (if pc < 1645 then .jump
  1708 else .jump 1709) else (if pc < 1647 then .jump 1710 else .jump 1711))))

def _program_108 (pc : ℕ) : Instr :=
  (if pc < 1656 then (if pc < 1652 then (if pc < 1650 then (if pc < 1649 then .jump 1712 else
  .jump 1713) else (if pc < 1651 then .jump 1714 else .jump 1715)) else (if pc < 1654 then (if pc
  < 1653 then .jump 1716 else .jump 1717) else (if pc < 1655 then .jump 1718 else .jump 1719)))
  else (if pc < 1660 then (if pc < 1658 then (if pc < 1657 then .jump 1720 else .jump 1721) else
  (if pc < 1659 then .jump 1722 else .jump 1723)) else (if pc < 1662 then (if pc < 1661 then .jump
  1724 else .jump 1725) else (if pc < 1663 then .jump 1726 else .jump 1727))))

def _program_109 (pc : ℕ) : Instr :=
  (if pc < 1672 then (if pc < 1668 then (if pc < 1666 then (if pc < 1665 then .jump 1792 else
  .jump 1793) else (if pc < 1667 then .jump 1794 else .jump 1795)) else (if pc < 1670 then (if pc
  < 1669 then .jump 1796 else .jump 1797) else (if pc < 1671 then .jump 1798 else .jump 1799)))
  else (if pc < 1676 then (if pc < 1674 then (if pc < 1673 then .jump 1800 else .jump 1801) else
  (if pc < 1675 then .jump 1802 else .jump 1803)) else (if pc < 1678 then (if pc < 1677 then .jump
  1804 else .jump 1805) else (if pc < 1679 then .jump 1806 else .jump 1807))))

def _program_110 (pc : ℕ) : Instr :=
  (if pc < 1688 then (if pc < 1684 then (if pc < 1682 then (if pc < 1681 then .jump 1808 else
  .jump 1809) else (if pc < 1683 then .jump 1810 else .jump 1811)) else (if pc < 1686 then (if pc
  < 1685 then .jump 1812 else .jump 1813) else (if pc < 1687 then .jump 1814 else .jump 1815)))
  else (if pc < 1692 then (if pc < 1690 then (if pc < 1689 then .jump 1816 else .jump 1817) else
  (if pc < 1691 then .jump 1818 else .jump 1819)) else (if pc < 1694 then (if pc < 1693 then .jump
  1820 else .jump 1821) else (if pc < 1695 then .jump 1822 else .jump 1823))))

def _program_111 (pc : ℕ) : Instr :=
  (if pc < 1704 then (if pc < 1700 then (if pc < 1698 then (if pc < 1697 then .jump 1824 else
  .jump 1825) else (if pc < 1699 then .jump 1826 else .jump 1827)) else (if pc < 1702 then (if pc
  < 1701 then .jump 1828 else .jump 1829) else (if pc < 1703 then .jump 1830 else .jump 1831)))
  else (if pc < 1708 then (if pc < 1706 then (if pc < 1705 then .jump 1832 else .jump 1833) else
  (if pc < 1707 then .jump 1834 else .jump 1835)) else (if pc < 1710 then (if pc < 1709 then .jump
  1836 else .jump 1837) else (if pc < 1711 then .jump 1838 else .jump 1839))))

def _program_112 (pc : ℕ) : Instr :=
  (if pc < 1720 then (if pc < 1716 then (if pc < 1714 then (if pc < 1713 then .jump 1840 else
  .jump 1841) else (if pc < 1715 then .jump 1842 else .jump 1843)) else (if pc < 1718 then (if pc
  < 1717 then .jump 1844 else .jump 1845) else (if pc < 1719 then .jump 1846 else .jump 1847)))
  else (if pc < 1724 then (if pc < 1722 then (if pc < 1721 then .jump 1848 else .jump 1849) else
  (if pc < 1723 then .jump 1850 else .jump 1851)) else (if pc < 1726 then (if pc < 1725 then .jump
  1852 else .jump 1853) else (if pc < 1727 then .jump 1854 else .jump 1855))))

def _program_113 (pc : ℕ) : Instr :=
  (if pc < 1736 then (if pc < 1732 then (if pc < 1730 then (if pc < 1729 then .jump 1856 else
  .jump 1857) else (if pc < 1731 then .jump 1858 else .jump 1859)) else (if pc < 1734 then (if pc
  < 1733 then .jump 1860 else .jump 1861) else (if pc < 1735 then .jump 1862 else .jump 1863)))
  else (if pc < 1740 then (if pc < 1738 then (if pc < 1737 then .jump 1864 else .jump 1865) else
  (if pc < 1739 then .jump 1866 else .jump 1867)) else (if pc < 1742 then (if pc < 1741 then .jump
  1868 else .jump 1869) else (if pc < 1743 then .jump 1870 else .jump 1871))))

def _program_114 (pc : ℕ) : Instr :=
  (if pc < 1752 then (if pc < 1748 then (if pc < 1746 then (if pc < 1745 then .jump 1872 else
  .jump 1873) else (if pc < 1747 then .jump 1874 else .jump 1875)) else (if pc < 1750 then (if pc
  < 1749 then .jump 1876 else .jump 1877) else (if pc < 1751 then .jump 1878 else .jump 1879)))
  else (if pc < 1756 then (if pc < 1754 then (if pc < 1753 then .jump 1880 else .jump 1881) else
  (if pc < 1755 then .jump 1882 else .jump 1883)) else (if pc < 1758 then (if pc < 1757 then .jump
  1884 else .jump 1885) else (if pc < 1759 then .jump 1886 else .jump 1887))))

def _program_115 (pc : ℕ) : Instr :=
  (if pc < 1768 then (if pc < 1764 then (if pc < 1762 then (if pc < 1761 then .jump 1888 else
  .jump 1889) else (if pc < 1763 then .jump 1890 else .jump 1891)) else (if pc < 1766 then (if pc
  < 1765 then .jump 1892 else .jump 1893) else (if pc < 1767 then .jump 1894 else .jump 1895)))
  else (if pc < 1772 then (if pc < 1770 then (if pc < 1769 then .jump 1896 else .jump 1897) else
  (if pc < 1771 then .jump 1898 else .jump 1899)) else (if pc < 1774 then (if pc < 1773 then .jump
  1900 else .jump 1901) else (if pc < 1775 then .jump 1902 else .jump 1903))))

def _program_116 (pc : ℕ) : Instr :=
  (if pc < 1784 then (if pc < 1780 then (if pc < 1778 then (if pc < 1777 then .jump 1904 else
  .jump 1905) else (if pc < 1779 then .jump 1906 else .jump 1907)) else (if pc < 1782 then (if pc
  < 1781 then .jump 1908 else .jump 1909) else (if pc < 1783 then .jump 1910 else .jump 1911)))
  else (if pc < 1788 then (if pc < 1786 then (if pc < 1785 then .jump 1912 else .jump 1913) else
  (if pc < 1787 then .jump 1914 else .jump 1915)) else (if pc < 1790 then (if pc < 1789 then .jump
  1916 else .jump 1917) else (if pc < 1791 then .jump 1918 else .jump 1919))))

def _program_117 (pc : ℕ) : Instr :=
  (if pc < 1800 then (if pc < 1796 then (if pc < 1794 then (if pc < 1793 then .jump 0 else .jump
  1) else (if pc < 1795 then .jump 2 else .jump 3)) else (if pc < 1798 then (if pc < 1797 then
  .jump 4 else .jump 5) else (if pc < 1799 then .jump 6 else .jump 7))) else (if pc < 1804 then
  (if pc < 1802 then (if pc < 1801 then .jump 8 else .jump 9) else (if pc < 1803 then .jump 10
  else .jump 11)) else (if pc < 1806 then (if pc < 1805 then .jump 12 else .jump 13) else (if pc <
  1807 then .jump 14 else .jump 15))))

def _program_118 (pc : ℕ) : Instr :=
  (if pc < 1816 then (if pc < 1812 then (if pc < 1810 then (if pc < 1809 then .jump 16 else .jump
  17) else (if pc < 1811 then .jump 18 else .jump 19)) else (if pc < 1814 then (if pc < 1813 then
  .jump 20 else .jump 21) else (if pc < 1815 then .jump 22 else .jump 23))) else (if pc < 1820
  then (if pc < 1818 then (if pc < 1817 then .jump 24 else .jump 25) else (if pc < 1819 then .jump
  26 else .jump 27)) else (if pc < 1822 then (if pc < 1821 then .jump 28 else .jump 29) else (if
  pc < 1823 then .jump 30 else .jump 31))))

def _program_119 (pc : ℕ) : Instr :=
  (if pc < 1832 then (if pc < 1828 then (if pc < 1826 then (if pc < 1825 then .jump 32 else .jump
  33) else (if pc < 1827 then .jump 34 else .jump 35)) else (if pc < 1830 then (if pc < 1829 then
  .jump 36 else .jump 37) else (if pc < 1831 then .jump 38 else .jump 39))) else (if pc < 1836
  then (if pc < 1834 then (if pc < 1833 then .jump 40 else .jump 41) else (if pc < 1835 then .jump
  42 else .jump 43)) else (if pc < 1838 then (if pc < 1837 then .jump 44 else .jump 45) else (if
  pc < 1839 then .jump 46 else .jump 47))))

def _program_120 (pc : ℕ) : Instr :=
  (if pc < 1848 then (if pc < 1844 then (if pc < 1842 then (if pc < 1841 then .jump 48 else .jump
  49) else (if pc < 1843 then .jump 50 else .jump 51)) else (if pc < 1846 then (if pc < 1845 then
  .jump 52 else .jump 53) else (if pc < 1847 then .jump 54 else .jump 55))) else (if pc < 1852
  then (if pc < 1850 then (if pc < 1849 then .jump 56 else .jump 57) else (if pc < 1851 then .jump
  58 else .jump 59)) else (if pc < 1854 then (if pc < 1853 then .jump 60 else .jump 61) else (if
  pc < 1855 then .jump 62 else .jump 63))))

def _program_121 (pc : ℕ) : Instr :=
  (if pc < 1864 then (if pc < 1860 then (if pc < 1858 then (if pc < 1857 then .jump 64 else .jump
  65) else (if pc < 1859 then .jump 66 else .jump 67)) else (if pc < 1862 then (if pc < 1861 then
  .jump 68 else .jump 69) else (if pc < 1863 then .jump 70 else .jump 71))) else (if pc < 1868
  then (if pc < 1866 then (if pc < 1865 then .jump 72 else .jump 73) else (if pc < 1867 then .jump
  74 else .jump 75)) else (if pc < 1870 then (if pc < 1869 then .jump 76 else .jump 77) else (if
  pc < 1871 then .jump 78 else .jump 79))))

def _program_122 (pc : ℕ) : Instr :=
  (if pc < 1880 then (if pc < 1876 then (if pc < 1874 then (if pc < 1873 then .jump 80 else .jump
  81) else (if pc < 1875 then .jump 82 else .jump 83)) else (if pc < 1878 then (if pc < 1877 then
  .jump 84 else .jump 85) else (if pc < 1879 then .jump 86 else .jump 87))) else (if pc < 1884
  then (if pc < 1882 then (if pc < 1881 then .jump 88 else .jump 89) else (if pc < 1883 then .jump
  90 else .jump 91)) else (if pc < 1886 then (if pc < 1885 then .jump 92 else .jump 93) else (if
  pc < 1887 then .jump 94 else .jump 95))))

def _program_123 (pc : ℕ) : Instr :=
  (if pc < 1896 then (if pc < 1892 then (if pc < 1890 then (if pc < 1889 then .jump 96 else .jump
  97) else (if pc < 1891 then .jump 98 else .jump 99)) else (if pc < 1894 then (if pc < 1893 then
  .jump 100 else .jump 101) else (if pc < 1895 then .jump 102 else .jump 103))) else (if pc < 1900
  then (if pc < 1898 then (if pc < 1897 then .jump 104 else .jump 105) else (if pc < 1899 then
  .jump 106 else .jump 107)) else (if pc < 1902 then (if pc < 1901 then .jump 108 else .jump 109)
  else (if pc < 1903 then .jump 110 else .jump 111))))

def _program_124 (pc : ℕ) : Instr :=
  (if pc < 1912 then (if pc < 1908 then (if pc < 1906 then (if pc < 1905 then .jump 112 else .jump
  113) else (if pc < 1907 then .jump 114 else .jump 115)) else (if pc < 1910 then (if pc < 1909
  then .jump 116 else .jump 117) else (if pc < 1911 then .jump 118 else .jump 119))) else (if pc <
  1916 then (if pc < 1914 then (if pc < 1913 then .jump 120 else .jump 121) else (if pc < 1915
  then .jump 122 else .jump 123)) else (if pc < 1918 then (if pc < 1917 then .jump 124 else .jump
  125) else (if pc < 1919 then .jump 126 else .jump 127))))

def _program_125 (pc : ℕ) : Instr :=
  (if pc < 1928 then (if pc < 1924 then (if pc < 1922 then (if pc < 1921 then .jump 128 else .jump
  129) else (if pc < 1923 then .jump 130 else .jump 131)) else (if pc < 1926 then (if pc < 1925
  then .jump 132 else .jump 133) else (if pc < 1927 then .jump 134 else .jump 135))) else (if pc <
  1932 then (if pc < 1930 then (if pc < 1929 then .jump 136 else .jump 137) else (if pc < 1931
  then .jump 138 else .jump 139)) else (if pc < 1934 then (if pc < 1933 then .jump 140 else .jump
  141) else (if pc < 1935 then .jump 142 else .jump 143))))

def _program_126 (pc : ℕ) : Instr :=
  (if pc < 1944 then (if pc < 1940 then (if pc < 1938 then (if pc < 1937 then .jump 144 else .jump
  145) else (if pc < 1939 then .jump 146 else .jump 147)) else (if pc < 1942 then (if pc < 1941
  then .jump 148 else .jump 149) else (if pc < 1943 then .jump 150 else .jump 151))) else (if pc <
  1948 then (if pc < 1946 then (if pc < 1945 then .jump 152 else .jump 153) else (if pc < 1947
  then .jump 154 else .jump 155)) else (if pc < 1950 then (if pc < 1949 then .jump 156 else .jump
  157) else (if pc < 1951 then .jump 158 else .jump 159))))

def _program_127 (pc : ℕ) : Instr :=
  (if pc < 1960 then (if pc < 1956 then (if pc < 1954 then (if pc < 1953 then .jump 160 else .jump
  161) else (if pc < 1955 then .jump 162 else .jump 163)) else (if pc < 1958 then (if pc < 1957
  then .jump 164 else .jump 165) else (if pc < 1959 then .jump 166 else .jump 167))) else (if pc <
  1964 then (if pc < 1962 then (if pc < 1961 then .jump 168 else .jump 169) else (if pc < 1963
  then .jump 170 else .jump 171)) else (if pc < 1966 then (if pc < 1965 then .jump 172 else .jump
  173) else (if pc < 1967 then .jump 174 else .jump 175))))

def _program_128 (pc : ℕ) : Instr :=
  (if pc < 1976 then (if pc < 1972 then (if pc < 1970 then (if pc < 1969 then .jump 176 else .jump
  177) else (if pc < 1971 then .jump 178 else .jump 179)) else (if pc < 1974 then (if pc < 1973
  then .jump 180 else .jump 181) else (if pc < 1975 then .jump 182 else .jump 183))) else (if pc <
  1980 then (if pc < 1978 then (if pc < 1977 then .jump 184 else .jump 185) else (if pc < 1979
  then .jump 186 else .jump 187)) else (if pc < 1982 then (if pc < 1981 then .jump 188 else .jump
  189) else (if pc < 1983 then .jump 190 else .jump 191))))

def _program_129 (pc : ℕ) : Instr :=
  (if pc < 1992 then (if pc < 1988 then (if pc < 1986 then (if pc < 1985 then .jump 192 else .jump
  193) else (if pc < 1987 then .jump 194 else .jump 195)) else (if pc < 1990 then (if pc < 1989
  then .jump 196 else .jump 197) else (if pc < 1991 then .jump 198 else .jump 199))) else (if pc <
  1996 then (if pc < 1994 then (if pc < 1993 then .jump 200 else .jump 201) else (if pc < 1995
  then .jump 202 else .jump 203)) else (if pc < 1998 then (if pc < 1997 then .jump 204 else .jump
  205) else (if pc < 1999 then .jump 206 else .jump 207))))

def _program_130 (pc : ℕ) : Instr :=
  (if pc < 2008 then (if pc < 2004 then (if pc < 2002 then (if pc < 2001 then .jump 208 else .jump
  209) else (if pc < 2003 then .jump 210 else .jump 211)) else (if pc < 2006 then (if pc < 2005
  then .jump 212 else .jump 213) else (if pc < 2007 then .jump 214 else .jump 215))) else (if pc <
  2012 then (if pc < 2010 then (if pc < 2009 then .jump 216 else .jump 217) else (if pc < 2011
  then .jump 218 else .jump 219)) else (if pc < 2014 then (if pc < 2013 then .jump 220 else .jump
  221) else (if pc < 2015 then .jump 222 else .jump 223))))

def _program_131 (pc : ℕ) : Instr :=
  (if pc < 2024 then (if pc < 2020 then (if pc < 2018 then (if pc < 2017 then .jump 224 else .jump
  225) else (if pc < 2019 then .jump 226 else .jump 227)) else (if pc < 2022 then (if pc < 2021
  then .jump 228 else .jump 229) else (if pc < 2023 then .jump 230 else .jump 231))) else (if pc <
  2028 then (if pc < 2026 then (if pc < 2025 then .jump 232 else .jump 233) else (if pc < 2027
  then .jump 234 else .jump 235)) else (if pc < 2030 then (if pc < 2029 then .jump 236 else .jump
  237) else (if pc < 2031 then .jump 238 else .jump 239))))

def _program_132 (pc : ℕ) : Instr :=
  (if pc < 2040 then (if pc < 2036 then (if pc < 2034 then (if pc < 2033 then .jump 240 else .jump
  241) else (if pc < 2035 then .jump 242 else .jump 243)) else (if pc < 2038 then (if pc < 2037
  then .jump 244 else .jump 245) else (if pc < 2039 then .jump 246 else .jump 247))) else (if pc <
  2044 then (if pc < 2042 then (if pc < 2041 then .jump 248 else .jump 249) else (if pc < 2043
  then .jump 250 else .jump 251)) else (if pc < 2046 then (if pc < 2045 then .jump 252 else .jump
  253) else (if pc < 2047 then .jump 254 else .jump 255))))

def _program_133 (pc : ℕ) : Instr :=
  (if pc < 1664 then (if pc < 1600 then (if pc < 1568 then (if pc < 1552 then _program_101 pc else
  _program_102 pc) else (if pc < 1584 then _program_103 pc else _program_104 pc)) else (if pc <
  1632 then (if pc < 1616 then _program_105 pc else _program_106 pc) else (if pc < 1648 then
  _program_107 pc else _program_108 pc))) else (if pc < 1728 then (if pc < 1696 then (if pc < 1680
  then _program_109 pc else _program_110 pc) else (if pc < 1712 then _program_111 pc else
  _program_112 pc)) else (if pc < 1760 then (if pc < 1744 then _program_113 pc else _program_114
  pc) else (if pc < 1776 then _program_115 pc else _program_116 pc))))

def _program_134 (pc : ℕ) : Instr :=
  (if pc < 1920 then (if pc < 1856 then (if pc < 1824 then (if pc < 1808 then _program_117 pc else
  _program_118 pc) else (if pc < 1840 then _program_119 pc else _program_120 pc)) else (if pc <
  1888 then (if pc < 1872 then _program_121 pc else _program_122 pc) else (if pc < 1904 then
  _program_123 pc else _program_124 pc))) else (if pc < 1984 then (if pc < 1952 then (if pc < 1936
  then _program_125 pc else _program_126 pc) else (if pc < 1968 then _program_127 pc else
  _program_128 pc)) else (if pc < 2016 then (if pc < 2000 then _program_129 pc else _program_130
  pc) else (if pc < 2032 then _program_131 pc else _program_132 pc))))

def program (pc : ℕ) : Instr :=
  (if pc < 1024 then (if pc < 512 then (if pc < 256 then _program_31 pc else _program_32 pc) else
  (if pc < 768 then _program_65 pc else _program_66 pc)) else (if pc < 1536 then (if pc < 1280
  then _program_99 pc else _program_100 pc) else (if pc < 1792 then _program_133 pc else
  _program_134 pc)))

/-- Boolean verification predicate checking that `initWin pc` executes `ins : Instr` in the
bounded window. -/
def checkPcInstr (pc : ℕ) (ins : Instr) : Bool :=
  match ins with
  | .initReg =>
    winNSteps 12 (initWin pc) == some (postPcWin 32 pc)
  | .incr k =>
    winNSteps 12 (initWin pc) == some (postPcWin (regIncrState k.val) pc)
  | .decr k =>
    winNSteps 12 (initWin pc) == some (postPcWin (regDecrState k.val) pc)
  | .jump target =>
    (target < 2048) && (winRunToEntry 25 (initWin pc) == some (initWin target))
  | .halt =>
    match winNSteps 11 (initWin pc) with
    | none => false
    | some s' => (refTrans s'.q s'.hd).isNone

def checkPc (pc : ℕ) : Bool :=
  checkPcInstr pc (program pc)

def checkRange (P : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => P start && checkRange P (start + 1) n

theorem checkRange_all (P : ℕ → Bool) :
    ∀ (start n k : ℕ), k < n → checkRange P start n = true → P (start + k) = true := by
  intro start n
  induction n generalizing start with
  | zero => intro k hk _; omega
  | succ n ih =>
    intro k hk h
    unfold checkRange at h
    rw [Bool.and_eq_true] at h
    cases k with
    | zero => simpa [Nat.add_zero] using h.1
    | succ k =>
      have hk' : k < n := Nat.lt_of_succ_lt_succ hk
      have hrec := ih (start + 1) k hk' h.2
      have heq : start + 1 + k = start + (k + 1) := by omega
      rw [heq] at hrec
      exact hrec

theorem checkRange_append (P : ℕ → Bool) (start a b : ℕ) :
    checkRange P start (a + b) = (checkRange P start a && checkRange P (start + a) b) := by
  induction a generalizing start with
  | zero => simp [checkRange]
  | succ a ih =>
    simp only [Nat.succ_add, checkRange, ih (start + 1), Bool.and_assoc]
    congr 2

set_option maxRecDepth 20000 in
private theorem allPcs_0 : checkRange checkPc 0 512 = true := by decide
set_option maxRecDepth 20000 in
private theorem allPcs_1 : checkRange checkPc (0 + 512) 512 = true := by decide
set_option maxRecDepth 20000 in
private theorem allPcs_2 : checkRange checkPc (0 + 512 + 512) 512 = true := by decide
set_option maxRecDepth 20000 in
private theorem allPcs_3 : checkRange checkPc (0 + 512 + 512 + 512) 512 = true := by decide

theorem allPcs_valid : checkRange checkPc 0 2048 = true := by
  rw [show (2048 : ℕ) = 512 + (512 + (512 + 512)) from rfl]
  simp only [checkRange_append, allPcs_0, allPcs_1, allPcs_2, allPcs_3, Bool.and_self]

theorem checkPc_of_lt {pc : ℕ} (hpc : pc < 2048) : checkPc pc = true := by
  have h := checkRange_all checkPc 0 2048 pc hpc allPcs_valid
  simpa using h

/-!
## 4. Universal BDD Dispatch Theorems
-/

theorem dispatch_initReg {pc : ℕ} (hpc : pc < 2048) (hins : program pc = .initReg)
    (R : ListBlank (Fin 2)) :
    nSteps refM 12 (entryCfgR pc R) = some (postPcCfgR 32 pc R) := by
  have h := checkPc_of_lt hpc
  unfold checkPc checkPcInstr at h
  rw [hins, beq_iff_eq] at h
  simpa using winNSteps_sound h R

theorem dispatch_incr {pc : ℕ} {k : Fin 16} (hpc : pc < 2048) (hins : program pc = .incr k)
    (R : ListBlank (Fin 2)) :
    nSteps refM 12 (entryCfgR pc R) = some (postPcCfgR (regIncrState k.val) pc R) := by
  have h := checkPc_of_lt hpc
  unfold checkPc checkPcInstr at h
  rw [hins, beq_iff_eq] at h
  simpa using winNSteps_sound h R

theorem dispatch_decr {pc : ℕ} {k : Fin 16} (hpc : pc < 2048) (hins : program pc = .decr k)
    (R : ListBlank (Fin 2)) :
    nSteps refM 12 (entryCfgR pc R) = some (postPcCfgR (regDecrState k.val) pc R) := by
  have h := checkPc_of_lt hpc
  unfold checkPc checkPcInstr at h
  rw [hins, beq_iff_eq] at h
  simpa using winNSteps_sound h R

theorem dispatch_jump {pc target : ℕ} (hpc : pc < 2048) (hins : program pc = .jump target)
    (R : ListBlank (Fin 2)) :
    target < 2048 ∧ ∃ s, 1 ≤ s ∧ nSteps refM s (entryCfgR pc R) =
      some (entryCfgR target R) := by
  have h := checkPc_of_lt hpc
  unfold checkPc checkPcInstr at h
  rw [hins, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  obtain ⟨s, hs, hsteps⟩ := winRunToEntry_sound h.2 R
  exact ⟨s, hs, by simpa using hsteps⟩

theorem dispatch_halt {pc : ℕ} (hpc : pc < 2048) (hins : program pc = .halt)
    (R : ListBlank (Fin 2)) :
    ∃ ch, nSteps refM 11 (entryCfgR pc R) = some ch ∧ step refM ch = none := by
  have h := checkPc_of_lt hpc
  unfold checkPc checkPcInstr at h
  rw [hins] at h
  dsimp only at h
  rcases hs : winNSteps 11 (initWin pc) with _ | s'
  · rw [hs] at h; cases h
  · rw [hs] at h
    exact ⟨winCfg s' R, by simpa using winNSteps_sound hs R, winStep_halt h R⟩

/-- Universal BDD Dispatch Theorem: for every `pc < 2048` and arbitrary register tape tail `R`,
`refM` starting from `entryCfgR pc R` executes the dispatch/jump phase of `program pc`
without touching `R`. -/
theorem dispatch_step {pc : ℕ} (hpc : pc < 2048) (R : ListBlank (Fin 2)) :
    match program pc with
    | .initReg =>
      nSteps refM 12 (entryCfgR pc R) = some (postPcCfgR 32 pc R)
    | .incr k =>
      nSteps refM 12 (entryCfgR pc R) = some (postPcCfgR (regIncrState k.val) pc R)
    | .decr k =>
      nSteps refM 12 (entryCfgR pc R) = some (postPcCfgR (regDecrState k.val) pc R)
    | .jump target =>
      target < 2048 ∧ ∃ s, 1 ≤ s ∧ nSteps refM s (entryCfgR pc R) = some (entryCfgR target R)
    | .halt =>
      ∃ ch, nSteps refM 11 (entryCfgR pc R) = some ch ∧ step refM ch = none := by
  rcases hins : program pc with _ | k | k | target | _
  · exact dispatch_initReg hpc hins R
  · exact dispatch_incr hpc hins R
  · exact dispatch_decr hpc hins R
  · exact dispatch_jump hpc hins R
  · exact dispatch_halt hpc hins R

/-!
## 5. Abstract Register Machine & Halting Equivalence
-/

/-- Abstract state of the 16-register machine compiled from `riemann.nql`. -/
structure RegCfg where
  pc : ℕ
  regs : List ℕ
  deriving DecidableEq, Repr

/-- Initial configuration of the abstract register machine (`pc = 0, regs = []`). -/
def regInit : RegCfg := ⟨0, []⟩

/-- Single step of the abstract register machine. -/
def regStep (c : RegCfg) : Option RegCfg :=
  match program c.pc with
  | .initReg => some ⟨c.pc + 1, c.regs ++ [0]⟩
  | .incr k => some ⟨c.pc + 1, c.regs.set k.val (c.regs.getD k.val 0 + 1)⟩
  | .decr k =>
    if c.regs.getD k.val 0 == 0 then
      some ⟨c.pc + 1, c.regs⟩
    else
      some ⟨c.pc + 2, c.regs.set k.val (c.regs.getD k.val 0 - 1)⟩
  | .jump target => some ⟨target, c.regs⟩
  | .halt => none

/-- `n`-step execution of the abstract register machine. -/
def regNSteps : ℕ → RegCfg → Option RegCfg
  | 0, c => some c
  | n + 1, c => (regStep c).bind (regNSteps n)

/-- The abstract register machine halts starting from `regInit = ⟨0, []⟩`. -/
def RegHalts : Prop :=
  (eval regStep regInit).Dom

theorem mem_eval_regStep_iff_regNSteps {c₀ ch : RegCfg} :
    ch ∈ eval regStep c₀ ↔ ∃ n, regNSteps n c₀ = some ch ∧ regStep ch = none := by
  constructor
  · intro h
    refine StateTransition.evalInduction h fun a ha ih => ?_
    rcases hs : regStep a with _ | a'
    · have hmem : a ∈ eval regStep a :=
        StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hs⟩
      have heq : ch = a := Part.mem_unique ha hmem
      subst heq
      exact ⟨0, rfl, hs⟩
    · obtain ⟨n, hn, hnone⟩ := ih a' hs
      exact ⟨n + 1, by simp [regNSteps, hs, hn], hnone⟩
  · rintro ⟨n, hn, hnone⟩
    have hreach : Reaches regStep c₀ ch := by
      induction n generalizing c₀ with
      | zero =>
        injection hn with h'
        subst h'
        exact Relation.ReflTransGen.refl
      | succ n ih =>
        unfold regNSteps at hn
        rcases hs : regStep c₀ with _ | c'
        · rw [hs] at hn; cases hn
        · rw [hs, Option.bind_some] at hn
          exact Relation.ReflTransGen.head hs (ih hn)
    exact StateTransition.mem_eval.mpr ⟨hreach, hnone⟩

theorem regHalts_iff_exists_regNSteps :
    RegHalts ↔ ∃ n c, regNSteps n regInit = some c ∧ regStep c = none := by
  unfold RegHalts
  rw [Part.dom_iff_mem]
  simp only [mem_eval_regStep_iff_regNSteps]
  exact ⟨fun ⟨c, n, h⟩ => ⟨n, c, h⟩, fun ⟨n, c, h⟩ => ⟨c, n, h⟩⟩

/-- Structural invariant of the program table on the active range `16 ≤ pc < 1540`. -/
def checkActivePc (pc : ℕ) : Bool :=
  match program pc with
  | .initReg => false
  | .incr _ => (16 ≤ pc + 1) && (pc + 1 < 1540)
  | .decr _ => (16 ≤ pc + 1) && (pc + 2 < 1540)
  | .jump target => (16 ≤ target) && (target < 1540)
  | .halt => pc == 1539

theorem initPcs_valid : checkRange (fun pc => program pc == .initReg) 0 16 = true := by decide

set_option maxRecDepth 20000 in
private theorem activePcs_0 : checkRange checkActivePc 16 381 = true := by decide
set_option maxRecDepth 20000 in
private theorem activePcs_1 : checkRange checkActivePc (16 + 381) 381 = true := by decide
set_option maxRecDepth 20000 in
private theorem activePcs_2 : checkRange checkActivePc (16 + 381 + 381) 381 = true := by decide
set_option maxRecDepth 20000 in
private theorem activePcs_3 :
    checkRange checkActivePc (16 + 381 + 381 + 381) 381 = true := by decide

theorem activePcs_valid : checkRange checkActivePc 16 1524 = true := by
  rw [show (1524 : ℕ) = 381 + (381 + (381 + 381)) from rfl]
  simp only [checkRange_append, activePcs_0, activePcs_1, activePcs_2, activePcs_3,
    Bool.and_self]

theorem program_eq_initReg_of_lt_16 {pc : ℕ} (hpc : pc < 16) :
    program pc = .initReg := by
  have h := checkRange_all (fun pc => program pc == .initReg) 0 16 pc hpc initPcs_valid
  simpa [beq_iff_eq] using h

theorem checkActivePc_of_bounds {pc : ℕ} (h16 : 16 ≤ pc) (h1540 : pc < 1540) :
    checkActivePc pc = true := by
  have h := checkRange_all checkActivePc 16 1524 (pc - 16) (by omega) activePcs_valid
  have heq : 16 + (pc - 16) = pc := by omega
  rw [heq] at h
  exact h

/-- Structural invariant of reachable `RegCfg` states:
either in the initialization phase (`pc < 16` with `regs.length = pc`),
or in the main program (`16 ≤ pc < 1540` with `regs.length = 16`). -/
def RegInv (c : RegCfg) : Prop :=
  (c.pc < 16 ∧ c.regs.length = c.pc) ∨ (16 ≤ c.pc ∧ c.pc < 1540 ∧ c.regs.length = 16)

theorem regInv_init : RegInv regInit :=
  Or.inl ⟨by decide, rfl⟩

theorem regStep_preserves_regInv {c c' : RegCfg} (hInv : RegInv c) (hs : regStep c = some c') :
    RegInv c' := by
  rcases hInv with ⟨hpc, hlen⟩ | ⟨h16, h1540, hlen⟩
  · have hins := program_eq_initReg_of_lt_16 hpc
    unfold regStep at hs
    rw [hins] at hs
    injection hs with hs'
    subst hs'
    dsimp only [RegInv]
    by_cases h15 : c.pc + 1 < 16
    · exact Or.inl ⟨h15, by simp [hlen]⟩
    · exact Or.inr ⟨by omega, by omega, by simp [hlen]; omega⟩
  · have hact := checkActivePc_of_bounds h16 h1540
    unfold checkActivePc at hact
    unfold regStep at hs
    rcases hins : program c.pc with _ | k | k | target | _
    · rw [hins] at hact; cases hact
    · rw [hins, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hact
      rw [hins] at hs
      injection hs with hs'
      subst hs'
      dsimp only [RegInv]
      exact Or.inr ⟨hact.1, hact.2, by simp [hlen]⟩
    · rw [hins, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hact
      rw [hins] at hs
      dsimp only at hs
      rcases h12 : hact with ⟨hact1, hact2⟩
      by_cases hzero : (c.regs.getD k.val 0 == 0) = true
      · rw [ite_eq_left hzero] at hs
        injection hs with hs'
        subst hs'
        dsimp only [RegInv]
        exact Or.inr ⟨hact1, by omega, hlen⟩
      · rw [ite_eq_right hzero] at hs
        injection hs with hs'
        subst hs'
        dsimp only [RegInv]
        exact Or.inr ⟨by omega, hact2, by simp [hlen]⟩
    · rw [hins, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hact
      rw [hins] at hs
      injection hs with hs'
      subst hs'
      dsimp only [RegInv]
      exact Or.inr ⟨hact.1, hact.2, hlen⟩
    · rw [hins] at hs; cases hs

/-- Combining the Layer 2 BDD Dispatcher with the three Layer 1 primitive register gadget lemmas
yields a complete single-step simulation of `regStep` by `refM`:
for any configuration `c : RegCfg` satisfying `RegInv c`,
- if `regStep c = some c'`, then `refM` steps from `entryCfg c.pc c.regs` to
  `entryCfg c'.pc c'.regs` in `s ≥ 1` steps;
- if `regStep c = none`, then `refM` reaches a halting configuration in 11 steps. -/
theorem tm_simulates_regStep
    (hInit : ∀ pc regs, pc + 1 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg 32 pc regs) =
        some (entryCfg (pc + 1) (regs ++ [0])))
    (hIncr : ∀ (k : Fin 16) pc (regs : List ℕ), k.val < regs.length → pc + 1 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg (regIncrState k.val) pc regs) =
        some (entryCfg (pc + 1) (regs.set k.val (regs.getD k.val 0 + 1))))
    (hDecr : ∀ (k : Fin 16) pc (regs : List ℕ), k.val < regs.length → pc + 2 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg (regDecrState k.val) pc regs) =
        some (if regs.getD k.val 0 == 0 then
          entryCfg (pc + 1) regs
        else
          entryCfg (pc + 2) (regs.set k.val (regs.getD k.val 0 - 1))))
    {c : RegCfg} (hInv : RegInv c) :
    match regStep c with
    | some c' =>
      ∃ s, 1 ≤ s ∧ nSteps refM s (entryCfg c.pc c.regs) = some (entryCfg c'.pc c'.regs)
    | none =>
      ∃ ch, nSteps refM 11 (entryCfg c.pc c.regs) = some ch ∧ step refM ch = none := by
  have hpc2048 : c.pc < 2048 := by
    rcases hInv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega
  unfold regStep
  rcases hins : program c.pc with _ | k | k | target | _
  · have hd := dispatch_initReg hpc2048 hins (regsTape c.regs)
    have hpc1 : c.pc + 1 < 2048 := by
      rcases hInv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> omega
    obtain ⟨s, hs, hleaf⟩ := hInit c.pc c.regs hpc1
    exact ⟨12 + s, by omega, nSteps_bind_eq hd hleaf⟩
  · have h16 : 16 ≤ c.pc ∧ c.pc < 1540 ∧ c.regs.length = 16 := by
      rcases hInv with ⟨h, _⟩ | hmain
      · have := program_eq_initReg_of_lt_16 h; rw [hins] at this; cases this
      · exact hmain
    have hd := dispatch_incr hpc2048 hins (regsTape c.regs)
    have hk : k.val < c.regs.length := by rw [h16.2.2]; exact k.isLt
    obtain ⟨s, hs, hleaf⟩ := hIncr k c.pc c.regs hk (by omega)
    exact ⟨12 + s, by omega, nSteps_bind_eq hd hleaf⟩
  · have h16 : 16 ≤ c.pc ∧ c.pc < 1540 ∧ c.regs.length = 16 := by
      rcases hInv with ⟨h, _⟩ | hmain
      · have := program_eq_initReg_of_lt_16 h; rw [hins] at this; cases this
      · exact hmain
    have hd := dispatch_decr hpc2048 hins (regsTape c.regs)
    have hk : k.val < c.regs.length := by rw [h16.2.2]; exact k.isLt
    obtain ⟨s, hs, hleaf⟩ := hDecr k c.pc c.regs hk (by omega)
    dsimp only
    by_cases hzero : (c.regs.getD k.val 0 == 0) = true
    · rw [ite_eq_left hzero] at hleaf ⊢
      dsimp only
      exact ⟨12 + s, by omega, nSteps_bind_eq hd hleaf⟩
    · rw [ite_eq_right hzero] at hleaf ⊢
      dsimp only
      exact ⟨12 + s, by omega, nSteps_bind_eq hd hleaf⟩
  · obtain ⟨_, s, hs, hd⟩ := dispatch_jump hpc2048 hins (regsTape c.regs)
    exact ⟨s, hs, hd⟩
  · exact dispatch_halt hpc2048 hins (regsTape c.regs)

/-- Forward simulation: if the abstract register machine halts from `c` (`RegInv c`),
then `refM` halts from `entryCfg c.pc c.regs`. -/
theorem tm_eval_dom_of_reg_eval_dom
    (hInit : ∀ pc regs, pc + 1 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg 32 pc regs) =
        some (entryCfg (pc + 1) (regs ++ [0])))
    (hIncr : ∀ (k : Fin 16) pc (regs : List ℕ), k.val < regs.length → pc + 1 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg (regIncrState k.val) pc regs) =
        some (entryCfg (pc + 1) (regs.set k.val (regs.getD k.val 0 + 1))))
    (hDecr : ∀ (k : Fin 16) pc (regs : List ℕ), k.val < regs.length → pc + 2 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg (regDecrState k.val) pc regs) =
        some (if regs.getD k.val 0 == 0 then
          entryCfg (pc + 1) regs
        else
          entryCfg (pc + 2) (regs.set k.val (regs.getD k.val 0 - 1))))
    {c : RegCfg} (hInv : RegInv c) (hDom : (eval regStep c).Dom) :
    (eval (step refM) (entryCfg c.pc c.regs)).Dom := by
  rw [Part.dom_iff_mem] at hDom
  rcases hDom with ⟨ch_reg, hmem⟩
  revert hInv
  refine StateTransition.evalInduction hmem fun a _ ih hInv => ?_
  have hsim := tm_simulates_regStep hInit hIncr hDecr hInv
  rcases hs : regStep a with _ | a'
  · rw [hs] at hsim
    obtain ⟨ch, h11, hnone⟩ := hsim
    rw [Part.dom_iff_mem]
    exact ⟨ch, mem_eval_iff_nSteps.mpr ⟨11, h11, hnone⟩⟩
  · rw [hs] at hsim
    obtain ⟨s, _, hsteps⟩ := hsim
    have hInv' := regStep_preserves_regInv hInv hs
    exact (nSteps_eval_dom hsteps).mpr (ih a' hs hInv')

/-- Backward simulation: if `refM` halts in `N` steps from `entryCfg c.pc c.regs` (`RegInv c`),
then the abstract register machine halts from `c`. -/
theorem reg_eval_dom_of_tm_nSteps_halt
    (hInit : ∀ pc regs, pc + 1 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg 32 pc regs) =
        some (entryCfg (pc + 1) (regs ++ [0])))
    (hIncr : ∀ (k : Fin 16) pc (regs : List ℕ), k.val < regs.length → pc + 1 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg (regIncrState k.val) pc regs) =
        some (entryCfg (pc + 1) (regs.set k.val (regs.getD k.val 0 + 1))))
    (hDecr : ∀ (k : Fin 16) pc (regs : List ℕ), k.val < regs.length → pc + 2 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg (regDecrState k.val) pc regs) =
        some (if regs.getD k.val 0 == 0 then
          entryCfg (pc + 1) regs
        else
          entryCfg (pc + 2) (regs.set k.val (regs.getD k.val 0 - 1)))) :
    ∀ N {c : RegCfg} {ch : Cfg 744 2},
      RegInv c →
      nSteps refM N (entryCfg c.pc c.regs) = some ch →
      step refM ch = none →
      (eval regStep c).Dom := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro c ch hInv hN hnone
    have hsim := tm_simulates_regStep hInit hIncr hDecr hInv
    rcases hs : regStep c with _ | c'
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
      have hInv' := regStep_preserves_regInv hInv hs
      have hDom' := ih (N - s) (by omega) hInv' hN hnone
      have hreach : Reaches regStep c c' :=
        Relation.ReflTransGen.head hs Relation.ReflTransGen.refl
      rwa [StateTransition.reaches_eval hreach]

/-- Complete equivalence between `Halts refM` and `RegHalts`, given the Layer 1 leaf
evaluation theorems. -/
theorem halts_reference_iff_regHalts
    (hInit0 : entryCfg 0 [] = init)
    (hInit : ∀ pc regs, pc + 1 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg 32 pc regs) =
        some (entryCfg (pc + 1) (regs ++ [0])))
    (hIncr : ∀ (k : Fin 16) pc (regs : List ℕ), k.val < regs.length → pc + 1 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg (regIncrState k.val) pc regs) =
        some (entryCfg (pc + 1) (regs.set k.val (regs.getD k.val 0 + 1))))
    (hDecr : ∀ (k : Fin 16) pc (regs : List ℕ), k.val < regs.length → pc + 2 < 2048 →
      ∃ s, 1 ≤ s ∧ nSteps refM s (postPcCfg (regDecrState k.val) pc regs) =
        some (if regs.getD k.val 0 == 0 then
          entryCfg (pc + 1) regs
        else
          entryCfg (pc + 2) (regs.set k.val (regs.getD k.val 0 - 1)))) :
    Halts refM ↔ RegHalts := by
  unfold ConjectureMachines.Halts RegHalts
  have hInit_eq : entryCfg regInit.pc regInit.regs = init := hInit0
  rw [← hInit_eq]
  constructor
  · intro hDom
    rw [Part.dom_iff_mem] at hDom
    rcases hDom with ⟨ch, hmem⟩
    obtain ⟨N, hN, hnone⟩ := mem_eval_iff_nSteps.mp hmem
    exact reg_eval_dom_of_tm_nSteps_halt hInit hIncr hDecr N regInv_init hN hnone
  · intro hDom
    exact tm_eval_dom_of_reg_eval_dom hInit hIncr hDecr regInv_init hDom

end ConjectureMachines.Riemann543.Semantics
