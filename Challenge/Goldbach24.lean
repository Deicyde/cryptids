/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Machines.Goldbach25
public import Cryptids.Machines.Goldbach24
public import Cryptids.Propositions

/-!
# Challenge.Goldbach24

24-state Goldbach Turing machine challenge specification.
-/

@[expose] public section

namespace ConjectureMachines.Goldbach24

/-- 25-state Goldbach reference machine (`goldbach_25`, Yao & Leng 2024). -/
abbrev reference : Machine 25 2 := Machines.goldbach25

/-- 24-state Goldbach candidate machine (`goldbach_24`). -/
abbrev candidate : Machine 24 2 := Machines.goldbach24

theorem candidate_equivalent : Halts candidate ↔ Halts reference := by
  sorry

namespace Semantics

/-- The 25-state baseline machine `reference` (`goldbach_25`) halts on the blank tape
if and only if Goldbach's conjecture is false. -/
theorem halts_reference_iff_not_goldbach :
    Halts reference ↔ ¬ GoldbachConjecture := by
  sorry

/-- The 24-state machine `candidate` (`goldbach_24`) halts on the blank tape
if and only if Goldbach's conjecture is false. -/
theorem halts_candidate_iff_not_goldbach :
    Halts candidate ↔ ¬ GoldbachConjecture := by
  sorry

end Semantics

end ConjectureMachines.Goldbach24
