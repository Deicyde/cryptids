/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Propositions

/-!
# Challenge.Goldbach24

24-state Goldbach Turing machine challenge specification.
-/

@[expose] public section

namespace ConjectureMachines.Goldbach24

/-- 25 states, 2 symbols,
SHA-256 `da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67`. -/
def reference : Machine 25 2 := Machine.ofRows [
  [some (1, .right, 1), some (1, .right, 3)],
  [some (1, .left, 2), some (1, .right, 1)],
  [some (0, .right, 0), some (1, .left, 2)],
  [some (0, .left, 16), some (1, .right, 4)],
  [some (0, .left, 5), some (1, .right, 6)],
  [some (0, .left, 2), some (1, .left, 5)],
  [some (0, .left, 5), some (0, .left, 7)],
  [some (1, .left, 16), some (1, .left, 8)],
  [some (0, .right, 9), some (0, .left, 8)],
  [some (1, .right, 10), some (0, .left, 9)],
  [some (0, .right, 11), some (0, .right, 18)],
  [some (1, .right, 11), some (0, .right, 12)],
  [some (1, .right, 13), some (1, .right, 12)],
  [some (0, .left, 14), some (0, .left, 20)],
  [some (0, .left, 15), some (1, .left, 14)],
  [some (1, .right, 7), some (1, .left, 23)],
  [some (1, .left, 17), some (1, .left, 16)],
  [some (0, .right, 10), some (0, .left, 19)],
  [some (1, .left, 17), some (1, .right, 18)],
  [none, some (1, .right, 2)],
  [some (1, .left, 21), some (1, .left, 20)],
  [some (0, .left, 22), some (0, .left, 9)],
  [some (0, .right, 10), some (0, .left, 22)],
  [some (1, .right, 24), some (1, .left, 23)],
  [some (1, .right, 4), some (1, .right, 24)]]

/-- 24 states, 2 symbols,
SHA-256 `9b8b92a609ca9ae891856957b21a4d5ff9ba4317c27835e31265a249d236b2dc`. -/
def candidate : Machine 24 2 := Machine.ofRows [
  [some (1, .right, 1), some (1, .right, 3)],
  [some (1, .right, 17), some (1, .right, 1)],
  [some (0, .right, 0), some (1, .left, 2)],
  [some (0, .left, 5), some (1, .right, 4)],
  [some (0, .left, 15), some (1, .right, 6)],
  [some (0, .left, 2), some (1, .left, 5)],
  [some (0, .left, 5), some (0, .left, 7)],
  [some (1, .left, 15), some (1, .left, 21)],
  [some (1, .right, 9), some (0, .left, 8)],
  [some (0, .right, 10), some (0, .right, 17)],
  [some (1, .right, 10), some (0, .right, 11)],
  [some (1, .right, 12), some (1, .right, 11)],
  [some (0, .left, 13), some (0, .left, 19)],
  [some (0, .left, 14), some (1, .left, 13)],
  [some (1, .right, 7), some (1, .left, 22)],
  [some (1, .left, 16), some (1, .left, 15)],
  [some (0, .right, 9), some (0, .left, 18)],
  [some (1, .left, 16), some (1, .right, 17)],
  [none, some (1, .right, 2)],
  [some (1, .left, 20), some (1, .left, 19)],
  [some (0, .left, 21), some (0, .left, 8)],
  [some (0, .right, 9), some (0, .left, 21)],
  [some (1, .right, 23), some (1, .left, 22)],
  [some (1, .right, 4), some (1, .right, 23)]]

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
