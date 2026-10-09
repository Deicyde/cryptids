/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Propositions
public import Cryptids.Goldbach24
public import Cryptids.Riemann543
public import Cryptids.Zf429
public import Cryptids.Zf430
public import Cryptids.Zf431
public import Cryptids.Semantics.Goldbach
public import Cryptids.Semantics.Riemann
public import Cryptids.Semantics.Zf

/-!
# Certified State Reductions of Conjecture-Checking Turing Machines

This library formalizes smaller 2-symbol Turing machines for **Goldbach's Conjecture** (`25 → 24`
states), **ZF Set Theory Consistency** (`432 → 429` states), and the **Riemann Hypothesis**
(`744 → 543` states), together with Lean 4 proofs of their state reduction, halting equivalence,
and end-to-end mathematical semantics:

- `Cryptids.Propositions` — Shared definitions of `GoldbachConjecture`,
  `MatiyasevichRiemannCounterexample`, `ZFInconsistent`, and `WadeZFInconsistent`.
- `Cryptids.Machines` — Turing machine execution model, bundled machines (`BundledMachine`), and
  all reference and candidate machine definitions (`ConjectureMachines.Machines.*`).
- `Cryptids.Goldbach24`, `Cryptids.Zf431`, `Cryptids.Zf430`, `Cryptids.Zf429`,
  `Cryptids.Riemann543` — Proofs of `candidate.states < reference.states` and
  `Halts candidate ↔ Halts reference`.
- `Cryptids.Semantics.Goldbach`, `Cryptids.Semantics.Zf`, `Cryptids.Semantics.Riemann` —
  End-to-end proofs linking halting from the blank tape to the corresponding mathematical
  conjectures.
-/
