/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines
public import Cryptids.Propositions
public import Cryptids.Goldbach24
public import Cryptids.Riemann120
public import Cryptids.Riemann543
public import Cryptids.Zf393
public import Cryptids.Zf429
public import Cryptids.Zf430
public import Cryptids.Zf431
public import Cryptids.Semantics.Goldbach
public import Cryptids.Semantics.Riemann
public import Cryptids.Semantics.Riemann120
public import Cryptids.Semantics.Zf
public import Cryptids.Semantics.Zf393

/-!
# Certified State Reductions & Formalized Conjecture-Checking Turing Machines

This library formalizes smaller 2-symbol Turing machines for **Goldbach's Conjecture** (`25 → 24`
states), **ZF Set Theory Consistency** (`432 → 429` states), and the **Riemann Hypothesis**
(`744 → 543` states), as well as complete Lean 4 formalizations of the 2026 state-of-the-art
machines for **ZF Set Theory Consistency** (`393` states, Wade, August 2026) and the **Riemann
Hypothesis** (`120` states, Shunia, September 2026), linking their blank-tape halting problem to
Mathlib's statements:

- `Cryptids.Propositions` — Shared definitions of `GoldbachConjecture`,
  `MatiyasevichRiemannCounterexample`, `ZFInconsistent`, and `WadeZFInconsistent`.
- `Cryptids.Machines` — Turing machine execution model, bundled machines (`BundledMachine`), and
  machine table definitions (`ConjectureMachines.Machines.*`).
- `Cryptids.Goldbach24`, `Cryptids.Zf431`, `Cryptids.Zf430`, `Cryptids.Zf429`,
  `Cryptids.Riemann543` — Proofs of `candidate.states < reference.states` and
  `Halts candidate ↔ Halts reference`.
- `Cryptids.Zf393`, `Cryptids.Semantics.Zf393` — Wade's 393-state ZF machine (`zf393`) and
  end-to-end proofs of `ConjectureMachines.Zf393.halts_zf393_iff_zfInconsistent` and
  `ConjectureMachines.Zf393.not_halts_zf393`.
- `Cryptids.Riemann120`, `Cryptids.Semantics.Riemann120` — Shunia's 120-state Riemann Hypothesis
  machine (`riemann120`) and end-to-end proof of
  `ConjectureMachines.Riemann120.halts_riemann120_iff_not_riemannHypothesis`.
- `Cryptids.Semantics.Goldbach`, `Cryptids.Semantics.Zf`, `Cryptids.Semantics.Riemann` —
  End-to-end proofs linking halting from the blank tape to the corresponding mathematical
  conjectures.
-/

