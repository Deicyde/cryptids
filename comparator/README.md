# Verification with `leanprover/comparator`

This directory contains configuration files for verifying the proofs in [`Cryptids/`](../Cryptids/)
and [`BusyBeaver/`](../BusyBeaver/) against the self-contained challenge specifications in
[`Challenge.lean`](../Challenge.lean) and [`BusyBeaverChallenge.lean`](../BusyBeaverChallenge.lean)
using [`leanprover/comparator`](https://github.com/leanprover/comparator).

## Overview

- [`Challenge.lean`](../Challenge.lean) imports **only** Mathlib and Lean core (`Lean.Elab.Term`),
  defines all conjecture-checking baseline and candidate machines (`reference` and `candidate`),
  states the target mathematical propositions (`GoldbachConjecture`,
  `MatiyasevichRiemannCounterexample`, `ZFProvable`, `WadeZFProvable`, etc.), and states all 22
  target state-reduction, equivalence, and semantics theorems with `sorry`.
- [`BusyBeaverChallenge.lean`](../BusyBeaverChallenge.lean) imports **only** Mathlib and Lean core
  (`Lean.Elab.Term`), defines the shared `BusyBeaver` Post-Turing execution model, accelerated
  `TapePatternSet`, `StackPatternSet`, and Collatz-like acceleration semantics (`IsClosedPatternSet`,
  `HasCollatzReduction`, `IsClosedStackPatternSet`, `HasStackedCollatzReduction`,
  `IsValidAcceleration`, `CollatzHalts`, `IsHalt`, `IsNotHalt`), and `load_rle_machine%` once,
  and states all 236 `BB(6)` and `BB(3, 3)` holdout theorems (`is_closed_pattern_set` /
  `is_closed_stack_pattern_set`, `has_collatz_reduction` / `has_stacked_collatz_reduction`,
  `is_valid_acceleration`, and `isHalt_iff_acceleration` across the 59 machines) with `sorry`.
- [`IndependenceChallenge.lean`](../IndependenceChallenge.lean) imports `Challenge` and states
  that `zf393` and `zf380` are independent of ZFC in model-theoretic form: some model of ZFC
  thinks the machine halts and some model thinks it runs forever. ZFC is a structure whose fields
  are the textbook axioms (`IsZFC`), with Separation and Replacement restricted to first-order
  definable properties, and "the machine halts" (`HaltsIn`) is a halting run inside the model.
  Unlike `Halts zf393 ↔ ZFInconsistent`, the target is provably false for trivially non-halting
  machines, so it cannot be discharged through Lean's proof of `Con(ZF)`. The targets are open;
  `independence.json` audits the companion theorems and reductions proved so far.

Comparator exports both the challenge module (`Challenge` or `BusyBeaverChallenge`) and the
solution module (`Cryptids` or `BusyBeaver`) via `leanexport`, verifying in a Bubblewrap sandbox
that:
1. Every target theorem and all of its transitive definition dependencies match identically between
   the challenge module and the solution module.
2. Only the standard Lean 4 axioms (`propext`, `Quot.sound`, `Classical.choice`) are used.
3. The exported proof terms are accepted by the Lean default kernel.

## Configurations

| Config File | Challenge Module | Solution Module | Verified Theorems |
| :--- | :--- | :--- | :--- |
| [`all.json`](./all.json) | `Challenge` | `Cryptids` | All 22 conjecture-checking state-reduction, equivalence, and semantics theorems |
| [`busy_beaver.json`](./busy_beaver.json) | `BusyBeaverChallenge` | `BusyBeaver` | All 236 `BB(6)` and `BB(3, 3)` holdout Level A and Level B theorems (`is_closed_pattern_set`, `has_collatz_reduction`, `is_closed_stack_pattern_set`, `has_stacked_collatz_reduction`, `is_valid_acceleration`, `isHalt_iff_acceleration`) |
| [`goldbach_21.json`](./goldbach_21.json) | `Challenge` | `Cryptids.Goldbach21` | `candidate_fewer_states`, `candidate_equivalent` |
| [`goldbach_semantics.json`](./goldbach_semantics.json) | `Challenge` | `Cryptids.Semantics.Goldbach` | `halts_reference_iff_not_goldbach`, `halts_candidate_iff_not_goldbach` |
| [`zf_380.json`](./zf_380.json) | `Challenge` | `Cryptids.Zf380` | `candidate_fewer_states`, `candidate_equivalent` |
| [`zf_393.json`](./zf_393.json) | `Challenge` | `Cryptids.Semantics.Zf393` | `halts_zf393_iff_zfInconsistent`, `not_halts_zf393`, `halts_candidate_iff_zfInconsistent`, `not_halts_candidate` |
| [`zf_semantics.json`](./zf_semantics.json) | `Challenge` | `Cryptids.Semantics.Zf` | `zfProvable_sound_zfSet`, `not_zfInconsistent`, `halts_zf432_iff_wadeZFInconsistent` |
| [`riemann_104.json`](./riemann_104.json) | `Challenge` | `Cryptids.Riemann104` | `candidate_fewer_states`, `candidate_equivalent` |
| [`riemann_95.json`](./riemann_95.json) | `Challenge` | `Cryptids.Semantics.Riemann95` | `candidate_fewer_states`, `candidate_equivalent`, `halts_candidate_iff_not_riemannHypothesis` |
| [`riemann_120.json`](./riemann_120.json) | `Challenge` | `Cryptids.Semantics.Riemann120` | `halts_riemann120_iff_not_riemannHypothesis`, `halts_candidate_iff_not_riemannHypothesis` |
| [`riemann_semantics.json`](./riemann_semantics.json) | `Challenge` | `Cryptids.Semantics.Riemann` | `halts_riemann744_iff_exists_counterexample`, `halts_riemann744_iff_not_riemannHypothesis` |
| [`independence.json`](./independence.json) | `IndependenceChallenge` | `Cryptids.Independence` | The 11 proved companions and reductions toward the open independence targets (`isZFC_zfSet`, `haltsIn_zfSet_iff`, `haltsIn_firstOrder`, `haltsIn_zfFormula`, `not_haltsIn_haltOnOne`, `easy_half`, `independent_without_Foundation_of_ZFC`, `not_haltsIn_of_total`, `not_independent_of_total`, `rightForever_not_independent_of_ZFC`, `haltOnOne_not_independent_of_ZFC`) |

## Usage

From the repository root (with `bwrap` installed):

```bash
lake exe cache get
lake comparator --config comparator/all.json
lake comparator --config comparator/independence.json
lake comparator --config comparator/busy_beaver.json
```
