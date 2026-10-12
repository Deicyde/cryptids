# Verification with `leanprover/comparator`

This directory contains configuration files for verifying the proofs in [`Cryptids/`](../Cryptids/)
against the self-contained challenge specification in [`Challenge.lean`](../Challenge.lean) using
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## Overview

[`Challenge.lean`](../Challenge.lean) imports **only** Mathlib and Lean core (`Lean.Elab.Term`),
defines all baseline and candidate machines (`reference` and `candidate`), states the target
mathematical propositions (`GoldbachConjecture`, `MatiyasevichRiemannCounterexample`,
`ZFProvable`, `WadeZFProvable`, etc.), and states all 23 target equivalence and semantics theorems
with `sorry`.

Comparator exports both `Challenge` and `Cryptids` via `lean4export`, verifies in a Bubblewrap
sandbox that:
1. Every target theorem and all of its transitive definition dependencies (`reference`, `candidate`,
   `Halts`, `GoldbachConjecture`, etc.) match identically between `Challenge` and `Cryptids`.
2. Only the standard Lean 4 axioms (`propext`, `Quot.sound`, `Classical.choice`) are used.
3. The exported proof terms are accepted by the Lean default kernel.

## Configurations

| Config File | Challenge Module | Solution Module | Verified Theorems |
| :--- | :--- | :--- | :--- |
| [`all.json`](./all.json) | `Challenge` | `Cryptids` | All 23 state-reduction, equivalence, and semantics theorems |
| [`goldbach_21.json`](./goldbach_21.json) | `Challenge` | `Cryptids.Goldbach21` | `candidate_fewer_states`, `candidate_equivalent` |
| [`goldbach_semantics.json`](./goldbach_semantics.json) | `Challenge` | `Cryptids.Semantics.Goldbach` | `halts_reference_iff_not_goldbach`, `halts_candidate_iff_not_goldbach` |
| [`zf_431.json`](./zf_431.json) | `Challenge` | `Cryptids.Zf431` | `candidate_fewer_states`, `candidate_equivalent` |
| [`zf_430.json`](./zf_430.json) | `Challenge` | `Cryptids.Zf430` | `candidate_fewer_states`, `candidate_equivalent` |
| [`zf_429.json`](./zf_429.json) | `Challenge` | `Cryptids.Zf429` | `candidate_fewer_states`, `candidate_equivalent` |
| [`zf_393.json`](./zf_393.json) | `Challenge` | `Cryptids.Semantics.Zf393` | `halts_zf393_iff_zfInconsistent`, `not_halts_zf393` |
| [`zf_semantics.json`](./zf_semantics.json) | `Challenge` | `Cryptids.Semantics.Zf` | `zfProvable_sound_zfSet`, `not_zfInconsistent`, `halts_reference_iff_wadeZFInconsistent`, `halts_candidate_429_iff_wadeZFInconsistent` |
| [`riemann_543.json`](./riemann_543.json) | `Challenge` | `Cryptids.Riemann543` | `candidate_fewer_states`, `candidate_equivalent` |
| [`riemann_120.json`](./riemann_120.json) | `Challenge` | `Cryptids.Semantics.Riemann120` | `halts_riemann120_iff_not_riemannHypothesis` |
| [`riemann_semantics.json`](./riemann_semantics.json) | `Challenge` | `Cryptids.Semantics.Riemann` | `halts_reference_iff_exists_counterexample`, `halts_candidate_iff_exists_counterexample`, `halts_reference_iff_not_riemannHypothesis`, `halts_candidate_iff_not_riemannHypothesis` |

## Usage

From the repository root (with `bwrap` installed):

```bash
lake exe cache get
lake comparator --config comparator/all.json
```
