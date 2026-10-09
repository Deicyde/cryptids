# Verification with `leanprover/comparator`

This directory contains configuration files for verifying the proofs in [`Cryptids/`](../Cryptids/)
against the unproved challenge specifications in [`Challenge/`](../Challenge/) using
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## Overview

Each [`Challenge/*.lean`](../Challenge/) module imports only the base Turing machine definitions
([`Cryptids/Machines.lean`](../Cryptids/Machines.lean)) and Mathlib, defines the `reference` and
`candidate` machines (and `GoldbachConjecture`), and states the target equivalence theorems with
`sorry`.

Comparator exports both the `Challenge` and `Cryptids` modules via `lean4export`, verifies that:
1. Every target theorem and all of its transitive definition dependencies (`reference`, `candidate`,
   `Halts`, `GoldbachConjecture`, etc.) match identically between `Challenge` and `Cryptids`.
2. Only the standard Lean 4 axioms (`propext`, `Quot.sound`, `Classical.choice`) are used.
3. The exported proof terms are accepted by the Lean kernel (and any configured external kernels
   such as `nanoda`).

## Configurations

| Config File | Challenge Module | Solution Module | Verified Theorems |
| :--- | :--- | :--- | :--- |
| [`all.json`](./all.json) | `Challenge` | `Cryptids` | All 20 state-reduction, equivalence, and semantics theorems |
| [`goldbach_24.json`](./goldbach_24.json) | `Challenge.Goldbach24` | `Cryptids.Goldbach24` | `candidate_fewer_states`, `candidate_equivalent` |
| [`goldbach_semantics.json`](./goldbach_semantics.json) | `Challenge.Goldbach24` | `Cryptids.Semantics.Goldbach` | `halts_reference_iff_not_goldbach`, `halts_candidate_iff_not_goldbach` |
| [`zf_431.json`](./zf_431.json) | `Challenge.Zf431` | `Cryptids.Zf431` | `candidate_fewer_states`, `candidate_equivalent` |
| [`zf_430.json`](./zf_430.json) | `Challenge.Zf430` | `Cryptids.Zf430` | `candidate_fewer_states`, `candidate_equivalent` |
| [`zf_429.json`](./zf_429.json) | `Challenge.Zf429` | `Cryptids.Zf429` | `candidate_fewer_states`, `candidate_equivalent` |
| [`zf_semantics.json`](./zf_semantics.json) | `Challenge.Zf429` | `Cryptids.Semantics.Zf` | `zfProvable_sound_zfSet`, `not_zfInconsistent`, `halts_reference_iff_wadeZFInconsistent`, `halts_candidate_429_iff_wadeZFInconsistent` |
| [`riemann_543.json`](./riemann_543.json) | `Challenge.Riemann543` | `Cryptids.Riemann543` | `candidate_fewer_states`, `candidate_equivalent` |
| [`riemann_semantics.json`](./riemann_semantics.json) | `Challenge.Riemann543` | `Cryptids.Semantics.Riemann` | `halts_reference_iff_exists_counterexample`, `halts_candidate_iff_exists_counterexample`, `halts_reference_iff_not_riemannHypothesis`, `halts_candidate_iff_not_riemannHypothesis` |

## Usage

Ensure [`landrun`](https://github.com/Zouuup/landrun) and
[`lean4export`](https://github.com/leanprover/lean4export) are in `PATH`, then run from the
repository root:

```bash
lake exe cache get
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory "$(pwd)" -- \
  bash -c 'lake env comparator comparator/all.json'
```
