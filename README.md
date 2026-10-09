# Certified State Reductions of Conjecture-Checking Turing Machines

This repository contains smaller, formally verified 2-symbol Turing machines for **Goldbach's Conjecture** (`25 -> 24` states), **ZF Set Theory Consistency** (`432 -> 429` states), and the **Riemann Hypothesis** (`744 -> 543` states), together with Lean 4 proofs of their halting equivalence and mathematical semantics, discovered and formalized by **Maxence Faldor** and **Moritz Firsching** using **Gemini Argon**.

> [!IMPORTANT]
> **Formal Verification & Secondary-Metric Trade-offs:**
> 1. **What Lean 4 formally proves:**
>    - **Halting equivalence (`Halts candidate ↔ Halts reference`):** Each proof module in [`Cryptids/`](Cryptids/) is checked from scratch by the Lean 4 kernel (`v4.34.1`) with zero `sorry`s and only standard axioms (`{propext, Classical.choice, Quot.sound}`) against [`Cryptids/Machines.lean`](Cryptids/Machines.lean) and can be independently audited with [`leanprover/comparator`](comparator/README.md). The proved theorems certify that each reduced candidate machine halts starting from the blank tape (`init`) if and only if the published reference baseline machine (`goldbach_25`, `zf_432`, or `riemann_744`) halts starting from the blank tape.
>    - **End-to-end Goldbach semantics (`Halts candidate ↔ ¬ GoldbachConjecture`):** [`Cryptids/Semantics/Goldbach.lean`](Cryptids/Semantics/Goldbach.lean) formally proves in Lean 4 that both the 25-state baseline (`goldbach_25`) and the 24-state candidate (`goldbach_24`) halt on the blank tape if and only if Goldbach's conjecture (`∀ n > 2, Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q`) is false.
>    - **End-to-end ZF Consistency semantics (`Halts candidate ↔ WadeZFInconsistent`, `¬ ZFInconsistent`, `0 sorry`s):** [`Cryptids/Semantics/Zf.lean`](Cryptids/Semantics/Zf.lean) (and [`Cryptids/Semantics/Zf/`](Cryptids/Semantics/Zf/)) formally proves in Lean 4 with **zero `sorry`s** that the 432-state baseline (`zf_432_wade.tm`) and the 431-, 430-, and 429-state candidates (`zf_431`, `zf_430`, `zf_429`) halt on the blank tape if and only if the 20-clause deductive system `WadeZFProvable` enumerated by `zf_432_wade.tm` derives $v_0 \in v_0$ (`WadeZFInconsistent`), and proves full soundness of O'Rear's `zf2.nql` Hilbert system `ZFProvable` in Mathlib's cumulative hierarchy `ZFSet.{0}` (`not_zfInconsistent`). In verifying all 135 steps of `main()`, this formalization also uncovered the `B6a` register-restoration bug in `zf_432_wade.tm` (subsequently fixed upstream by Wade in commit `10fcf152b3`).
>    - **End-to-end Riemann Hypothesis semantics (`Halts candidate ↔ ¬ RiemannHypothesis`, `0 sorry`s):** [`Cryptids/Semantics/Riemann.lean`](Cryptids/Semantics/Riemann.lean) (and [`Cryptids/Semantics/Riemann/`](Cryptids/Semantics/Riemann/)) formally proves in Lean 4 with **zero `sorry`s** that both the 744-state NQL baseline (`riemann_744`) and the 543-state candidate (`riemann_543`) halt on the blank tape if and only if Mathlib's `RiemannHypothesis` is false, including full formalizations of the 16-register NQL counter machine, the harmonic/LCM/Chebyshev $\psi(x)$ bridge, Schmidt's (1903) oscillation theorem, and Schoenfeld's (1976) explicit bound. See [`Cryptids/Semantics/README.md`](Cryptids/Semantics/README.md) for architecture and provenance.
> 2. **Upstream baseline provenance:** [`verify.py`](verify.py) re-compiles all three baseline tables byte-for-byte from their verbatim upstream source files (`baselines/sources/`).
> 3. **Secondary runtime step trade-offs:**
>    - **`goldbach_24` (`25 -> 24` states, `-4.00%`):** Trades **`+11.74%` runtime steps** (`232,580` vs `208,135` steps at outer-loop checkpoint `155`) for `-1` state by shifting unary representations by `+1` (`LBase2`/`REnd2`), which eliminates the unreachable bootstrap state `8` (`I`).
>    - **`zf_429` (`432 -> 429` states, `-0.69%`):** Incurs **`0.00%` step overhead** (`1.000000x` speedup). The candidate executes the exact same head movements, bit writes, and tape configurations at every single step $t \ge 0$.
>    - **`riemann_543` (`744 -> 543` states, `-27.02%`):** Achieves a **`-3.69%` step reduction (`1.0383x` speedup)** (`240,702` vs `249,921` steps across `3,254` outer-loop checkpoints, saving `9,219` steps) because eliminating pass-bounce states bypasses 2 redundant head-reversal steps per bounce.

---

## Summary of Certified Reductions

| Domain & Mathematical Target | Published Baseline (`2`-Symbol TM) | Certified Candidate (`2`-Symbol TM) | Primary Metric: State Delta | Secondary Metric: Runtime Step Delta | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Goldbach's Conjecture** (`goldbach`) | `goldbach_25` (`25` states, Yao / Yijun Leng / bbchallenge) | **`goldbach_24`** (`24` states) | **`-1` state (`-4.00%`)** | `+11.74%` steps (`+1` unary shift) | [`Cryptids/Goldbach24.lean`](Cryptids/Goldbach24.lean) & [`Cryptids/Semantics/Goldbach.lean`](Cryptids/Semantics/Goldbach.lean) |
| **ZF Consistency** (`zf`) | `zf_432` (`432` states, Andrew Wade 2025) | **`zf_429`** (`429` states; via `431`, `430`) | **`-3` states (`-0.69%`)** | **`0.00%` steps** (1-to-1 step identity) | [`Cryptids/Zf429.lean`](Cryptids/Zf429.lean) ([`Zf431.lean`](Cryptids/Zf431.lean), [`Zf430.lean`](Cryptids/Zf430.lean)) & [`Cryptids/Semantics/Zf.lean`](Cryptids/Semantics/Zf.lean) |
| **Riemann Hypothesis** (`riemann`) | `riemann_744` (`744` states, Matiyasevich-Davis-O'Rear 2016 NQL TM) | **`riemann_543`** (`543` states) | **`-201` states (`-27.02%`)** | **`-3.69%` steps** (`1.0383x` speedup) | [`Cryptids/Riemann543.lean`](Cryptids/Riemann543.lean) & [`Cryptids/Semantics/Riemann.lean`](Cryptids/Semantics/Riemann.lean) |

---

## Installation and Usage

### 1. Build All Lean 4 Proofs

```bash
lake exe cache get
lake build
```

### 2. Verify with `leanprover/comparator`

See [`comparator/README.md`](comparator/README.md) for full details. With [`comparator`](https://github.com/leanprover/comparator) installed:

```bash
lake env comparator comparator/all.json
```

### 3. Run the Standalone First-Principles Python Verifier

[`verify.py`](verify.py) uses only the Python 3 standard library (finishes in `< 1` second):

```bash
python3 verify.py
```

---

## Repository Guide

* [`Cryptids/`](Cryptids/) -- Lean 4 formalizations:
  * [`Cryptids/Machines.lean`](Cryptids/Machines.lean) -- Core 2-symbol Turing machine definitions (`Machine`, `Cfg`, `step`, `init`, `Halts`) on top of `Mathlib.Computability.PostTuringMachine`.
  * [`Cryptids/Goldbach24.lean`](Cryptids/Goldbach24.lean) -- Proof of `Halts candidate ↔ Halts reference` (`24` vs `25` states).
  * [`Cryptids/Semantics/Goldbach.lean`](Cryptids/Semantics/Goldbach.lean) -- End-to-end proof of `Halts reference ↔ ¬ GoldbachConjecture` and `Halts candidate ↔ ¬ GoldbachConjecture` (see [`Cryptids/Semantics/README.md`](Cryptids/Semantics/README.md)).
  * [`Cryptids/Zf431.lean`](Cryptids/Zf431.lean), [`Cryptids/Zf430.lean`](Cryptids/Zf430.lean), [`Cryptids/Zf429.lean`](Cryptids/Zf429.lean) -- Proofs of `Halts candidate ↔ Halts reference` (`431`, `430`, and `429` vs `432` states).
  * [`Cryptids/Semantics/Zf.lean`](Cryptids/Semantics/Zf.lean) & [`Cryptids/Semantics/Zf/`](Cryptids/Semantics/Zf/) -- End-to-end formal semantics of `zf_432`, `zf_431`, `zf_430`, and `zf_429` connecting halting to `ZFInconsistent` and proving soundness in Mathlib's `ZFSet.{0}` (see [`Cryptids/Semantics/README.md`](Cryptids/Semantics/README.md)).
  * [`Cryptids/Riemann543.lean`](Cryptids/Riemann543.lean) -- Proof of `Halts candidate ↔ Halts reference` (`543` vs `744` states).
  * [`Cryptids/Semantics/Riemann.lean`](Cryptids/Semantics/Riemann.lean) & [`Cryptids/Semantics/Riemann/`](Cryptids/Semantics/Riemann/) -- Formal semantics of `riemann_744` and `riemann_543` connecting `Halts reference` and `Halts candidate` to `¬ RiemannHypothesis` (see [`Cryptids/Semantics/README.md`](Cryptids/Semantics/README.md)).
* [`Challenge/`](Challenge/) & [`comparator/`](comparator/) -- `sorry`-stubbed target modules and configuration files for [`leanprover/comparator`](https://github.com/leanprover/comparator).
* [`verify.py`](verify.py) -- Standalone zero-dependency Python 3 verifier (re-compiles upstream sources, checks SHA-256 digests, verifies `Machine.ofRows` tables and invariants, and simulates `250,000` steps per domain).
* [`RELATED_WORK.md`](RELATED_WORK.md) -- Historical lineage (Yedidia-Aaronson 2016 through Wade 2025) and cost-model boundaries (`(Q, 2)` standard TM convention).
* [`artifacts/`](artifacts/) -- Canonical `machine.txt` tables and mathematical overviews for `goldbach_24`, `zf_431`, `zf_430`, `zf_429`, and `riemann_543`.
* [`baselines/`](baselines/) -- Verbatim upstream source files (`sources/`), canonical 5-tuple tables (`tables/`), and [`PROVENANCE.md`](baselines/PROVENANCE.md).

---

## License and disclaimer

Copyright 2026 Google LLC

All software is licensed under the Apache License, Version 2.0 (Apache 2.0);
you may not use this file except in compliance with the Apache 2.0 license.
You may obtain a copy of the Apache 2.0 license at:
https://www.apache.org/licenses/LICENSE-2.0

All other materials are licensed under the Creative Commons Attribution 4.0
International License (CC-BY). You may obtain a copy of the CC-BY license at:
https://creativecommons.org/licenses/by/4.0/legalcode

Unless required by applicable law or agreed to in writing, all software and
materials distributed here under the Apache 2.0 or CC-BY licenses are
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied. See the licenses for the specific language governing
permissions and limitations under those licenses.

This is not an official Google product.
