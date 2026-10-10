# Certified State Reductions and Semantics of Conjecture-Checking Turing Machines

This repository contains formally verified 2-symbol Turing machines and Lean 4 semantics proofs for **Goldbach's Conjecture**, **ZF Set Theory Consistency**, and the **Riemann Hypothesis**, developed by Maxence Faldor and Moritz Firsching using Gemini Argon.

## Formalized Machines

| Conjecture | Machine | States | Source / Provenance | Proved Halting Condition (`Halts M ↔ ...`) | Lean 4 Proofs |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Goldbach's Conjecture | `goldbach_24` | `24` | Reduced from `goldbach_25` (`25` states, Yao / Leng 2024) | `¬ GoldbachConjecture` | [`Goldbach24.lean`](Cryptids/Goldbach24.lean), [`Semantics/Goldbach.lean`](Cryptids/Semantics/Goldbach.lean) |
| ZF Consistency | `zf_393` | `393` | Andrew Wade ([`turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer) `9c5c2e82`, Aug 2026) | `ZFInconsistent` (`¬ Halts zf393` proved) | [`Zf393.lean`](Cryptids/Zf393.lean), [`Semantics/Zf393.lean`](Cryptids/Semantics/Zf393.lean) |
| ZF Consistency | `zf_429` | `429` | Reduced from `zf_432` (`432` states, Wade 2025; via `431`, `430`) | `WadeZFInconsistent` | [`Zf429.lean`](Cryptids/Zf429.lean), [`Semantics/Zf.lean`](Cryptids/Semantics/Zf.lean) |
| Riemann Hypothesis | `riemann_120` | `120` | Joseph M. Shunia ([`arXiv:2609.30306`](https://arxiv.org/abs/2609.30306), Sept 2026) | `¬ RiemannHypothesis` | [`Riemann120.lean`](Cryptids/Riemann120.lean), [`Semantics/Riemann120.lean`](Cryptids/Semantics/Riemann120.lean) |
| Riemann Hypothesis | `riemann_543` | `543` | Reduced from `riemann_744` (`744` states, Matiyasevich–O'Rear–Aaronson 2016) | `¬ RiemannHypothesis` | [`Riemann543.lean`](Cryptids/Riemann543.lean), [`Semantics/Riemann.lean`](Cryptids/Semantics/Riemann.lean) |

See [`RELATED_WORK.md`](RELATED_WORK.md) for the historical progression across each domain.

## What Is Formally Proved

All proofs in [`Cryptids/`](Cryptids/) are checked by the Lean 4 kernel (`v4.35.0-rc4`) without `sorry` and use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. **State reduction and halting equivalence (`candidate.states < reference.states` and `Halts candidate ↔ Halts reference`):** Each reduced machine (`goldbach_24`, `zf_431`, `zf_430`, `zf_429`, `riemann_543`) has fewer states than its reference machine (`goldbach_25`, `zf_432`, `riemann_744`) and halts from the blank tape if and only if the reference machine halts ([`Goldbach24.lean`](Cryptids/Goldbach24.lean), [`Zf431.lean`](Cryptids/Zf431.lean), [`Zf430.lean`](Cryptids/Zf430.lean), [`Zf429.lean`](Cryptids/Zf429.lean), [`Riemann543.lean`](Cryptids/Riemann543.lean)).
2. **End-to-end mathematical semantics ([`Cryptids/Semantics/`](Cryptids/Semantics/README.md)):**
   - **Goldbach:** Both `goldbach_25` and `goldbach_24` halt if and only if Goldbach's conjecture is false (`Halts candidate ↔ ¬ GoldbachConjecture`).
   - **Riemann Hypothesis (`riemann_744`, `riemann_543`, and `riemann_120`):** All three machines (`riemann_744`, `riemann_543`, and Shunia's 120-state machine `riemann_120`) halt if and only if Mathlib's `RiemannHypothesis` is false (`Halts candidate ↔ ¬ RiemannHypothesis` and `Halts riemann120 ↔ ¬ RiemannHypothesis`).
   - **ZF Consistency (`zf_432`–`zf_429` and `zf_393`):** `zf_432` through `zf_429` halt if and only if the 20-clause deductive system enumerated by `zf_432_wade.tm` derives $v_0 \in v_0$ (`WadeZFInconsistent`), while Wade's 393-state machine `zf_393` (incorporating upstream fix `10fcf152b3`) halts if and only if O'Rear's `zf2.nql` Hilbert system proves $v_0 \in v_0$ (`Halts zf393 ↔ ZFInconsistent`), and hence never halts in `ZFSet.{0}` (`not_halts_zf393 : ¬ Halts zf393`).

Details on the proof architecture and mathematical background are in [`Cryptids/Semantics/README.md`](Cryptids/Semantics/README.md).

## Runtime Step Behavior

For the reduced machines in [`artifacts/`](artifacts/), the state-space transformations affect execution step counts as follows:

- **`goldbach_24` (`232,580` vs. `208,135` steps at checkpoint `155`):** Shifting the unary tape encoding by `+1` eliminates bootstrap state `8` at the cost of slightly longer unary scans.
- **`zf_429` (`0` step difference):** Eliminating states `42`, `95`, and `91` preserves step-for-step identity—both machines execute the same head movements, bit writes, and tape configurations at every step $t \ge 0$.
- **`riemann_543` (`240,702` vs. `249,921` steps across `3,254` checkpoints):** Removing pass-bounce intermediary states bypasses two head-reversal steps per bounce.

## Building and Verifying

Build all Lean 4 proofs:

```bash
lake exe cache get
lake build
```

Independently audit the proofs against [`Challenge.lean`](Challenge.lean) with [`leanprover/comparator`](comparator/README.md):

```bash
lake comparator --config comparator/all.json
```

Run the standalone zero-dependency Python verifier (re-compiles upstream baseline sources, checks SHA-256 digests and transition tables, and simulates `250,000` steps per domain):

```bash
python3 verify.py
```

## Repository Structure

- [`Cryptids/`](Cryptids/) — Shared problem definitions ([`Propositions.lean`](Cryptids/Propositions.lean)), Turing machine specifications ([`Machines.lean`](Cryptids/Machines.lean)), halting-equivalence proofs, and end-to-end semantics ([`Cryptids/Semantics/README.md`](Cryptids/Semantics/README.md)).
- [`Challenge.lean`](Challenge.lean) & [`comparator/`](comparator/) — Self-contained target theorem specification and configuration files for [`leanprover/comparator`](comparator/README.md).
- [`artifacts/`](artifacts/) — Canonical `machine.txt` transition tables and reduction write-ups for [`goldbach_24`](artifacts/goldbach_24/README.md), [`zf_431`](artifacts/zf_431/README.md), [`zf_430`](artifacts/zf_430/README.md), [`zf_429`](artifacts/zf_429/README.md), and [`riemann_543`](artifacts/riemann_543/README.md).
- [`baselines/`](baselines/) — Verbatim upstream source files, canonical 5-tuple tables, and [`PROVENANCE.md`](baselines/PROVENANCE.md).
- [`RELATED_WORK.md`](RELATED_WORK.md) — Literature lineage and `(Q, 2)` Turing machine conventions.
- [`verify.py`](verify.py) — Standalone Python 3 verification script.

## Contributing

Pull requests and issues are welcome, especially for smaller Turing machines for these problems, machines for other conjectures, or streamlined Lean proofs. Please also open an issue if you notice anything amiss, such as a missing reference or provenance detail. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for general guidelines.

## Acknowledgements

We thank Eric Wieser for careful review, as well as the Busy Beaver Challenge community, Yijun Leng, Stefan O'Rear, Yuri Matiyasevich, Scott Aaronson, Adam Yedidia, Andrew Wade, and Joseph Shunia for the baseline Turing machines and compilers, and the Mathlib community.

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
