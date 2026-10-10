# Related Work & Literature Lineage (`RELATED_WORK.md`)

To evaluate the independence of mathematical statements from formal axiomatic systems via the Busy Beaver function $\text{BB}(Q, 2)$, Yedidia and Aaronson (2016) initiated the systematic construction of small, standard 2-symbol deterministic Turing machines whose halting is equivalent to the falsity of major conjectures or the inconsistency of foundational axiom systems.

---

## Cost-Model Convention: Standard `(Q, 2)` Turing Machines

All baselines and candidate reductions in this repository adhere to the standard **Radó / bbchallenge `(Q, 2)` cost model**:
1. **Tape:** Two-way infinite binary tape ($\Gamma = \{0, 1\}$), initialized entirely to the blank symbol $0$.
2. **Initial State:** Deterministic start state $q_0 = 0$.
3. **Transition Function:** Partial function $\delta : \text{Fin}(Q) \times \text{Fin}(2) \to \text{Option}(\text{Fin}(2) \times \{\text{L}, \text{R}\} \times \text{Fin}(Q))$, where `none` (`---`) denotes an immediate halting transition.
4. **Formal Equivalence Requirement:** The candidate machine must satisfy `Halts candidate <-> Halts reference` from the blank tape, proved in Lean 4 without custom axioms.

---

## Historical Progression by Domain

Community records for conjecture-checking and ZFC-independent Turing machines are tracked on the Busy Beaver Challenge wiki ([Larger Cryptids](https://wiki.bbchallenge.org/wiki/Cryptids#Larger_Cryptids) and [Logical Independence](https://wiki.bbchallenge.org/wiki/Logical_independence)).

- **Goldbach (`goldbach_24`):** Improves on the smallest known `(Q, 2)` Turing machine (`25 -> 24` states).
- **ZF Consistency (`zf_429` & `zf_393`) and Riemann Hypothesis (`riemann_543` & `riemann_120`):** **We do not claim that `zf_429` (`429` states) or `riemann_543` (`543` states) are the smallest Turing machines overall** for these problems — recent compiler and algorithmic reworks by Andrew Wade (`zf_393`, `393` states for ZF, Aug 2026) and Joseph M. Shunia (`riemann_120`, `120` states for RH, Sept 2026) reach smaller state counts by changing the register microcode, axiom order, or underlying number-theoretic algorithm. In this repository, `zf_429` and `riemann_543` are certified pure state-space compressions of the historical `zf_432` (2025) and `riemann_744` (2016) baseline machines, **and we provide complete Lean 4 end-to-end semantics proofs for all of `zf_432`–`zf_429`, `zf_393`, `riemann_744`, `riemann_543`, and `riemann_120`.**

### 1. Goldbach's Conjecture (`goldbach`)

Searches even integers $2n \ge 4$ for a counterexample to Goldbach's conjecture (an even integer that cannot be written as the sum of two primes) and halts if and only if a counterexample exists.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Equivalence Proof |
| :--- | :--- | :--- :--- | :--- | :--- |
| 2015 | CodeGolf (`user23013` / Aaronson announcement) | `27` | Hand-crafted unary trial-division counterexample search | Informal |
| 2016 | JaredCorduan (`gid3138251`) | `27` | Verified 27-state unary Goldbach machine | Informal |
| 2024 | Andrew Yao & Yijun Leng (`lengyijun/goldbach_tm`, `bbchallenge` wiki) | `25` | Merged initialization and primality test return paths (`goldbach_25`) | Lean 4 proof (`lengyijun/goldbach_tm`) |
| **2026** | **Faldor & Firsching, using Gemini Argon (`goldbach_24`)** | **`24`** | **`+1` unary shift (`LBase2`/`REnd2`) via 4 transition edits, eliminating bootstrap state `8` (`I`)** | **Lean 4 proofs ([`Cryptids/Goldbach24.lean`](Cryptids/Goldbach24.lean), [`Cryptids/Semantics/Goldbach.lean`](Cryptids/Semantics/Goldbach.lean))** |

### 2. Zermelo-Fraenkel Set Theory Consistency (`zf`)

Enumerates deductions in a finite axiomatization of ZF (or metamath `set.mm` / Tarski minimal ZF encoding) and halts if and only if an inconsistency is derived.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Equivalence Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2016 | Yedidia & Aaronson (Laconic compiler) | `7,910` | Laconic-compiled register machine for ZF consistency | Compiler pipeline |
| 2016 | Stefan O'Rear (`sorear/metamath-turing-machines`) | `748` | NQL-compiled Metamath `set.mm` verifier | Compiler pipeline |
| 2023 | Riebel | `745` | State-merging pass on O'Rear's 748-state machine | Informal |
| 2024 | Ridenour | `643` | Optimized NQL compilation + dead-branch pruning | Informal |
| 2025 | Andrew Wade ([`ajwade/turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer), commit `33b30300`, `zf_432_wade.tm`) | `432` | Tarski minimal first-order ZF encoding (`zf_432`, `bbchallenge` benchmark) | **Lean 4 proofs in this repo ([`Cryptids/Semantics/Zf.lean`](Cryptids/Semantics/Zf.lean))** |
| **2026** | **Faldor & Firsching, using Gemini Argon (`zf_429`)** | **`429`** | **Certified pure state reduction of `zf_432` (`432 -> 431 -> 430 -> 429`): Moore merge (`42->13`), head-symbol merge (`95->331`), and 4-cell window split (`91->{46,93,94}`)** | **Lean 4 proofs ([`Cryptids/Zf429.lean`](Cryptids/Zf429.lean), [`Cryptids/Semantics/Zf.lean`](Cryptids/Semantics/Zf.lean))** |
| **2026** | **Andrew Wade ([`ajwade/turing_machine_explorer`](https://codeberg.org/ajwade/turing_machine_explorer), commit `9c5c2e82`, Aug 2026)** | **`393`** | **Reworked register microcode (`00` moving marker), run-length dispatch, and axiom-order search (`69` framework + `324` decision DAG)** | **Lean 4 proofs in this repo ([`Cryptids/Zf393.lean`](Cryptids/Zf393.lean), [`Cryptids/Semantics/Zf393.lean`](Cryptids/Semantics/Zf393.lean))** |

### 3. Riemann Hypothesis (`riemann`)

Enumerates positive integers $n$ and tests an elementary arithmetic inequality equivalent to the Riemann Hypothesis across all $n \ge 1$.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Equivalence Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2016 | Matiyasevich, O'Rear & Aaronson (`riemann_744_sorear.tm`) | `744` | NQL-compiled Matiyasevich–Schoenfeld harmonic-LCM checker (`riemann_744`) | **Lean 4 proofs in this repo ([`Cryptids/Semantics/Riemann.lean`](Cryptids/Semantics/Riemann.lean))** |
| **2026** | **Faldor & Firsching, using Gemini Argon (`riemann_543`)** | **`543`** | **Certified pure state reduction of `riemann_744`: 25-cell window invariant (`m0Nat`/`m1Nat`), pass-bounce macro-step elimination (`140` bounces), and `52` `SyncCountdown` chains** | **Lean 4 proofs ([`Cryptids/Riemann543.lean`](Cryptids/Riemann543.lean), [`Cryptids/Semantics/Riemann.lean`](Cryptids/Semantics/Riemann.lean))** |
| **2026** | **Joseph M. Shunia ([`arXiv:2609.30306`](https://arxiv.org/abs/2609.30306), Sept 2026)** | **`120`** | **5-register self-sieving recurrence + base-$n$ offset digit count via specialized `TMBuilder` backend** | **Lean 4 proofs in this repo ([`Cryptids/Riemann120.lean`](Cryptids/Riemann120.lean), [`Cryptids/Semantics/Riemann120.lean`](Cryptids/Semantics/Riemann120.lean))** |

