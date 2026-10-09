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

### 1. Goldbach's Conjecture (`goldbach`)

Searches even integers $2n \ge 4$ for a counterexample to Goldbach's conjecture (an even integer that cannot be written as the sum of two primes) and halts if and only if a counterexample exists.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Equivalence Proof |
| :--- | :--- | :--- | :--- | :--- |
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
| 2025 | Andrew Wade (`ajwade/turing_machine_explorer`, `zf_432_wade.tm`) | `432` | Tarski minimal first-order ZF encoding (`zf_432`) | Compiler pipeline |
| **2026** | **Faldor & Firsching, using Gemini Argon (`zf_429`)** | **`429`** | **Moore merge (`42->13`), head-symbol merge (`95->331`), and 4-cell window contextual split (`91->{46,93,94}`)** | **Lean 4 proofs ([`Cryptids/Zf429.lean`](Cryptids/Zf429.lean), [`Cryptids/Semantics/Zf.lean`](Cryptids/Semantics/Zf.lean))** |

### 3. Riemann Hypothesis (`riemann`)

Enumerates positive integers $n$ and tests Matiyasevich's / Robin's / Lagarias's elementary inequality equivalent to the Riemann Hypothesis across all $n \ge 1$.

| Year | Authors / Source | States (`(Q, 2)`) | Construction / Reduction Method | Formal Equivalence Proof |
| :--- | :--- | :--- | :--- | :--- |
| 2016 | Matiyasevich, Davis & O'Rear (`riemann_744_sorear.tm`) | `744` | NQL-compiled integer inequality checker (`riemann_744`) | Compiler pipeline |
| **2026** | **Faldor & Firsching, using Gemini Argon (`riemann_543`)** | **`543`** | **25-cell window invariant (`m0Nat`/`m1Nat`), pass-bounce macro-step elimination (`140` bounces), and `52` `SyncCountdown` chains** | **Lean 4 proofs ([`Cryptids/Riemann543.lean`](Cryptids/Riemann543.lean), [`Cryptids/Semantics/Riemann.lean`](Cryptids/Semantics/Riemann.lean))** |
