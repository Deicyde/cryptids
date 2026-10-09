# Riemann Hypothesis Machine (`744 -> 543` States)

* **Domain:** `riemann` (2-symbol deterministic Turing machine halting if and only if the Riemann Hypothesis is false, starting from Matiyasevich, Davis, and O'Rear's 2016 744-state NQL-compiled machine [`baselines/sources/riemann_744_sorear.tm`](../../baselines/sources/riemann_744_sorear.tm))
* **State Reduction:** `744 -> 543` states (`-201` states, `-27.02%`)
* **Secondary Runtime Trade-off:** `-3.69%` step reduction (`1.038300x` speedup: `240,702` candidate steps vs `249,921` baseline steps at outer-loop checkpoint `3,254`, saving `9,219` steps while preserving 100% bit-exact relative tape equality at every outer-loop entry)
* **Machine SHA-256:** `14c7d827a8ef5ff7671f4642fe31d956c4880a0ce8270c74286b453313f4824e` ([`machine.txt`](machine.txt))
* **Formal Equivalence Proof:** [`Cryptids/Riemann543.lean`](../../Cryptids/Riemann543.lean) (Lean 4 kernel, standard axioms `{propext, Classical.choice, Quot.sound}`)

## Mathematical Mechanism

Across a 7-milestone progression (`744 -> 665 -> 563 -> 559 -> 551 -> 547 -> 546 -> 543`), this reduction removes 201 states (`-27.02%`) from the 2016 Matiyasevich-Davis-O'Rear NQL machine (`riemann_744_sorear.tm`).

The formal proof ([`Cryptids/Riemann543.lean`](../../Cryptids/Riemann543.lean)) defines a surjective state homomorphism `fNat : Fin 744 -> Fin 543` (`max = 542`, all `543` values attained) paired with a **25-cell sliding-window tape bitmask invariant** (`m0Nat` and `m1Nat`, each a 25-bit mask specifying whether symbol `0` or `1` can appear at relative tape offset `k - 11` for `k in 0..24`, where `k = 11` is the current head cell):

1. **Unreachable State-Symbol Slot Elimination (`293` of `1,488` slots):**
   - For `293` `(q, b)` pairs in `riemann_744`, `!allowBit (m0Nat q) (m1Nat q) 11 b` holds (`bit 11` is `0` in `m0Nat q` or `m1Nat q`), proving by induction on the 25-cell window (`checkAllCells`) that state `q` never reads symbol `b` on any reachable configuration from the blank tape. States whose single reachable branch matches another state's opposite or same branch can therefore be merged into a single state in `Fin 543`.
2. **Pass-Bounce Macro-Step Elimination (`140` transitions):**
   - In `riemann_744`, NQL subroutine transitions frequently step `q --(b / w, d)--> p`, where `p` is a pure "pass-through" state (`0 -> 0, -d, j1` and `1 -> 1, -d, j1`) that immediately reverses the head back to the cell just written (`w`) in state `j1`, which then executes `refTrans(j1, w) = (w2, d2, q2)`.
   - `riemann_543` replaces the 3-step excursion `q -> p -> j1 -> q2` with the single transition `(fNat q, b) -> (w2, d2, fNat q2)`, saving 2 head-reversal steps per bounce (`9,219` steps saved over the first `250,000` steps) and allowing the pass states to be pruned.
3. **Multi-Step `SyncCountdown` Chains (`52` special entries):**
   - Where merging compatible single-branch states redirects an entry into a multi-step sequence before re-synchronizing with `fNat`, [`Cryptids/Riemann543.lean`](../../Cryptids/Riemann543.lean) proves `52` explicit `SyncCountdown` theorems (`sync_from_63_0` through `sync_from_713_1` plus the 5 base cases), showing that `candidate` and `reference` step in lockstep to a common `SimRel` configuration `(fNat q_base, T)` and `(q_base, T)` with `WindowInv (m0 q_base) (m1 q_base) T` restored.
