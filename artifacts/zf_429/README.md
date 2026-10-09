# ZF Set Theory Consistency Machine (`432 -> 429` States)

* **Domain:** `zf` (2-symbol deterministic Turing machine halting if and only if Zermelo-Fraenkel set theory is inconsistent, starting from Andrew Wade's 2025 432-state machine [`baselines/sources/zf_432_wade.tm`](../../baselines/sources/zf_432_wade.tm))
* **State Reduction:** `432 -> 429` states (`-3` states, `-0.69%`)
* **Secondary Runtime Trade-off:** `0.00%` step overhead (`1.000000x` speedup; exact 1-to-1 step-by-step head movement, bit writes, and tape configurations at every step $t \ge 0$)
* **Machine SHA-256:** `041919e91a6a5cb2afee60ecdf97975a57811c0c8e0cff52c771d66501f7f730` ([`machine.txt`](machine.txt))
* **Formal Equivalence Proof:** [`Cryptids/Zf429.lean`](../../Cryptids/Zf429.lean) (Lean 4 kernel, standard axioms `{propext, Classical.choice, Quot.sound}`)

## Mathematical Mechanism

Across the progression (`432 -> 431 -> 430 -> 429`), three states are eliminated from Wade's 432-state baseline (`42`, `95`, and `91`) while maintaining **strict step-for-step lockstep identity** (`step candidate^t = mapState(step reference^t)` for all $t \ge 0$).

The proof defines a finite 4-cell sliding-window tape invariant `validState(q, l2, l1, l0, h)` tracking the three cells immediately to the left of the tape head (`l2 = head - 3`, `l1 = head - 2`, `l0 = head - 1`) and the symbol currently under the head (`h = head`):

1. **Pure Moore Bisimulation (`432 -> 431`, eliminating state `42`):**
   - In `zf_432`, state `42` (`1R43`, `1R331`) and state `13` (`1R43`, `1R331`) have identical transitions on both symbols `0` and `1`. Redirecting all incoming transitions from `42` to `13` removes state `42` ([`Cryptids/Zf431.lean`](../../Cryptids/Zf431.lean)).
2. **Head-Symbol Reachability Merge (`431 -> 430`, eliminating state `95`):**
   - Under `validState`, state `95` is only ever entered when `(h = 1, l0 = 1, l1 = 1)`. On `h = 1`, state `95` transitions via `1L94`, which is identical to state `331` on `h = 1` (`1L94`). Therefore `mapState` collapses `95 -> 331` without altering any reachable transition ([`Cryptids/Zf430.lean`](../../Cryptids/Zf430.lean)).
3. **Contextual 4-Cell Window State Splitting (`430 -> 429`, eliminating state `91`):**
   - Under `validState`, states `94`, `93`, and `91` satisfy strict local window constraints:
     - `q = 94`: `(h = 0 /\ l0 = 1 /\ l1 = 1) \/ (h = 1 /\ l0 = 1)`
     - `q = 93`: `(h = 0 /\ l0 = 1) \/ (h = 1)`
     - `q = 91`: `(h = 1 /\ l0 = 1 /\ l1 = 0) \/ (h = 1 /\ l0 = 0) \/ (h = 0)`
   - Because `94` and `93` have disjoint or matching behaviors on `h = 1` with states `372` and `420`, `mapState(q, l0, h)` routes:
     - `94 -> 94` (when `h = 0`) and `94 -> 372` (when `h = 1`), freeing the `h = 1` slot of candidate states `93` and `94`.
     - `93 -> 93` (when `h = 0`) and `93 -> 420` (when `h = 1`).
     - `91 -> 46` (when `h = 0`), `91 -> 93` (when `h = 1, l0 = 1`), and `91 -> 94` (when `h = 1, l0 = 0`).
   - Because `validState_next` and `transition_mapState` are finite predicates over `(q : Fin 432) x (l2 l1 l0 h x : Fin 2)` ($432 \times 32 = 13,824$ cases), Lean 4 discharges both inductive obligations by `decide`, and lifts the step-by-step simulation to `Halts candidate <-> Halts reference` in [`Cryptids/Zf429.lean`](../../Cryptids/Zf429.lean).
