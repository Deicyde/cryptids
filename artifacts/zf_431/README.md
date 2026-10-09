# ZF Set Theory Consistency Machine (`432 -> 431` States)

* **Domain:** `zf` (Andrew Wade's 2025 432-state machine [`baselines/sources/zf_432_wade.tm`](../../baselines/sources/zf_432_wade.tm))
* **State Reduction:** `432 -> 431` states (`-1` state, `-0.23%`)
* **Machine SHA-256:** `6414d9a1a4bebd72761483505a7581e936dbeb5e4790e39436080f0b0bd302ca` ([`machine.txt`](machine.txt))
* **Formal Equivalence Proof:** [`Cryptids/Zf431.lean`](../../Cryptids/Zf431.lean)

## Mechanism

States `42` and `13` in `zf_432` have identical outgoing transitions on both symbols (`0 -> 1R43`, `1 -> 1R331`). The state projection `f(q) = 13` if `q == 42`, `q` if `q < 42`, and `q - 1` if `q > 42` is an exact Moore-machine homomorphism (`candidate.transition (f q) a = (reference.transition q a).map ...`), proved by `decide` over `Fin 432 x Fin 2` in [`Cryptids/Zf431.lean`](../../Cryptids/Zf431.lean).
