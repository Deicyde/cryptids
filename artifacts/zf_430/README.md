# ZF Set Theory Consistency Machine (`432 -> 430` States)

* **Domain:** `zf` (Andrew Wade's 2025 432-state machine [`baselines/sources/zf_432_wade.tm`](../../baselines/sources/zf_432_wade.tm))
* **State Reduction:** `432 -> 430` states (`-2` states, `-0.46%`)
* **Machine SHA-256:** `9a4829d0f084177b045612e444b6cd63070168a55d7b582e1f34b10b3daca26c` ([`machine.txt`](machine.txt))
* **Formal Equivalence Proof:** [`Cryptids/Zf430.lean`](../../Cryptids/Zf430.lean)

## Mechanism

Combines the Moore merge `42 -> 13` with a 4-cell window invariant (`validState(q, l2, l1, l0, h)`) proving that state `95` is only ever entered with `h = 1`, where its transition (`1L94`) matches state `331` on `h = 1` (`1L94`). Merging `42 -> 13` and `95 -> 331` reduces the machine to 430 states with 0% step overhead, certified in [`Cryptids/Zf430.lean`](../../Cryptids/Zf430.lean).
