# 24-State Goldbach Machine (`goldbach_24`)

* **Instance:** `goldbach`
* **Reference Machine:** `25` states, `2` symbols ([`baselines/tables/goldbach_25.txt`](../../baselines/tables/goldbach_25.txt), SHA-256: `da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67`)
* **Candidate Machine:** `24` states, `2` symbols ([`machine.txt`](machine.txt), SHA-256: `9b8b92a609ca9ae891856957b21a4d5ff9ba4317c27835e31265a249d236b2dc`)
* **Formal Equivalence Proof:** [`Cryptids/Goldbach24.lean`](../../Cryptids/Goldbach24.lean) (`0` axioms beyond `{propext, Classical.choice, Quot.sound}`)
* **End-to-End Semantics Proof:** [`Cryptids/Semantics/Goldbach.lean`](../../Cryptids/Semantics/Goldbach.lean) (`Halts candidate ↔ ¬ GoldbachConjecture`)

## Mathematical Overview of the `25 -> 24` State Reduction

The published 25-state Goldbach machine tests each even integer `N = 2w + 4`
(`N = 4, 6, 8, ...`) by enumerating additive partitions `q + p` in unary on the
tape and testing both summands for primality by trial division. Its 25 states
partition into five functional routines:

1. **Initialization & Summand Scan (`States 0..4`):** Scans the current unary
   block `p` and branches on small cases (`p = 1` composite, `p = 2` prime,
   `p >= 3` enters trial division).
2. **Leftward Return Scanners (`States 5..8`):** Scans left across `1`s and `0`s
   to return the tape head to the partition separator after testing a summand.
3. **Trial Division Loop (`States 9..15`):** Tests whether `p >= 3` is divisible
   by successive trial divisors using unary subtraction (`counterTape`).
4. **Partition Step & Halting Check (`States 16..19`):** Shifts one `1` from the
   left summand `q` to the right summand `p`, or halts at transition `(19, 0)`
   (`---`) if all partitions of the current even integer have failed.
5. **Divisor Increment & Reset (`States 20..24`):** Resets the dividend and
   advances to the next trial divisor or next even number.

### The 4 Transition Edits That Eliminate Reference State 8

In the 25-state reference, state `8` (`return_0_to_check_even_loop`: `0R9`,
`0L8`) and state `5` (`return_0_to_check_prime_loop`: `0L2`, `1L5`) both perform
leftward return scans across unary blocks, differing only in how they cross the
left delimiter `0`.

By making four targeted transition edits to the 25-state reference (yielding the
intermediate 25-state machine `edited` in [`Cryptids/Goldbach24.lean`](../../Cryptids/Goldbach24.lean)):

* `(1, 0): 1R2 -> 1R18`
* `(3, 0): 1L8 -> 0L5`
* `(4, 0): 1L17 -> 0L16`
* `(7, 1): 1L8 -> 1L22`

every transition into state `8` is redirected through states `5`, `16`, `18`,
and `22`. State `8` becomes completely unreachable from `init` (`state 0` on
the blank tape) and is removed via the order-preserving state embedding
(`embed : Fin 24 -> Fin 25` in [`Cryptids/Goldbach24.lean`](../../Cryptids/Goldbach24.lean)):

```lean
def embed (q : Fin 24) : Fin 25 :=
  if q.val < 8 then ⟨q.val, by omega⟩ else ⟨q.val + 1, by omega⟩
```

### The `+1` Shifted Unary Invariant (`LBase1`/`REnd1` vs `LBase2`/`REnd2`)

Redirecting `(3, 0) -> 0L5` and `(4, 0) -> 0L16` causes `edited` (and hence the
24-state `candidate`) to deposit one additional `1` on each side of the
partition separator during the bootstrap phase (`init` reaches the first halting
check at `state 19` in `47` steps in `reference` vs `101` steps in `edited`),
and thereafter preserves a uniform `+1` unary offset on both the left base block
(`LBase2` has `q + 2` ones vs `LBase1` with `q + 1` ones when `is_right = true`)
and the right unary block (`p + 1` ones vs `p` ones, and `REnd2` with `q + 1`
ones vs `REnd1` with `q` ones when `is_right = false`).

Because the trial-division entry (`sim_state0_p1`, `sim_state0_p2`,
`sim_state0_p_ge3`) in `edited` also consumes one additional `1` before entering
state `6`, the shifted `(q + 1, p + 1)` tape representation in `edited` executes
the exact same sequence of trial divisions (`chk6`, `chk11`), primality outcomes
(`chkExit`), and partition checks (`chk0`) as `(q, p)` in `reference`.

## Guide to Reading [`Cryptids/Goldbach24.lean`](../../Cryptids/Goldbach24.lean)

1. **`edited` and `candidate_iff_edited`:**
   Defines the 25-state `edited` machine (with state `8` isolated) and proves
   `candidate_iff_edited : Halts candidate ↔ Halts edited` via `Turing.tr_eval_dom`
   and `transition_embed` (`by revert q a; decide`).
2. **`nSteps` and Bootstrap Equivalence:**
   Defines `nSteps` via `Nat.rec` and proves `boot_reference_47` (`47`
   steps from `init` to `state 19`) and `boot_edited_101` (`101` steps from
   `init` to `state 19`).
3. **Symbolic Scanner Inductions:**
   Proves parametric multi-step symbolic execution lemmas over arbitrary
   `ListBlank (Fin 2)` tails (`nSteps_mkL_left_scan`, `nSteps_mk'_right_scan`,
   `counterTape` division passes `nSteps_pass_11_b0`, `nSteps_pass_11_bsucc`,
   `nSteps_pass_11_to_6`, `nSteps_pass_11_to_16`, and return passes
   `sim_state5_to_0_left_from_0_ref` / `sim_state5_to_0_left_from_0_edit`).
4. **`BaseTr`, `MacroStep`, and `candidate_equivalent`:**
   Defines the four-clause inductive synchronization relation `BaseTr` (`chk0`,
   `chk6`, `chk11`, `chkExit`) relating configurations of `reference` and
   `edited`, proves `baseTr_macroStep : BaseTr c₁ c₂ -> MacroStep BaseTr c₁ c₂`,
   and concludes `edited_iff_reference : Halts edited ↔ Halts reference` and
   `candidate_equivalent : Halts candidate ↔ Halts reference`.
