# Busy Beaver Holdouts (`BusyBeaver/`)

This library contains formal Lean 4 specifications and kernel-verified behavioral proofs for Busy Beaver 6 (`BB(6)`) holdouts, connected to `ConjectureMachines.Machine` via [`BusyBeaver/Bridge.lean`](./Bridge.lean).

## Cryptids and Collatz-like Reductions in `BB(6)`

Broadly speaking, [cryptids](https://wiki.bbchallenge.org/wiki/Cryptids) are Turing machines whose halting problem corresponds to a known open mathematical problem (such as the machines for Goldbach's conjecture, ZF consistency, and the Riemann Hypothesis in [`Cryptids/`](../Cryptids/README.md)). In the context of `BB(6)`, however, the term is commonly used more broadly for holdout machines whose dynamics exhibit a **Collatz-like structure** (piecewise affine or modular transitions on integer counters), rather than encoding the classical Collatz conjecture itself or a named open problem.

Accordingly, for these machines we look for and formalize **Collatz-like reductions** (`HasCollatzReduction` and `IsValidAcceleration`). Some well-known `BB(6)` cryptids, such as [Antihydra](https://wiki.bbchallenge.org/wiki/Antihydra), are widely considered genuinely hard and have attracted dedicated mathematical research. At the same time, other machines with Collatz-like reductions have subsequently been resolved—either through automated deciders or via number-theoretic methods such as Baker's theorem on linear forms in logarithms (e.g., [`1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---)). It is therefore reasonable to expect that some of the machines in this directory will eventually be resolved as halting (`IsHalt`) or non-halting (`IsNotHalt`) over time, with or without the reductions provided here.

## Behavioral Predicates ([`Defs.lean`](./Defs.lean))

All proofs in `BusyBeaver/` target machine-checked behavioral predicates over the Post-Turing execution model `BusyBeaver.Machine Γ Λ` starting from the all-blank tape (`BusyBeaver.init []`), capturing both **Level A** (explicit closed `TapePatternSet` invariants) and **Level B** (explicit Collatz-like arithmetic accelerations):

| Predicate | Meaning |
| :--- | :--- |
| `IsHalt M` | `M` eventually reaches a halting configuration (`(step M cfg).isNone`) from `init []`. |
| `IsNotHalt M` (`IsDoesNotHalt M`) | Every configuration reachable from `init []` has a well-defined successor (`(step M cfg).isSome`). |
| `IsClosedPatternSet M ps` | **Level A**: `M`'s blank-tape trajectory enters the explicit `TapePatternSet` `ps`, and every member configuration advances (`ReachesPlus`) either to another member of `ps` or to a halting configuration. |
| `HasCollatzReduction M` | `∃ ps, IsClosedPatternSet M ps`. |
| `IsValidAcceleration M start encode next` | **Level B**: `encode : S → Cfg Γ Λ` and `next : S → Option S` form a certified Collatz-like acceleration of `M` from `start : S` (`init []` reaches `encode start`, `next s = some s'` implies `ReachesPlus M (encode s) (encode s')`, and `next s = none` implies halting from `encode s`), yielding `IsHalt M ↔ CollatzHalts next start`. |

## Foundational Lemmas ([`Basic.lean`](./Basic.lean))

[`BusyBeaver/Basic.lean`](./Basic.lean) provides clean-room multi-step and reachability lemmas (`multiStep`, `ReachesIn`, `ReachesStar`, `ReachesPlus` with `Trans` instances), closed-invariant non-halting theorems (`NeverHaltsFrom.of_reachesPlus_invariant`, `IsNotHalt.of_reachesPlus_invariant`), certified Collatz acceleration halting equivalence (`IsValidAcceleration.isHalt_iff`), finite block repetition (`l ^ n`) and `ListBlank` identities, standard 6-state labels (`BusyBeaver.SixState.A..F`), directed-head (`Cfg.headRight` / `Cfg.headLeft`) step transitions, and concrete execution/halting tactics (`bb_steps`, `bb_halt`).

## Machine Loader and Bridge ([`Bridge.lean`](./Bridge.lean))

Machines can be defined using either the `.txt` transition-table loader `load_machine_rows%` from [`Cryptids/Machines.lean`](../Cryptids/Machines.lean) or the elaboration-time `bbchallenge.org` RLE string parsers `load_rle_machine%` and `load_rle_rows%`:

```lean
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

abbrev target : BusyBeaver.Machine (Fin 2) (Fin 6) :=
  machine.toBB
```

The canonical embedding `ConjectureMachines.Machine.toBB` maps any `ConjectureMachines.Machine states symbols` to `BusyBeaver.Machine (Fin symbols) (Fin states)`, with certified halting equivalence:

```lean
theorem isHalt_toBB_iff_halts (M : ConjectureMachines.Machine states symbols) :
    BusyBeaver.IsHalt M.toBB ↔ ConjectureMachines.Halts M

theorem isNotHalt_toBB_iff_not_halts (M : ConjectureMachines.Machine states symbols) :
    BusyBeaver.IsNotHalt M.toBB ↔ ¬ ConjectureMachines.Halts M
```

## Formalized Machines

Each machine module exposes both **Level A** (`ps`, `is_closed_pattern_set`, `has_collatz_reduction`) and **Level B** (`State`, `start`, `encode`, `next`, `is_valid_acceleration`, `isHalt_iff_acceleration`):

| Machine (`bbchallenge` RLE) | States | Symbols | Proved Properties | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- |
| `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean`](./Machines/M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean) |
| `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean`](./Machines/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean) |
| `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean`](./Machines/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) |
| `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean`](./Machines/M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean) |
| `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean`](./Machines/M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean) |
| `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean`](./Machines/M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean) |
| `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean`](./Machines/M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean) |
| `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean`](./Machines/M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean) |
| `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean`](./Machines/M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean) |
| `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE.lean`](./Machines/M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE.lean) |
| `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [`M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE.lean`](./Machines/M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE.lean) |

## Building and Verifying

Build the `BusyBeaver` and `BusyBeaverChallenge` targets and audit with [`leanprover/comparator`](../comparator/README.md):

```bash
lake exe cache get
lake build BusyBeaver BusyBeaverChallenge
lake comparator --config comparator/busy_beaver.json
```

## Acknowledgements

We thank the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) project for the Busy Beaver Post-Turing machine model (`BusyBeaver.Machine`), the Busy Beaver Challenge community, and `int-y1` (`BusyLean`) for pioneering Lean 4 Busy Beaver holdout formalizations and inspiring the directed-head configuration style (`Cfg.headRight` / `Cfg.headLeft`).
