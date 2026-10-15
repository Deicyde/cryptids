# Busy Beaver Holdouts (`BusyBeaver/`)

This library contains formal Lean 4 specifications and kernel-verified behavioral proofs for Busy Beaver 6 (`BB(6)`) holdouts (some are potential Cryptids, subject to community acceptance), connected to `ConjectureMachines.Machine` via [`BusyBeaver/Bridge.lean`](./Bridge.lean).

## Behavioral Predicates ([`Defs.lean`](./Defs.lean))

All proofs in `BusyBeaver/` target one of three machine-checked behavioral predicates over the Post-Turing execution model `BusyBeaver.Machine Γ Λ` starting from the all-blank tape (`BusyBeaver.init []`):

| Predicate | Meaning |
| :--- | :--- |
| `IsHalt M` | `M` eventually reaches a halting configuration (`(step M cfg).isNone`) from `init []`. |
| `IsNotHalt M` (`IsDoesNotHalt M`) | Every configuration reachable from `init []` has a well-defined successor (`(step M cfg).isSome`). |
| `IsCryptid M` | `M`'s blank-tape trajectory enters a closed accelerated regular-expression `TapePatternSet` in which every member configuration advances (`ReachesPlus`) either to another member or to a halting state. |

## Foundational Lemmas ([`Basic.lean`](./Basic.lean))

[`BusyBeaver/Basic.lean`](./Basic.lean) provides clean-room multi-step and reachability lemmas (`multiStep`, `ReachesIn`, `ReachesStar`, `ReachesPlus` with `Trans` instances), closed-invariant non-halting theorems (`NeverHaltsFrom.of_reachesPlus_invariant`, `IsNotHalt.of_reachesPlus_invariant`), finite block repetition (`l ^ n`) and `ListBlank` identities, standard 6-state labels (`BusyBeaver.SixState.A..F`), directed-head (`Cfg.headRight` / `Cfg.headLeft`) step transitions, and concrete execution/halting tactics (`bb_steps`, `bb_halt`).

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

| Machine (`bbchallenge` RLE) | States | Symbols | Proved Property | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- |
| `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` | `6` | `2` | `IsCryptid` | [`M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean`](./Machines/M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean) |
| `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` | `6` | `2` | `IsCryptid` | [`M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean`](./Machines/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean) |
| `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` | `6` | `2` | `IsCryptid` | [`M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean`](./Machines/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) |
| `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` | `6` | `2` | `IsCryptid` | [`M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean`](./Machines/M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean) |

## Building

Build the `BusyBeaver` library target:

```bash
lake exe cache get
lake build BusyBeaver
```

## Acknowledgements

We thank the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) project for the Busy Beaver Post-Turing machine model (`BusyBeaver.Machine`), the Busy Beaver Challenge community, and `int-y1` (`BusyLean`) for pioneering Lean 4 Busy Beaver holdout formalizations and inspiring the directed-head configuration style (`Cfg.headRight` / `Cfg.headLeft`).
