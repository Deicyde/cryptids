# Busy Beaver Holdouts (`BusyBeaver/`)

This library contains formal Lean 4 specifications and kernel-verified behavioral proofs for Busy Beaver 6 (`BB(6)`) holdouts (some are potential Cryptids, subject to community acceptance), connected to `ConjectureMachines.Machine` via [`BusyBeaver/Bridge.lean`](./Bridge.lean).

## Behavioral Predicates ([`Defs.lean`](./Defs.lean))

All proofs in `BusyBeaver/` target one of three machine-checked behavioral predicates over the Post-Turing execution model `BusyBeaver.Machine Γ Λ` starting from the all-blank tape (`BusyBeaver.init []`):

| Predicate | Meaning |
| :--- | :--- |
| `IsHalt M` | `M` eventually reaches a halting configuration (`(step M cfg).isNone`) from `init []`. |
| `IsNotHalt M` (`IsDoesNotHalt M`) | Every configuration reachable from `init []` has a well-defined successor (`(step M cfg).isSome`). |
| `IsCryptid M` | `M`'s blank-tape trajectory enters a closed accelerated regular-expression `TapePatternSet` in which every member configuration advances (`ReachesPlus`) either to another member or to a halting state. |

## Machine Loader and Bridge ([`Bridge.lean`](./Bridge.lean))

Machines can be defined using either the `.txt` transition-table loader `load_machine_rows%` from [`Cryptids/Machines.lean`](../Cryptids/Machines.lean) or the elaboration-time `bbchallenge.org` RLE string parser `load_rle_rows%`:

```lean
def targetRows : List (List (Option (Fin 2 × Turing.Dir × Fin 6))) :=
  load_rle_rows% "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

def target : ConjectureMachines.Machine 6 2 :=
  ConjectureMachines.Machine.ofRows targetRows
```

The canonical embedding `ConjectureMachines.Machine.toBB` maps any `ConjectureMachines.Machine states symbols` to `BusyBeaver.Machine (Fin symbols) (Fin states)`, with certified halting equivalence:

```lean
theorem isHalt_toBB_iff_halts (M : ConjectureMachines.Machine states symbols) :
    BusyBeaver.IsHalt M.toBB ↔ ConjectureMachines.Halts M

theorem isNotHalt_toBB_iff_not_halts (M : ConjectureMachines.Machine states symbols) :
    BusyBeaver.IsNotHalt M.toBB ↔ ¬ ConjectureMachines.Halts M
```

## Formalized Machines

*(Individual `BB(6)` holdout proofs will be listed here as they are added.)*

| Machine (`bbchallenge` RLE) | States | Symbols | Proved Property | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- |
| *Forthcoming* | `6` | `2` | `IsHalt` / `IsNotHalt` / `IsCryptid` | — |

## Building

Build the `BusyBeaver` library target:

```bash
lake exe cache get
lake build BusyBeaver
```
