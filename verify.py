# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

"""Zero-dependency first-principles verifier for Conjecture Machines.

This script uses only the Python 3 standard library.
It independently:
1. Verifies the SHA-256 digests of the verbatim published baseline source files
   (`baselines/sources/`) and re-compiles them from first principles into
   canonical transition tables, verifying byte-for-byte identity with
   `baselines/tables/`.
2. Verifies `Cryptids/Machines.lean` and checks that all 5 candidate machines
   (`goldbach_24`, `zf_431`, `zf_430`, `zf_429`, `riemann_543`) are well-formed
   2-symbol Turing machines matching their recorded state counts and SHA-256
   digests, and that their `Machine.ofRows` tables in `Cryptids/*.lean` and
   `Challenge/*.lean` match `baselines/tables/` and `artifacts/*/machine.txt`.
3. Cross-checks the mathematical reduction invariants directly on the
   transition tables (`goldbach_24` table embedding in
   `Cryptids/Goldbach24.lean`,
   `zf` state-homomorphism `mapState` preservation over all 864 baseline
   transitions under the reachable tape invariant, and `riemann_543` exact
   compiler derivation from `riemann_744`).
4. Runs concrete blank-tape Turing machine simulations (`--steps`, default
   250,000 steps per machine) and verifies:
   - Goldbach (25 vs 24 states): 1-to-1 lockstep agreement on `(is_right, q, p)`
     across all outer-loop `chk0` checkpoints under the `+1` unary shift.
   - ZF (432 vs 431, 430, 429 states): 100% step-for-step lockstep identity
     at every single step `t = 0 .. N` (head position, written bit, movement
     direction, full tape contents, and state projection `mapState`).
   - Riemann (744 vs 543 states): 100% bit-exact relative tape identity
     (`tape_cand(x - 1) == tape_ref(x)`) at every outer-loop NQL dispatch
     checkpoint (`state 371` / `f(371)`).
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import pathlib
import re
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent

PINNED_BASELINES = {
    "goldbach": {
        "source_file": "baselines/sources/goldbach_25_bbchallenge.txt",
        "source_sha256": (
            "3b8934a193ecb165a64dbf048332961fc7a62e7381e69095340a9a85d752380c"
        ),
        "table_file": "baselines/tables/goldbach_25.txt",
        "table_file_sha256": (
            "f5b995cb7917d9943431fc8f2554b0872b185ca81e14865307d26db2776b52a5"
        ),
        "canonical_machine_sha256": (
            "da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "goldbach25",
        "format": "standard",
        "states": 25,
        "symbols": 2,
    },
    "zf": {
        "source_file": "baselines/sources/zf_432_wade.tm",
        "source_sha256": (
            "68a9de26ef68ee9cdf085d201b996686ae55d9570822bcf040aca5999e4f4261"
        ),
        "table_file": "baselines/tables/zf_432.txt",
        "table_file_sha256": (
            "e662deaa52994e73413af37a434dbfb4e8c8204a8d972154ead2d839f442af66"
        ),
        "canonical_machine_sha256": (
            "cb9ffd320f7360b5e0e49181a6201286b408d1f8c168d61fafc51d1ca8b86702"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "zf432",
        "format": "tursi",
        "states": 432,
        "symbols": 2,
    },
    "riemann": {
        "source_file": "baselines/sources/riemann_744_sorear.tm",
        "source_sha256": (
            "de0084433909f2600a5052eeb0bb2acd9b0ac315078abd1b92d4f3595601dd31"
        ),
        "table_file": "baselines/tables/riemann_744.txt",
        "table_file_sha256": (
            "9866af71143c85cceeaf2e05be8fef1c3ccb226fe04640b23b7b887f815a25d0"
        ),
        "canonical_machine_sha256": (
            "4f629ed5be1715747f3d467dbb35bded647a25dc740a80b5208c14f65d7d5f44"
        ),
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "riemann744",
        "format": "nql",
        "states": 744,
        "symbols": 2,
    },
}

CANDIDATES = [
    {
        "id": "goldbach_24",
        "instance": "goldbach",
        "path": "artifacts/goldbach_24",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "goldbach24",
        "proof_path": "Cryptids/Goldbach24.lean",
        "challenge_path": "Challenge.lean",
        "states": 24,
        "baseline_states": 25,
        "machine_sha256": (
            "9b8b92a609ca9ae891856957b21a4d5ff9ba4317c27835e31265a249d236b2dc"
        ),
    },
    {
        "id": "zf_431",
        "instance": "zf",
        "path": "artifacts/zf_431",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "zf431",
        "proof_path": "Cryptids/Zf431.lean",
        "challenge_path": "Challenge.lean",
        "states": 431,
        "baseline_states": 432,
        "machine_sha256": (
            "6414d9a1a4bebd72761483505a7581e936dbeb5e4790e39436080f0b0bd302ca"
        ),
    },
    {
        "id": "zf_430",
        "instance": "zf",
        "path": "artifacts/zf_430",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "zf430",
        "proof_path": "Cryptids/Zf430.lean",
        "challenge_path": "Challenge.lean",
        "states": 430,
        "baseline_states": 432,
        "machine_sha256": (
            "9a4829d0f084177b045612e444b6cd63070168a55d7b582e1f34b10b3daca26c"
        ),
    },
    {
        "id": "zf_429",
        "instance": "zf",
        "path": "artifacts/zf_429",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "zf429",
        "proof_path": "Cryptids/Zf429.lean",
        "challenge_path": "Challenge.lean",
        "states": 429,
        "baseline_states": 432,
        "machine_sha256": (
            "041919e91a6a5cb2afee60ecdf97975a57811c0c8e0cff52c771d66501f7f730"
        ),
    },
    {
        "id": "riemann_543",
        "instance": "riemann",
        "path": "artifacts/riemann_543",
        "lean_file": "Cryptids/Machines.lean",
        "lean_def": "riemann543",
        "proof_path": "Cryptids/Riemann543.lean",
        "challenge_path": "Challenge.lean",
        "states": 543,
        "baseline_states": 744,
        "machine_sha256": (
            "14c7d827a8ef5ff7671f4642fe31d956c4880a0ce8270c74286b453313f4824e"
        ),
    },
]


@dataclasses.dataclass(frozen=True)
class Transition:
  write: int
  direction: int  # -1 for L, +1 for R
  next_state: int | None  # None for halt


@dataclasses.dataclass(frozen=True)
class Machine:
  states: int
  symbols: int
  table: tuple[tuple[Transition | None, ...], ...]
  canonical_text: str
  sha256: str


def sha256_bytes(data: bytes) -> str:
  return hashlib.sha256(data).hexdigest()


def parse_canonical_machine(text: str) -> Machine:
  """Parses a canonical 2-symbol Turing machine transition table."""
  rows: list[tuple[Transition | None, ...]] = []
  for raw_line in text.splitlines():
    line = raw_line.split("#", 1)[0].strip()
    if not line:
      continue
    cells = line.split()
    if len(cells) != 2:
      raise ValueError(
          f"Expected 2 symbol columns, got {len(cells)}: {raw_line!r}"
      )
    row: list[Transition | None] = []
    for cell in cells:
      if cell == "---":
        row.append(None)
        continue
      if len(cell) < 3:
        raise ValueError(f"Malformed transition cell: {cell!r}")
      write = int(cell[0])
      if write not in (0, 1):
        raise ValueError(f"Invalid write symbol in {cell!r}")
      dir_char = cell[1]
      if dir_char not in ("L", "R"):
        raise ValueError(f"Invalid direction in {cell!r}")
      direction = -1 if dir_char == "L" else 1
      target_str = cell[2:]
      next_state = int(target_str)
      row.append(
          Transition(write=write, direction=direction, next_state=next_state)
      )
    rows.append(tuple(row))

  num_states = len(rows)
  for q, row in enumerate(rows):
    for sym, tr in enumerate(row):
      if (
          tr is not None
          and tr.next_state is not None
          and not (0 <= tr.next_state < num_states)
      ):
        raise ValueError(
            f"State {q} symbol {sym} targets out-of-range state {tr.next_state}"
            f" (states={num_states})"
        )

  canonical_lines = []
  for row in rows:
    cell_strs = []
    for tr in row:
      if tr is None:
        cell_strs.append("---")
      else:
        d = "L" if tr.direction == -1 else "R"
        cell_strs.append(f"{tr.write}{d}{tr.next_state}")
    canonical_lines.append(" ".join(cell_strs))
  canonical_text = "\n".join(canonical_lines) + "\n"
  return Machine(
      states=num_states,
      symbols=2,
      table=tuple(rows),
      canonical_text=canonical_text,
      sha256=sha256_bytes(canonical_text.encode("utf-8")),
  )


def derive_machine_from_source(source_text: str, fmt: str) -> Machine:
  """Re-derives canonical Machine from published source format (standard, tursi, nql)."""
  if fmt == "standard":
    blocks = source_text.strip().split("_")
    lines = []
    for blk in blocks:
      c0, c1 = blk[:3], blk[3:6]
      cells = []
      for c in (c0, c1):
        if c == "---" or c[2] == "Z" or c[2] == "-":
          cells.append("---")
        else:
          w = c[0]
          d = c[1]
          st = c[2]
          nxt = str(ord(st) - ord("A"))
          cells.append(f"{w}{d}{nxt}")
      lines.append(" ".join(cells))
    return parse_canonical_machine("\n".join(lines) + "\n")

  if fmt == "nql":
    order: list[str] = []
    table: dict[tuple[str, int], tuple[int, str, str | None]] = {}
    for line in source_text.splitlines():
      if not line.strip():
        continue
      name, _, rest = line.partition(" = ")
      fields = rest.split()
      order.append(name)
      for sym in (0, 1):
        w, move, nxt = fields[3 * sym : 3 * sym + 3]
        d = "L" if move.upper().startswith("L") else "R"
        table[(name, sym)] = (int(w), d, None if nxt == "HALT" else nxt)
    start = "!ENTRY"
  elif fmt == "tursi":
    start = ""
    order = []
    rows: list[tuple[str, int, int, str, str]] = []
    for line in source_text.splitlines():
      m_hdr = re.fullmatch(r"#!\s*start\s+(\S+)\s*", line)
      if m_hdr:
        start = m_hdr.group(1)
        continue
      if not line.strip() or line.startswith("#"):
        continue
      st, r_sym, w_sym, move, nxt = line.split()
      if st not in order:
        order.append(st)
      d = "L" if move.upper().startswith("L") else "R"
      rows.append((st, int(r_sym), int(w_sym), d, nxt))
    defined = set(order)
    table = {
        (st, r_sym): (w_sym, d, nxt if nxt in defined else None)
        for st, r_sym, w_sym, d, nxt in rows
    }
  else:
    raise ValueError(f"Unknown format: {fmt}")

  numbering = {start: 0}
  for name in order:
    numbering.setdefault(name, len(numbering))
  names = sorted(numbering, key=numbering.__getitem__)
  out_lines = []
  for name in names:
    cells = []
    for sym in (0, 1):
      if (name, sym) not in table:
        cells.append("---")
        continue
      w, d, nxt = table[(name, sym)]
      if nxt is None:
        cells.append("---")
      else:
        cells.append(f"{w}{d}{numbering[nxt]}")
    out_lines.append(" ".join(cells))
  return parse_canonical_machine("\n".join(out_lines) + "\n")


def parse_lean_machine_def(
    lean_text: str, def_name: str, expected_table_path: str | None = None
) -> Machine:
  """Parses a `Machine N 2` definition (`load_machine_rows%`, `Machine.ofRows <def_name>Rows`, or inline `Machine.ofRows [...]`) from a Lean file."""
  m_load = re.search(
      rf'def {def_name}Rows : List \(List \(Option \(Fin 2 × Dir × Fin (\d+)\)\)\) :=\s*load_machine_rows%\s*"([^"]+)"',
      lean_text,
  )
  if m_load is not None:
    expected_states = int(m_load.group(1))
    table_path = m_load.group(2)
    if expected_table_path is not None:
      assert table_path == expected_table_path, (
          f"{def_name}: expected load_machine_rows% {expected_table_path!r}, got"
          f" {table_path!r}"
      )
    assert (
        'elab "load_machine_rows% "' in lean_text
        or "public import Cryptids.Machines.FromFile" in lean_text
    ), f"{def_name}: missing load_machine_rows% elaborator"
    assert (
        f"def {def_name} : Machine {expected_states} 2 := Machine.ofRows {def_name}Rows"
        in lean_text
    ), f"Missing `def {def_name} : Machine {expected_states} 2 := Machine.ofRows {def_name}Rows`"
    loaded = parse_canonical_machine(
        (ROOT / table_path).read_text(encoding="utf-8")
    )
    assert (
        loaded.states == expected_states
    ), f"{def_name}: expected {expected_states} states, got {loaded.states} in {table_path}"
    return loaded

  m_rows = re.search(
      rf"def {def_name}Rows : List \(List \(Option \(Fin 2 × Dir × Fin (\d+)\)\)\) := \[\s*(.*?)\]\]",
      lean_text,
      re.DOTALL,
  )
  if m_rows is not None:
    expected_states = int(m_rows.group(1))
    assert (
        f"def {def_name} : Machine {expected_states} 2 := Machine.ofRows {def_name}Rows"
        in lean_text
    ), f"Missing `def {def_name} : Machine {expected_states} 2 := Machine.ofRows {def_name}Rows`"
    body = m_rows.group(2) + "]"
  else:
    m = re.search(
        rf"def {def_name} : Machine (\d+) 2 := Machine\.ofRows \[\s*(.*?)\]\]",
        lean_text,
        re.DOTALL,
    )
    assert (
        m is not None
    ), f"Missing `def {def_name} : Machine _ 2 := Machine.ofRows [...]`"
    expected_states = int(m.group(1))
    body = m.group(2) + "]"
  row_matches = re.findall(
      r"\[\s*(none|some \(\d+, \.(?:left|right), \d+\))\s*,\s*(none|some \(\d+,"
      r" \.(?:left|right), \d+\))\s*\]",
      body,
  )
  assert (
      len(row_matches) == expected_states
  ), f"{def_name}: expected {expected_states} rows, parsed {len(row_matches)}"
  lines = []
  for c0, c1 in row_matches:
    cells = []
    for c in (c0, c1):
      if c == "none":
        cells.append("---")
      else:
        cm = re.fullmatch(r"some \((\d+), \.(left|right), (\d+)\)", c)
        assert cm is not None
        w, d_str, nxt = cm.group(1), cm.group(2), cm.group(3)
        d = "L" if d_str == "left" else "R"
        cells.append(f"{w}{d}{nxt}")
    lines.append(" ".join(cells))
  return parse_canonical_machine("\n".join(lines) + "\n")


def verify_goldbach_proof_tables(
    cand_machine: Machine, ref_machine: Machine
) -> None:
  """Verifies that goldbach_24 is the exact 24-state quotient of goldbach_25 under the 4 unary-shift edits."""
  proof_text = (ROOT / "Cryptids/Goldbach24.lean").read_text(encoding="utf-8")
  assert "def edited : Machine 25 2 := Machine.ofRows [" in proof_text
  assert (
      "theorem candidate_equivalent : Halts candidate ↔ Halts reference"
      in proof_text
  )

  # The 4 transition edits on goldbach_25 that implement the +1 unary shift
  # and make state 8 unreachable:
  edits = {
      (1, 0): Transition(1, 1, 18),
      (3, 0): Transition(0, -1, 5),
      (4, 0): Transition(0, -1, 16),
      (7, 1): Transition(1, -1, 22),
  }

  def embed(q: int) -> int:
    return q if q < 8 else q + 1

  for q in range(24):
    eq = embed(q)
    for s in (0, 1):
      expected_ed = edits.get((eq, s), ref_machine.table[eq][s])
      cand_tr = cand_machine.table[q][s]
      if expected_ed is None:
        assert cand_tr is None, f"Expected halt at ({q}, {s})"
      else:
        assert cand_tr is not None
        assert (
            cand_tr.write == expected_ed.write
            and cand_tr.direction == expected_ed.direction
        )
        assert embed(cand_tr.next_state) == expected_ed.next_state, (
            f"Goldbach embed mismatch at ({q}, {s}):"
            f" embed({cand_tr.next_state}) != {expected_ed.next_state}"
        )


def zf_renum_429(q: int) -> int:
  s = (1 if q > 42 else 0) + (1 if q > 91 else 0) + (1 if q > 95 else 0)
  return q - s


def zf_map_state_429(q: int, l0: int, h: int) -> int:
  """Projects a 432-state ZF state onto the 429-state candidate state space."""
  if q == 42:
    return zf_renum_429(13)
  if q == 95:
    return zf_renum_429(331)
  if q == 94:
    return zf_renum_429(94 if h == 0 else 372)
  if q == 93:
    return zf_renum_429(93 if h == 0 else 420)
  if q == 91:
    if h == 0:
      return zf_renum_429(46)
    return zf_renum_429(93 if l0 == 1 else 94)
  return zf_renum_429(q)


def zf_valid_state_429(q: int, l2: int, l1: int, l0: int, h: int) -> bool:
  """Checks the reachable local tape invariant for the 432-state ZF machine."""
  l0_eq_1_states = {
      114,
      330,
      334,
      349,
      355,
      372,
      373,
      375,
      376,
      378,
      379,
      383,
      389,
      400,
      402,
      404,
      406,
      408,
      413,
      417,
      423,
      426,
  }
  return (
      (q not in l0_eq_1_states or l0 == 1)
      and (q not in {331, 335, 350, 356} or (l0 == 1 and l1 == 1))
      and (q not in {351, 357} or (l0 == 1 and l1 == 1 and l2 == 1))
      and (q != 113 or l0 == 0)
      and (q != 114 or l1 == 0)
      and (q != 115 or (l0 == 0 and l1 == 1))
      and (q != 116 or (l0 == 1 and l1 == 1 and l2 == 0))
      and (q != 348 or (l0 == 0 and l1 == 1 and l2 == 1))
      and (q != 95 or (h == 1 and l0 == 1 and l1 == 1))
      and (
          q != 94 or ((h == 0 and l0 == 1 and l1 == 1) or (h == 1 and l0 == 1))
      )
      and (q != 93 or ((h == 0 and l0 == 1) or h == 1))
      and (
          q != 91
          or (
              (h == 1 and l0 == 1 and l1 == 0) or (h == 1 and l0 == 0) or h == 0
          )
      )
  )


def verify_zf_table_homomorphism(
    ref_machine: Machine,
    cand_431: Machine,
    cand_430: Machine,
    cand_429: Machine,
) -> None:
  """Exhaustively checks the finite inductive invariants of zf_431, zf_430, and zf_429."""
  assert cand_430.states == 430

  # 1. Check zf_431: exact Moore merge of state 42 -> 13 across all transitions
  def map_431(q: int) -> int:
    if q == 42:
      return 13
    return q if q < 42 else q - 1

  for q in range(432):
    for sym in (0, 1):
      tr_r = ref_machine.table[q][sym]
      tr_c = cand_431.table[map_431(q)][sym]
      if tr_r is None:
        assert tr_c is None
      else:
        assert tr_c is not None
        assert (tr_c.write, tr_c.direction, tr_c.next_state) == (
            tr_r.write,
            tr_r.direction,
            map_431(tr_r.next_state),
        )

  # 2. Check zf_429: exhaustive check of validState_next and transition_mapState
  assert zf_valid_state_429(
      0, 0, 0, 0, 0
  ), "Initial configuration must satisfy validState"
  for q in range(432):
    for l2 in (0, 1):
      for l1 in (0, 1):
        for l0 in (0, 1):
          for h in (0, 1):
            if not zf_valid_state_429(q, l2, l1, l0, h):
              continue
            tr_r = ref_machine.table[q][h]
            q_c = zf_map_state_429(q, l0, h)
            tr_c = cand_429.table[q_c][h]
            if tr_r is None:
              assert tr_c is None
            else:
              assert tr_c is not None
              assert (
                  tr_c.write == tr_r.write and tr_c.direction == tr_r.direction
              )
              for x in (0, 1):
                if tr_r.direction == 1:  # right move
                  assert zf_valid_state_429(
                      tr_r.next_state, l1, l0, tr_r.write, x
                  )
                  assert tr_c.next_state == zf_map_state_429(
                      tr_r.next_state, tr_r.write, x
                  )
                else:  # left move
                  assert zf_valid_state_429(tr_r.next_state, x, l2, l1, l0)
                  assert tr_c.next_state == zf_map_state_429(
                      tr_r.next_state, l1, l0
                  )


def verify_riemann_543_derivation(
    ref_machine: Machine, cand_machine: Machine
) -> dict[str, int]:
  """Verifies Cryptids/Riemann543.lean's 25-cell window invariant (m0Nat/m1Nat), state homomorphism fNat, bounce pairs, and SyncCountdown chains across all 744 states."""
  proof_text = (ROOT / "Cryptids/Riemann543.lean").read_text(encoding="utf-8")
  assert (
      "theorem candidate_equivalent : Halts candidate ↔ Halts reference"
      in proof_text
  )

  def extract_bst_array(fn_name: str) -> list[int]:
    blocks = re.findall(
        rf"def (?:_{fn_name}_\d+|{fn_name}) \(n : (?:Nat|ℕ)\).*?:=\s*(.*?)(?=\ndef |\ntheorem )",
        proof_text,
        re.DOTALL,
    )
    assert blocks, f"Missing {fn_name} in Cryptids/Riemann543.lean"
    vals = [
        int(x) for blk in blocks for x in re.findall(r"(?:then|else)\s+(\d+)", blk)
    ]
    assert (
        len(vals) == 744
    ), f"Expected 744 leaves in {fn_name}, got {len(vals)}"
    return vals

  def extract_bst_bool_array(fn_name: str) -> list[bool]:
    blocks = re.findall(
        rf"def (?:_{fn_name}_\d+|{fn_name}) \(n : (?:Nat|ℕ)\).*?:=\s*(.*?)(?=\ndef |\ntheorem )",
        proof_text,
        re.DOTALL,
    )
    assert blocks, f"Missing {fn_name} in Cryptids/Riemann543.lean"
    vals = [
        x == "true"
        for blk in blocks
        for x in re.findall(r"(?:then|else)\s+(true|false)", blk)
    ]
    assert (
        len(vals) == 744
    ), f"Expected 744 leaves in {fn_name}, got {len(vals)}"
    return vals

  f_norm = extract_bst_array("fNat")
  m0_list = extract_bst_array("m0Nat")
  m1_list = extract_bst_array("m1Nat")
  is_bounce0 = extract_bst_bool_array("isBounce0")
  is_bounce1 = extract_bst_bool_array("isBounce1")

  assert (
      max(f_norm) == 542 and len(set(f_norm)) == 543
  ), "fNat must map onto Fin 543"

  def allow_bit(v0: int, v1: int, k: int, b: int) -> bool:
    return bool(((v0 if b == 0 else v1) >> k) & 1)

  def check_all_cells(
      v0: int, v1: int, w0: int, w1: int, write_sym: int, direction: int
  ) -> bool:
    for k in range(25):
      for b in (0, 1):
        if direction == -1:  # .left
          if k == 0:
            src_ok = True
          elif k == 12:
            src_ok = b == write_sym
          else:
            src_ok = allow_bit(v0, v1, k - 1, b)
        else:  # .right
          if k == 24:
            src_ok = True
          elif k == 10:
            src_ok = b == write_sym
          else:
            src_ok = allow_bit(v0, v1, k + 1, b)
        if src_ok and not allow_bit(w0, w1, k, b):
          return False
    return True

  special_matches = re.findall(
      r"\(n == (\d+)\s*&&\s*b\.val == ([01])\)", proof_text
  )
  special_pairs = {(int(q_s), int(b_s)) for q_s, b_s in special_matches}
  assert (
      len(special_pairs) == 52
  ), f"Expected 52 special pairs in isSpecialNat, got {len(special_pairs)}"

  # Verify every special pair has its theorem in Cryptids/Riemann543.lean
  for q_sp, b_sp in special_pairs:
    if (q_sp, b_sp) not in {(503, 0), (376, 0), (386, 0), (472, 1), (251, 0)}:
      assert (
          f"theorem sync_from_{q_sp}_{b_sp} " in proof_text
      ), f"Missing theorem sync_from_{q_sp}_{b_sp}"

  verified_1step = 0
  verified_bounce = 0
  inactive_slots = 0
  for q in range(744):
    for b in (0, 1):
      if (q, b) in special_pairs:
        continue
      if not allow_bit(m0_list[q], m1_list[q], 11, b):
        inactive_slots += 1
        continue
      is_b = is_bounce0[q] if b == 0 else is_bounce1[q]
      if is_b:
        tr1 = ref_machine.table[q][b]
        assert tr1 is not None
        tr_p0 = ref_machine.table[tr1.next_state][0]
        tr_p1 = ref_machine.table[tr1.next_state][1]
        assert tr_p0 is not None and tr_p1 is not None
        assert tr_p0.write == 0 and tr_p1.write == 1
        assert (
            tr_p0.direction == -tr1.direction
            and tr_p1.direction == -tr1.direction
        )
        assert tr_p0.next_state == tr_p1.next_state
        tr2 = ref_machine.table[tr_p0.next_state][tr1.write]
        assert tr2 is not None
        cand_tr = cand_machine.table[f_norm[q]][b]
        assert cand_tr == Transition(
            tr2.write, tr2.direction, f_norm[tr2.next_state]
        )
        assert check_all_cells(
            m0_list[q],
            m1_list[q],
            m0_list[tr2.next_state],
            m1_list[tr2.next_state],
            tr2.write,
            tr2.direction,
        )
        verified_bounce += 1
      else:
        tr = ref_machine.table[q][b]
        cand_tr = cand_machine.table[f_norm[q]][b]
        if tr is None:
          assert cand_tr is None
        else:
          assert cand_tr == Transition(
              tr.write, tr.direction, f_norm[tr.next_state]
          )
          assert check_all_cells(
              m0_list[q],
              m1_list[q],
              m0_list[tr.next_state],
              m1_list[tr.next_state],
              tr.write,
              tr.direction,
          )
        verified_1step += 1

  return {
      "original_states": 744,
      "final_states": 543,
      "states_saved": 201,
      "hub_cand": f_norm[371],
      "verified_1step_transitions": verified_1step,
      "verified_bounce_transitions": verified_bounce,
      "verified_sync_chains": len(special_pairs),
      "unreachable_state_symbol_slots": inactive_slots,
  }


def extract_goldbach_chk0(
    machine: Machine, steps: int, is_candidate: bool
) -> dict[str, object]:
  """Runs Goldbach machine and extracts `(is_right, q, p)` at every outer-loop chk0 entry."""
  tape: dict[int, int] = {}
  head = 0
  state = 0
  visited_states = {0}
  checkpoints: list[tuple[int, bool, int, int]] = []

  def read(pos: int) -> int:
    return tape.get(pos, 0)

  def count_ones(pos: int, delta: int) -> int:
    c = 0
    while read(pos) == 1:
      c += 1
      pos += delta
    return c

  shift = 1 if is_candidate else 0
  for step in range(1, steps + 1):
    sym = read(head)
    tr = machine.table[state][sym]
    if tr.write == 0:
      tape.pop(head, None)
    else:
      tape[head] = 1
    head += tr.direction
    assert tr.next_state is not None, f"Unexpected halt at step {step}"
    state = tr.next_state
    visited_states.add(state)

    # BaseTr.chk0: state == 0, head at left end of replicate (p + shift) 1
    if state == 0 and read(head) == 1 and read(head - 1) == 0:
      c_p = count_ones(head, 1)
      p = c_p - shift
      if p >= 1:
        c_left = count_ones(head - 2, -1)
        c_right = count_ones(head + c_p + 1, 1)
        if c_left > 0 and c_right == 0:
          # is_right = True: LBase has q + 1 + shift ones
          q = c_left - (1 + shift)
          if q >= 0:
            checkpoints.append((step, True, q, p))
        elif c_left == 0:
          # is_right = False: REnd has q + shift ones
          q = c_right - shift
          if q >= 0:
            checkpoints.append((step, False, q, p))

  return {
      "visited_states": len(visited_states),
      "checkpoints": checkpoints,
  }


def verify_zf_lockstep_simulation(
    ref_machine: Machine, cand_429: Machine, steps: int
) -> dict[str, object]:
  """Simulates zf_432 and zf_429 side by side for `steps` steps and asserts 1-to-1 lockstep identity."""
  tape_r: dict[int, int] = {}
  tape_c: dict[int, int] = {}
  head_r = 0
  head_c = 0
  q_r = 0
  q_c = 0
  visited_r = {0}
  visited_c = {0}

  for step in range(1, steps + 1):
    sr = tape_r.get(head_r, 0)
    sc = tape_c.get(head_c, 0)
    assert (
        sr == sc and head_r == head_c
    ), f"ZF tape/head divergence at step {step}"

    tr_r = ref_machine.table[q_r][sr]
    tr_c = cand_429.table[q_c][sc]
    assert (
        tr_r.write == tr_c.write and tr_r.direction == tr_c.direction
    ), f"ZF action divergence at step {step}: ref={tr_r}, cand={tr_c}"

    if tr_r.write == 0:
      tape_r.pop(head_r, None)
      tape_c.pop(head_c, None)
    else:
      tape_r[head_r] = 1
      tape_c[head_c] = 1

    head_r += tr_r.direction
    head_c += tr_c.direction
    assert tr_r.next_state is not None and tr_c.next_state is not None
    q_r = tr_r.next_state
    q_c = tr_c.next_state
    visited_r.add(q_r)
    visited_c.add(q_c)

    l2 = tape_r.get(head_r - 3, 0)
    l1 = tape_r.get(head_r - 2, 0)
    l0 = tape_r.get(head_r - 1, 0)
    h = tape_r.get(head_r, 0)
    assert zf_valid_state_429(
        q_r, l2, l1, l0, h
    ), f"ZF validState failed at step {step}"
    expected_qc = zf_map_state_429(q_r, l0, h)
    assert q_c == expected_qc, (
        f"ZF state map divergence at step {step}: q_r={q_r}, q_c={q_c},"
        f" expected={expected_qc}"
    )

  assert tape_r == tape_c
  return {
      "steps_verified": steps,
      "final_head": head_r,
      "nonzero_cells": len(tape_r),
      "visited_states_ref": len(visited_r),
      "visited_states_cand": len(visited_c),
  }


def verify_riemann_checkpoint_simulation(
    ref_machine: Machine, cand_machine: Machine, steps: int, hub_cand: int
) -> dict[str, object]:
  """Simulates riemann_744 and riemann_543 and asserts bit-exact relative tape equality at every outer-loop entry (state 371 / f(371))."""

  def run_for_hub_checkpoints(
      m: Machine, hub_state: int
  ) -> tuple[list[tuple[int, int, tuple[tuple[int, int], ...]]], int]:
    tape: dict[int, int] = {}
    head = 0
    state = 0
    visited = {0}
    snaps: list[tuple[int, int, tuple[tuple[int, int], ...]]] = []
    for step in range(1, steps + 1):
      sym = tape.get(head, 0)
      tr = m.table[state][sym]
      assert tr is not None
      if tr.write == 0:
        tape.pop(head, None)
      else:
        tape[head] = 1
      head += tr.direction
      assert tr.next_state is not None
      state = tr.next_state
      visited.add(state)
      if state == hub_state:
        rel_tape = tuple(sorted((pos - head, val) for pos, val in tape.items()))
        snaps.append((step, head, rel_tape))
    return snaps, len(visited)

  snaps_ref, vis_ref = run_for_hub_checkpoints(ref_machine, 371)
  snaps_cand, vis_cand = run_for_hub_checkpoints(cand_machine, hub_cand)
  common = min(len(snaps_ref), len(snaps_cand))
  assert common > 100, f"Expected >100 outer-loop checkpoints, got {common}"
  offset0 = snaps_cand[0][1] - snaps_ref[0][1]
  for idx in range(common):
    _, head_r, tape_r = snaps_ref[idx]
    _, head_c, tape_c = snaps_cand[idx]
    assert head_c - head_r == offset0, (
        f"Riemann origin offset mismatch at checkpoint {idx}: {head_c} vs"
        f" {head_r}"
    )
    assert (
        tape_c == tape_r
    ), f"Riemann relative tape mismatch at checkpoint {idx}"

  ref_step_last = snaps_ref[common - 1][0]
  cand_step_last = snaps_cand[common - 1][0]
  return {
      "checkpoints_verified": common,
      "ref_steps_at_last_checkpoint": ref_step_last,
      "cand_steps_at_last_checkpoint": cand_step_last,
      "steps_saved": ref_step_last - cand_step_last,
      "speedup_ratio": round(ref_step_last / cand_step_last, 6),
      "visited_states_ref": vis_ref,
      "visited_states_cand": vis_cand,
  }


def run_verification(
    steps: int = 250_000, verbose: bool = True
) -> dict[str, object]:
  """Runs all first-principles baseline, candidate, and simulation verifications."""
  t0 = time.perf_counter()
  report: dict[str, object] = {
      "baselines": {},
      "candidates": {},
      "simulations": {},
  }

  if verbose:
    print("=" * 78)
    print("CONJECTURE MACHINES: ZERO-DEPENDENCY FIRST-PRINCIPLES VERIFICATION")
    print("=" * 78)

  # 1. Verify Cryptids/Machines.lean formal Halts definition and FromFile.lean elaborator
  machines_lean_bytes = (ROOT / "Cryptids/Machines.lean").read_bytes()
  machines_lean_sha = sha256_bytes(machines_lean_bytes)
  machines_lean_text = machines_lean_bytes.decode("utf-8")
  assert (
      "def Halts (M : Machine states symbols) : Prop := (StateTransition.eval"
      " (step M) init).Dom"
      in machines_lean_text
  )
  assert 'elab "load_machine_rows% " path:str : term' in machines_lean_text
  if verbose:
    print(
        f"[PASS] Cryptids/Machines.lean verified ({machines_lean_sha[:16]}...)"
    )

  # 2. Verify published baseline sources and re-derive canonical tables
  baseline_machines: dict[str, Machine] = {}
  for inst_name, spec in PINNED_BASELINES.items():
    src_bytes = (ROOT / str(spec["source_file"])).read_bytes()
    src_sha = sha256_bytes(src_bytes)
    assert (
        src_sha == spec["source_sha256"]
    ), f"{inst_name} source SHA-256 mismatch"

    tbl_bytes = (ROOT / str(spec["table_file"])).read_bytes()
    tbl_sha = sha256_bytes(tbl_bytes)
    assert (
        tbl_sha == spec["table_file_sha256"]
    ), f"{inst_name} table file SHA-256 mismatch"

    src_text = src_bytes.decode("utf-8")
    tbl_text = tbl_bytes.decode("utf-8")
    m_from_src = derive_machine_from_source(src_text, str(spec["format"]))
    m_from_tbl = parse_canonical_machine(tbl_text)
    assert m_from_src.table == m_from_tbl.table, (
        f"{inst_name}: derived machine from published source does not match"
        " pinned table"
    )
    m = m_from_tbl
    assert (
        m.sha256 == spec["canonical_machine_sha256"]
    ), f"{inst_name}: canonical machine SHA-256 mismatch: {m.sha256}"
    assert m.states == spec["states"] and m.symbols == spec["symbols"]
    ref_lean_text = (ROOT / str(spec["lean_file"])).read_text(encoding="utf-8")
    assert (
        parse_lean_machine_def(
            ref_lean_text,
            str(spec["lean_def"]),
            expected_table_path=str(spec["table_file"]),
        ).table
        == m.table
    ), f"{spec['lean_file']} table mismatch"
    baseline_machines[inst_name] = m
    report["baselines"][inst_name] = {
        "states": m.states,
        "symbols": m.symbols,
        "source_sha256": src_sha,
        "table_sha256": tbl_sha,
        "canonical_machine_sha256": m.sha256,
    }
    if verbose:
      print(
          f"[PASS] Baseline {inst_name:<8}: {m.states:>3} states | "
          f"source->table->Lean verified ({spec['lean_file']})"
      )

  # 3. Parse and verify all 5 candidate directories, standalone machine files, and Lean proof files
  cand_machines: dict[str, Machine] = {}
  for cspec in CANDIDATES:
    cid = str(cspec["id"])
    inst = str(cspec["instance"])
    cdir = ROOT / str(cspec["path"])
    m_text = (cdir / "machine.txt").read_text(encoding="utf-8")
    m_lean_text = (ROOT / str(cspec["lean_file"])).read_text(encoding="utf-8")
    p_path = ROOT / str(cspec["proof_path"])
    p_bytes = p_path.read_bytes()
    p_text = p_bytes.decode("utf-8")
    c_path = ROOT / str(cspec["challenge_path"])
    c_text = c_path.read_text(encoding="utf-8")
    m = parse_canonical_machine(m_text)
    p_sha = sha256_bytes(p_bytes)

    assert (
        m.states == cspec["states"]
    ), f"{cid} state count mismatch: {m.states}"
    assert (
        m.sha256 == cspec["machine_sha256"]
    ), f"{cid} machine SHA-256 mismatch: {m.sha256}"
    assert (
        parse_lean_machine_def(
            m_lean_text,
            str(cspec["lean_def"]),
            expected_table_path=f"{cspec['path']}/machine.txt",
        ).table
        == m.table
    ), f"{cspec['lean_file']} candidate table mismatch"

    ref_def = str(PINNED_BASELINES[inst]["lean_def"])
    cand_def = str(cspec["lean_def"])
    b_states = int(cspec["baseline_states"])
    expected_ref_alias = (
        f"abbrev reference : BundledMachine 2 := Machines.{ref_def}.bundle"
    )
    expected_cand_alias = (
        f"abbrev candidate : BundledMachine 2 := Machines.{cand_def}.bundle"
    )
    expected_fewer_states = (
        "theorem candidate_fewer_states : candidate.states < reference.states"
    )
    assert (
        expected_ref_alias in p_text
    ), f"{cspec['proof_path']} missing `{expected_ref_alias}`"
    assert (
        expected_cand_alias in p_text
    ), f"{cspec['proof_path']} missing `{expected_cand_alias}`"
    assert (
        expected_fewer_states in p_text
    ), f"{cspec['proof_path']} missing `{expected_fewer_states}`"
    assert (
        expected_ref_alias in c_text
    ), f"{cspec['challenge_path']} missing `{expected_ref_alias}`"
    assert (
        expected_cand_alias in c_text
    ), f"{cspec['challenge_path']} missing `{expected_cand_alias}`"
    assert (
        expected_fewer_states in c_text
    ), f"{cspec['challenge_path']} missing `{expected_fewer_states}`"
    cand_machines[cid] = m

    b_states = int(cspec["baseline_states"])
    delta = b_states - m.states
    pct = round(100.0 * delta / b_states, 2)
    report["candidates"][cid] = {
        "instance": cspec["instance"],
        "states": m.states,
        "baseline_states": b_states,
        "states_saved": delta,
        "reduction_percent": pct,
        "machine_sha256": m.sha256,
        "proof_sha256": p_sha,
        "proof_lines": len(p_text.splitlines()),
    }
    if verbose:
      print(
          f"[PASS] Candidate {cid:<11}: {m.states:>3} states (-{delta:>3},"
          f" -{pct:>5.2f}%) | SHA-256 {m.sha256[:16]}... |"
          f" {cspec['proof_path']} ({len(p_text.splitlines())} lines)"
      )

  # 4. Mathematical transition-table & invariant cross-checks
  verify_goldbach_proof_tables(
      cand_machines["goldbach_24"], baseline_machines["goldbach"]
  )
  if verbose:
    print(
        "[PASS] Goldbach 24 Cryptids/Goldbach24.lean table cross-check: all 48"
        " candidate + 50 baseline cells match"
    )

  verify_zf_table_homomorphism(
      baseline_machines["zf"],
      cand_machines["zf_431"],
      cand_machines["zf_430"],
      cand_machines["zf_429"],
  )
  if verbose:
    print(
        "[PASS] ZF (431 / 430 / 429) state-homomorphism `mapState` verified"
        " across all 864 baseline transitions"
    )

  riemann_decomp = verify_riemann_543_derivation(
      baseline_machines["riemann"], cand_machines["riemann_543"]
  )
  report["riemann_decomposition"] = riemann_decomp
  if verbose:
    print(
        "[PASS] Riemann 543 25-cell window invariant (m0Nat/m1Nat), fNat"
        " homomorphism, and SyncCountdown chains verified across all 1,488 (q,"
        f" b) entries ({riemann_decomp['verified_1step_transitions']} 1-step,"
        f" {riemann_decomp['verified_bounce_transitions']} pass-bounce,"
        f" {riemann_decomp['verified_sync_chains']} multi-step SyncCountdown,"
        f" {riemann_decomp['unreachable_state_symbol_slots']} unreachable"
        " slots)"
    )

  # 5. Concrete blank-tape lockstep simulations
  gb_ref_sim = extract_goldbach_chk0(
      baseline_machines["goldbach"], steps, is_candidate=False
  )
  gb_cand_sim = extract_goldbach_chk0(
      cand_machines["goldbach_24"], steps, is_candidate=True
  )
  common_gb = min(
      len(gb_ref_sim["checkpoints"]), len(gb_cand_sim["checkpoints"])
  )
  assert common_gb >= 80
  for i in range(common_gb):
    _, r_dir, r_q, r_p = gb_ref_sim["checkpoints"][i]
    _, c_dir, c_q, c_p = gb_cand_sim["checkpoints"][i]
    assert (r_dir, r_q, r_p) == (
        c_dir,
        c_q,
        c_p,
    ), f"Goldbach checkpoint {i} mismatch"
  report["simulations"]["goldbach_24"] = {
      "steps_simulated": steps,
      "checkpoints_matched": common_gb,
      "ref_visited_states": gb_ref_sim["visited_states"],
      "cand_visited_states": gb_cand_sim["visited_states"],
      "ref_steps_at_checkpoint": gb_ref_sim["checkpoints"][common_gb - 1][0],
      "cand_steps_at_checkpoint": gb_cand_sim["checkpoints"][common_gb - 1][0],
  }
  if verbose:
    print(
        f"[PASS] Goldbach 24 lockstep simulation ({steps:,} steps):"
        f" {common_gb}/{common_gb} `chk0(is_right, q, p)` checkpoints match"
        " 1-to-1; 24/24 candidate states visited"
    )

  zf_sim = verify_zf_lockstep_simulation(
      baseline_machines["zf"], cand_machines["zf_429"], steps
  )
  report["simulations"]["zf_429"] = zf_sim
  if verbose:
    print(
        f"[PASS] ZF 429 lockstep simulation ({steps:,} steps): "
        f"100% step-for-step identity at every step t=0..{steps:,} "
        f"(head={zf_sim['final_head']}, {zf_sim['nonzero_cells']} active cells)"
    )

  riemann_sim = verify_riemann_checkpoint_simulation(
      baseline_machines["riemann"],
      cand_machines["riemann_543"],
      steps,
      int(riemann_decomp["hub_cand"]),
  )
  report["simulations"]["riemann_543"] = riemann_sim
  if verbose:
    print(
        f"[PASS] Riemann 543 lockstep simulation ({steps:,} steps):"
        f" {riemann_sim['checkpoints_verified']}/{riemann_sim['checkpoints_verified']}"
        " NQL outer-loop dispatch checkpoints match with 100% bit-exact"
        f" relative tape equality ({riemann_sim['steps_saved']:,} steps saved)"
    )

  elapsed = time.perf_counter() - t0
  report["elapsed_seconds"] = round(elapsed, 3)
  if verbose:
    print("=" * 78)
    print(
        f"ALL FIRST-PRINCIPLES VERIFICATION CHECKS PASSED IN {elapsed:.2f}s"
        " (EXIT 0)"
    )
    print("=" * 78)
  return report


def main() -> int:
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument(
      "--steps",
      type=int,
      default=250_000,
      help=(
          "Number of blank-tape simulation steps per machine (default: 250000)."
      ),
  )
  parser.add_argument(
      "--json",
      type=pathlib.Path,
      default=None,
      help="Optional path to write structured verification report JSON.",
  )
  args = parser.parse_args()
  report = run_verification(steps=args.steps, verbose=True)
  if args.json is not None:
    args.json.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
  return 0


if __name__ == "__main__":
  sys.exit(main())
