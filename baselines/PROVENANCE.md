# Baseline Provenance & Upstream Re-Compilation (`baselines/PROVENANCE.md`)

All three baseline transition tables (`baselines/tables/*.txt`) are deterministically compiled from their verbatim published upstream source files (`baselines/sources/*`). Our standalone verifier (`verify.py`) parses each upstream source from first principles and verifies byte-for-byte identity against the canonical 5-tuple tables.

| Domain | Upstream Source File | Upstream Format | Source SHA-256 | Canonical Table File | Table SHA-256 | Canonical Machine SHA-256 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `goldbach` (`25` states) | `sources/goldbach_25_bbchallenge.txt` | `standard` (bbchallenge 1-line underscore-separated) | `3b8934a193ecb165a64dbf048332961fc7a62e7381e69095340a9a85d752380c` | `tables/goldbach_25.txt` | `f5b995cb7917d9943431fc8f2554b0872b185ca81e14865307d26db2776b52a5` | `da5bdb63c1ad0d0e3e97f8ca75addc2b6622dea483b3e3cdfbd2fc55363a5a67` |
| `zf` (`432` states) | `sources/zf_432_wade.tm` | `tursi` (Andrew Wade 2025 `q s -> w d q'`) | `68a9de26ef68ee9cdf085d201b996686ae55d9570822bcf040aca5999e4f4261` | `tables/zf_432.txt` | `e662deaa52994e73413af37a434dbfb4e8c8204a8d972154ead2d839f442af66` | `cb9ffd320f7360b5e0e49181a6201286b408d1f8c168d61fafc51d1ca8b86702` |
| `riemann` (`744` states) | `sources/riemann_744_sorear.tm` | `nql` (Stefan O'Rear 2016 named-state NQL output) | `de0084433909f2600a5052eeb0bb2acd9b0ac315078abd1b92d4f3595601dd31` | `tables/riemann_744.txt` | `9866af71143c85cceeaf2e05be8fef1c3ccb226fe04640b23b7b887f815a25d0` | `4f629ed5be1715747f3d467dbb35bded647a25dc740a80b5208c14f65d7d5f44` |

## Lean 4 Machine Specification ([`Cryptids/Machines.lean`](../Cryptids/Machines.lean))

* **File:** [`Cryptids/Machines.lean`](../Cryptids/Machines.lean)
* **Contents:** Defines `ConjectureMachines.Dir`, `ConjectureMachines.Machine`, `ConjectureMachines.Tape`, `ConjectureMachines.Cfg`, `ConjectureMachines.step`, `ConjectureMachines.init`, and `ConjectureMachines.Halts`.
