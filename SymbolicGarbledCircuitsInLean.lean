import SymbolicGarbledCircuitsInLean.Garbling.Security
import SymbolicGarbledCircuitsInLean.Garbling.Correctness

/-!
# Two garbling schemes

This repository builds **two** independent garbling schemes.  They share no Lean code — both
declare the same names in the same namespaces, so they cannot even appear in one import graph.

| | scheme | root module |
|---|---|---|
| **Encryption only** | LM18 / the base paper: `Gb(Dup,·)` duplicates the wire label | `SymbolicGarbledCircuitsInLean` |
| **PRG + encryption** | this extension: `Gb(Dup,·)` derives both output labels with `G0`/`G1` | `PRGExtension` |

Import whichever root you want; `lake build` builds both, so neither can rot unnoticed.

The circuit language (`Circuit`, `WireBundle`) is identical in both.  The expression algebras
differ by exactly two constructors — the extension adds `G0` and `G1`.  The schemes differ by
exactly one gate: how `DupC` derives its output labels.  Everything else is the same argument
carried out twice.

What only the extension has: computational correctness (`garbleCorrectComp`), projectivity
(`Garble_projective`), a concrete `IsPolyTime` (`GenPolyTime`), and a repaired efficiency
hypothesis — the encryption-only `garblingSecure` still quantifies `_Hreduction` over **all**
encryption schemes, a form that is false in any concrete cost model and that
`PRGExtension/Expression/ComputationalSemantics/Efficiency/PolyTime.lean` fixes.

See `CHECKPOINT.md`, `report.md` and `FUTURE-WORK.md`.
-/

/-!
## This root: the encryption-only scheme

`garblingSecure` (`Garbling/Security.lean`) and `garbleCorrect` (`Garbling/Correctness.lean`).
This is the base paper's development, unmodified apart from the import-path repair of
2026-09-21j.  For the PRG extension's stronger results see the `PRGExtension` root.
-/
