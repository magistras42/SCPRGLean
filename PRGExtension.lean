import PRGExtension.Core.Fixpoints
import PRGExtension.Core.CardinalityLemmas
import PRGExtension.Core.UniformProduct
import PRGExtension.ComputationalIndistinguishability.Def
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Renamings
import PRGExtension.Expression.Lemmas.Renaming
import PRGExtension.Expression.Lemmas.NormalizeIdempotent
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.Expression.Lemmas.ReplacePRG
import PRGExtension.Expression.Lemmas.GStar
import PRGExtension.Expression.HoleFree
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.Expression.ComputationalSemantics.Executable.Executable
import PRGExtension.Expression.ComputationalSemantics.Executable.ExecutableDistribution
import PRGExtension.Expression.ComputationalSemantics.Executable.SeededEnvironment
import PRGExtension.Expression.ComputationalSemantics.Soundness
import PRGExtension.Expression.ComputationalSemantics.RenamePreserves
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKeyGen
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.FixpointStep
import PRGExtension.Expression.ComputationalSemantics.Efficiency.PolyTime
import PRGExtension.Expression.ComputationalSemantics.Efficiency.CostModel
import PRGExtension.Expression.ComputationalSemantics.Efficiency.GeneratedPolyTime
import PRGExtension.Expression.Lemmas.PseudorandomRenaming
import PRGExtension.Garbling.Circuits
import PRGExtension.Garbling.GarblingDef
import PRGExtension.Garbling.Simulate
import PRGExtension.Garbling.Correctness.Correctness
import PRGExtension.Garbling.Correctness.ComputationalCorrectness
import PRGExtension.Garbling.Correctness.ExecutableCorrectness
import PRGExtension.Garbling.HoleFree
import PRGExtension.Garbling.EvaluatorTotality
import PRGExtension.Crypto.ChaCha20
import PRGExtension.Crypto.StreamCipher
import PRGExtension.Crypto.Ggm
import PRGExtension.Crypto.DomainSeparation
import PRGExtension.Garbling.SymbolicHiding.Lemmas
import PRGExtension.Garbling.SymbolicHiding.GarbleProof
import PRGExtension.Garbling.SymbolicHiding.GarbleHole
import PRGExtension.Garbling.SymbolicHiding.SimulateProof
import PRGExtension.Garbling.SymbolicHiding.GarbleHoleBitSwap
import PRGExtension.Garbling.Security.Security
import PRGExtension.Garbling.Security.SecurityFromPrimitives
import PRGExtension.Garbling.Security.ExecutableSecurity

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

What only the extension has: computational correctness (`garbleCorrectComp`), an executable
implementation refining it (`garbleExecCorrect`), projectivity (`Garble_projective`), a
concrete `IsPolyTime` (`GenPolyTime`), and a repaired efficiency
hypothesis — the encryption-only `garblingSecure` still quantifies `_Hreduction` over **all**
encryption schemes, a form that is false in any concrete cost model and that
`PRGExtension/Expression/ComputationalSemantics/Efficiency/PolyTime.lean` fixes.

See `CHECKPOINT.md`, `report.md` and `FUTURE-WORK.md`.
-/

/-!
## This root: the PRG + encryption scheme

Entry points, weakest hypotheses last:
`garblingSecure` ⊃ `garblingSecureFromEfficiency` ⊃ `garblingSecureFromCostModel` ⊃
`garblingSecureGenerated`, and separately **`garblingSecureRelative`** — the one to cite, which
states security against an arbitrary adversary class.  Correctness: `garbleCorrect`
(symbolic), `garbleCorrectComp` (computational) and `garbleExecCorrect` (the executable
implementation, `Garbling/Correctness/ExecutableCorrectness.lean`), with ChaCha20 instantiating both
primitives (`Crypto/ChaCha20.lean`).
-/
