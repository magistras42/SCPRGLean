-- This module serves as the root of the `SymbolicGarbledCircuitsInLean` library.
-- Import modules here that should be built as part of the library.

import PRGExtension.Core.Fixpoints
import PRGExtension.Core.CardinalityLemmas
import PRGExtension.ComputationalIndistinguishability.Def
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Renamings
import PRGExtension.Expression.Lemmas.Renaming
import PRGExtension.Expression.Lemmas.NormalizeIdempotent
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.Expression.Lemmas.ReplacePRG
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.Expression.ComputationalSemantics.Soundness
import PRGExtension.Expression.ComputationalSemantics.RenamePreserves

-- PRG-based garbled circuits (LM18 §3-§5): definitions and the independence invariants.
import PRGExtension.Garbling.Circuits
import PRGExtension.Garbling.GarblingDef
import PRGExtension.Garbling.Evaluation
import PRGExtension.Garbling.Freshness
import PRGExtension.Garbling.Independence
import PRGExtension.Garbling.Correctness
import PRGExtension.Garbling.Lemma5
import PRGExtension.Garbling.Lemma6
import PRGExtension.Garbling.GarbleKeys
import PRGExtension.Garbling.GarbleFixpoint
import PRGExtension.Garbling.GbStage
import PRGExtension.Garbling.ViewKeys
import PRGExtension.Garbling.Lemma7
import PRGExtension.Garbling.Lemma8
import PRGExtension.Garbling.ValueInvariant
import PRGExtension.Garbling.Alignment
import PRGExtension.Garbling.Theorem5
import PRGExtension.Garbling.Security

import VCVio2.ToMathlib.Control.MonadTransformer
import VCVio2.VCVio.OracleComp.OracleComp
import VCVio2.VCVio.OracleComp.DistSemantics.EvalDist

-- Garbled Circuit Files I Didn't Get To Yet
-- import SymbolicGarbledCircuitsInLean.Garbling.Circuits
-- import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef
-- import SymbolicGarbledCircuitsInLean.Garbling.Simulate
-- import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleHole
-- import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleProof
-- import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.SimulateProof
-- import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleHoleBitSwap

-- import SymbolicGarbledCircuitsInLean.Garbling.Security
-- import SymbolicGarbledCircuitsInLean.Garbling.Correctness
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKeyGen
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.FixpointStep
