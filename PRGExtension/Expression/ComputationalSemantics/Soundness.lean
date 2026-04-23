import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.ComputationalIndistinguishability.Def

import PRGExtension.Expression.ComputationalSemantics.EncryptionIndCpa
import PRGExtension.Expression.ComputationalSemantics.PrgSecurity
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.AdversaryView

import PRGExtension.Core.Fixpoints
import Mathlib.Probability.Distributions.Uniform

import Mathlib.Data.Finset.SDiff

-- This file proves the soundness theorem: if two expressions are symbolically indistinguishable, then their computational semantics (distributions over bitstrings)  are computationally indistinguishable. The technical details of this proof are in `SoundnessProof/`.

open PRG

theorem symbolicToSemanticIndistinguishability
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
  (Hreduction : ∀ (enc : encryptionScheme) (prg : prgScheme) (shape : Shape) (expr : Expression shape) (key₀ : ℕ),
    IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (HreductionPrg : forall (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape) (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
  (enc : encryptionScheme)
  (prg : prgScheme)
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
  {shape : Shape} (expr1 expr2 : Expression shape)
  (Hi : symIndistinguishable expr1 expr2) :
  CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg expr1))
    (famDistrLift (exprToFamDistr enc prg expr2)) := by
  -- Unfold the pure symbolic structural equivalence
  simp [symIndistinguishable] at Hi
  let ⟨r, Hr, Hi⟩ := Hi
  -- Push the equality down to the distribution semantics
  let fab {X Y : Type} {a b : X} (f : X -> Y) (H : a = b) : f a = f b := by rw [H]
  have Hi2 := fab (exprToFamDistr enc prg) Hi
  -- Normalize and apply renaming
  rw [<-normalizeExprToDistr] at Hi2
  rw [<-normalizeExprToDistr] at Hi2
  rw [<-applyRenamePreservesCompSem2 enc prg] at Hi2 <;> try assumption
  -- Computational Transitivity Hop 1: expr1 ≈ adversaryView expr1
  apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
  -- HOP 1: Prove expr1 ≈ adversaryView expr1
  exact symbolicToSemanticIndistinguishabilityAdversaryView IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure expr1
  -- HOP 2: adversaryView expr1 ≈ expr2
  rw [Hi2]
  apply indSym
  exact symbolicToSemanticIndistinguishabilityAdversaryView IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure expr2
