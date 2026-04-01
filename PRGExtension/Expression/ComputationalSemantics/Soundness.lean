import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability
import SymbolicGarbledCircuitsInLean.Expression.Lemmas.HideEncrypted
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.Def
import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Def

import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.EncryptionIndCpa
import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Lemmas
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.SoundnessProof.AdversaryView

import SymbolicGarbledCircuitsInLean.Core.Fixpoints
import Mathlib.Probability.Distributions.Uniform

import Mathlib.Data.Finset.SDiff

-- This file proves the soundness theorem: if two expressions are symbolically indistinguishable, then their computational semantics (distributions over bitstrings)  are computationally indistinguishable. The technical details of this proof are in `SoundnessProof/`.

theorem symbolicToSemanticIndistinguishability
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (Hreduction : forall enc shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc expr key₀))
  (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  (shape : Shape) (expr1 expr2 : Expression shape)
  (Hi : symIndistinguishable expr1 expr2)
  : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc expr1)) (famDistrLift (exprToFamDistr enc expr2)) :=
  by
    simp [symIndistinguishable] at Hi
    let ⟨r, Hr, Hi⟩ := Hi
    let fab {X Y : Type} {a b : X} (f : X -> Y) (H : a = b) : f a = f b := by rw [H]
    have Hi2 := fab (exprToFamDistr enc) Hi
    rw [<-normalizeExprToDistr] at Hi2
    rw [<-normalizeExprToDistr] at Hi2
    rw [<-applyRenamePreservesCompSem2 enc] at Hi2 <;> try assumption
    apply indTrans _ (symbolicToSemanticIndistinguishabilityAdversaryView IsPolyTime HPolyTime Hreduction enc HEncIndCpa expr1)
    simp [Hi2]
    apply indSym
    apply symbolicToSemanticIndistinguishabilityAdversaryView <;> try assumption
