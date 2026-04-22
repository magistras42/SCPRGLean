import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability
import SymbolicGarbledCircuitsInLean.Expression.Lemmas.HideEncrypted
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.Def
import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Def

/-
import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.ComputationalIndistinguishability.Def
-/

import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.EncryptionIndCpa
import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Lemmas
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.SoundnessProof.AdversaryView

/-
import PRGExtension.Expression.ComputationalSemantics.EncryptionIndCpa
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.AdversaryView
-/

import SymbolicGarbledCircuitsInLean.Core.Fixpoints
-- import PRGExtension.Core.Fixpoints
import Mathlib.Probability.Distributions.Uniform

import Mathlib.Data.Finset.SDiff

-- This file proves the soundness theorem: if two expressions are symbolically indistinguishable, then their computational semantics (distributions over bitstrings)  are computationally indistinguishable. The technical details of this proof are in `SoundnessProof/`.

-- open PRG

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

/-
-- imports

-- THIS WILL REPLACE SOUNDNESS.LEAN

theorem symbolicEquivalenceImpliesComputationalIndistinguishability
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  (prg : prgScheme) (HPrgSecure : prgSchemeSecure IsPolyTime prg)
  -- Include polynomial time reduction assumptions for BOTH IND-CPA and PRG
  (HreductionCpa : forall enc prg shape expr key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (HreductionPrg : forall enc prg shape expr seed, IsPolyTime (reductionToPrgOracle enc prg expr seed))
  {shape : Shape} (e1 e2 : Expression shape)
  -- The symbolic game hop assumption:
  (H_equiv : symbolicEquivalence e1 e2) :
  -- The semantic guarantee:
  CompIndistinguishabilityDistr IsPolyTime
    (famDistrLift (exprToFamDistr enc prg e1))
    (famDistrLift (exprToFamDistr enc prg e2)) := by

  -- We prove this by induction on the structure of the symbolic game hops!
  induction H_equiv with

  | structural expr1 expr2 H_sym_ind =>
      -- 1. Use `symbolicToSemanticIndistinguishabilityAdversaryView` (from IND-CPA proof)
      -- 2. Use normalization/renaming lemmas to show structural equality implies distribution equality
      sorry

  | idealize_PRG expr targetSeed idx0 idx1 H_no_seed H_diff H_fresh0 H_fresh1 =>
      -- This matches the PRG theorem we just defined!
      apply symbolicToSemanticIndistinguishabilityPrgIdealization
      exact IsPolyTime
      -- ... pass assumptions

  | trans expr1 expr2 expr3 H1 H2 IH1 IH2 =>
      -- Use the transitivity of computational indistinguishability (`indTrans`)
      apply indTrans
      exact IH1
      exact IH2

  | symm expr1 expr2 H1 IH1 =>
      -- Use the symmetry of computational indistinguishability (`indSymm`)
      apply indSymm
      exact IH1
-/
