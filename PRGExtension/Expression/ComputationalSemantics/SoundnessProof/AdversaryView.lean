import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability
-- import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.Def
-- import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Def

import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.NormalizePreserves
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.RenamePreserves
import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Lemmas
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey

import SymbolicGarbledCircuitsInLean.Core.Fixpoints
import Mathlib.Probability.Distributions.Uniform

import Mathlib.Data.Finset.SDiff



noncomputable
def hideSelectedFreshKeys {s : Shape} (keyToRemove : Finset (Expression Shape.KeyS)) (expr : Expression s) (_H : keyToRemove ∩ extractKeys expr = ∅) :=
  hideSelectedS keyToRemove expr

lemma noFreshKeysAfterRemoveOneKeyProper {s : Shape} (expr : Expression s)  (key : Expression Shape.KeyS) (H : key ∉ extractKeys expr)
  (keyToRemove : Finset (Expression Shape.KeyS)) (Hset : keyToRemove ∩ extractKeys expr = ∅) :
  (keyToRemove \ {key}) ∩ extractKeys (removeOneKeyProper key expr H) = ∅ :=
by
  have H2 : extractKeys (removeOneKeyProper key expr H) ⊆ extractKeys expr := by
    apply keyPartsMonotoneP
    apply hideKeys2SmallerValue
  refine Eq.symm (Finset.Subset.antisymm ?_ ?_)
  · simp
  · have Hl : ((keyToRemove \ {key}) ∩ extractKeys (removeOneKeyProper key expr H)) ⊆ keyToRemove ∩ extractKeys expr :=
    by
      refine Finset.inter_subset_inter ?_ H2
      exact Finset.sdiff_subset
    exact subset_of_subset_of_eq Hl Hset

noncomputable
def expressionRecoveryNegTwoStep {s : Shape} (keyToRemove : Finset (Expression Shape.KeyS)) (expr : Expression s) (H : keyToRemove ∩ extractKeys expr = ∅) (key : Expression Shape.KeyS) (Hkey : key ∈ keyToRemove) :=
  let keyMinus := keyToRemove \ {key}
  let first := removeOneKeyProper key expr (by
    intro Hc
    have Hz : key ∉ keyToRemove ∩ extractKeys expr := by simp [H]
    apply Hz
    exact Finset.mem_inter_of_mem Hkey Hc
    )
  hideSelectedFreshKeys keyMinus first (by
    apply noFreshKeysAfterRemoveOneKeyProper
    assumption
    )

lemma twoHideEncryptedS {y z : Set (Expression Shape.KeyS)} (expr : Expression s):
  hideEncryptedS y (hideEncryptedS z expr) = hideEncryptedS (y ∩ z) expr := by
  induction expr <;> simp [hideEncryptedS, hideSelectedS, extractKeys, extractKeys] <;> try tauto
  case Enc s e1 e2 H1 H2 =>
    rw [apply_ite (hideEncryptedS ↑y)]
    simp [hideEncryptedS]
    simp [H1, H2]
    split <;> try simp
    next he1 =>
      split <;> try simp
      next he2 =>
        rw [ite_cond_eq_true]
        simp; constructor <;> assumption
      next he2 =>
        rw [ite_cond_eq_false]
        simp; intro hcontra; exfalso
        apply he2; assumption
    next he1 =>
      rw [ite_cond_eq_false]
      simp; intro; apply he1

lemma twoHiding {y z : Finset (Expression Shape.KeyS)} (expr : Expression s):
  (y ⊆ z) ->
  hideEncrypted y (hideEncrypted z expr) =
  hideEncrypted y expr := by
    intro; simp [← hideEncryptedEqS, twoHideEncryptedS]
    congr; symm; apply Set.left_eq_inter.mpr
    assumption

lemma twoHideKeys2 {y z : Set (Expression Shape.KeyS)} (expr : Expression s):
  hideSelectedS y (hideSelectedS z expr) =
  hideSelectedS (y ∪ z) expr :=
  by
    simp [hideSelectedS, ← hideEncryptedEqS]
    rw [twoHideEncryptedS]

lemma expressionRecoveryNegEq {s : Shape} (keyToRemove : Finset (Expression Shape.KeyS)) (key : Expression Shape.KeyS) (Hkey : key ∈ keyToRemove) (expr : Expression s) (H : keyToRemove ∩ extractKeys expr = ∅)   :
  hideSelectedFreshKeys keyToRemove expr H = expressionRecoveryNegTwoStep keyToRemove expr H key Hkey :=
  by
    rw [expressionRecoveryNegTwoStep, hideSelectedFreshKeys]
    simp [hideSelectedFreshKeys, removeOneKeyProper, twoHideKeys2]
    congr
    exact Eq.symm (Set.insert_eq_of_mem Hkey)


def expressionRecovery {s : Shape} (p : Expression s) : Expression s :=
  let key := extractKeys p
  hideEncrypted key p


def symbolicToSemanticIndistinguishabilityHidingInnerMotive (z : Finset (Expression Shape.KeyS)) : Prop :=
  forall
   (IsPolyTime : PolyFamOracleCompPred) (_HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (_Hreduction : forall enc shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc expr key₀))
  (enc : encryptionScheme) (_HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  {shape : Shape} (expr : Expression shape)
  (_HexprZ : ((extractKeys expr) ∩ z = ∅)),
   CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc expr)) (famDistrLift (exprToFamDistr enc (hideSelectedS z expr)))

theorem symbolicToSemanticIndistinguishabilityHidingInner  (z : Finset (Expression Shape.KeyS)) : symbolicToSemanticIndistinguishabilityHidingInnerMotive z :=
by
  induction z using Finset.induction_on'
  case empty =>
    intro IsPolyTime HPolyTime Hreduction enc HEncIndCpa shape expr Hexpr Hempty
    -- rw [symbolicToSemanticIndistinguishabilityHidingInnerMotive]
    conv =>
      arg 2
      simp [emptyHide]
    apply indRfl
  case insert key keySet Hkey Hkey2 HkeyFresh Hind  =>
    intro IsPolyTime HPolyTime Hreduction enc HEncIndCpa shape expr Hexpr
    rw [<-hideSelectedFreshKeys]
    case _H =>
      simp [Finset.inter_comm]
      assumption
    rw [expressionRecoveryNegEq _ key, expressionRecoveryNegTwoStep, hideSelectedFreshKeys]
    case Hkey =>
      exact Finset.mem_insert_self key keySet
    have Hnot : key ∉ extractKeys expr := by
      intro Hcontr
      have L : key ∈ extractKeys expr ∩ insert key keySet := by
        refine Finset.mem_inter.mpr ?_
        constructor <;> try assumption
        exact Finset.mem_insert_self key keySet
      rw [Hexpr] at L
      simp at L
    apply indTransRev
    · have Heq : insert key keySet \ {key} = keySet := by
        apply Finset.ext_iff.mpr
        intro a
        rw [Finset.mem_sdiff]
        rw [Finset.mem_insert]
        simp
        if Ha : a = key then
          subst a
          tauto
        else
          tauto
      rw [Heq]
      apply indSym
      apply Hind <;> try assumption
      · simp [removeOneKeyProper] at *
        rw [<-Heq, Finset.inter_comm]
        apply noFreshKeysAfterRemoveOneKeyProper <;> try assumption
        rw [Finset.inter_comm]
        assumption
    · apply symbolicToSemanticIndistinguishabilityHidingOneKey <;> try assumption

theorem symbolicToSemanticIndistinguishabilityHiding
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (Hreduction : forall enc shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc expr key₀))
  (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  {shape : Shape} (expr : Expression shape)
  : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc expr)) (famDistrLift (exprToFamDistr enc (expressionRecovery expr))) :=
by
  rw [expressionRecovery]
  rw [<-hideKeysUniv]
  rw [← Finset.coe_sdiff]
  apply symbolicToSemanticIndistinguishabilityHidingInner <;> try assumption
  rw [Finset.inter_sdiff_self]

def exprCompInd (IsPolyTime : PolyFamOracleCompPred) (enc : encryptionScheme) {shape : Shape} (expr1 expr2 : Expression shape) :=
  CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc expr1)) (famDistrLift (exprToFamDistr enc expr2))


lemma iterationOrFresh {z : Finset (Expression Shape.KeyS)} (expr : Expression s):
  (extractKeys (hideEncrypted z expr) ⊆ z) ->
  hideEncrypted (extractKeys (hideEncrypted z expr)) (hideEncrypted z expr) =
  hideEncrypted (extractKeys (hideEncrypted z expr)) expr :=
  by
    apply twoHiding

theorem symbolicToSemanticIndistinguishabilityAdversaryView
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (Hreduction : forall enc shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc expr key₀))
  (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  {shape : Shape} (expr: Expression shape)
  : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc expr)) (famDistrLift (exprToFamDistr enc (adversaryView expr))) :=
  by
  let R (e1 e2 : Expression shape) := exprCompInd IsPolyTime enc e1 e2
  have Z := fixaccess (fun key => hideEncrypted key expr) extractKeys (keyRecoveryMonotone expr) expr (keyRecoveryContained expr) R
    (by
      intro e1 e2 e3 Ha Hb
      simp [R, exprCompInd] at *
      apply indTrans _ Ha Hb)
    (by
      intro z
      simp [R, exprCompInd]
      apply indRfl)
    (by
      intro z Hz
      simp [R, exprCompInd]
      have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction enc HEncIndCpa (hideEncrypted z expr)
      simp [expressionRecovery] at Z
      rw [iterationOrFresh] at Z
      apply Z
      assumption
    )
    (by
      intro z
      simp [R, exprCompInd]
      have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction enc HEncIndCpa expr
      simp [expressionRecovery] at Z
      apply Z
      )
  apply Z
