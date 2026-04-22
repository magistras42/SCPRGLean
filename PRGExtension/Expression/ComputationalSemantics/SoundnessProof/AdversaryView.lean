import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability

import PRGExtension.Expression.ComputationalSemantics.NormalizePreserves
import PRGExtension.Expression.ComputationalSemantics.RenamePreserves
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey
import PRGExtension.Expression.ComputationalSemantics.PrgSecurity

import PRGExtension.Core.Fixpoints
import Mathlib.Probability.Distributions.Uniform

import Mathlib.Data.Finset.SDiff

open PRG

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
    -- hideEncryptedS_K reduces all nested keys back to themselves.
    -- H2 collapses the encrypted message.
    simp [hideEncryptedS, hideEncryptedS_K, H2]
    split_ifs <;> simp_all [hideEncryptedS_K]

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
  (_Hreduction : forall enc prg shape (expr : Expression shape) (key₀ : ℕ), IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (enc : encryptionScheme) (prg : prgScheme)
  (_HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  (_HPrgSecure : prgSchemeSecure IsPolyTime prg)
  {shape : Shape} (expr : Expression shape)
  (_HexprZ : ((extractKeys expr) ∩ z = ∅)),
   CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc prg expr)) (famDistrLift (exprToFamDistr enc prg (hideSelectedS z expr)))

-- def symbolicToSemanticIndistinguishabilityHidingInnerMotive (z : Finset (Expression Shape.KeyS)) : Prop :=
--   forall
--    (IsPolyTime : PolyFamOracleCompPred) (_HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
--   (_Hreduction : forall enc prg shape (expr : Expression shape) (key₀ : ℕ), IsPolyTime (reductionHidingOneKey enc prg expr key₀))
--   (enc : encryptionScheme) (prg : prgScheme) (_HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
--   {shape : Shape} (expr : Expression shape)
--   (_HexprZ : ((extractKeys expr) ∩ z = ∅)),
--    CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc prg expr)) (famDistrLift (exprToFamDistr enc prg (hideSelectedS z expr)))

theorem symbolicToSemanticIndistinguishabilityHidingInner  (z : Finset (Expression Shape.KeyS)) : symbolicToSemanticIndistinguishabilityHidingInnerMotive z :=
by
  induction z using Finset.induction_on'
  case empty =>
    intro IsPolyTime HPolyTime Hreduction enc prg HEncIndCpa HPrgSecure shape expr Hexpr Hempty
    conv =>
      arg 2
      simp [emptyHide]
    apply indRfl
  case insert key keySet Hkey Hkey2 HkeyFresh Hind  =>
    intro IsPolyTime HPolyTime Hreduction enc prg HEncIndCpa HPrgSecure shape expr Hexpr
    rw [<-hideSelectedFreshKeys]
    case _H =>
      rw [Finset.inter_comm]
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
    ·  -- Can only guarantee IND-CPA hiding for truly random base keys
      cases key
      case VarK key₀ =>
          simp [removeOneKeyProper, removeOneKey]
          exact symbolicToSemanticIndistinguishabilityHidingOneKey IsPolyTime HPolyTime Hreduction enc HEncIndCpa expr key₀ Hnot
      -- TODO - need the PRG indistinguishability result
      case G0 ek =>
        simp [removeOneKeyProper, removeOneKey]
        let idx0 := 9998
        let idx1 := 9999
        apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
        · -- Goal 1: PRG Soundness Axiom!
          exact idealize_PRG_soundness enc prg expr ek idx0 idx1 IsPolyTime HPrgSecure (by sorry) (by decide) (by sorry) (by sorry)
        · -- Step B: Apply IND-CPA and Reverse PRG
          apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
          · -- Goal 2: IND-CPA Soundness
            exact symbolicToSemanticIndistinguishabilityHidingOneKey IsPolyTime HPolyTime Hreduction enc HEncIndCpa (replacePRG ek idx0 idx1 expr) idx0 (by sorry)
          · -- Goal 3: Reverse PRG Soundness
            apply indSym
            convert idealize_PRG_soundness enc prg (hideSelectedS {ek.G0} expr) ek idx0 idx1 IsPolyTime HPrgSecure (by sorry) (by decide) (by sorry) (by sorry)
            -- This leaves one new subgoal: proving the distributions are equal
          -- famDistrLift (exprToFamDistr ... (replacePRG ... (hideSelectedS ...))) =
          -- famDistrLift (exprToFamDistr ... (removeOneKey ... (replacePRG ...)))
            sorry
      case G1 ek =>
        simp [removeOneKeyProper, removeOneKey]
        let idx0 := 9998
        let idx1 := 9999
        apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
        · -- Goal 1: PRG Soundness Axiom!
          exact idealize_PRG_soundness enc prg expr ek idx0 idx1 IsPolyTime HPrgSecure (by sorry) (by decide) (by sorry) (by sorry)
        · -- Step B: Apply IND-CPA and Reverse PRG
          apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
          · -- Goal 2: IND-CPA Soundness
            exact symbolicToSemanticIndistinguishabilityHidingOneKey IsPolyTime HPolyTime Hreduction enc HEncIndCpa (replacePRG ek idx0 idx1 expr) idx0 (by sorry)
          · -- Goal 3: Reverse PRG Soundness
            apply indSym
            convert idealize_PRG_soundness enc prg (hideSelectedS {ek.G1} expr) ek idx0 idx1 IsPolyTime HPrgSecure (by sorry) (by decide) (by sorry) (by sorry)
            -- This leaves one new subgoal: proving the distributions are equal
          -- famDistrLift (exprToFamDistr ... (replacePRG ... (hideSelectedS ...))) =
          -- famDistrLift (exprToFamDistr ... (removeOneKey ... (replacePRG ...)))
            sorry

theorem symbolicToSemanticIndistinguishabilityHiding
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (Hreduction : forall enc prg shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (enc : encryptionScheme) (prg : prgScheme)
  (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  (HPrgSecure : prgSchemeSecure IsPolyTime prg)
  {shape : Shape} (expr : Expression shape)
  : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc prg expr)) (famDistrLift (exprToFamDistr enc prg (expressionRecovery expr))) :=
by
  rw [expressionRecovery]
  rw [← hideKeysUniv]
  rw [← Finset.coe_sdiff]
  -- allParts \ extractKeys is guaranteed to be a finite set due to our fixed point calculations earlier
  apply symbolicToSemanticIndistinguishabilityHidingInner (allParts expr \ extractKeys expr) IsPolyTime HPolyTime Hreduction enc prg HEncIndCpa HPrgSecure
  -- extractKeys expr ∩ (allParts expr \ extractKeys expr) = ∅
  apply Finset.eq_empty_of_forall_not_mem
  intro x
  simp

-- Deprecated theorem
-- theorem symbolicToSemanticIndistinguishabilityHiding
--   (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
--   (Hreduction : forall enc shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc expr key₀))
--   (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
--   {shape : Shape} (expr : Expression shape)
--   : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc expr)) (famDistrLift (exprToFamDistr enc (expressionRecovery expr))) :=
-- by
--   rw [expressionRecovery]
--   rw [<-hideKeysUniv]
--   rw [← Finset.coe_sdiff]
--   apply symbolicToSemanticIndistinguishabilityHidingInner <;> try assumption
--   rw [Finset.inter_sdiff_self]

def exprCompInd (IsPolyTime : PolyFamOracleCompPred) (enc : encryptionScheme) (prg : prgScheme) {shape : Shape} (expr1 expr2 : Expression shape) :=
  CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc prg expr1)) (famDistrLift (exprToFamDistr enc prg expr2))

lemma iterationOrFresh {z : Finset (Expression Shape.KeyS)} (expr : Expression s):
  (extractKeys (hideEncrypted z expr) ⊆ z) ->
  hideEncrypted (extractKeys (hideEncrypted z expr)) (hideEncrypted z expr) =
  hideEncrypted (extractKeys (hideEncrypted z expr)) expr :=
  by
    apply twoHiding

theorem symbolicToSemanticIndistinguishabilityAdversaryView
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (Hreduction : forall enc prg shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (enc : encryptionScheme) (prg : prgScheme)
  (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  (HPrgSecure : prgSchemeSecure IsPolyTime prg)
  {shape : Shape} (expr: Expression shape)
  : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc prg expr)) (famDistrLift (exprToFamDistr enc prg (adversaryView expr))) :=
  by
  let R (e1 e2 : Expression shape) := exprCompInd IsPolyTime enc prg e1 e2
  have Z := fixaccess
    (fun key => hideEncrypted key expr) -- f1
    (keyRecovery expr)                  -- f
    (keyRecoveryMonotone expr)          -- f_monotone
    expr                                -- fBound
    (keySubterms expr)                  -- boundSet
    (keyRecoveryContained expr)         -- HfBound
    R
    (by -- RTrans
      intro e1 e2 e3 Ha Hb
      simp [R, exprCompInd] at *
      apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
      · exact Ha
      · exact Hb)
    (by -- Ras block
      intro z Hz
      simp [R, exprCompInd]
      have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction enc prg HEncIndCpa HPrgSecure (hideEncrypted z expr)
      simp [expressionRecovery] at Z
      -- rw [iterationOrFresh] at Z
      -- apply Z
      -- assumption
      have Hsubset: extractKeys (hideEncrypted z expr) ⊆ z := by
        apply Finset.Subset.trans _ Hz
        simp [keyRecovery]
        -- apply Finset.subset_union_left
        sorry
      -- rw [iterationOrFresh Hsubset] at Z
      -- convert Z
      sorry
    )
    (by -- Rsup
      simp [R, exprCompInd]
      have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction enc prg HEncIndCpa HPrgSecure expr
      simp [expressionRecovery] at Z
      -- apply Z
      sorry
    )
  exact Z

-- Deprecated theorem
-- theorem symbolicToSemanticIndistinguishabilityAdversaryView
--   (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
--   (Hreduction : forall enc shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc expr key₀))
--   (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
--   {shape : Shape} (expr: Expression shape)
--   : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc expr)) (famDistrLift (exprToFamDistr enc (adversaryView expr))) :=
--   by
--   let R (e1 e2 : Expression shape) := exprCompInd IsPolyTime enc e1 e2
--   have Z := fixaccess (fun key => hideEncrypted key expr) extractKeys (keyRecoveryMonotone expr) expr (keyRecoveryContained expr) R
--     (by
--       intro e1 e2 e3 Ha Hb
--       simp [R, exprCompInd] at *
--       apply indTrans _ Ha Hb)
--     (by
--       intro z
--       simp [R, exprCompInd]
--       apply indRfl)
--     (by
--       intro z Hz
--       simp [R, exprCompInd]
--       have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction enc HEncIndCpa (hideEncrypted z expr)
--       simp [expressionRecovery] at Z
--       rw [iterationOrFresh] at Z
--       apply Z
--       assumption
--     )
--     (by
--       intro z
--       simp [R, exprCompInd]
--       have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction enc HEncIndCpa expr
--       simp [expressionRecovery] at Z
--       apply Z
--       )
--   apply Z
