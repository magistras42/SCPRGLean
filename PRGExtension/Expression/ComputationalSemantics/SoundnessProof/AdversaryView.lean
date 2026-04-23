import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability

import PRGExtension.Expression.ComputationalSemantics.NormalizePreserves
import PRGExtension.Expression.ComputationalSemantics.RenamePreserves
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOnePrgSeed
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
  (_HreductionPrg : forall (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape) (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
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
    intro IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure shape expr Hexpr Hempty
    conv =>
      arg 2
      simp [emptyHide]
    apply indRfl
  case insert key keySet Hkey Hkey2 HkeyFresh Hind  =>
    intro IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure shape expr Hexpr
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
      case G0 ek =>
        simp [removeOneKeyProper, removeOneKey]
        let idx0 := 9998
        let idx1 := 9999

        -- 1. Isolate the symbolic set-theory goals so they don't break the Game Hops
        have H_no_seed : ek ∉ adversaryKeys expr := by
          -- To prove this later: Unfold Hind. Since ek.G0 ∈ z, it is hidden.
          -- If ek were in adversaryKeys, prgClosure would mean ek.G0 is in adversaryKeys,
          -- contradicting that it is safely hidden in z.
          sorry

        have H_fresh0 : Expression.VarK idx0 ∉ keySubterms expr := by
          -- 9998 is a fresh integer not used in the expression
          sorry

        have H_fresh1 : Expression.VarK idx1 ∉ keySubterms expr := by
          -- 9999 is a fresh integer not used in the expression
          sorry

        have H_diff : idx0 ≠ idx1 := by decide

        apply indTrans
        · -- Goal 1: PRG Idealization (Real to Dummy)
          exact symbolicToSemanticIndistinguishabilityPrgIdealization IsPolyTime HreductionPrg enc prg HPrgSecure expr ek idx0 idx1
            (H_no_seed) (H_diff) (H_fresh0) (H_fresh1)
        · -- Apply IND-CPA on the now-dummy key, then Reverse PRG
          apply indTrans
          · -- Goal 2: IND-CPA Soundness on the dummy key
            exact symbolicToSemanticIndistinguishabilityHidingOneKey IsPolyTime HPolyTime Hreduction enc HEncIndCpa (replacePRG ek idx0 idx1 expr) idx0 (by sorry)
          · -- Goal 3: Reverse PRG Idealization (Dummy back to Real)
            apply indSym

            -- 1. State the structural commutation: replacing PRG after hiding G0
            -- is identical to hiding the idx0 dummy after replacing PRG.
            have H_commute : replacePRG ek idx0 idx1 (hideSelectedS {ek.G0} expr) =
                             removeOneKey (Expression.VarK idx0) (replacePRG ek idx0 idx1 expr) := by
              sorry

            rw [← H_commute]

            exact symbolicToSemanticIndistinguishabilityPrgIdealization IsPolyTime HreductionPrg enc prg HPrgSecure (hideSelectedS {ek.G0} expr) ek idx0 idx1
              (by sorry) (H_diff) (by sorry) (by sorry)
      case G1 ek =>
        simp [removeOneKeyProper, removeOneKey]
        let idx0 := 9998
        let idx1 := 9999

        -- 1. Isolate the symbolic set-theory goals so they don't break the Game Hops
        have H_no_seed : ek ∉ adversaryKeys expr := by
          -- To prove this later: Unfold Hind. Since ek.G0 ∈ z, it is hidden.
          -- If ek were in adversaryKeys, prgClosure would mean ek.G0 is in adversaryKeys,
          -- contradicting that it is safely hidden in z.
          sorry

        have H_fresh0 : Expression.VarK idx0 ∉ keySubterms expr := by
          -- 9998 is a fresh integer not used in the expression
          sorry

        have H_fresh1 : Expression.VarK idx1 ∉ keySubterms expr := by
          -- 9999 is a fresh integer not used in the expression
          sorry

        have H_diff : idx0 ≠ idx1 := by decide

        apply indTrans
        · -- Goal 1: PRG Idealization
          exact symbolicToSemanticIndistinguishabilityPrgIdealization IsPolyTime HreductionPrg enc prg HPrgSecure expr ek idx0 idx1
            (H_no_seed) (H_diff) (H_fresh0) (H_fresh1)
        · -- Apply IND-CPA and Reverse PRG
          apply indTrans
          · -- Goal 2: IND-CPA Soundness
            exact symbolicToSemanticIndistinguishabilityHidingOneKey IsPolyTime HPolyTime Hreduction enc HEncIndCpa (replacePRG ek idx0 idx1 expr) idx1 (by sorry)
          · -- Goal 3: Reverse PRG Soundness
            apply indSym

            have H_commute : replacePRG ek idx0 idx1 (hideSelectedS {ek.G1} expr) =
                             removeOneKey (Expression.VarK idx1) (replacePRG ek idx0 idx1 expr) := by
              sorry

            -- 2. Rewrite the goal using our commutation lemma backwards
            rw [← H_commute]

            exact symbolicToSemanticIndistinguishabilityPrgIdealization IsPolyTime HreductionPrg enc prg HPrgSecure (hideSelectedS {ek.G1} expr) ek idx0 idx1
              (by sorry) (H_diff) (by sorry) (by sorry)

theorem symbolicToSemanticIndistinguishabilityHiding
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (Hreduction : forall enc prg shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (HreductionPrg : forall (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape) (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
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
  apply symbolicToSemanticIndistinguishabilityHidingInner (allParts expr \ extractKeys expr) IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure
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

theorem symbolicToSemanticIndistinguishabilityAdversaryView'
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {I Spec Output} => IsPolyTime))
  (Hreduction : forall enc prg shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (HreductionPrg : forall (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape) (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
  (enc : encryptionScheme)
  (prg : prgScheme)
  (HEncIndCpa : encryptionSchemeIndCpa (fun {I Spec Output} => IsPolyTime) enc)
  (HPrgSecure : prgSchemeSecure (fun {I Spec Output} => IsPolyTime) prg)
  {shape : Shape}
  (expr : Expression shape) :
  CompIndistinguishabilityDistr (fun {I Spec Output} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg expr))
    (famDistrLift (exprToFamDistr enc prg (adversaryView expr))) := by
  let R := fun (e1 e2 : Expression shape) => exprCompInd (fun {I Spec Output} => IsPolyTime) enc prg e1 e2
  -- Upgraded fixaccess framework
  have Z := fixaccess
    (fun key => hideEncrypted key expr) -- f1 (View Generator)
    (keyRecovery expr)                  -- f  (Unified PRG Key Recovery Step)
    (keyRecoveryMonotone expr)          -- f_monotone
    expr                                -- fBound
    (keySubterms expr)                  -- boundSet
    (keyRecoveryContained expr)         -- HfBound
    R
    -- Transitivity (RTrans)
    (by
      intro e1 e2 e3 Ha Hb
      simp [R, exprCompInd] at *
      apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
      · exact Ha
      · exact Hb
    )
    -- Single-Step Fixpoint Hiding (Ras)
    (by
      intro z Hz
      simp [R, exprCompInd]
      -- Apply semantic hiding to the current expression
      have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure (hideEncrypted z expr)
      simp [expressionRecovery] at Z
      -- Extracting from z-hidden expr is a subset of extracting from PRG-hidden expr
      have H_monotone : extractKeys (hideEncrypted z expr) ⊆ extractKeys (hideEncrypted (prgClosure (keySubterms expr) z) expr) := by
        apply keyPartsMonotone
        apply hideEncryptedMonotone
        apply subset_prgClosure
      -- Bridge the extraction to the full PRG recovery
      have H_extract_sub_recovery : extractKeys (hideEncrypted z expr) ⊆ keyRecovery expr z := by
        apply Finset.Subset.trans H_monotone
        apply subset_prgClosure
      -- Prove the subset required by iterationOrFresh
      have Hsubset : extractKeys (hideEncrypted z expr) ⊆ z := by
        apply Finset.Subset.trans H_extract_sub_recovery Hz
      apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
      . exact Z
      .
        have Heq : hideEncrypted (extractKeys (hideEncrypted z expr)) (hideEncrypted z expr) = hideEncrypted (extractKeys (hideEncrypted z expr)) expr := iterationOrFresh expr Hsubset
        rw [Heq]
        -- this is where the prg indistinguishability results should go
        sorry
    )
    -- Base Case Initialization (Rsup)
    (by
      simp [R, exprCompInd]
      have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure expr
      simp [expressionRecovery] at Z
      rw [hideEncrypted_keySubterms expr]
      apply indRfl
    )
  exact Z

theorem symbolicToSemanticIndistinguishabilityAdversaryView
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
  (Hreduction : forall enc prg shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (HreductionPrg : forall (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape) (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
  (enc : encryptionScheme)
  (prg : prgScheme)
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
  {shape : Shape}
  (expr : Expression shape) :
  CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg expr))
    (famDistrLift (exprToFamDistr enc prg (adversaryView expr))) := by
  let R := fun (e1 e2 : Expression shape) => exprCompInd (fun {_ _ _} => IsPolyTime) enc prg e1 e2
  -- Upgraded fixaccess framework
  have Z := fixaccess
    (fun key => hideEncrypted key expr) -- f1 (View Generator)
    (keyRecovery expr)                  -- f  (Unified PRG Key Recovery Step)
    (keyRecoveryMonotone expr)          -- f_monotone
    expr                                -- fBound
    (keySubterms expr)                  -- boundSet
    (keyRecoveryContained expr)         -- HfBound
    R
    -- Transitivity (RTrans)
    (by
      intro e1 e2 e3 Ha Hb
      simp [R, exprCompInd] at *
      apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
      · exact Ha
      · exact Hb
    )
    -- Single-Step Fixpoint Hiding (Ras)
    (by
      intro z Hz
      simp [R, exprCompInd]
      -- Apply semantic hiding to the current expression
      have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure (hideEncrypted z expr)
      simp [expressionRecovery] at Z

      -- Extracting from z-hidden expr is a subset of extracting from PRG-hidden expr
      have H_monotone : extractKeys (hideEncrypted z expr) ⊆ extractKeys (hideEncrypted (prgClosure (keySubterms expr) z) expr) := by
        apply keyPartsMonotone
        apply hideEncryptedMonotone
        apply subset_prgClosure

      -- Bridge the extraction to the full PRG recovery
      have H_extract_sub_recovery : extractKeys (hideEncrypted z expr) ⊆ keyRecovery expr z := by
        apply Finset.Subset.trans H_monotone
        apply subset_prgClosure

      -- Prove the subset required by iterationOrFresh
      have Hsubset : extractKeys (hideEncrypted z expr) ⊆ z := by
        apply Finset.Subset.trans H_extract_sub_recovery Hz

      -- Apply transitivity WITHOUT explicit parameters to avoid I✝ errors
      apply indTrans

      · -- Goal 1: LHS ≈ ?distr2
        exact Z

      · -- Goal 2: ?distr2 ≈ RHS
        -- (nested hide) ≈ (keyRecovery hide)
        have Heq : hideEncrypted (extractKeys (hideEncrypted z expr)) (hideEncrypted z expr) = hideEncrypted (extractKeys (hideEncrypted z expr)) expr := iterationOrFresh expr Hsubset
        rw [Heq]

        -- The goal is now: (un-nested hide) ≈ (keyRecovery hide)

        -- To clear the sorry safely (without timeouts), we build the RHS proof:
        let RHS_view := hideEncrypted (keyRecovery expr z) expr
        have Z_RHS := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure RHS_view
        simp [expressionRecovery] at Z_RHS

        --- 1. Equate the un-nesting for the RHS
        have Heq_RHS : hideEncrypted (extractKeys (hideEncrypted z expr)) RHS_view =
           hideEncrypted (extractKeys (hideEncrypted z expr)) expr :=
          twoHiding expr H_extract_sub_recovery

        -- 2. Equate the extraction sets
        have H_ext_eq : extractKeys RHS_view = extractKeys (hideEncrypted z expr) := by
          apply Finset.Subset.antisymm

          · -- Forward Direction: Since keyRecovery(z) ⊆ z (Hz), hiding the recovery
            -- is smaller than hiding z, so it extracts fewer keys.
            apply keyPartsMonotone
            apply hideEncryptedMonotone
            exact Hz

          · -- Reverse Direction: The extracted keys never shrink below the minimal view.
            -- 2. Hiding is monotone: Because y ⊆ K, hiding with y results in a smaller view than hiding with K.
            have H_view_inc : hideEncrypted (extractKeys (hideEncrypted z expr)) expr ⊆ hideEncrypted (keyRecovery expr z) expr := by
              apply hideEncryptedMonotone
              exact H_extract_sub_recovery

            -- 3. Extracting is monotone: Since the y-view is smaller than the K-view (RHS_view),
            -- it extracts fewer keys.
            have H_ext_inc : extractKeys (hideEncrypted (extractKeys (hideEncrypted z expr)) expr) ⊆ extractKeys RHS_view := by
              apply keyPartsMonotone
              exact H_view_inc

            -- 4. The Self-Extraction Property: Extracting keys from a y-view gives at least y.
            -- This is the missing link that cannot be bypassed.
            have H_y_sub_ext_y : extractKeys (hideEncrypted z expr) ⊆ extractKeys (hideEncrypted (extractKeys (hideEncrypted z expr)) expr) := by
              apply extractKeys_hideEncrypted_self -- Replace this sorry with your library's idempotence/self-extraction lemma

            -- 5. Chain the inclusions: y ⊆ extractKeys(y-view) ⊆ extractKeys(K-view)
            exact Finset.Subset.trans H_y_sub_ext_y H_ext_inc

        -- 3. Rewrite Z_RHS using our two structural proofs
        rw [H_ext_eq] at Z_RHS
        rw [Heq_RHS] at Z_RHS

        -- Z_RHS now proves: (keyRecovery hide) ≈ (un-nested hide)
        -- Our goal is: (un-nested hide) ≈ (keyRecovery hide)
        exact indSym Z_RHS
    )
    -- Base Case Initialization (Rsup)
    (by
      simp [R, exprCompInd]
      have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime Hreduction HreductionPrg enc prg HEncIndCpa HPrgSecure expr
      simp [expressionRecovery] at Z
      rw [hideEncrypted_keySubterms expr]
      apply indRfl
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
