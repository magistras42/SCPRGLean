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

/-!
# The adversary's view, and the fixpoint step

An adversary holding an expression can recover some keys — by decrypting what it can with what
it already knows, and by applying the PRG — and not others.  `expressionRecovery` computes that
closure, as the greatest fixpoint of `Core/Fixpoints.lean`, and `adversaryView_eq_gStar`
identifies it with LM18's `G*`.

`symbolicToSemanticIndistinguishabilityAdversaryView` is the payoff: replacing every subterm
encrypted under an unrecoverable key by a hole is computationally invisible.  It is proved by
iterating the one-key lemma of `HidingOneKey.lean` over the unrecoverable set, with
`hidingSideCondition` recording what must hold at each step.
-/

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

/--
  LM18's standing hypothesis for Lemma 3, in the form the hiding argument actually needs:
  every key that the hiding step removes from `e` is atomic.

  LM18 derives this from `Roots(Keys(e)) ⊆ 𝐊` together with the ancestor clause of the
  key-recovery function `r` (now implemented, see `keyRecovery`).  It is carried as an
  explicit hypothesis rather than proved because `Roots(Keys(e)) ⊆ 𝐊` is **not** preserved
  by the greatest-fixpoint iteration: hiding can bury an atomic key `K` inside a payload
  while `G0(K)` survives as an encryption key.  `scratch/TwoGateFixpoint.lean` exhibits
  exactly that on a two-gate garbled circuit.  Discharging it in general is LM18
  Lemma 2 / Theorem 1 (pseudorandom key renaming), which is future work.
-/
def hidingSideCondition {s : Shape} (e : Expression s) : Prop :=
  -- property 1: every key removed by the hiding step is atomic
  (∀ k ∈ allParts e \ extractKeys e, ∃ n : ℕ, k = Expression.VarK n) ∧
  -- property 3: no key removed by the hiding step is used as a PRG seed in `e`
  (∀ n : ℕ, Expression.VarK n ∈ allParts e \ extractKeys e → seedFree n e)

/-- Hiding never manufactures new key subterms, so being PRG-free is preserved. -/
lemma atomicKeys_hideEncrypted {s : Shape} (S : Finset (Expression Shape.KeyS))
    {e : Expression s} (h : AtomicKeys e) : AtomicKeys (hideEncrypted S e) :=
  atomicKeys_of_subset (keySubtermsMonotone _ _ (hideEncryptedSmallerValue S e)) h

/--
  The side condition is discharged outright for expressions with no PRG structure:
  every key is atomic (property 1) and nothing can be a seed (property 3).

  So on the PRG-free fragment the extended soundness theorem carries *no* extra
  hypotheses, i.e. it specialises exactly to the original encryption-only framework.
  It also shows the side condition is not vacuous.
-/
lemma hidingSideCondition_of_atomicKeys {s : Shape} {e : Expression s} (h : AtomicKeys e) :
  hidingSideCondition e := by
  constructor
  · intro k hk
    have hat : isAtomicKey k = true :=
      h k (allParts_subset_keySubterms e (Finset.mem_sdiff.mp hk).1)
    cases k with
    | VarK n => exact ⟨n, rfl⟩
    | G0 _ => simp [isAtomicKey] at hat
    | G1 _ => simp [isAtomicKey] at hat
  · intro n _
    exact seedFree_of_atomicKeys h n

def symbolicToSemanticIndistinguishabilityHidingInnerMotive (z : Finset (Expression Shape.KeyS)) : Prop :=
  forall
   (IsPolyTime : PolyFamOracleCompPred) (_HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (enc : encryptionScheme) (prg : prgScheme)
  (_Hreduction : EncReductionPolyTime IsPolyTime enc prg)
  (_HreductionPrg : PrgReductionPolyTime IsPolyTime enc prg)
  (_HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  (_HPrgSecure : prgSchemeSecure IsPolyTime prg)
  {shape : Shape} (expr : Expression shape)
  (_HexprZ : ((extractKeys expr) ∩ z = ∅))
  -- LM18 Lemma 3, property 1: every key we are about to hide is atomic.  Under the
  -- corrected `keyRecovery` this follows from `Roots(Keys(e)) ⊆ 𝐊`; it is carried as an
  -- explicit side condition because that premise is *not* preserved by the fixpoint
  -- iteration (see PRGExtension-Analysis.md §4.3 and scratch/TwoGateFixpoint.lean).
  (_Hatomic : ∀ k ∈ z, ∃ n : ℕ, k = Expression.VarK n)
  -- LM18 Lemma 3, property 3: none of the keys being hidden is a PRG seed of `expr`.
  (_Hseed : ∀ n : ℕ, Expression.VarK n ∈ z → seedFree n expr),
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
    intro IsPolyTime HPolyTime enc prg Hreduction HreductionPrg HEncIndCpa HPrgSecure shape expr Hexpr _Hatomic _Hseed Hempty
    conv =>
      arg 2
      simp [emptyHide]
    apply indRfl
  case insert key keySet Hkey Hkey2 HkeyFresh Hind  =>
    intro IsPolyTime HPolyTime enc prg Hreduction HreductionPrg HEncIndCpa HPrgSecure shape expr Hexpr Hatomic Hseed
    -- the key removed at this step is atomic ...
    have Hkatomic : ∃ n : ℕ, key = Expression.VarK n :=
      Hatomic key (Finset.mem_insert_self key keySet)
    -- ... and so is every key left for the induction hypothesis
    have HatomicSub : ∀ k ∈ keySet, ∃ n : ℕ, k = Expression.VarK n :=
      fun k hk => Hatomic k (Finset.mem_insert_of_mem hk)
    -- hiding only shrinks `exprKeys`, so seed-freeness survives `removeOneKeyProper`
    have HseedSub : ∀ (H' : key ∉ extractKeys expr) (n : ℕ), Expression.VarK n ∈ keySet →
        seedFree n (removeOneKeyProper key expr H') := by
      intro H' n hn
      exact seedFree_mono (exprKeysMonotone _ _ (hideKeys2SmallerValue _ _))
        (Hseed n (Finset.mem_insert_of_mem hn))
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
      refine Hind IsPolyTime HPolyTime enc prg Hreduction HreductionPrg HEncIndCpa HPrgSecure
        _ ?_ HatomicSub (HseedSub _)
      · simp [removeOneKeyProper] at *
        rw [<-Heq, Finset.inter_comm]
        apply noFreshKeysAfterRemoveOneKeyProper <;> try assumption
        rw [Finset.inter_comm]
        assumption
    ·  -- IND-CPA hiding is only available for truly random base keys.  By `Hkatomic`
       -- the key being removed here *is* one, so the two PRG-derived cases are vacuous.
       --
       -- This replaces ~90 lines and 12 `sorry`s of `replacePRG` game hops (removed
       -- 2026-09-16, see CHANGELOG): under LM18's key-recovery function a non-atomic key
       -- is never a member of the set being hidden, so there is nothing to prove there.
      cases key
      case VarK key₀ =>
          simp [removeOneKeyProper, removeOneKey]
          exact symbolicToSemanticIndistinguishabilityHidingOneKey IsPolyTime HPolyTime enc prg Hreduction HEncIndCpa expr key₀ Hnot
            (Hseed key₀ (Finset.mem_insert_self _ _))
      case G0 ek =>
        obtain ⟨n, hn⟩ := Hkatomic
        simp at hn
      case G1 ek =>
        obtain ⟨n, hn⟩ := Hkatomic
        simp at hn

theorem symbolicToSemanticIndistinguishabilityHiding
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (enc : encryptionScheme) (prg : prgScheme)
  (Hreduction : EncReductionPolyTime IsPolyTime enc prg)
  (HreductionPrg : PrgReductionPolyTime IsPolyTime enc prg)
  (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  (HPrgSecure : prgSchemeSecure IsPolyTime prg)
  {shape : Shape} (expr : Expression shape)
  (Hatomic : hidingSideCondition expr)
  : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc prg expr)) (famDistrLift (exprToFamDistr enc prg (expressionRecovery expr))) :=
by
  rw [expressionRecovery]
  rw [← hideKeysUniv]
  rw [← Finset.coe_sdiff]
  -- allParts \ extractKeys is guaranteed to be a finite set due to our fixed point calculations earlier
  apply symbolicToSemanticIndistinguishabilityHidingInner (allParts expr \ extractKeys expr) IsPolyTime HPolyTime enc prg Hreduction HreductionPrg HEncIndCpa HPrgSecure
  -- extractKeys expr ∩ (allParts expr \ extractKeys expr) = ∅
  · apply Finset.eq_empty_of_forall_not_mem
    intro x
    simp
  -- ... and the two components of the side condition
  · exact Hatomic.1
  · exact Hatomic.2

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

-- REMOVED (2026-09-16): `iterationOrFresh`, used only by the old fixpoint step.

theorem symbolicToSemanticIndistinguishabilityAdversaryView
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
  (enc : encryptionScheme) (prg : prgScheme)
  (Hreduction : EncReductionPolyTime IsPolyTime enc prg)
  (HreductionPrg : PrgReductionPolyTime IsPolyTime enc prg)
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
  {shape : Shape}
  (expr : Expression shape)
  -- Side condition (see `hidingSideCondition`): at every stage of the fixpoint iteration,
  -- the keys the hiding step removes are atomic.
  (Hatomic : ∀ S : Finset (Expression Shape.KeyS), hidingSideCondition (hideEncrypted S expr)) :
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
      -- `Hz : keyRecovery expr z ⊆ z`, so moving from `z` to `K := keyRecovery expr z`
      -- HIDES the keys of `z \ K`.  None of those is extractable from the z-view, so this
      -- is exactly one application of the IND-CPA hiding theorem.
      --
      -- The earlier route went through
      --   `H_ext_eq : extractKeys (hide K expr) = extractKeys (hide z expr)`,
      -- which is FALSE (counterexample: `expr = Enc (VarK 0) (VarK 1)`, `z = {VarK 0, VarK 1}`
      -- gives `K = {VarK 1}`, `hide K expr = Hidden (VarK 0)`, so `∅ = {VarK 1}`), and it
      -- was only closed by the equally false `extractKeys_hideEncrypted_self`.
      -- See CHANGELOG 2026-09-16 / PRGExtension-Analysis.md §4.5.
      simp only [R, exprCompInd]
      have H_monotone : extractKeys (hideEncrypted z expr) ⊆
          extractKeys (hideEncrypted (prgClosure (keySubterms expr) z) expr) := by
        apply keyPartsMonotone
        apply hideEncryptedMonotone
        apply subset_prgClosure
      have H_extract_sub_recovery : extractKeys (hideEncrypted z expr) ⊆ keyRecovery expr z := by
        apply Finset.Subset.trans H_monotone
        exact Finset.Subset.trans Finset.subset_union_left (subset_prgClosure _ _)

      -- The keys we are about to hide.  Intersecting with `allParts` keeps the set inside
      -- the expression (so the side conditions apply) without changing the result.
      have Hdisj : extractKeys (hideEncrypted z expr) ∩
          ((z \ keyRecovery expr z) ∩ allParts (hideEncrypted z expr)) = ∅ := by
        apply Finset.eq_empty_of_forall_not_mem
        intro x hx
        rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_sdiff] at hx
        exact hx.2.1.2 (H_extract_sub_recovery hx.1)

      -- Hiding `z \ K` on top of the z-view is the same as hiding with `K` directly.
      have Hrw : hideSelectedS (↑((z \ keyRecovery expr z) ∩ allParts (hideEncrypted z expr)))
          (hideEncrypted z expr) = hideEncrypted (keyRecovery expr z) expr := by
        rw [Finset.coe_inter, hideSelectedRestrict]
        simp only [hideSelectedS]
        rw [← hideEncryptedEqS (keyRecovery expr z) expr]
        rw [← hideEncryptedEqS z expr, twoHideEncryptedS]
        congr 1
        ext x
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff,
          not_and, not_not]
        exact ⟨fun h => h.1 h.2, fun h => ⟨fun _ => h, Hz h⟩⟩

      have Zstep := symbolicToSemanticIndistinguishabilityHidingInner
        ((z \ keyRecovery expr z) ∩ allParts (hideEncrypted z expr))
        IsPolyTime HPolyTime enc prg Hreduction HreductionPrg HEncIndCpa HPrgSecure
        (hideEncrypted z expr) Hdisj
        (fun k hk => (Hatomic z).1 k (by
          rw [Finset.mem_sdiff]
          rw [Finset.mem_inter, Finset.mem_sdiff] at hk
          refine ⟨hk.2, fun hc => hk.1.2 (H_extract_sub_recovery hc)⟩))
        (fun n hn => (Hatomic z).2 n (by
          rw [Finset.mem_sdiff]
          rw [Finset.mem_inter, Finset.mem_sdiff] at hn
          refine ⟨hn.2, fun hc => hn.1.2 (H_extract_sub_recovery hc)⟩))
      rw [Hrw] at Zstep
      exact Zstep
    )
    -- Base Case Initialization (Rsup)
    (by
      simp [R, exprCompInd]
      -- at the top of the lattice nothing is hidden yet, so the two sides are equal
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
--       have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime enc prg Hreduction HEncIndCpa (hideEncrypted z expr)
--       simp [expressionRecovery] at Z
--       rw [iterationOrFresh] at Z
--       apply Z
--       assumption
--     )
--     (by
--       intro z
--       simp [R, exprCompInd]
--       have Z := symbolicToSemanticIndistinguishabilityHiding IsPolyTime HPolyTime enc prg Hreduction HEncIndCpa expr
--       simp [expressionRecovery] at Z
--       apply Z
--       )
--   apply Z

-- ===================================================================================
-- Isolating the remaining obligation.
-- ===================================================================================

/--
  Soundness of **one step** of the greatest-fixpoint iteration: going from the keys `z` to
  the keys `keyRecovery e z` (which hides more) is undetectable.

  This is the only thing the adversary-view argument needs.  The version proved above
  discharges it from `hidingSideCondition`, which holds on the PRG-free fragment but
  **not** for PRG garbled circuits (`scratch/GarbleSideCondition.lean`): at an intermediate
  stage the keys being hidden include `G0 K₅`, `G1 K₅`, whose root `K₅` has itself been
  hidden, so `Roots(Keys(view)) ⊄ 𝐊`.

  That is precisely the situation LM18's Lemma 3 covers with its *general* case, and the
  ingredients are now all present:

  * `hiddenKeys_atomic_of_atomicRoots` — the atomic case: with `Roots(Keys(v)) ⊆ 𝐊`, every
    key the step hides is atomic, hence a legitimate IND-CPA target;
  * `prgRename` (LM18 Lemma 2) — the two renaming hops, which cost PRG security;
  * `PrgRenameRel.idealize` with `replacePRG (VarK t) i j` — the renaming itself: pick a
    non-atomic root `k` of `Keys(v)`, walk down its chain to its atomic bottom `VarK t`.
    Because `k` is a root, nothing in `Keys(v)` yields it, so in particular
    `VarK t ∉ exprKeys v` — exactly the side condition `idealize` requires.  The hop
    shortens every chain through `VarK t` by one, so iterating terminates with atomic roots.

  **That bookkeeping is now done.**  `fixpointStepSound` (`SoundnessProof/FixpointStep.lean`)
  proves `FixpointStepSound` outright — the iteration terminates and commutes with
  `hideEncrypted`/`keyRecovery` — which is why `symbolicToSemanticSoundness` carries neither
  `hidingSideCondition` nor an atomicity hypothesis.  The paragraphs above describe the route
  taken, not an outstanding obligation.
-/
def FixpointStepSound (IsPolyTime : PolyFamOracleCompPred)
    (enc : encryptionScheme) (prg : prgScheme) : Prop :=
  ∀ {s : Shape} (e : Expression s) (z : Finset (Expression Shape.KeyS)),
    (keyRecovery e z ⊆ z) →
    CompIndistinguishabilityDistr IsPolyTime
      (famDistrLift (exprToFamDistr enc prg (hideEncrypted z e)))
      (famDistrLift (exprToFamDistr enc prg (hideEncrypted (keyRecovery e z) e)))

/-- The adversary-view theorem needs nothing beyond one sound fixpoint step. -/
theorem symbolicToSemanticIndistinguishabilityAdversaryViewOfStep
  (IsPolyTime : PolyFamOracleCompPred)
  (enc : encryptionScheme) (prg : prgScheme)
  (Hstep : FixpointStepSound (fun {_ _ _} => IsPolyTime) enc prg)
  {shape : Shape} (expr : Expression shape) :
  CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg expr))
    (famDistrLift (exprToFamDistr enc prg (adversaryView expr))) := by
  let R := fun (e1 e2 : Expression shape) => exprCompInd (fun {_ _ _} => IsPolyTime) enc prg e1 e2
  have Z := fixaccess
    (fun key => hideEncrypted key expr)
    (keyRecovery expr)
    (keyRecoveryMonotone expr)
    expr
    (keySubterms expr)
    (keyRecoveryContained expr)
    R
    (by
      intro e1 e2 e3 Ha Hb
      simp only [R, exprCompInd] at *
      apply indTrans (fun {I Spec Output} ↦ IsPolyTime)
      · exact Ha
      · exact Hb)
    (by
      intro z Hz
      simp only [R, exprCompInd]
      exact Hstep expr z Hz)
    (by
      simp [R, exprCompInd]
      rw [hideEncrypted_keySubterms expr]
      apply indRfl)
  exact Z
