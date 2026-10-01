import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.AdversaryView
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKeyGen

/-!
# The fixpoint step is sound

`FixpointStepSound` was the last obligation of the expression layer.  The version proved in
`AdversaryView.lean` needed `hidingSideCondition` — "every key the step hides is atomic" —
which holds on the PRG-free fragment but **not** for PRG garbled circuits: at an
intermediate stage of the fixpoint the keys being hidden can include `G0 K₅` whose root
`K₅` has itself been hidden away (`scratch/probes/GarbleSideCondition.lean`).

This file removes that hypothesis, following LM18 Lemma 3's general case.  `hidingGen` is
the set-level hiding theorem with the atomicity requirement replaced by two conditions read
off `Keys(expr)`, and `hideOneKeyGen` discharges the single-key step for a non-atomic key by
a pseudorandom key renaming.  `fixpointStepSound` then derives those two conditions from the
fixpoint itself: a key the step hides has no strict ancestor and no strict descendant in the
view, because either would put it in the recovery set.
-/

open PRG
namespace PRG

def hidingGenMotive (z : Finset (Expression Shape.KeyS)) : Prop :=
  ∀ (IsPolyTime : PolyFamOracleCompPred)
    (_HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
    (enc : encryptionScheme) (prg : prgScheme)
    (_Hreduction : EncReductionPolyTime IsPolyTime enc prg)
    (_HreductionPrg : PrgReductionPolyTime IsPolyTime enc prg)
    (_HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
    (_HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
    {shape : Shape} (expr : Expression shape)
    (_HexprZ : extractKeys expr ∩ z = ∅)
    (_Hroot : ∀ k ∈ z, ∀ k' ∈ exprKeys expr, strictYields k' k = false)
    (_Hdesc : ∀ k ∈ z, ∀ k' ∈ exprKeys expr, strictYields k k' = false),
    CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (exprToFamDistr enc prg expr))
      (famDistrLift (exprToFamDistr enc prg (hideSelectedS z expr)))

/--
  **Hiding a whole set of keys, with no atomicity restriction.**  The set version of
  `hideOneKeyGen`; it replaces `symbolicToSemanticIndistinguishabilityHidingInner`'s
  "every key removed is atomic" hypothesis by the two `Keys(expr)` conditions LM18 states.
-/
theorem hidingGen (z : Finset (Expression Shape.KeyS)) : hidingGenMotive z := by
  induction z using Finset.induction_on'
  case empty =>
    intro IsPolyTime _ _ _ enc prg _ _ shape expr _ _ _
    simp only [Finset.coe_empty, emptyHide]
    apply indRfl
  case insert key keySet Hkey Hkey2 HkeyFresh Hind =>
    intro IsPolyTime HPolyTime enc prg Hreduction HreductionPrg HEncIndCpa HPrgSecure
      shape expr Hexpr Hroot Hdesc
    have Hnot : key ∉ extractKeys expr := by
      intro Hcontr
      have L : key ∈ extractKeys expr ∩ insert key keySet :=
        Finset.mem_inter.mpr ⟨Hcontr, Finset.mem_insert_self key keySet⟩
      rw [Hexpr] at L; simp at L
    -- hiding only shrinks `Keys`, so both conditions survive `removeOneKeyProper`
    have Hsub : ∀ (H' : key ∉ extractKeys expr),
        exprKeys (removeOneKeyProper key expr H') ⊆ exprKeys expr :=
      fun H' => exprKeysMonotone _ _ (hideKeys2SmallerValue _ _)
    rw [<-hideSelectedFreshKeys]
    case _H => rw [Finset.inter_comm]; assumption
    rw [expressionRecoveryNegEq _ key, expressionRecoveryNegTwoStep, hideSelectedFreshKeys]
    case Hkey => exact Finset.mem_insert_self key keySet
    apply indTransRev
    · have Heq : insert key keySet \ {key} = keySet := by
        apply Finset.ext_iff.mpr
        intro a
        rw [Finset.mem_sdiff, Finset.mem_insert]
        simp
        if Ha : a = key then subst a; tauto else tauto
      rw [Heq]
      apply indSym
      refine Hind IsPolyTime HPolyTime enc prg Hreduction HreductionPrg HEncIndCpa HPrgSecure
        _ ?_ ?_ ?_
      · simp only [removeOneKeyProper] at *
        rw [<-Heq, Finset.inter_comm]
        apply noFreshKeysAfterRemoveOneKeyProper <;> try assumption
        rw [Finset.inter_comm]; assumption
      · exact fun k hk k' hk' =>
          Hroot k (Finset.mem_insert_of_mem hk) k' (Hsub Hnot hk')
      · exact fun k hk k' hk' =>
          Hdesc k (Finset.mem_insert_of_mem hk) k' (Hsub Hnot hk')
    · simp only [removeOneKeyProper, removeOneKey] at *
      exact hideOneKeyGen IsPolyTime HPolyTime enc prg Hreduction HreductionPrg HEncIndCpa
        HPrgSecure (keySize key) expr key (le_refl _) Hnot
        (Hroot key (Finset.mem_insert_self key keySet))
        (Hdesc key (Finset.mem_insert_self key keySet))

lemma encKeys_key : ∀ k : Expression Shape.KeyS, encKeys k = ∅
  | Expression.VarK _ => rfl
  | Expression.G0 _ => rfl
  | Expression.G1 _ => rfl

/-- `hideEncryptedS` only tests keys that are actually used for encryption. -/
lemma hideEncryptedEncAux {s : Shape} (keys Z : Set (Expression Shape.KeyS)) (p : Expression s) :
    (↑(encKeys p) ⊆ Z) → hideEncryptedS keys p = hideEncryptedS (keys ∩ Z) p := by
  induction p <;> simp [hideEncryptedS, encKeys] <;> try tauto
  case G0 e ih => exact ih (by rw [encKeys_key]; simp)
  case G1 e ih => exact ih (by rw [encKeys_key]; simp)
  case Enc e1 e2 ih1 ih2 =>
    intro hins
    rw [Set.insert_subset_iff] at hins
    obtain ⟨h₁, h₂⟩ := hins
    split
    next heq =>
      have h_intersect : e1 ∈ keys ∩ Z := ⟨heq, h₁⟩
      simp [h_intersect]
      rw [ih1 (by rw [encKeys_key]; simp), ih2 h₂]
      exact ⟨rfl, rfl⟩
    next hn =>
      have h_intersect : ¬(e1 ∈ keys ∩ Z) := fun h => hn h.1
      simp [h_intersect]
      rw [ih1 (by rw [encKeys_key]; simp)]

lemma hideSelectedRestrictEnc {s : Shape} (S : Set (Expression Shape.KeyS)) (p : Expression s) :
    hideSelectedS (S ∩ ↑(encKeys p)) p = hideSelectedS S p := by
  simp only [hideSelectedS]
  rw [hideEncryptedEncAux (S ∩ ↑(encKeys p))ᶜ ↑(encKeys p) p (Set.Subset.refl _),
    hideEncryptedEncAux Sᶜ ↑(encKeys p) p (Set.Subset.refl _)]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_inter_iff, not_and]
  tauto

/--
  **`FixpointStepSound` holds.**  The last obligation of the expression layer.

  The two conditions `hidingGen` needs are read straight off the fixpoint.  The keys the
  step hides are `W = (z \ 𝓕(z)) ∩ encKeys(v)` — restricting to *encryption* keys is what
  makes them available, and changes nothing (`hideSelectedRestrictEnc`).  For `k ∈ W`:

  * no strict **descendant** of `k` occurs in the view, because if one did then `k` would be
    collected by the ancestor clause of LM18 Definition 3, hence recovered, hence not in
    `z \ 𝓕(z)`;
  * no strict **ancestor** `k'` of `k` occurs in the view, because such a `k'` is itself in
    the recovery base — directly if it is a part, and via the ancestor clause if it is an
    encryption key — and then `k` lies in its PRG closure, so again `k` is recovered.
-/
theorem fixpointStepSound
    (IsPolyTime : PolyFamOracleCompPred)
    (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
    (enc : encryptionScheme) (prg : prgScheme)
    (Hreduction : EncReductionPolyTime IsPolyTime enc prg)
    (HreductionPrg : PrgReductionPolyTime IsPolyTime enc prg)
    (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
    (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg) :
    FixpointStepSound (fun {_ _ _} => IsPolyTime) enc prg := by
  intro s e z Hz
  set S := keyRecovery e z with hS
  set v := hideEncrypted z e with hv
  set view := hideEncrypted (prgClosure (keySubterms e) z) e with hview
  set W := (z \ S) ∩ encKeys v with hW
  have hEK : exprKeys v ⊆ exprKeys view :=
    exprKeysMonotone _ _ (hideEncryptedMonotone z (prgClosure (keySubterms e) z) e (subset_prgClosure (keySubterms e) z))
  have hmono : extractKeys v ⊆ extractKeys view :=
    keyPartsMonotone _ _ (hideEncryptedMonotone z (prgClosure (keySubterms e) z) e (subset_prgClosure (keySubterms e) z))
  have H_extract_sub_recovery : extractKeys v ⊆ S := by
    intro x hx
    rw [hS]
    simp only [keyRecovery]
    exact subset_prgClosure _ _ (Finset.mem_union_left _ (hmono hx))
  have hmemE : ∀ k ∈ encKeys v, k ∈ exprKeys v := by
    intro k hk
    rw [exprKeys_eq_extractKeys_union_encKeys]; exact Finset.mem_union_right _ hk
  have hvsub : keySubterms v ⊆ keySubterms e := by
    rw [hv]; exact keySubtermsMonotone _ _ (hideEncryptedSmallerValue z e)
  have hUsub : ∀ k ∈ encKeys v, keySubterms k ⊆ keySubterms e := fun k hk =>
    Finset.Subset.trans
      (keySubterms_subset_of_mem_exprKeys v k (hmemE k hk)) hvsub
  have Hdisj : extractKeys v ∩ W = ∅ := by
    apply Finset.eq_empty_of_forall_not_mem
    intro x hx
    rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_sdiff] at hx
    exact hx.2.1.2 (H_extract_sub_recovery hx.1)
  have Hdesc : ∀ k ∈ W, ∀ k' ∈ exprKeys v, strictYields k k' = false := by
    intro k hk k' hk'
    rw [Finset.mem_inter, Finset.mem_sdiff] at hk
    cases hy : strictYields k k'
    · rfl
    · exfalso
      refine hk.1.2 ?_
      rw [hS]; simp only [keyRecovery]
      refine subset_prgClosure _ _ (Finset.mem_union_right _ ?_)
      exact mem_ancestorKeys.mpr ⟨hEK (hmemE k hk.2), k', hEK hk', hy⟩
  have Hroot : ∀ k ∈ W, ∀ k' ∈ exprKeys v, strictYields k' k = false := by
    intro k hk k' hk'
    rw [Finset.mem_inter, Finset.mem_sdiff] at hk
    cases hy : strictYields k' k
    · rfl
    · exfalso
      refine hk.1.2 ?_
      have hk'view : k' ∈ exprKeys view := hEK hk'
      have hbase : k' ∈ extractKeys view ∪ ancestorKeys (exprKeys view) := by
        rw [exprKeys_eq_extractKeys_union_encKeys, Finset.mem_union] at hk'view
        rcases hk'view with h | h
        · exact Finset.mem_union_left _ h
        · refine Finset.mem_union_right _ (mem_ancestorKeys.mpr ⟨?_, k, hEK (hmemE k hk.2), hy⟩)
          rw [exprKeys_eq_extractKeys_union_encKeys]; exact Finset.mem_union_right _ h
      rw [hS]; simp only [keyRecovery]
      exact mem_prgClosure_of_strictYields hy hbase (hUsub k hk.2)
  have Hrw : hideSelectedS (↑W) v = hideEncrypted S e := by
    rw [hW, Finset.coe_inter, hideSelectedRestrictEnc]
    simp only [hideSelectedS, hv]
    rw [← hideEncryptedEqS S e, ← hideEncryptedEqS z e, twoHideEncryptedS]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff,
      not_and, not_not]
    exact ⟨fun h => h.1 h.2, fun h => ⟨fun _ => h, Hz h⟩⟩
  have Zstep := hidingGen W IsPolyTime HPolyTime enc prg Hreduction HreductionPrg
    HEncIndCpa HPrgSecure v Hdisj Hroot Hdesc
  rw [Hrw] at Zstep
  exact Zstep

end PRG
