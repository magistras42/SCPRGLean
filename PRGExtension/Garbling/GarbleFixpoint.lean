import PRGExtension.Garbling.GarbleKeys

/-!
# The garbled expression's fixpoint

`makeLabels` produces strongly independent labels, so Lemmas 5 and 6 apply at the top
level; from there we get the two facts LM18 Lemma 7's `Dup` case needs about
`adversaryKeys (Garble c x)`:

* it is **closed** under derivation — `adversaryKeys_G0_closed` (in
  `SymbolicIndistinguishability.lean`), given that the derived key occurs in the expression;
* it **reflects** derivation — `adversaryKeys_G0_seed` below: the adversary knows `G0 k`
  only if it knows `k`.
-/

namespace PRG


/-- Every key variable occurring in `k` has index `≥ n`. -/
def keyVarsAbove (n : ℕ) (k : Expression Shape.KeyS) : Prop :=
  ∀ m, Expression.VarK m ∈ keySubterms k → n ≤ m

def LabelsAbove (ctr : ℕ) : {b : WireBundle} -> labelType b -> Prop
  | WireBundle.SimpleB, l =>
      keyVarsAbove (2*ctr) l.key0 ∧ keyVarsAbove (2*ctr) l.key1
  | WireBundle.PairB _ _, (l1, l2) => LabelsAbove ctr l1 ∧ LabelsAbove ctr l2

lemma labelsAbove_mono : ∀ {b : WireBundle} {ctr ctr' : ℕ} (u : labelType b),
    ctr' ≤ ctr -> LabelsAbove ctr u -> LabelsAbove ctr' u
  | WireBundle.SimpleB, _, _, l, h, hl =>
      ⟨fun m hm => le_trans (by omega) (hl.1 m hm), fun m hm => le_trans (by omega) (hl.2 m hm)⟩
  | WireBundle.PairB _ _, _, _, (l1, l2), h, hl =>
      ⟨labelsAbove_mono l1 h hl.1, labelsAbove_mono l2 h hl.2⟩

lemma makeLabels_above : ∀ (b : WireBundle) (i : ℕ), LabelsAbove i (makeLabels b i).1
  | WireBundle.SimpleB, i => by
      constructor <;>
      · intro m hm
        simp only [makeLabels, keySubterms, Finset.mem_singleton] at hm
        injection hm with hm; omega
  | WireBundle.PairB o1 o2, i => by
      refine ⟨makeLabels_above o1 i, ?_⟩
      exact labelsAbove_mono _ (makeLabels_below o1 i).1 (makeLabels_above o2 (makeLabels o1 i).2)

lemma labelKeys_above : ∀ {bd : WireBundle} {ctr : ℕ} (u : labelType bd),
    LabelsAbove ctr u → ∀ k ∈ labelKeys u, keyVarsAbove (2*ctr) k
  | WireBundle.SimpleB, ctr, l, h, k, hk => by
      simp only [labelKeys, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl; exacts [h.1, h.2]
  | WireBundle.PairB o1 o2, ctr, (l1, l2), h, k, hk => by
      simp only [labelKeys, Finset.mem_union] at hk
      rcases hk with hk | hk
      · exact labelKeys_above l1 h.1 k hk
      · exact labelKeys_above l2 h.2 k hk

/-- `Label(s)` produces a strongly independent label expression. -/
theorem makeLabels_stronglyIndependent (b : WireBundle) (i : ℕ) :
    StronglyIndependent (makeLabels b i).1 := by
  constructor
  · -- all keys are atomic variables, and no atomic key yields another
    intro x _ y hy
    have : isAtomicKey y = true := makeLabels_atomic b i y hy
    cases y with
    | VarK n => exact sy_to_varK _ _
    | G0 _ => simp [isAtomicKey] at this
    | G1 _ => simp [isAtomicKey] at this
  · -- distinctness
    induction b generalizing i with
    | SimpleB =>
        simp only [makeLabels, DistinctLabels]
        intro hc; injection hc with hc; omega
    | PairB o1 o2 ih1 ih2 =>
        refine ⟨ih1 i, ih2 _, ?_⟩
        refine inter_empty_of (fun x hx1 hx2 => ?_)
        have h1 := labelKeys_below (makeLabels o1 i).1 (makeLabels_below o1 i).2 x hx1
        have h2 := labelKeys_above (makeLabels o2 (makeLabels o1 i).2).1
          (makeLabels_above o2 (makeLabels o1 i).2) x hx2
        -- x is atomic, so its own variable index is both < and ≥ the middle counter
        have hat : isAtomicKey x = true := makeLabels_atomic o1 i x hx1
        cases x with
        | VarK n =>
            have ha := h1 n (by simp [keySubterms])
            have hb := h2 n (by simp [keySubterms])
            omega
        | G0 _ => simp [isAtomicKey] at hat
        | G1 _ => simp [isAtomicKey] at hat

lemma exprKeys_bit : ∀ e : Expression Shape.BitS, exprKeys e = ∅
  | Expression.BitE _ => rfl

lemma exprKeys_maskedLabelToExpr : ∀ {b : WireBundle} (m : maskedLabelType b),
    exprKeys (maskedLabelToExpr m) = ∅
  | WireBundle.SimpleB, m => exprKeys_bit m
  | WireBundle.PairB o1 o2, (m1, m2) => by
      simp only [maskedLabelToExpr, exprKeys]
      rw [exprKeys_maskedLabelToExpr m1, exprKeys_maskedLabelToExpr m2]; simp

lemma exprKeys_gEnc : ∀ {b : WireBundle} (u : labelType b) (x : bundleBool b),
    exprKeys (encodedLabelToExpr (gEnc u x)) ⊆ labelKeys u
  | WireBundle.SimpleB, l, x => by
      cases x <;> simp [gEnc, encodedLabelToExpr, exprKeys, exprKeys_key, labelKeys]
  | WireBundle.PairB o1 o2, (l1, l2), (x1, x2) => by
      simp only [gEnc, encodedLabelToExpr, exprKeys, labelKeys]
      exact Finset.union_subset_union (exprKeys_gEnc l1 x1) (exprKeys_gEnc l2 x2)

/-- A non-atomic key of the whole garbled expression is an *encryption* key of the tables. -/
lemma nonatomic_mem_encKeys {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    {k : Expression Shape.KeyS} (hk : k ∈ exprKeys (Garble c x)) (hna : isAtomicKey k = false) :
    k ∈ encKeys (gb c (makeLabels s 0).1 (makeLabels s 0).2).1 := by
  simp only [Garble, exprKeys, Finset.mem_union] at hk
  rcases hk with h | h | h
  · rw [exprKeys_eq_extractKeys_union_encKeys, Finset.mem_union] at h
    rcases h with h | h
    · rw [lemma4 c _ _ k h] at hna; exact Bool.noConfusion hna
    · exact h
  · rw [makeLabels_atomic s 0 k (exprKeys_gEnc _ x h)] at hna; exact Bool.noConfusion hna
  · exact absurd h (by rw [exprKeys_maskedLabelToExpr]; simp)

/-- **LM18 Lemma 6(1), for the whole garbled expression.** -/
theorem lemma6_garble_cond1 {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    {k : Expression Shape.KeyS} (hk : k ∈ exprKeys (Garble c x)) (hna : isAtomicKey k = false) :
    ∀ k' ∈ exprKeys (Garble c x), strictYields k k' = false := by
  intro k' hk'
  have henc := nonatomic_mem_encKeys c x hk hna
  have h6 := (lemma6 c (makeLabels s 0).1 (makeLabels s 0).2
    (makeLabels_stronglyIndependent s 0) (makeLabels_below s 0).2 k henc).1
  simp only [Garble, exprKeys, Finset.mem_union] at hk'
  rcases hk' with h | h | h
  · exact h6 k' h
  · have : isAtomicKey k' = true := makeLabels_atomic s 0 k' (exprKeys_gEnc _ x h)
    cases k' with
    | VarK n => exact sy_to_varK _ _
    | G0 _ => simp [isAtomicKey] at this
    | G1 _ => simp [isAtomicKey] at this
  · exact absurd h (by rw [exprKeys_maskedLabelToExpr]; simp)

/-- **The key fact LM18 Lemma 7's `Dup` case needs**: the adversary knows a derived key only
    if it knows the seed.  Contrapositive: `k ∉ S ⟹ G0 k ∉ S`. -/
theorem adversaryKeys_G0_seed {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    {k : Expression Shape.KeyS} (h : Expression.G0 k ∈ adversaryKeys (Garble c x)) :
    k ∈ adversaryKeys (Garble c x) := by
  rcases adversaryKeys_reflects_G0 (Garble c x) h with hb | hc
  · exfalso
    rw [Finset.mem_union] at hb
    rcases hb with hb | hb
    · have := lemma4_adversaryView c x _ hb; simp [isAtomicKey] at this
    · obtain ⟨hmem, k'', hk'', hy⟩ := mem_ancestorKeys.mp hb
      have hsub : exprKeys (adversaryView (Garble c x)) ⊆ exprKeys (Garble c x) :=
        exprKeysMonotone _ _ (hideEncryptedSmallerValue _ _)
      rw [lemma6_garble_cond1 c x (hsub hmem) (by simp [isAtomicKey]) k'' (hsub hk'')] at hy
      exact Bool.noConfusion hy
  · exact hc

theorem adversaryKeys_G1_seed {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    {k : Expression Shape.KeyS} (h : Expression.G1 k ∈ adversaryKeys (Garble c x)) :
    k ∈ adversaryKeys (Garble c x) := by
  rcases adversaryKeys_reflects_G1 (Garble c x) h with hb | hc
  · exfalso
    rw [Finset.mem_union] at hb
    rcases hb with hb | hb
    · have := lemma4_adversaryView c x _ hb; simp [isAtomicKey] at this
    · obtain ⟨hmem, k'', hk'', hy⟩ := mem_ancestorKeys.mp hb
      have hsub : exprKeys (adversaryView (Garble c x)) ⊆ exprKeys (Garble c x) :=
        exprKeysMonotone _ _ (hideEncryptedSmallerValue _ _)
      rw [lemma6_garble_cond1 c x (hsub hmem) (by simp [isAtomicKey]) k'' (hsub hk'')] at hy
      exact Bool.noConfusion hy
  · exact hc

end PRG
