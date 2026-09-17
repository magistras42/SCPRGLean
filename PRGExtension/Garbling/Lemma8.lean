import PRGExtension.Garbling.Lemma7

/-!
# LM18 Lemma 8

The simulator's counterpart of Lemma 7.  Two things make it shorter than it looks:

* `Sim` threads labels and counters exactly as `Gb` does (`sim_snd_eq_gb_snd`), so the same
  `GbStage` relation applies and the proof can be stated over `gb`'s output labels.
* `Sim` uses the *same encryption keys* as `Gb` and a subset of its key set
  (`encKeys_sim_eq_gb`, `exprKeys_sim_subset_gb`), so LM18 Lemma 6 transports to it for free
  — which is what `atomic_recovered_simulate` needs.

The `NAnd` case is easier than Lemma 7's: every row of a simulated table carries the same
payload `K_h⁰`, so whichever row decrypts, the recovered key is `K_{2n}` and `K_{2n+1}` is
never recovered at all.
-/

namespace PRG

-- ==== the `sim` analogues of the `gb` machinery in ViewKeys.lean ====

lemma sim_snd_fst {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ) :
    (sim c u ctr).2.1 = (gb c u ctr).2.1 := congrArg Prod.fst (sim_snd_eq_gb_snd c u ctr)

lemma sim_snd_snd {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ) :
    (sim c u ctr).2.2 = (gb c u ctr).2.2 := congrArg Prod.snd (sim_snd_eq_gb_snd c u ctr)

theorem extractKeys_view_range_sim (S : Finset (Expression Shape.KeyS)) :
    ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
      ∀ K ∈ extractKeys (hideEncrypted S (sim c u ctr).1),
        ∃ j, 2 * ctr ≤ j ∧ j < 2 * (gb c u ctr).2.2 ∧ K = Expression.VarK j := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨i1, i2⟩ ctr K hK; simp [sim, hideEncrypted, extractKeys] at hK
  | AssocC a b d => rintro ⟨i1, i2, i3⟩ ctr K hK; simp [sim, hideEncrypted, extractKeys] at hK
  | UnAssocC a b d => rintro ⟨⟨i1, i2⟩, i3⟩ ctr K hK; simp [sim, hideEncrypted, extractKeys] at hK
  | DupC => intro l ctr K hK; simp [sim, hideEncrypted, extractKeys] at hK
  | NandC =>
      rintro ⟨li, lj⟩ ctr K hK
      have hfin : (gb Circuit.NandC (li, lj) ctr).2.2 = ctr + 1 := rfl
      rw [hfin]
      have key : ∀ (P : Prop) [Decidable P] (m : ℕ),
          K ∈ (if P then extractKeys (Expression.VarK m) else (∅ : Finset (Expression Shape.KeyS))) →
          K = Expression.VarK m := by
        intro P _ m hm
        split_ifs at hm
        · simpa [extractKeys] using hm
        · simp at hm
      simp only [sim, hideEncrypted, extractKeys, Finset.mem_union,
        extractKeys_view_gbEntry] at hK
      rcases hK with ((h | h) | (h | h)) <;>
        exact ⟨2*ctr, by omega, by omega, key _ _ h⟩
  | FirstC c1 wb ih =>
      rintro ⟨b1, b2⟩ ctr K hK
      simp only [sim] at hK
      simp only [gb]
      exact ih b1 ctr K hK
  | ComposeC c1 c2 ih1 ih2 =>
      intro b ctr K hK
      have hfin : (gb (Circuit.ComposeC c1 c2) b ctr).2.2
          = (gb c2 (gb c1 b ctr).2.1 (gb c1 b ctr).2.2).2.2 := rfl
      rw [hfin]
      simp only [sim, hideEncrypted, extractKeys, Finset.mem_union, sim_snd_fst,
        sim_snd_snd] at hK
      have hm1 := gb_ctr_mono c1 b ctr
      have hm2 := gb_ctr_mono c2 (gb c1 b ctr).2.1 (gb c1 b ctr).2.2
      rcases hK with hK | hK
      · obtain ⟨j, h1, h2, h3⟩ := ih1 b ctr K hK; exact ⟨j, h1, by omega, h3⟩
      · obtain ⟨j, h1, h2, h3⟩ := ih2 (gb c1 b ctr).2.1 (gb c1 b ctr).2.2 K hK
        exact ⟨j, by omega, h2, h3⟩

theorem GbStage.view_extract_iso_sim (S : Finset (Expression Shape.KeyS))
    {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') {j : ℕ}
    (hlo : 2 * ctr' ≤ j) (hhi : j < 2 * (gb c' u' ctr').2.2)
    (hK : Expression.VarK j ∈ extractKeys (hideEncrypted S (sim c u ctr).1)) :
    Expression.VarK j ∈ extractKeys (hideEncrypted S (sim c' u' ctr').1) := by
  induction h with
  | refl => exact hK
  | @composeL a b d s' t' c1 c2 u ctr c'' u'' ctr'' hst ih =>
      simp only [sim, hideEncrypted, extractKeys, Finset.mem_union, sim_snd_fst,
        sim_snd_snd] at hK
      refine ih hlo hhi ?_
      rcases hK with hK | hK
      · exact hK
      · exfalso
        obtain ⟨j', hj1, hj2, hj3⟩ := extractKeys_view_range_sim S c2 _ _ _ hK
        have hfe : (gb c'' u'' ctr'').2.2 ≤ (gb c1 u ctr).2.2 := hst.final_le
        rw [Expression.VarK.injEq] at hj3
        subst hj3
        have hstep : 2 * (gb c'' u'' ctr'').2.2 ≤ 2 * (gb c1 u ctr).2.2 := by omega
        exact absurd (lt_of_lt_of_le hhi hstep) (not_lt.mpr hj1)
  | @composeR a b d s' t' c1 c2 u ctr c'' u'' ctr'' hst ih =>
      simp only [sim, hideEncrypted, extractKeys, Finset.mem_union, sim_snd_fst,
        sim_snd_snd] at hK
      refine ih hlo hhi ?_
      rcases hK with hK | hK
      · exfalso
        obtain ⟨j', hj1, hj2, hj3⟩ := extractKeys_view_range_sim S c1 u ctr _ hK
        have hcl : (gb c1 u ctr).2.2 ≤ ctr'' := hst.ctr_le
        rw [Expression.VarK.injEq] at hj3
        subst hj3
        have hstep : 2 * (gb c1 u ctr).2.2 ≤ 2 * ctr'' := by omega
        exact absurd (lt_of_lt_of_le hj2 hstep) (not_lt.mpr hlo)
      · exact hK
  | @first v1 v2 wb s' t' c u1 u2 ctr c'' u'' ctr'' _ ih =>
      simp only [sim] at hK
      exact ih hlo hhi hK

lemma GbStage.view_extract_mono_sim (S : Finset (Expression Shape.KeyS))
    {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') :
    extractKeys (hideEncrypted S (sim c' u' ctr').1)
      ⊆ extractKeys (hideEncrypted S (sim c u ctr).1) := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @composeL a b d s' t' c1 c2 u ctr c'' u'' ctr'' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      simp only [sim, hideEncrypted, extractKeys, Finset.mem_union, sim_snd_fst, sim_snd_snd]
      exact Or.inl hy
  | @composeR a b d s' t' c1 c2 u ctr c'' u'' ctr'' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      simp only [sim, hideEncrypted, extractKeys, Finset.mem_union, sim_snd_fst, sim_snd_snd]
      exact Or.inr hy
  | @first v1 v2 wb s' t' c u1 u2 ctr c'' u'' ctr'' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy; simp only [sim]; exact hy

lemma GbStage.keySubterms_subset_sim {s t s' t' : WireBundle} {c : Circuit s t}
    {u : labelType s} {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') :
    keySubterms (sim c' u' ctr').1 ⊆ keySubterms (sim c u ctr).1 := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @composeL a b d s' t' c1 c2 u ctr c'' u'' ctr'' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      simp only [sim, keySubterms, Finset.mem_union, sim_snd_fst, sim_snd_snd]
      exact Or.inl hy
  | @composeR a b d s' t' c1 c2 u ctr c'' u'' ctr'' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      simp only [sim, keySubterms, Finset.mem_union, sim_snd_fst, sim_snd_snd]
      exact Or.inr hy
  | @first v1 v2 wb s' t' c u1 u2 ctr c'' u'' ctr'' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy; simp only [sim]; exact hy

/-- `Sim` uses the same encryption keys as `Gb` — only the payloads differ. -/
theorem encKeys_sim_eq_gb : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    encKeys (sim c u ctr).1 = encKeys (gb c u ctr).1 := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨i1, i2⟩ ctr; rfl
  | AssocC a b d => rintro ⟨i1, i2, i3⟩ ctr; rfl
  | UnAssocC a b d => rintro ⟨⟨i1, i2⟩, i3⟩ ctr; rfl
  | DupC => intro l ctr; rfl
  | NandC => rintro ⟨li, lj⟩ ctr; simp [sim, gb, gbEntry, encKeys]
  | FirstC c1 wb ih => rintro ⟨b1, b2⟩ ctr; simp only [sim, gb]; exact ih b1 ctr
  | ComposeC c1 c2 ih1 ih2 =>
      intro b ctr
      simp only [sim, gb, encKeys, sim_snd_fst, sim_snd_snd]
      rw [ih1 b ctr, ih2 _ _]

/-- `Sim`'s payload is always `K_h⁰`, one of the two keys `Gb` uses, so its key set is
    contained in `Gb`'s.  This is what transports LM18 Lemma 6 to the simulator. -/
theorem exprKeys_sim_subset_gb : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s)
    (ctr : ℕ), exprKeys (sim c u ctr).1 ⊆ exprKeys (gb c u ctr).1 := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨i1, i2⟩ ctr; exact Finset.Subset.refl _
  | AssocC a b d => rintro ⟨i1, i2, i3⟩ ctr; exact Finset.Subset.refl _
  | UnAssocC a b d => rintro ⟨⟨i1, i2⟩, i3⟩ ctr; exact Finset.Subset.refl _
  | DupC => intro l ctr; exact Finset.Subset.refl _
  | NandC =>
      rintro ⟨li, lj⟩ ctr
      intro y hy
      simp only [sim, gb, gbEntry, exprKeys, exprKeys_key, Finset.mem_union,
        Finset.mem_singleton] at hy ⊢
      tauto
  | FirstC c1 wb ih => rintro ⟨b1, b2⟩ ctr; simp only [sim, gb]; exact ih b1 ctr
  | ComposeC c1 c2 ih1 ih2 =>
      intro b ctr
      intro y hy
      simp only [sim, gb, exprKeys, Finset.mem_union, sim_snd_fst, sim_snd_snd] at hy ⊢
      exact hy.imp (fun h => ih1 b ctr h)
        (fun h => ih2 (gb c1 b ctr).2.1 (gb c1 b ctr).2.2 h)

/-- **LM18 Lemma 6(1) for the simulator.** -/
theorem lemma6_sim_cond1 {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ)
    (hSI : StronglyIndependent u) (hb : LabelsBelow ctr u)
    {k : Expression Shape.KeyS} (hk : k ∈ encKeys (sim c u ctr).1) :
    ∀ k' ∈ exprKeys (sim c u ctr).1, strictYields k k' = false := by
  rw [encKeys_sim_eq_gb] at hk
  intro k' hk'
  exact (lemma6 c u ctr hSI hb k hk).1 k' (exprKeys_sim_subset_gb c u ctr hk')

lemma encKeys_sEnc : ∀ {b : WireBundle} (u : labelType b),
    encKeys (encodedLabelToExpr (sEnc u)) = ∅
  | WireBundle.SimpleB, l => by simp [sEnc, encodedLabelToExpr, encKeys]
  | WireBundle.PairB o1 o2, (l1, l2) => by
      simp [sEnc, encodedLabelToExpr, encKeys, encKeys_sEnc l1, encKeys_sEnc l2]

lemma exprKeys_sEnc : ∀ {b : WireBundle} (u : labelType b),
    exprKeys (encodedLabelToExpr (sEnc u)) ⊆ labelKeys u
  | WireBundle.SimpleB, l => by
      simp [sEnc, encodedLabelToExpr, exprKeys, exprKeys_key, labelKeys]
  | WireBundle.PairB o1 o2, (l1, l2) => by
      simp only [sEnc, encodedLabelToExpr, exprKeys, labelKeys]
      exact Finset.union_subset_union (exprKeys_sEnc l1) (exprKeys_sEnc l2)

lemma exprKeys_sMask : ∀ {b : WireBundle} (m : labelType b) (y : bundleBool b),
    exprKeys (maskedLabelToExpr (sMask m y)) = ∅
  | WireBundle.SimpleB, l, y => by cases y <;> simp [sMask, maskedLabelToExpr, exprKeys]
  | WireBundle.PairB o1 o2, (l1, l2), (y1, y2) => by
      simp [sMask, maskedLabelToExpr, exprKeys, exprKeys_sMask l1 y1, exprKeys_sMask l2 y2]

lemma encKeys_sMask : ∀ {b : WireBundle} (m : labelType b) (y : bundleBool b),
    encKeys (maskedLabelToExpr (sMask m y)) = ∅
  | WireBundle.SimpleB, l, y => by cases y <;> simp [sMask, maskedLabelToExpr, encKeys]
  | WireBundle.PairB o1 o2, (l1, l2), (y1, y2) => by
      simp [sMask, maskedLabelToExpr, encKeys, encKeys_sMask l1 y1, encKeys_sMask l2 y2]

/-- **LM18 Lemma 6(1) for the whole simulated expression.** -/
theorem lemma6_simulate_enc {s t : WireBundle} (c : Circuit s t) (y : bundleBool t)
    {k : Expression Shape.KeyS} (hk : k ∈ encKeys (Simulate c y)) :
    ∀ k' ∈ exprKeys (Simulate c y), strictYields k k' = false := by
  intro k' hk'
  have henc : k ∈ encKeys (sim c (makeLabels s 0).1 (makeLabels s 0).2).1 := by
    simp only [Simulate, encKeys, Finset.mem_union] at hk
    rcases hk with h | h | h
    · exact h
    · exact absurd h (by rw [encKeys_sEnc]; simp)
    · exact absurd h (by rw [encKeys_sMask]; simp)
  have h6 := lemma6_sim_cond1 c (makeLabels s 0).1 (makeLabels s 0).2
    (makeLabels_stronglyIndependent s 0) (makeLabels_below s 0).2 henc
  simp only [Simulate, exprKeys, Finset.mem_union] at hk'
  rcases hk' with h | h | h
  · exact h6 k' h
  · have : isAtomicKey k' = true := makeLabels_atomic s 0 k' (exprKeys_sEnc _ h)
    cases k' with
    | VarK n => exact sy_to_varK _ _
    | G0 _ => simp [isAtomicKey] at this
    | G1 _ => simp [isAtomicKey] at this
  · exact absurd h (by rw [exprKeys_sMask]; simp)

/-- **An atomic key is recovered from the simulated expression only by decryption.** -/
theorem atomic_recovered_simulate {s t : WireBundle} (c : Circuit s t) (y : bundleBool t)
    {k : Expression Shape.KeyS} (hat : isAtomicKey k = true)
    (h : k ∈ adversaryKeys (Simulate c y)) :
    k ∈ extractKeys (adversaryView (Simulate c y)) := by
  set f := Simulate c y with hf
  have hfix : keyRecovery f (adversaryKeys f) = adversaryKeys f := adversaryKeysIsFix f
  have h' : k ∈ keyRecovery f (adversaryKeys f) := by rw [hfix]; exact h
  simp only [keyRecovery] at h'
  rw [adversaryKeys_prgClosed] at h'
  have hview : hideEncrypted (adversaryKeys f) f = adversaryView f := rfl
  rw [hview] at h'
  have h'' := atomic_mem_prgClosure hat h'
  rw [Finset.mem_union] at h''
  rcases h'' with h'' | h''
  · exact h''
  · obtain ⟨hmem, k', hk', hy⟩ := mem_ancestorKeys.mp h''
    rw [exprKeys_eq_extractKeys_union_encKeys, Finset.mem_union] at hmem
    rcases hmem with hmem | hmem
    · exact hmem
    · exfalso
      have hke : k ∈ encKeys f := encKeys_hideEncrypted _ _ hmem
      have hsub : exprKeys (adversaryView f) ⊆ exprKeys f :=
        exprKeysMonotone _ _ (hideEncryptedSmallerValue _ _)
      rw [lemma6_simulate_enc c y hke k' (hsub hk')] at hy
      exact Bool.noConfusion hy

/-- The simulator's counterpart of `adversaryKeys_G0_seed`. -/
theorem adversaryKeys_G0_seed_sim {s t : WireBundle} (c : Circuit s t) (y : bundleBool t)
    {k : Expression Shape.KeyS} (h : Expression.G0 k ∈ adversaryKeys (Simulate c y)) :
    k ∈ adversaryKeys (Simulate c y) := by
  rcases adversaryKeys_reflects_G0 (Simulate c y) h with hb | hc
  · exfalso
    rw [Finset.mem_union] at hb
    rcases hb with hb | hb
    · have := lemma4_simulate_adversaryView c y _ hb; simp [isAtomicKey] at this
    · obtain ⟨hmem, k'', hk'', hy⟩ := mem_ancestorKeys.mp hb
      have hsub : exprKeys (adversaryView (Simulate c y)) ⊆ exprKeys (Simulate c y) :=
        exprKeysMonotone _ _ (hideEncryptedSmallerValue _ _)
      have hke : Expression.G0 k ∈ encKeys (Simulate c y) := by
        rw [exprKeys_eq_extractKeys_union_encKeys, Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact absurd (lemma4_simulate_adversaryView c y _ hmem) (by simp [isAtomicKey])
        · exact encKeys_hideEncrypted _ _ hmem
      rw [lemma6_simulate_enc c y hke k'' (hsub hk'')] at hy
      exact Bool.noConfusion hy
  · exact hc

theorem adversaryKeys_G1_seed_sim {s t : WireBundle} (c : Circuit s t) (y : bundleBool t)
    {k : Expression Shape.KeyS} (h : Expression.G1 k ∈ adversaryKeys (Simulate c y)) :
    k ∈ adversaryKeys (Simulate c y) := by
  rcases adversaryKeys_reflects_G1 (Simulate c y) h with hb | hc
  · exfalso
    rw [Finset.mem_union] at hb
    rcases hb with hb | hb
    · have := lemma4_simulate_adversaryView c y _ hb; simp [isAtomicKey] at this
    · obtain ⟨hmem, k'', hk'', hy⟩ := mem_ancestorKeys.mp hb
      have hsub : exprKeys (adversaryView (Simulate c y)) ⊆ exprKeys (Simulate c y) :=
        exprKeysMonotone _ _ (hideEncryptedSmallerValue _ _)
      have hke : Expression.G1 k ∈ encKeys (Simulate c y) := by
        rw [exprKeys_eq_extractKeys_union_encKeys, Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact absurd (lemma4_simulate_adversaryView c y _ hmem) (by simp [isAtomicKey])
        · exact encKeys_hideEncrypted _ _ hmem
      rw [lemma6_simulate_enc c y hke k'' (hsub hk'')] at hy
      exact Bool.noConfusion hy
  · exact hc

lemma extractKeys_view_sMask (T : Finset (Expression Shape.KeyS)) :
    ∀ {b : WireBundle} (m : labelType b) (y : bundleBool b),
      extractKeys (hideEncrypted T (maskedLabelToExpr (sMask m y))) = ∅
  | WireBundle.SimpleB, l, y => by
      cases y <;> simp [sMask, maskedLabelToExpr, hideEncrypted, extractKeys]
  | WireBundle.PairB o1 o2, (l1, l2), (y1, y2) => by
      simp [sMask, maskedLabelToExpr, hideEncrypted, extractKeys,
        extractKeys_view_sMask T l1 y1, extractKeys_view_sMask T l2 y2]

lemma extractKeys_view_sEnc (T : Finset (Expression Shape.KeyS)) :
    ∀ {b : WireBundle} (u : labelType b),
      extractKeys (hideEncrypted T (encodedLabelToExpr (sEnc u))) ⊆ labelKeys u
  | WireBundle.SimpleB, l => by
      have he : hideEncrypted T (encodedLabelToExpr (sEnc (b := WireBundle.SimpleB) l))
          = Expression.Pair (Expression.BitE l.bitE) l.key0 := by
        simp only [sEnc, encodedLabelToExpr, hideEncrypted, hideEncrypted_key]
      rw [he]; simp [extractKeys, extractKeys_key, labelKeys]
  | WireBundle.PairB o1 o2, (l1, l2) => by
      simp only [sEnc, encodedLabelToExpr, hideEncrypted, extractKeys, labelKeys]
      exact Finset.union_subset_union (extractKeys_view_sEnc T l1) (extractKeys_view_sEnc T l2)

/-- What the adversary reads off one *simulated* `NAnd` table: always `K_h⁰`. -/
lemma sim_view_extract (T : Finset (Expression Shape.KeyS)) (li lj : WireLabel) (n : ℕ) :
    extractKeys (hideEncrypted T (sim Circuit.NandC (li, lj) n).1)
      = ((if li.key0 ∈ T ∧ lj.key0 ∈ T then {Expression.VarK (2*n)} else ∅)
         ∪ (if li.key0 ∈ T ∧ lj.key1 ∈ T then {Expression.VarK (2*n)} else ∅))
      ∪ ((if li.key1 ∈ T ∧ lj.key0 ∈ T then {Expression.VarK (2*n)} else ∅)
         ∪ (if li.key1 ∈ T ∧ lj.key1 ∈ T then {Expression.VarK (2*n)} else ∅)) := by
  simp only [sim, hideEncrypted, extractKeys, extractKeys_view_gbEntry, extractKeys_key]

lemma nand_keySubterms_sim (li lj : WireLabel) (n : ℕ) :
    li.key0 ∈ keySubterms (sim Circuit.NandC (li, lj) n).1 ∧
    li.key1 ∈ keySubterms (sim Circuit.NandC (li, lj) n).1 ∧
    lj.key0 ∈ keySubterms (sim Circuit.NandC (li, lj) n).1 ∧
    lj.key1 ∈ keySubterms (sim Circuit.NandC (li, lj) n).1 := by
  simp only [sim, gbEntry, keySubterms, Finset.mem_union]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Or.inl (Or.inl (Or.inl (keySubterms_self _)))
  · exact Or.inr (Or.inl (Or.inl (keySubterms_self _)))
  · exact Or.inl (Or.inl (Or.inr (Or.inl (keySubterms_self _))))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (keySubterms_self _))))

lemma extractKeys_adversaryView_simulate {s t : WireBundle} (c : Circuit s t)
    (y : bundleBool t) :
    extractKeys (adversaryView (Simulate c y))
      = extractKeys (hideEncrypted (adversaryKeys (Simulate c y))
            (sim c (makeLabels s 0).1 (makeLabels s 0).2).1)
        ∪ extractKeys (hideEncrypted (adversaryKeys (Simulate c y))
            (encodedLabelToExpr (sEnc (makeLabels s 0).1))) := by
  simp only [adversaryView, Simulate, hideEncrypted, extractKeys, extractKeys_view_sMask,
    Finset.union_empty]

lemma keySubterms_simulate_sim {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    keySubterms (sim c (makeLabels s 0).1 (makeLabels s 0).2).1
      ⊆ keySubterms (Simulate c y) := by
  intro z hz
  simp only [Simulate, keySubterms, Finset.mem_union]
  exact Or.inl hz

lemma fresh_not_input_sim {s : WireBundle} (T : Finset (Expression Shape.KeyS)) {m n : ℕ}
    (hn : (makeLabels s 0).2 ≤ n) (hm : 2 * n ≤ m) :
    Expression.VarK m ∉ extractKeys (hideEncrypted T
      (encodedLabelToExpr (sEnc (makeLabels s 0).1))) := by
  intro hcon
  have h1 : Expression.VarK m ∈ labelKeys (makeLabels s 0).1 :=
    extractKeys_view_sEnc T _ hcon
  have h2 := labelKeys_below (makeLabels s 0).1 (makeLabels_below s 0).2 _ h1
  have h3 := h2 m (by simp [keySubterms])
  omega

/-- Lemma 8's content, stated over `gb`'s output labels — which are `sim`'s
    (`sim_snd_eq_gb_snd`) and make the `Compose` case chain directly. -/
theorem lemma8_gb {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    ∀ {s' t' : WireBundle} (c' : Circuit s' t') (u' : labelType s') (ctr' : ℕ),
      GbStage c (makeLabels s 0).1 (makeLabels s 0).2 c' u' ctr' →
      LabelInvariantIn (keySubterms (Simulate c y)) (adversaryKeys (Simulate c y)) u' →
      LabelInvariantIn (keySubterms (Simulate c y)) (adversaryKeys (Simulate c y))
        (gb c' u' ctr').2.1 := by
  intro s' t' c'
  set f := Simulate c y with hf
  set T := adversaryKeys f with hTdef
  set U := keySubterms f with hUdef
  have hsub : keySubterms (sim c (makeLabels s 0).1 (makeLabels s 0).2).1 ⊆ U :=
    keySubterms_simulate_sim c y
  induction c' with
  | SwapC a b => rintro ⟨i1, i2⟩ ctr _ ⟨h1, h2⟩; exact ⟨h2, h1⟩
  | AssocC a b d => rintro ⟨i1, i2, i3⟩ ctr _ ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  | UnAssocC a b d => rintro ⟨⟨i1, i2⟩, i3⟩ ctr _ ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  | DupC =>
      intro l ctr _ hinv
      simp only [gb, LabelInvariantIn] at hinv ⊢
      constructor
      · rintro ⟨hu0, hu1⟩
        rcases hinv ⟨keySubterms_of_G0 hu0, keySubterms_of_G0 hu1⟩ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨adversaryKeys_G0_closed f ha hu0,
            fun hc => hb (adversaryKeys_G0_seed_sim c y hc)⟩
        · exact Or.inr ⟨adversaryKeys_G0_closed f ha hu1,
            fun hc => hb (adversaryKeys_G0_seed_sim c y hc)⟩
      · rintro ⟨hu0, hu1⟩
        rcases hinv ⟨keySubterms_of_G1 hu0, keySubterms_of_G1 hu1⟩ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨adversaryKeys_G1_closed f ha hu0,
            fun hc => hb (adversaryKeys_G1_seed_sim c y hc)⟩
        · exact Or.inr ⟨adversaryKeys_G1_closed f ha hu1,
            fun hc => hb (adversaryKeys_G1_seed_sim c y hc)⟩
  | FirstC c1 wb ih =>
      rintro ⟨u1, u2⟩ ctr hstage ⟨h1, h2⟩
      exact ⟨ih u1 ctr (hstage.trans (GbStage.first (GbStage.refl c1 u1 ctr))) h1, h2⟩
  | ComposeC c1 c2 ih1 ih2 =>
      intro u' ctr' hstage hinv
      have st1 := hstage.trans (GbStage.composeL (GbStage.refl c1 u' ctr'))
      have inv1 := ih1 u' ctr' st1 hinv
      have st2 := hstage.trans (GbStage.composeR
        (GbStage.refl c2 (gb c1 u' ctr').2.1 (gb c1 u' ctr').2.2))
      exact ih2 _ _ st2 inv1
  | NandC =>
      rintro ⟨li, lj⟩ n hstage ⟨invi, invj⟩
      obtain ⟨m1, m2, m3, m4⟩ := nand_keySubterms_sim li lj n
      have hks := hstage.keySubterms_subset_sim
      have hi := invi ⟨hsub (hks m1), hsub (hks m2)⟩
      have hj := invj ⟨hsub (hks m3), hsub (hks m4)⟩
      have hE := sim_view_extract T li lj n
      have hin : ∀ K, K ∈ extractKeys (hideEncrypted T (sim Circuit.NandC (li, lj) n).1) →
          K ∈ T := by
        intro K hK
        apply extractKeys_adversaryView_subset
        rw [extractKeys_adversaryView_simulate, Finset.mem_union]
        exact Or.inl (hstage.view_extract_mono_sim T hK)
      have hout : ∀ (j : ℕ), 2*n ≤ j → j < 2*n+2 → Expression.VarK j ∈ T →
          Expression.VarK j ∈ extractKeys (hideEncrypted T (sim Circuit.NandC (li, lj) n).1) := by
        intro j hlo hhi hmem
        have h1 := atomic_recovered_simulate c y (by simp [isAtomicKey]) hmem
        rw [extractKeys_adversaryView_simulate, Finset.mem_union] at h1
        rcases h1 with h1 | h1
        · refine GbStage.view_extract_iso_sim T hstage hlo ?_ h1
          have : (gb Circuit.NandC (li, lj) n).2.2 = n + 1 := rfl
          rw [this]; omega
        · exact absurd h1 (fresh_not_input_sim T hstage.ctr_le hlo)
      simp only [gb, LabelInvariantIn]
      intro _
      have hEc : extractKeys (hideEncrypted T (sim Circuit.NandC (li, lj) n).1)
          = {Expression.VarK (2*n)} := by
        rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases hj with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
          · rw [hE]; simp [ha, hb, hc, hd]
      refine Or.inl ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
      have := hout (2*n+1) (by omega) (by omega) hcon
      rw [hEc] at this; simp at this

theorem lemma8 : Lemma8 := by
  intro s t c y s' t' c' u' ctr' hstage hinv
  rw [sim_snd_fst]
  exact lemma8_gb c y c' u' ctr' hstage hinv

end PRG
