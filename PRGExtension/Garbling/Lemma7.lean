import PRGExtension.Garbling.ViewKeys

/-!
# LM18 Lemma 7

`Gb` preserves the label invariant: at every stage of garbling `C`, if the input labels have
exactly one key of each pair in `S = Fix(𝓕_{Garble C x})`, so do the output labels.

The two interesting cases:

* **`NAnd`.**  With exactly one key of `l_i` and one of `l_j` in `S`, exactly one of the four
  table rows decrypts (`nand_view_extract`), yielding exactly one of the two fresh payload
  keys `K_{2n}, K_{2n+1}`.  That one is in `S` because everything readable off the view is
  (`extractKeys_adversaryView_subset`).  The other is *not*, and this is the step that needs
  global information: were it in `S` it would — being atomic — have to be readable off the
  view (`atomic_recovered_garble`), and `GbStage.view_extract_iso` then places it in *this
  gate's* contribution, which is the singleton we just computed.  Nothing elsewhere in the
  circuit can supply it, and it is too fresh to be an input key (`fresh_not_input`).

* **`Dup`.**  `adversaryKeys_G0_closed` pushes the known key through the PRG,
  `adversaryKeys_G0_seed` keeps the unknown one unknown.
-/

namespace PRG

lemma extractKeys_view_mask (S : Finset (Expression Shape.KeyS)) :
    ∀ {b : WireBundle} (m : maskedLabelType b),
      extractKeys (hideEncrypted S (maskedLabelToExpr m)) = ∅ := by
  intro b
  induction b with
  | SimpleB => intro m; cases m <;> simp [maskedLabelToExpr, hideEncrypted, extractKeys]
  | PairB b1 b2 ih1 ih2 =>
      rintro ⟨m1, m2⟩
      simp [maskedLabelToExpr, hideEncrypted, extractKeys, ih1, ih2]

/-- What the adversary reads off one `NAnd` table: the payload of each row it can decrypt. -/
lemma nand_view_extract (S : Finset (Expression Shape.KeyS)) (li lj : WireLabel) (n : ℕ) :
    extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
      = ((if li.key0 ∈ S ∧ lj.key0 ∈ S then {Expression.VarK (2*n+1)} else ∅)
         ∪ (if li.key0 ∈ S ∧ lj.key1 ∈ S then {Expression.VarK (2*n+1)} else ∅))
      ∪ ((if li.key1 ∈ S ∧ lj.key0 ∈ S then {Expression.VarK (2*n+1)} else ∅)
         ∪ (if li.key1 ∈ S ∧ lj.key1 ∈ S then {Expression.VarK (2*n)} else ∅)) := by
  simp only [gb, hideEncrypted, extractKeys, extractKeys_view_gbEntry, extractKeys_key]

/-- Both keys of a `NAnd` gate's input labels occur in the garbled table. -/
lemma nand_keySubterms (li lj : WireLabel) (n : ℕ) :
    li.key0 ∈ keySubterms (gb Circuit.NandC (li, lj) n).1 ∧
    li.key1 ∈ keySubterms (gb Circuit.NandC (li, lj) n).1 ∧
    lj.key0 ∈ keySubterms (gb Circuit.NandC (li, lj) n).1 ∧
    lj.key1 ∈ keySubterms (gb Circuit.NandC (li, lj) n).1 := by
  simp only [gb, gbEntry, keySubterms, Finset.mem_union]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Or.inl (Or.inl (Or.inl (keySubterms_self _)))
  · exact Or.inr (Or.inl (Or.inl (keySubterms_self _)))
  · exact Or.inl (Or.inl (Or.inr (Or.inl (keySubterms_self _))))
  · exact Or.inl (Or.inr (Or.inr (Or.inl (keySubterms_self _))))

lemma extractKeys_adversaryView_garble {s t : WireBundle} (c : Circuit s t)
    (x : bundleBool s) :
    extractKeys (adversaryView (Garble c x))
      = extractKeys (hideEncrypted (adversaryKeys (Garble c x))
            (gb c (makeLabels s 0).1 (makeLabels s 0).2).1)
        ∪ extractKeys (hideEncrypted (adversaryKeys (Garble c x))
            (encodedLabelToExpr (gEnc (makeLabels s 0).1 x))) := by
  simp only [adversaryView, Garble, hideEncrypted, extractKeys, extractKeys_view_mask,
    Finset.union_empty]

lemma keySubterms_garble_gb {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    keySubterms (gb c (makeLabels s 0).1 (makeLabels s 0).2).1 ⊆ keySubterms (Garble c x) := by
  intro y hy
  simp only [Garble, keySubterms, Finset.mem_union]
  exact Or.inl hy

/-- A key variable minted at or after the input counter is not one of the input label keys. -/
lemma fresh_not_input {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    (S : Finset (Expression Shape.KeyS)) {m n : ℕ}
    (hn : (makeLabels s 0).2 ≤ n) (hm : 2 * n ≤ m) :
    Expression.VarK m ∉ extractKeys (hideEncrypted S
      (encodedLabelToExpr (gEnc (makeLabels s 0).1 x))) := by
  intro hcon
  have h1 : Expression.VarK m ∈ labelKeys (makeLabels s 0).1 :=
    extractKeys_view_gEnc S _ x hcon
  have h2 := labelKeys_below (makeLabels s 0).1 (makeLabels_below s 0).2 _ h1
  have h3 := h2 m (by simp [keySubterms])
  omega

theorem lemma7 : Lemma7 := by
  intro s t c x s' t' c'
  set e := Garble c x with he
  set S := adversaryKeys e with hSdef
  set U := keySubterms e with hUdef
  have hsub : keySubterms (gb c (makeLabels s 0).1 (makeLabels s 0).2).1 ⊆ U :=
    keySubterms_garble_gb c x
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
        · exact Or.inl ⟨adversaryKeys_G0_closed e ha hu0,
            fun hc => hb (adversaryKeys_G0_seed c x hc)⟩
        · exact Or.inr ⟨adversaryKeys_G0_closed e ha hu1,
            fun hc => hb (adversaryKeys_G0_seed c x hc)⟩
      · rintro ⟨hu0, hu1⟩
        rcases hinv ⟨keySubterms_of_G1 hu0, keySubterms_of_G1 hu1⟩ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨adversaryKeys_G1_closed e ha hu0,
            fun hc => hb (adversaryKeys_G1_seed c x hc)⟩
        · exact Or.inr ⟨adversaryKeys_G1_closed e ha hu1,
            fun hc => hb (adversaryKeys_G1_seed c x hc)⟩
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
      obtain ⟨m1, m2, m3, m4⟩ := nand_keySubterms li lj n
      have hks := hstage.keySubterms_subset
      have hi := invi ⟨hsub (hks m1), hsub (hks m2)⟩
      have hj := invj ⟨hsub (hks m3), hsub (hks m4)⟩
      have hE := nand_view_extract S li lj n
      have hin : ∀ K, K ∈ extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1) →
          K ∈ S := by
        intro K hK
        apply extractKeys_adversaryView_subset
        rw [extractKeys_adversaryView_garble, Finset.mem_union]
        exact Or.inl (hstage.view_extract_mono S hK)
      have hout : ∀ (j : ℕ), 2*n ≤ j → j < 2*n+2 → Expression.VarK j ∈ S →
          Expression.VarK j ∈ extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1) := by
        intro j hlo hhi hmem
        have h1 := atomic_recovered_garble c x (by simp [isAtomicKey]) hmem
        rw [extractKeys_adversaryView_garble, Finset.mem_union] at h1
        rcases h1 with h1 | h1
        · refine GbStage.view_extract_iso S hstage hlo ?_ h1
          have : (gb Circuit.NandC (li, lj) n).2.2 = n + 1 := rfl
          rw [this]; omega
        · exact absurd h1 (fresh_not_input c x S hstage.ctr_le hlo)
      simp only [gb, LabelInvariantIn]
      intro _
      rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases hj with ⟨hc, hd⟩ | ⟨hc, hd⟩
      · have hEc : extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
            = {Expression.VarK (2*n+1)} := by rw [hE]; simp [ha, hb, hc, hd]
        refine Or.inr ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
        have := hout (2*n) (le_refl _) (by omega) hcon
        rw [hEc] at this; simp at this
      · have hEc : extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
            = {Expression.VarK (2*n+1)} := by rw [hE]; simp [ha, hb, hc, hd]
        refine Or.inr ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
        have := hout (2*n) (le_refl _) (by omega) hcon
        rw [hEc] at this; simp at this
      · have hEc : extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
            = {Expression.VarK (2*n+1)} := by rw [hE]; simp [ha, hb, hc, hd]
        refine Or.inr ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
        have := hout (2*n) (le_refl _) (by omega) hcon
        rw [hEc] at this; simp at this
      · have hEc : extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
            = {Expression.VarK (2*n)} := by rw [hE]; simp [ha, hb, hc, hd]
        refine Or.inl ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
        have := hout (2*n+1) (by omega) (by omega) hcon
        rw [hEc] at this; simp at this

end PRG
