import PRGExtension.Garbling.Lemma8

/-!
# Which key is recovered

Lemmas 7 and 8 say *exactly one* key of each label pair is recovered.  Theorem 5 needs to
know **which**: for the garbling it is the key for the wire's actual value, and for the
simulation it is always key `0` — that difference is precisely what the renaming in
Theorem 5 has to absorb.

Both proofs are the ones in `Lemma7.lean` / `Lemma8.lean` with the case analysis on "which
key is in `S`" replaced by the value it is determined by.  At a `NAnd` gate with input
values `(v_i, v_j)` exactly row `(v_i, v_j)` decrypts, and its payload is `K_h¹` unless
`(v_i,v_j) = (1,1)`, in which case it is `K_h⁰` — which is exactly `key_{¬(v_i ∧ v_j)}`.
-/

namespace PRG

/-- The value-tracking refinement of `LabelInvariantIn`: the key the adversary recovers is
    the one for the wire's **actual** value.  Lemma 7 only says *exactly one* of the pair is
    recovered; Theorem 5 needs to know *which*. -/
def LabelValueIn (U S : Finset (Expression Shape.KeyS)) :
    {b : WireBundle} -> labelType b -> bundleBool b -> Prop
  | WireBundle.SimpleB, l, v =>
      (l.key0 ∈ U ∧ l.key1 ∈ U) →
      (cond v l.key1 l.key0 ∈ S ∧ cond v l.key0 l.key1 ∉ S)
  | WireBundle.PairB _ _, (l1, l2), (v1, v2) =>
      LabelValueIn U S l1 v1 ∧ LabelValueIn U S l2 v2

/-- The simulator's invariant: it is always the *first* key that is recovered, whatever the
    circuit computes.  That is the whole point of `Sim` — every table row carries `K_h⁰`. -/
def LabelZeroIn (U T : Finset (Expression Shape.KeyS)) :
    {b : WireBundle} -> labelType b -> Prop
  | WireBundle.SimpleB, l => (l.key0 ∈ U ∧ l.key1 ∈ U) → (l.key0 ∈ T ∧ l.key1 ∉ T)
  | WireBundle.PairB _ _, (l1, l2) => LabelZeroIn U T l1 ∧ LabelZeroIn U T l2

theorem lemma7_value {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    ∀ {s' t' : WireBundle} (c' : Circuit s' t') (u' : labelType s') (ctr' : ℕ)
      (v : bundleBool s'),
      GbStage c (makeLabels s 0).1 (makeLabels s 0).2 c' u' ctr' →
      LabelValueIn (keySubterms (Garble c x)) (adversaryKeys (Garble c x)) u' v →
      LabelValueIn (keySubterms (Garble c x)) (adversaryKeys (Garble c x))
        (gb c' u' ctr').2.1 (evalCircuit c' v) := by
  intro s' t' c'
  set e := Garble c x with he
  set S := adversaryKeys e with hSdef
  set U := keySubterms e with hUdef
  have hsub : keySubterms (gb c (makeLabels s 0).1 (makeLabels s 0).2).1 ⊆ U :=
    keySubterms_garble_gb c x
  induction c' with
  | SwapC a b => rintro ⟨i1, i2⟩ ctr ⟨v1, v2⟩ _ ⟨h1, h2⟩; exact ⟨h2, h1⟩
  | AssocC a b d =>
      rintro ⟨i1, i2, i3⟩ ctr ⟨v1, v2, v3⟩ _ ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  | UnAssocC a b d =>
      rintro ⟨⟨i1, i2⟩, i3⟩ ctr ⟨⟨v1, v2⟩, v3⟩ _ ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  | DupC =>
      intro l ctr v _ hinv
      cases v <;>
        · simp only [gb, LabelValueIn, evalCircuit, cond_true, cond_false] at hinv ⊢
          refine ⟨?_, ?_⟩ <;> rintro ⟨hu0, hu1⟩
          · first
            | exact ⟨adversaryKeys_G0_closed e (hinv ⟨keySubterms_of_G0 hu0,
                keySubterms_of_G0 hu1⟩).1 hu0,
                fun hc => (hinv ⟨keySubterms_of_G0 hu0, keySubterms_of_G0 hu1⟩).2
                  (adversaryKeys_G0_seed c x hc)⟩
            | exact ⟨adversaryKeys_G0_closed e (hinv ⟨keySubterms_of_G0 hu0,
                keySubterms_of_G0 hu1⟩).1 hu1,
                fun hc => (hinv ⟨keySubterms_of_G0 hu0, keySubterms_of_G0 hu1⟩).2
                  (adversaryKeys_G0_seed c x hc)⟩
          · first
            | exact ⟨adversaryKeys_G1_closed e (hinv ⟨keySubterms_of_G1 hu0,
                keySubterms_of_G1 hu1⟩).1 hu0,
                fun hc => (hinv ⟨keySubterms_of_G1 hu0, keySubterms_of_G1 hu1⟩).2
                  (adversaryKeys_G1_seed c x hc)⟩
            | exact ⟨adversaryKeys_G1_closed e (hinv ⟨keySubterms_of_G1 hu0,
                keySubterms_of_G1 hu1⟩).1 hu1,
                fun hc => (hinv ⟨keySubterms_of_G1 hu0, keySubterms_of_G1 hu1⟩).2
                  (adversaryKeys_G1_seed c x hc)⟩
  | FirstC c1 wb ih =>
      rintro ⟨u1, u2⟩ ctr ⟨v1, v2⟩ hstage ⟨h1, h2⟩
      exact ⟨ih u1 ctr v1 (hstage.trans (GbStage.first (GbStage.refl c1 u1 ctr))) h1, h2⟩
  | ComposeC c1 c2 ih1 ih2 =>
      intro u' ctr' v hstage hinv
      have st1 := hstage.trans (GbStage.composeL (GbStage.refl c1 u' ctr'))
      have inv1 := ih1 u' ctr' v st1 hinv
      have st2 := hstage.trans (GbStage.composeR
        (GbStage.refl c2 (gb c1 u' ctr').2.1 (gb c1 u' ctr').2.2))
      exact ih2 _ _ _ st2 inv1
  | NandC =>
      rintro ⟨li, lj⟩ n ⟨vi, vj⟩ hstage ⟨invi, invj⟩
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
      simp only [gb, LabelValueIn, evalCircuit]
      intro _
      cases vi <;> cases vj <;>
        simp only [cond_true, cond_false, Bool.and_self, Bool.and_true, Bool.and_false,
          Bool.false_and, Bool.true_and, Bool.not_true, Bool.not_false] at hi hj ⊢
      · have hEc : extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
            = {Expression.VarK (2*n+1)} := by rw [hE]; simp [hi.1, hi.2, hj.1, hj.2]
        refine ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
        have := hout (2*n) (le_refl _) (by omega) hcon
        rw [hEc] at this; simp at this
      · have hEc : extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
            = {Expression.VarK (2*n+1)} := by rw [hE]; simp [hi.1, hi.2, hj.1, hj.2]
        refine ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
        have := hout (2*n) (le_refl _) (by omega) hcon
        rw [hEc] at this; simp at this
      · have hEc : extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
            = {Expression.VarK (2*n+1)} := by rw [hE]; simp [hi.1, hi.2, hj.1, hj.2]
        refine ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
        have := hout (2*n) (le_refl _) (by omega) hcon
        rw [hEc] at this; simp at this
      · have hEc : extractKeys (hideEncrypted S (gb Circuit.NandC (li, lj) n).1)
            = {Expression.VarK (2*n)} := by rw [hE]; simp [hi.1, hi.2, hj.1, hj.2]
        refine ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
        have := hout (2*n+1) (by omega) (by omega) hcon
        rw [hEc] at this; simp at this

/-- **The simulator recovers the first key of every label.**  This is Lemma 8 sharpened the
    way Theorem 5 needs it: not merely "exactly one of the pair", but always index `0`. -/
theorem lemma8_zero {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    ∀ {s' t' : WireBundle} (c' : Circuit s' t') (u' : labelType s') (ctr' : ℕ),
      GbStage c (makeLabels s 0).1 (makeLabels s 0).2 c' u' ctr' →
      LabelZeroIn (keySubterms (Simulate c y)) (adversaryKeys (Simulate c y)) u' →
      LabelZeroIn (keySubterms (Simulate c y)) (adversaryKeys (Simulate c y))
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
      simp only [gb, LabelZeroIn] at hinv ⊢
      refine ⟨?_, ?_⟩ <;> rintro ⟨hu0, hu1⟩
      · exact ⟨adversaryKeys_G0_closed f (hinv ⟨keySubterms_of_G0 hu0,
            keySubterms_of_G0 hu1⟩).1 hu0,
          fun hc => (hinv ⟨keySubterms_of_G0 hu0, keySubterms_of_G0 hu1⟩).2
            (adversaryKeys_G0_seed_sim c y hc)⟩
      · exact ⟨adversaryKeys_G1_closed f (hinv ⟨keySubterms_of_G1 hu0,
            keySubterms_of_G1 hu1⟩).1 hu0,
          fun hc => (hinv ⟨keySubterms_of_G1 hu0, keySubterms_of_G1 hu1⟩).2
            (adversaryKeys_G1_seed_sim c y hc)⟩
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
      simp only [gb, LabelZeroIn]
      intro _
      have hEc : extractKeys (hideEncrypted T (sim Circuit.NandC (li, lj) n).1)
          = {Expression.VarK (2*n)} := by rw [hE]; simp [hi.1, hi.2, hj.1, hj.2]
      refine ⟨hin _ (by rw [hEc]; simp), fun hcon => ?_⟩
      have := hout (2*n+1) (by omega) (by omega) hcon
      rw [hEc] at this; simp at this

end PRG
