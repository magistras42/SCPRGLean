import PRGExtension.Garbling.Lemma5

/-!
# LM18 Lemma 6

For every key `k` used as an *encryption* key inside a garbled circuit `C̃`:

1. `𝖦⁺(k) ∩ Keys(C̃) = ∅` — no strict PRG-descendant of `k` is visible anywhere in `C̃`;
2. `𝖦*(k) ∩ Keys(v) = ∅` — no output-label key is yielded by `k`;
3. some key appearing as a *part* of `(C̃, u)` yields `k` (proved in `Lemma5.lean`).

Condition (1) is precisely the `seedFree` side condition that
`symbolicToSemanticIndistinguishabilityHidingOneKey` needs: the IND-CPA reduction never
learns an encryption key, so it must never be asked to compute `prg0` of it.

The induction runs against `lemma5core`'s three outputs.
-/

namespace PRG


set_option maxHeartbeats 2000000

lemma freshKey_not_in {x : Expression Shape.KeyS} {N m : ℕ}
    (hx : keyVarsBelow N x) (hm : N ≤ m) : Expression.VarK m ∉ keySubterms x :=
  fun hc => absurd (hx m hc) (by omega)

/-- A fresh variable and an "old" key cannot both sit in the chain of one key. -/
lemma fresh_chain_contra {k k' : Expression Shape.KeyS} {N m : ℕ}
    (hk : keyVarsBelow N k) (hm : N ≤ m)
    (hmem : Expression.VarK m ∈ keySubterms k') (hkmem : k ∈ keySubterms k') : False := by
  rcases keySubterms_linear k' _ k hmem hkmem with hL | hL
  · exact freshKey_not_in hk hm hL
  · simp only [keySubterms, Finset.mem_singleton] at hL
    exact freshKey_not_in hk hm (by rw [hL]; simp [keySubterms])

lemma exprKeys_keyVarsBelow {s t : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    (hb : LabelsBelow ctr u) {k : Expression Shape.KeyS} (hk : k ∈ exprKeys (gb c u ctr).1) :
    keyVarsBelow (2*(gb c u ctr).2.2) k :=
  fun m hm => gb_circuit_below c u ctr hb m (keySubterms_subset_of_mem_exprKeys _ k hk hm)

lemma encKeys_subset_exprKeys {s : Shape} (e : Expression s) : encKeys e ⊆ exprKeys e := by
  intro k hk
  rw [exprKeys_eq_extractKeys_union_encKeys, Finset.mem_union]; exact Or.inr hk

-- one-off computations of the NAnd table's key sets (kept out of the main induction so
-- the big `simp`s run once)
lemma nand_exprKeys (li lj : WireLabel) (ctr : ℕ) :
    ∀ k' ∈ exprKeys (gb Circuit.NandC (li, lj) ctr).1,
      k' = li.key0 ∨ k' = li.key1 ∨ k' = lj.key0 ∨ k' = lj.key1 ∨
      k' = Expression.VarK (2*ctr) ∨ k' = Expression.VarK (2*ctr+1) := by
  intro k' h; simp [gb, gbEntry, exprKeys, exprKeys_key] at h; tauto

lemma nand_encKeys (li lj : WireLabel) (ctr : ℕ) :
    ∀ k ∈ encKeys (gb Circuit.NandC (li, lj) ctr).1,
      k = li.key0 ∨ k = li.key1 ∨ k = lj.key0 ∨ k = lj.key1 := by
  intro k h; simp [gb, gbEntry, encKeys] at h; tauto

lemma nand_labelKeys (li lj : WireLabel) (ctr : ℕ) :
    ∀ k ∈ labelKeys (gb Circuit.NandC (li, lj) ctr).2.1,
      k = Expression.VarK (2*ctr) ∨ k = Expression.VarK (2*ctr+1) := by
  intro k h; simp [gb, labelKeys] at h; tauto

/-- LM18 Lemma 6, conditions (1) and (2). -/
def L6core {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ) : Prop :=
  ∀ k ∈ encKeys (gb c u ctr).1,
    (∀ k' ∈ exprKeys (gb c u ctr).1, strictYields k k' = false) ∧
    (∀ k' ∈ labelKeys (gb c u ctr).2.1, ¬ yields k k')

theorem lemma6core : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    StronglyIndependent u → LabelsBelow ctr u → L6core c u ctr := by
  intro s t c
  induction c with
  | SwapC x y => rintro ⟨i1, i2⟩ ctr _ _ k hk; simp [gb, encKeys] at hk
  | AssocC x y z => rintro ⟨i1, i2, i3⟩ ctr _ _ k hk; simp [gb, encKeys] at hk
  | UnAssocC x y z => rintro ⟨⟨i1, i2⟩, i3⟩ ctr _ _ k hk; simp [gb, encKeys] at hk
  | DupC => intro l ctr _ _ k hk; simp [gb, encKeys] at hk
  | NandC =>
      rintro ⟨li, lj⟩ ctr ⟨hindU, _⟩ hbelow k hk
      simp only [LabelsBelow] at hbelow
      obtain ⟨⟨_, hi0, hi1⟩, ⟨_, hj0, hj1⟩⟩ := hbelow
      have hmemU : ∀ x, (x = li.key0 ∨ x = li.key1 ∨ x = lj.key0 ∨ x = lj.key1) →
          x ∈ labelKeys (b := WireBundle.PairB WireBundle.SimpleB WireBundle.SimpleB) (li, lj) := by
        intro x h; simp only [labelKeys, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton]; tauto
      have hkcase := nand_encKeys li lj ctr k hk
      have hkb : keyVarsBelow (2*ctr) k := by
        rcases hkcase with h|h|h|h <;> (subst h; first | exact hi0 | exact hi1 | exact hj0 | exact hj1)
      refine ⟨fun k' hk' => ?_, fun k' hk' hy => ?_⟩
      · have hC : k' = li.key0 ∨ k' = li.key1 ∨ k' = lj.key0 ∨ k' = lj.key1 ∨
            k' = Expression.VarK (2*ctr) ∨ k' = Expression.VarK (2*ctr+1) := by
          simp [gb, gbEntry, exprKeys, exprKeys_key] at hk'; tauto
        rcases hC with h|h|h|h|h|h
        · exact hindU k (hmemU k hkcase) k' (hmemU k' (by tauto))
        · exact hindU k (hmemU k hkcase) k' (hmemU k' (by tauto))
        · exact hindU k (hmemU k hkcase) k' (hmemU k' (by tauto))
        · exact hindU k (hmemU k hkcase) k' (hmemU k' (by tauto))
        · subst h; exact sy_to_varK _ _
        · subst h; exact sy_to_varK _ _
      · have hk2 : k' = Expression.VarK (2*ctr) ∨ k' = Expression.VarK (2*ctr+1) := by
          simp [gb, labelKeys] at hk'; tauto
        rcases hy with rfl | hy
        · rcases hk2 with h | h
          · exact absurd (hkb (2*ctr) (by rw [h]; simp [keySubterms])) (by omega)
          · exact absurd (hkb (2*ctr+1) (by rw [h]; simp [keySubterms])) (by omega)
        · rcases hk2 with h | h <;> (subst h; rw [sy_to_varK] at hy; exact Bool.noConfusion hy)
  | ComposeC c1 c2 ih1 ih2 =>
      intro u ctr hSI hb k hk
      have hSIw : StronglyIndependent (gb c1 u ctr).2.1 := (lemma5core c1 u ctr hSI hb).1
      have hbw : LabelsBelow (gb c1 u ctr).2.2 (gb c1 u ctr).2.1 := gb_labels_below c1 u ctr hb
      have h5w := (lemma5core c1 u ctr hSI hb).2.1
      have h5v := (lemma5core c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2 hSIw hbw).2.1
      have hL3v := (lemma5core c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2 hSIw hbw).2.2
      have H1 := ih1 u ctr hSI hb
      have H2 := ih2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2 hSIw hbw
      have hEnc : encKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = encKeys (gb c1 u ctr).1
            ∪ encKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by simp [gb, encKeys]
      have hE : exprKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = exprKeys (gb c1 u ctr).1
            ∪ exprKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by simp [gb, exprKeys]
      have hV : (gb (Circuit.ComposeC c1 c2) u ctr).2.1
          = (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).2.1 := by simp [gb]
      rw [hEnc, Finset.mem_union] at hk
      rcases hk with hk | hk
      · refine ⟨fun k' hk' => ?_, fun k' hk' hy => ?_⟩
        · rw [hE, Finset.mem_union] at hk'
          rcases hk' with h | h
          · exact (H1 k hk).1 k' h
          · cases hb2 : strictYields k k'
            · rfl
            · exfalso
              obtain ⟨r, hr, hyr⟩ := hL3v k' h
              rw [Finset.mem_union] at hr
              rcases hr with hr | hr
              · obtain ⟨m, rfl, hm1, _⟩ := gb_parts_fresh c2 _ _ _ hr
                exact fresh_chain_contra
                  (exprKeys_keyVarsBelow hb (encKeys_subset_exprKeys _ hk)) hm1
                  (yields_mem_keySubterms hyr) (strictYields_mem_keySubterms _ _ hb2)
              · rcases hyr with rfl | hyr
                · exact (H1 k hk).2 _ hr (Or.inr hb2)
                · rcases strictYields_comparable k' r k hyr hb2 with heq | hc | hc
                  · exact (H1 k hk).2 k (by rw [← heq]; exact hr) (yields_refl k)
                  · have hcon := (h5w r hr).1 k
                      (by rw [Finset.mem_union]; exact Or.inl (encKeys_subset_exprKeys _ hk))
                    rw [hc] at hcon; exact Bool.noConfusion hcon
                  · exact (H1 k hk).2 r hr (Or.inr hc)
        · rw [hV] at hk'
          obtain ⟨r, hr, hyr⟩ := (h5v k' hk').2
          rw [Finset.mem_union] at hr
          rcases hr with hr | hr
          · obtain ⟨m, rfl, hm1, _⟩ := gb_parts_fresh c2 _ _ _ hr
            exact fresh_chain_contra
              (exprKeys_keyVarsBelow hb (encKeys_subset_exprKeys _ hk)) hm1
              (yields_mem_keySubterms hyr) (yields_mem_keySubterms hy)
          · rcases hyr with rfl | hyr
            · exact (H1 k hk).2 _ hr hy
            · rcases hy with rfl | hy
              · have hcon := (h5w r hr).1 k
                  (by rw [Finset.mem_union]; exact Or.inl (encKeys_subset_exprKeys _ hk))
                rw [hyr] at hcon; exact Bool.noConfusion hcon
              · rcases strictYields_comparable k' r k hyr hy with heq | hc | hc
                · exact (H1 k hk).2 k (by rw [← heq]; exact hr) (yields_refl k)
                · have hcon := (h5w r hr).1 k
                    (by rw [Finset.mem_union]; exact Or.inl (encKeys_subset_exprKeys _ hk))
                  rw [hc] at hcon; exact Bool.noConfusion hcon
                · exact (H1 k hk).2 r hr (Or.inr hc)
      · refine ⟨fun k' hk' => ?_, fun k' hk' hy => ?_⟩
        · rw [hE, Finset.mem_union] at hk'
          rcases hk' with h | h
          · cases hb2 : strictYields k k'
            · rfl
            · exfalso
              obtain ⟨r, hr, hyr⟩ := hL3v k (encKeys_subset_exprKeys _ hk)
              rw [Finset.mem_union] at hr
              rcases hr with hr | hr
              · obtain ⟨m, rfl, hm1, _⟩ := gb_parts_fresh c2 _ _ _ hr
                exact absurd (exprKeys_keyVarsBelow hb h m
                    (keySubterms_subset_of_mem k' k (strictYields_mem_keySubterms _ _ hb2)
                      (yields_mem_keySubterms hyr))) (by omega)
              · have hcon := (h5w r hr).1 k' (by rw [Finset.mem_union]; exact Or.inl h)
                rw [yields_strictYields_trans hyr hb2] at hcon; exact Bool.noConfusion hcon
          · exact (H2 k hk).1 k' h
        · rw [hV] at hk'; exact (H2 k hk).2 k' hk' hy
  | FirstC c wb ih =>
      rintro ⟨u1, u2⟩ ctr ⟨hindU, hd1, hd2, hdisj⟩ ⟨hb1, hb2⟩ k hk
      have hSI1 : StronglyIndependent u1 :=
        ⟨hindU.subset (by intro x hx; simp only [labelKeys, Finset.mem_union]; exact Or.inl hx), hd1⟩
      have hE : exprKeys (gb (Circuit.FirstC c wb) (u1, u2) ctr).1
          = exprKeys (gb c u1 ctr).1 := by simp [gb]
      have hEnc : encKeys (gb (Circuit.FirstC c wb) (u1, u2) ctr).1
          = encKeys (gb c u1 ctr).1 := by simp [gb]
      have hV : (gb (Circuit.FirstC c wb) (u1, u2) ctr).2.1
          = ((gb c u1 ctr).2.1, u2) := by simp [gb]
      rw [hEnc] at hk
      have H := ih u1 ctr hSI1 hb1 k hk
      have hL3 := (lemma5core c u1 ctr hSI1 hb1).2.2
      refine ⟨fun k' hk' => ?_, fun k' hk' hy => ?_⟩
      · rw [hE] at hk'; exact H.1 k' hk'
      · rw [hV] at hk'
        simp only [labelKeys, Finset.mem_union] at hk'
        rcases hk' with h | h
        · exact H.2 k' h hy
        · obtain ⟨r, hr, hyr⟩ := hL3 k (encKeys_subset_exprKeys _ hk)
          have hyrk' : yields r k' := yields_trans hyr hy
          rw [Finset.mem_union] at hr
          rcases hr with hr | hr
          · obtain ⟨m, rfl, hm1, _⟩ := gb_parts_fresh c u1 ctr _ hr
            exact absurd (labelKeys_below u2 hb2 k' h m (yields_mem_keySubterms hyrk')) (by omega)
          · rcases hyrk' with rfl | hyrk'
            · exact mem_of_inter_empty hdisj hr h
            · have hcon := hindU r
                (by simp only [labelKeys, Finset.mem_union]; exact Or.inl hr) k'
                (by simp only [labelKeys, Finset.mem_union]; exact Or.inr h)
              rw [hyrk'] at hcon; exact Bool.noConfusion hcon

/-- **LM18 Lemma 6.** -/
theorem lemma6 : Lemma6 := by
  intro s t c u ctr hSI hb k hk
  exact ⟨(lemma6core c u ctr hSI hb k hk).1, (lemma6core c u ctr hSI hb k hk).2,
    lemma6_cond3 c u ctr hSI hb k hk⟩

end PRG
