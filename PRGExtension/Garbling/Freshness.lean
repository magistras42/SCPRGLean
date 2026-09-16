import PRGExtension.Garbling.GarblingDef

/-!
# Counter freshness

LM18 writes `h ← new` and thereafter treats `B_h`, `K_h⁰`, `K_h¹` as fresh.  Lemmas 5–8
all rest on that, so here it is made explicit and proved: `Gb` and `Sim` only ever move the
counter forward, and they keep every label strictly below it.
-/

namespace PRG

/-- Every key *variable* occurring in `k` has index `< n`. -/
def keyVarsBelow (n : ℕ) (k : Expression Shape.KeyS) : Prop :=
  ∀ m, Expression.VarK m ∈ keySubterms k → m < n

lemma keyVarsBelow_mono {n n' : ℕ} {k : Expression Shape.KeyS} (h : n ≤ n')
    (hk : keyVarsBelow n k) : keyVarsBelow n' k := fun m hm => lt_of_lt_of_le (hk m hm) h

lemma keyVarsBelow_G0 {n : ℕ} {k : Expression Shape.KeyS} (hk : keyVarsBelow n k) :
    keyVarsBelow n (Expression.G0 k) := by
  intro m hm
  simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hm
  rcases hm with h | h
  · exact absurd h (by simp)
  · exact hk m h

lemma keyVarsBelow_G1 {n : ℕ} {k : Expression Shape.KeyS} (hk : keyVarsBelow n k) :
    keyVarsBelow n (Expression.G1 k) := by
  intro m hm
  simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hm
  rcases hm with h | h
  · exact absurd h (by simp)
  · exact hk m h

/-- Every label in the bundle mentions only bits `< ctr` and key variables `< 2·ctr`. -/
def LabelsBelow (ctr : ℕ) : {b : WireBundle} -> labelType b -> Prop
  | WireBundle.SimpleB, l =>
      l.bit < ctr ∧ keyVarsBelow (2*ctr) l.key0 ∧ keyVarsBelow (2*ctr) l.key1
  | WireBundle.PairB _ _, (l1, l2) => LabelsBelow ctr l1 ∧ LabelsBelow ctr l2

lemma labelsBelow_mono : ∀ {b : WireBundle} {ctr ctr' : ℕ} (u : labelType b),
    ctr ≤ ctr' -> LabelsBelow ctr u -> LabelsBelow ctr' u
  | WireBundle.SimpleB, _, _, l, h, hl =>
      ⟨lt_of_lt_of_le hl.1 h,
       keyVarsBelow_mono (by omega) hl.2.1, keyVarsBelow_mono (by omega) hl.2.2⟩
  | WireBundle.PairB _ _, _, _, (l1, l2), h, hl =>
      ⟨labelsBelow_mono l1 h hl.1, labelsBelow_mono l2 h hl.2⟩

/-- `Label(s)` produces labels below the counter it returns. -/
lemma makeLabels_below : ∀ (b : WireBundle) (i : ℕ),
    i ≤ (makeLabels b i).2 ∧ LabelsBelow (makeLabels b i).2 (makeLabels b i).1
  | WireBundle.SimpleB, i => by
      refine ⟨by simp [makeLabels], ?_⟩
      simp only [makeLabels, LabelsBelow]
      refine ⟨by omega, ?_, ?_⟩ <;> · intro m hm
                                      simp only [keySubterms, Finset.mem_singleton] at hm
                                      injection hm with hm; omega
  | WireBundle.PairB o1 o2, i => by
      obtain ⟨h1, hl1⟩ := makeLabels_below o1 i
      obtain ⟨h2, hl2⟩ := makeLabels_below o2 (makeLabels o1 i).2
      refine ⟨by simp only [makeLabels]; omega, ?_⟩
      simp only [makeLabels, LabelsBelow]
      exact ⟨labelsBelow_mono _ h2 hl1, hl2⟩

/-- `Gb` never rewinds the counter. -/
lemma gb_ctr_mono : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    ctr ≤ (gb c u ctr).2.2 := by
  intro s t c
  induction c with
  | NandC => rintro ⟨li, lj⟩ ctr; simp [gb]
  | AssocC _ _ _ => rintro ⟨i1, i2, i3⟩ ctr; simp [gb]
  | UnAssocC _ _ _ => rintro ⟨⟨i1, i2⟩, i3⟩ ctr; simp [gb]
  | SwapC _ _ => rintro ⟨i1, i2⟩ ctr; simp [gb]
  | DupC => intro l ctr; simp [gb]
  | ComposeC c1 c2 ih1 ih2 =>
      intro u ctr
      have h1 := ih1 u ctr
      have h2 := ih2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2
      have he : (gb (Circuit.ComposeC c1 c2) u ctr).2.2
          = (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).2.2 := by simp [gb]
      rw [he]
      exact le_trans h1 h2
  | FirstC c w ih => rintro ⟨u1, u2⟩ ctr; simpa [gb] using ih u1 ctr

/-- `Gb` keeps every output label strictly below the counter it returns. -/
lemma gb_labels_below : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    LabelsBelow ctr u -> LabelsBelow (gb c u ctr).2.2 (gb c u ctr).2.1 := by
  intro s t c
  induction c with
  | NandC =>
      rintro ⟨li, lj⟩ ctr _
      simp only [gb, LabelsBelow]
      refine ⟨by omega, ?_, ?_⟩ <;> · intro m hm
                                      simp only [keySubterms, Finset.mem_singleton] at hm
                                      injection hm with hm; omega
  | AssocC _ _ _ => rintro ⟨i1, i2, i3⟩ ctr h; exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  | UnAssocC _ _ _ => rintro ⟨⟨i1, i2⟩, i3⟩ ctr h; exact ⟨h.1.1, h.1.2, h.2⟩
  | SwapC _ _ => rintro ⟨i1, i2⟩ ctr h; exact ⟨h.2, h.1⟩
  | DupC =>
      intro l ctr h
      simp only [gb, LabelsBelow] at h ⊢
      exact ⟨⟨h.1, keyVarsBelow_G0 h.2.1, keyVarsBelow_G0 h.2.2⟩,
             ⟨h.1, keyVarsBelow_G1 h.2.1, keyVarsBelow_G1 h.2.2⟩⟩
  | ComposeC c1 c2 ih1 ih2 =>
      intro u ctr h
      simpa [gb] using ih2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2 (ih1 u ctr h)
  | FirstC c w ih =>
      rintro ⟨u1, u2⟩ ctr h
      refine ⟨by simpa [gb] using ih u1 ctr h.1, ?_⟩
      exact labelsBelow_mono u2 (by simpa [gb] using gb_ctr_mono c u1 ctr) h.2

end PRG
