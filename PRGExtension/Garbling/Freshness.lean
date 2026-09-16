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

/-- Every key variable occurring anywhere in an expression has index `< n`. -/
def exprKeyVarsBelow (n : ℕ) {s : Shape} (e : Expression s) : Prop :=
  ∀ m, Expression.VarK m ∈ keySubterms e -> m < n

lemma exprKeyVarsBelow_mono {n n' : ℕ} {s : Shape} {e : Expression s} (h : n ≤ n')
    (he : exprKeyVarsBelow n e) : exprKeyVarsBelow n' e := fun m hm => lt_of_lt_of_le (he m hm) h

-- closure of `exprKeyVarsBelow` under the constructors we need
lemma ekvb_bitE {n : ℕ} (b : BitExpr) : exprKeyVarsBelow n (Expression.BitE b) := by
  intro m hm; simp [keySubterms] at hm
lemma ekvb_eps {n : ℕ} : exprKeyVarsBelow n (Expression.Eps) := by
  intro m hm; simp [keySubterms] at hm
lemma ekvb_varK {n j : ℕ} (h : j < n) : exprKeyVarsBelow n (Expression.VarK j) := by
  intro m hm; simp only [keySubterms, Finset.mem_singleton] at hm; injection hm with hm; omega
lemma ekvb_pair {n : ℕ} {s1 s2 : Shape} {a : Expression s1} {b : Expression s2}
    (ha : exprKeyVarsBelow n a) (hb : exprKeyVarsBelow n b) :
    exprKeyVarsBelow n (Expression.Pair a b) := by
  intro m hm; simp only [keySubterms, Finset.mem_union] at hm
  rcases hm with h | h; exacts [ha m h, hb m h]
lemma ekvb_perm {n : ℕ} {s1 : Shape} {bt : Expression Shape.BitS} {a b : Expression s1}
    (ha : exprKeyVarsBelow n a) (hb : exprKeyVarsBelow n b) :
    exprKeyVarsBelow n (Expression.Perm bt a b) := by
  intro m hm; simp only [keySubterms, Finset.mem_union] at hm
  rcases hm with h | h; exacts [ha m h, hb m h]
lemma ekvb_enc {n : ℕ} {s1 : Shape} {k : Expression Shape.KeyS} {e : Expression s1}
    (hk : keyVarsBelow n k) (he : exprKeyVarsBelow n e) :
    exprKeyVarsBelow n (Expression.Enc k e) := by
  intro m hm; simp only [keySubterms, Finset.mem_union] at hm
  rcases hm with h | h; exacts [hk m h, he m h]

lemma ekvb_gbEntry {n : ℕ} {ko ki kp : Expression Shape.KeyS} {bt : BitExpr}
    (hko : keyVarsBelow n ko) (hki : keyVarsBelow n ki) (hkp : keyVarsBelow n kp) :
    exprKeyVarsBelow n (gbEntry ko ki kp bt) :=
  ekvb_enc hko (ekvb_enc hki (ekvb_pair (ekvb_bitE bt) (fun m hm => hkp m hm)))

/-- The garbled circuit only mentions key variables below the counter `Gb` returns. -/
lemma gb_circuit_below : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    LabelsBelow ctr u -> exprKeyVarsBelow (2*(gb c u ctr).2.2) (gb c u ctr).1 := by
  intro s t c
  induction c with
  | NandC =>
      rintro ⟨li, lj⟩ ctr h
      simp only [LabelsBelow] at h
      have hi0 : keyVarsBelow (2*(ctr+1)) li.key0 := keyVarsBelow_mono (by omega) h.1.2.1
      have hi1 : keyVarsBelow (2*(ctr+1)) li.key1 := keyVarsBelow_mono (by omega) h.1.2.2
      have hj0 : keyVarsBelow (2*(ctr+1)) lj.key0 := keyVarsBelow_mono (by omega) h.2.2.1
      have hj1 : keyVarsBelow (2*(ctr+1)) lj.key1 := keyVarsBelow_mono (by omega) h.2.2.2
      have hk0 : keyVarsBelow (2*(ctr+1)) (Expression.VarK (2*ctr)) := by
        intro m hm; simp only [keySubterms, Finset.mem_singleton] at hm
        injection hm with hm; omega
      have hk1 : keyVarsBelow (2*(ctr+1)) (Expression.VarK (2*ctr+1)) := by
        intro m hm; simp only [keySubterms, Finset.mem_singleton] at hm
        injection hm with hm; omega
      have hres : (gb Circuit.NandC (li, lj) ctr).2.2 = ctr + 1 := by simp [gb]
      rw [hres]
      show exprKeyVarsBelow (2*(ctr+1)) (gb Circuit.NandC (li, lj) ctr).1
      simp only [gb]
      exact ekvb_perm (ekvb_perm (ekvb_gbEntry hi0 hj0 hk1) (ekvb_gbEntry hi0 hj1 hk1))
                      (ekvb_perm (ekvb_gbEntry hi1 hj0 hk1) (ekvb_gbEntry hi1 hj1 hk0))
  | AssocC _ _ _ => rintro ⟨i1, i2, i3⟩ ctr _; simpa [gb] using (ekvb_eps (n := 2*ctr))
  | UnAssocC _ _ _ => rintro ⟨⟨i1, i2⟩, i3⟩ ctr _; simpa [gb] using (ekvb_eps (n := 2*ctr))
  | SwapC _ _ => rintro ⟨i1, i2⟩ ctr _; simpa [gb] using (ekvb_eps (n := 2*ctr))
  | DupC => intro l ctr _; simpa [gb] using (ekvb_eps (n := 2*ctr))
  | ComposeC c1 c2 ih1 ih2 =>
      intro u ctr h
      have h1 := ih1 u ctr h
      have h2 := ih2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2 (gb_labels_below c1 u ctr h)
      have hmono := gb_ctr_mono c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2
      have he : (gb (Circuit.ComposeC c1 c2) u ctr).1
          = Expression.Pair (gb c1 u ctr).1 (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp [gb]
      have hc : (gb (Circuit.ComposeC c1 c2) u ctr).2.2
          = (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).2.2 := by simp [gb]
      rw [hc, he]
      exact ekvb_pair (exprKeyVarsBelow_mono (by omega) h1) h2
  | FirstC c w ih =>
      rintro ⟨u1, u2⟩ ctr h
      have := ih u1 ctr h.1
      have he : (gb (Circuit.FirstC c w) (u1, u2) ctr).1 = (gb c u1 ctr).1 := by simp [gb]
      have hc : (gb (Circuit.FirstC c w) (u1, u2) ctr).2.2 = (gb c u1 ctr).2.2 := by simp [gb]
      rw [hc, he]; exact this

/-- The keys appearing as *parts* of a garbled circuit are the fresh atomic keys created by
    its `NAnd` gates, so they lie in the counter window `[2·ctr, 2·ctr')`. -/
lemma gb_parts_fresh : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    ∀ k ∈ extractKeys (gb c u ctr).1,
      ∃ m, k = Expression.VarK m ∧ 2*ctr ≤ m ∧ m < 2*(gb c u ctr).2.2 := by
  intro s t c
  induction c with
  | NandC =>
      rintro ⟨li, lj⟩ ctr k hk
      have hres : (gb Circuit.NandC (li, lj) ctr).2.2 = ctr + 1 := by simp [gb]
      simp [gb, gbEntry, extractKeys] at hk
      rw [hres]
      rcases hk with h | h
      · exact ⟨2*ctr+1, h, by omega, by omega⟩
      · exact ⟨2*ctr, h, by omega, by omega⟩
  | AssocC _ _ _ => rintro ⟨i1, i2, i3⟩ ctr k hk; simp [gb, extractKeys] at hk
  | UnAssocC _ _ _ => rintro ⟨⟨i1, i2⟩, i3⟩ ctr k hk; simp [gb, extractKeys] at hk
  | SwapC _ _ => rintro ⟨i1, i2⟩ ctr k hk; simp [gb, extractKeys] at hk
  | DupC => intro l ctr k hk; simp [gb, extractKeys] at hk
  | ComposeC c1 c2 ih1 ih2 =>
      intro u ctr k hk
      have hmono1 := gb_ctr_mono c1 u ctr
      have hmono2 := gb_ctr_mono c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2
      have hc : (gb (Circuit.ComposeC c1 c2) u ctr).2.2
          = (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).2.2 := by simp [gb]
      have he : extractKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = extractKeys (gb c1 u ctr).1
            ∪ extractKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp [gb, extractKeys]
      rw [he, Finset.mem_union] at hk
      rw [hc]
      rcases hk with h | h
      · obtain ⟨m, hm, ha, hb⟩ := ih1 u ctr k h; exact ⟨m, hm, by omega, by omega⟩
      · obtain ⟨m, hm, ha, hb⟩ := ih2 _ _ k h; exact ⟨m, hm, by omega, by omega⟩
  | FirstC c w ih =>
      rintro ⟨u1, u2⟩ ctr k hk
      have hc : (gb (Circuit.FirstC c w) (u1, u2) ctr).2.2 = (gb c u1 ctr).2.2 := by simp [gb]
      have he : (gb (Circuit.FirstC c w) (u1, u2) ctr).1 = (gb c u1 ctr).1 := by simp [gb]
      rw [he] at hk
      rw [hc]
      exact ih u1 ctr k hk

end PRG