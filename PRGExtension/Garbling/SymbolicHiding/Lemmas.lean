import PRGExtension.Garbling.Simulate

/-!
# Supporting lemmas for the hiding proofs

Bookkeeping shared by the garbling and simulation sides: freshness of the key counter
(`keyVarsBelow`, `LabelsBelow`), strong independence of label expressions
(`IndependentKeys`, `DistinctLabels`, `StronglyIndependent`), the statements of LM18
Lemmas 4–8 and Theorems 4–5, and the *stage* relation `GbStage`.

`GbStage c u ctr c' u' ctr'` says that garbling `c` from `(u, ctr)` performs, as a
sub-computation, the garbling of `c'` from `(u', ctr')`.  LM18's Lemmas 7 and 8 read "for any
sub-circuit `C'` of `C` and any label expression `u`", but taken literally with `SubCircuit`
that is false here: `gb` takes the labels and the counter as *independent* arguments, so for
an arbitrary `u`/`ctr` the fresh keys a `NAnd` mints need not be keys of `Garble C x` at all.
`GbStage` records what the paper means.  Since `Sim` threads labels and counters exactly as
`Gb` does (`sim_snd_eq_gb_snd`), one stage relation serves both sides.
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

/-! ## Independence of label expressions -/

/-- `Keys(u)` for a label expression. -/
def labelKeys : {b : WireBundle} -> labelType b -> Finset (Expression Shape.KeyS)
  | WireBundle.SimpleB, l => {l.key0, l.key1}
  | WireBundle.PairB _ _, (l1, l2) => labelKeys l1 ∪ labelKeys l2
lemma exprKeys_labelToExpr : ∀ {b : WireBundle} (u : labelType b),
    exprKeys (labelToExpr u) = labelKeys u
  | WireBundle.SimpleB, l => by
      simp [labelToExpr, exprKeys, labelKeys, exprKeys_key, Finset.insert_eq]
  | WireBundle.PairB o1 o2, (l1, l2) => by
      simp only [labelToExpr, exprKeys, labelKeys]
      rw [exprKeys_labelToExpr l1, exprKeys_labelToExpr l2]
lemma extractKeys_labelToExpr : ∀ {b : WireBundle} (u : labelType b),
    extractKeys (labelToExpr u) = labelKeys u
  | WireBundle.SimpleB, l => by
      simp [labelToExpr, extractKeys, labelKeys, extractKeys_key, Finset.insert_eq]
  | WireBundle.PairB o1 o2, (l1, l2) => by
      simp only [labelToExpr, extractKeys, labelKeys]
      rw [extractKeys_labelToExpr l1, extractKeys_labelToExpr l2]
/-- The labels of a bundle are pairwise distinct and use disjoint key sets. -/
def DistinctLabels : {b : WireBundle} -> labelType b -> Prop
  | WireBundle.SimpleB, l => l.key0 ≠ l.key1
  | WireBundle.PairB _ _, (l1, l2) =>
      DistinctLabels l1 ∧ DistinctLabels l2 ∧ labelKeys l1 ∩ labelKeys l2 = ∅
/--
  LM18 §5: a label expression `w` is *strongly independent* when `Keys(w)` is an
  independent set of keys, each single label has `k⁰ ≠ k¹`, and the two halves of a pair
  use disjoint key sets.

  Note the first clause is about `Keys(w)` **as a whole** — disjointness of the two halves
  is not enough on its own, since `k` and `G0 k` can sit in disjoint halves yet still be
  dependent.
-/
def StronglyIndependent {b : WireBundle} (u : labelType b) : Prop :=
  IndependentKeys (labelKeys u) ∧ DistinctLabels u
/--
  LM18 equation (1), the *label invariant* (the paper's "Condition 1"): the bit is an
  atomic variable and exactly one of the two keys lies in the adversary's key set `S`.
  The index `z` with `k_z ∈ S` is the label's *actual value*.
-/
def LabelInvariant (S : Finset (Expression Shape.KeyS)) :
    {b : WireBundle} -> labelType b -> Prop
  -- the paper's "b ∈ 𝐁" clause is now part of `WireLabel` itself
  | WireBundle.SimpleB, l =>
      (l.key0 ∈ S ∧ l.key1 ∉ S) ∨ (l.key1 ∈ S ∧ l.key0 ∉ S)
  | WireBundle.PairB _ _, (l1, l2) => LabelInvariant S l1 ∧ LabelInvariant S l2
/--
  The label invariant **relativised to the keys that actually occur**.

  This is needed because the library's `prgClosure` is bounded by the expression's own key
  subterms, whereas LM18's `𝖦*` is unbounded (`𝖦*(S) = {𝖦ʷ(k) | k ∈ S, w ∈ {0,1}*}`,
  Definition 3).  The bounding is sound for computing the *pattern* — `p(e,S)` only ever
  tests keys occurring in `e` — but it changes membership for keys that do not occur, and
  the unrelativised invariant quantifies over exactly those.

  Concretely (`scratch/DupTrailing.lean`): for `Garble Dup true` the whole expression has
  key set `{K₁}`, while the output labels are `(b,(G0 K₀, G0 K₁))` and `(b,(G1 K₀, G1 K₁))`.
  In LM18, `S = 𝖦*({K₁} ∪ …)` contains `G0 K₁` but not `G0 K₀`, so exactly one of the pair
  is in `S` and the invariant holds.  With the bounded closure `G0 K₁ ∉ S` either, so
  *neither* is in `S` and the invariant fails.

  LM18 only ever uses Lemma 7 for labels that are actually used (as encryption keys at a
  later gate), so relativising is faithful and is what makes the statement provable here.
-/
def LabelInvariantIn (U S : Finset (Expression Shape.KeyS)) :
    {b : WireBundle} -> labelType b -> Prop
  | WireBundle.SimpleB, l =>
      -- The guard is a *conjunction*: the invariant says something only about labels both of
      -- whose keys occur in the ambient expression.  With a disjunction the `Dup` case is
      -- unprovable — from `G0 k¹ ∈ U` alone one cannot place `G0 k⁰` in `U`, which
      -- `adversaryKeys_G0_closed` requires.  A conjunction loses nothing: wherever a label is
      -- actually *used* (as the pair of encryption keys of a `NAnd` table, or `G`-applied by
      -- `Dup`) both of its keys occur, so the invariant fires exactly where Theorem 5 needs it.
      (l.key0 ∈ U ∧ l.key1 ∈ U) →
      ((l.key0 ∈ S ∧ l.key1 ∉ S) ∨ (l.key1 ∈ S ∧ l.key0 ∉ S))
  | WireBundle.PairB _ _, (l1, l2) => LabelInvariantIn U S l1 ∧ LabelInvariantIn U S l2
/-- LM18 writes `(C̃, u)` for a garbled circuit paired with its input label expression. -/
def garbledWithLabels {s t : WireBundle} (c : Circuit s t)
    (ctilde : Expression (garbledShape c)) (u : labelType s) :
    Expression (Shape.PairS (garbledShape c) (labelShape s)) :=
  Expression.Pair ctilde (labelToExpr u)
-- ---------------------------------------------------------------------------------
-- Lemma 4 (proved)
-- ---------------------------------------------------------------------------------

/--
  **LM18 Lemma 4.**  Every key that appears *as a part* of a garbled circuit is an atomic
  key symbol.

  Only the `NAnd` case has any content: the payload of each table entry is one of the two
  freshly created atomic output keys `K_h⁰ = VarK (2·ctr)`, `K_h¹ = VarK (2·ctr+1)`.  All
  PRG-derived keys produced by `Dup` occur only as *encryption* keys, never as parts, and
  `extractKeys` skips those.
-/
theorem lemma4 : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    ∀ k ∈ extractKeys (gb c u ctr).1, isAtomicKey k = true := by
  intro s t c
  induction c with
  | NandC =>
      rintro ⟨li, lj⟩ ctr k hk
      simp [gb, gbEntry, extractKeys] at hk
      rcases hk with h | h <;> simp [h, isAtomicKey]
  | AssocC _ _ _ => rintro ⟨i1, i2, i3⟩ ctr k hk; simp [gb, extractKeys] at hk
  | UnAssocC _ _ _ => rintro ⟨⟨i1, i2⟩, i3⟩ ctr k hk; simp [gb, extractKeys] at hk
  | SwapC _ _ => rintro ⟨i1, i2⟩ ctr k hk; simp [gb, extractKeys] at hk
  | DupC => intro l ctr k hk; simp [gb, extractKeys] at hk
  | ComposeC c1 c2 ih1 ih2 =>
      intro u ctr k hk
      simp only [gb, extractKeys, Finset.mem_union] at hk
      rcases hk with h | h
      · exact ih1 _ _ _ h
      · exact ih2 _ _ _ h
  | FirstC c w ih =>
      rintro ⟨u1, u2⟩ ctr k hk
      simp only [gb] at hk
      exact ih _ _ _ hk
-- ---------------------------------------------------------------------------------
-- Lemmas 5-8 (statements; remaining obligations)
-- ---------------------------------------------------------------------------------

/--
  **LM18 Lemma 5.**  `Gb` turns strongly independent input labels into strongly
  independent output labels, and every output key `k`

  1. has no strict PRG-descendant among the keys of `(C̃, u)`, and
  2. is yielded by some key that appears as a part of `(C̃, u)`.

  Proof: structural induction on `C` (LM18 appendix A).  `NAnd` is the base case that
  creates the two fresh atomic keys; `Dup` is the case where `G` is applied.

  The `LabelsBelow ctr u` hypothesis is LM18's implicit `h ← new` bookkeeping, made
  explicit: without it the statement is **false**, since `u` could already mention the key
  variables `2·ctr`, `2·ctr+1` that `NAnd` is about to create, or a `G`-descendant of them.
  `gb_labels_below` above shows the hypothesis propagates through `Gb`, so
  it is available at every inductive step, and `Garble` establishes it via
  `makeLabels_below`.

  **Proved** in `GarbleProof.lean` (`PRG.lemma5`).
-/
def Lemma5 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    StronglyIndependent u → LabelsBelow ctr u →
    StronglyIndependent (gb c u ctr).2.1 ∧
    ∀ k ∈ labelKeys (gb c u ctr).2.1,
      (∀ k' ∈ exprKeys (gb c u ctr).1 ∪ labelKeys u, strictYields k k' = false) ∧
      (∃ k' ∈ extractKeys (gb c u ctr).1 ∪ labelKeys u, yields k' k)
/--
  **LM18 Lemma 6.**  For every key `k` used as an *encryption* key inside a garbled
  circuit `C̃`:

  1. `𝖦⁺(k) ∩ Keys(C̃) = ∅`;
  2. `𝖦*(k) ∩ Keys(v) = ∅` for the output labels `v`;
  3. some key that appears as a part of `(C̃, u)` yields `k`.

  Together with Lemma 5 this is what rules out the key cycles that would otherwise break
  the IND-CPA reduction: (1) says no descendant of an encrypting key is ever visible, which
  is exactly the `seedFree` side condition of `symbolicToSemanticIndistinguishabilityHidingOneKey`.

  **Proved** in `GarbleProof.lean`: condition (3) as `PRG.lemma6_cond3` (from the same
  induction as Lemma 5), conditions (1) and (2) alongside it; `PRG.lemma6` assembles all
  three.
-/
def Lemma6 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    StronglyIndependent u → LabelsBelow ctr u →
    ∀ k ∈ encKeys (gb c u ctr).1,
      (∀ k' ∈ exprKeys (gb c u ctr).1, strictYields k k' = false) ∧
      (∀ k' ∈ labelKeys (gb c u ctr).2.1, ¬ yields k k') ∧
      (∃ k' ∈ extractKeys (gb c u ctr).1 ∪ labelKeys u, yields k' k)
/-- `c'` occurs as a sub-circuit of `c`.  LM18 quantifies Lemmas 7 and 8 over the
    sub-circuits of one fixed circuit, because the key set `S` they refer to is the
    fixpoint of the *whole* garbling. -/
inductive SubCircuit : {s t s' t' : WireBundle} → Circuit s' t' → Circuit s t → Prop
  | refl {s t : WireBundle} (c : Circuit s t) : SubCircuit c c
  | composeL {u v w s' t' : WireBundle} {c1 : Circuit u v} {c2 : Circuit v w} {c' : Circuit s' t'} :
      SubCircuit c' c1 → SubCircuit c' (Circuit.ComposeC c1 c2)
  | composeR {u v w s' t' : WireBundle} {c1 : Circuit u v} {c2 : Circuit v w} {c' : Circuit s' t'} :
      SubCircuit c' c2 → SubCircuit c' (Circuit.ComposeC c1 c2)
  | first {v₁ v₂ u s' t' : WireBundle} {c : Circuit v₁ v₂} {c' : Circuit s' t'} :
      SubCircuit c' c → SubCircuit c' (Circuit.FirstC c u)
-- `Lemma7`, `Lemma8` and `Theorem5` are stated below over `GbStage`, the *stage*
-- refinement of `SubCircuit`, which tracks the labels and key counter the garbling
-- actually reaches.  `SubCircuit` itself is kept because it is the right notion for
-- statements that do not mention labels.

/-! ## Which key is recovered -/
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

/-! ## Stages of a garbling -/

/--
  `GbStage c u ctr c' u' ctr'` : garbling `c` from labels `u` and counter `ctr` performs,
  as a sub-computation, the garbling of `c'` from labels `u'` and counter `ctr'`.

  This replaces the bare `SubCircuit` relation.  LM18 says "for any sub-circuit `C'` of `C`
  and any label expression `u`", but the labels and counter are not arbitrary — they are
  the ones that actually arise, and Lemma 7's `NAnd` case depends on that (the fresh keys
  it creates have to be the ones appearing in the *global* garbled expression).
-/
inductive GbStage : {s t s' t' : WireBundle} → Circuit s t → labelType s → ℕ →
    Circuit s' t' → labelType s' → ℕ → Prop
  | refl {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ) :
      GbStage c u ctr c u ctr
  | composeL {a b d s' t' : WireBundle} {c1 : Circuit a b} {c2 : Circuit b d}
      {u : labelType a} {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ} :
      GbStage c1 u ctr c' u' ctr' → GbStage (Circuit.ComposeC c1 c2) u ctr c' u' ctr'
  | composeR {a b d s' t' : WireBundle} {c1 : Circuit a b} {c2 : Circuit b d}
      {u : labelType a} {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ} :
      GbStage c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2 c' u' ctr' →
      GbStage (Circuit.ComposeC c1 c2) u ctr c' u' ctr'
  | first {v1 v2 wb s' t' : WireBundle} {c : Circuit v1 v2} {u1 : labelType v1}
      {u2 : labelType wb} {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ} :
      GbStage c u1 ctr c' u' ctr' → GbStage (Circuit.FirstC c wb) (u1, u2) ctr c' u' ctr'
/-- A stage never rewinds the counter. -/
lemma GbStage.ctr_le {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') : ctr ≤ ctr' := by
  induction h with
  | refl => exact le_refl _
  | composeL _ ih => exact ih
  | composeR hh ih => exact le_trans (gb_ctr_mono _ _ _) ih
  | first _ ih => exact ih
/-- A stage's garbled expression sits inside the global one. -/
lemma GbStage.exprKeys_subset {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s}
    {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') :
    exprKeys (gb c' u' ctr').1 ⊆ exprKeys (gb c u ctr).1 := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @composeL a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : exprKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = exprKeys (gb c1 u ctr).1
            ∪ exprKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by simp [gb, exprKeys]
      rw [this, Finset.mem_union]; exact Or.inl hx
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : exprKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = exprKeys (gb c1 u ctr).1
            ∪ exprKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by simp [gb, exprKeys]
      rw [this, Finset.mem_union]; exact Or.inr hx
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : exprKeys (gb (Circuit.FirstC c wb) (u1, u2) ctr).1
          = exprKeys (gb c u1 ctr).1 := by simp [gb]
      rw [this]; exact hx
lemma GbStage.extractKeys_subset {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s}
    {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') :
    extractKeys (gb c' u' ctr').1 ⊆ extractKeys (gb c u ctr).1 := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @composeL a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : extractKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = extractKeys (gb c1 u ctr).1
            ∪ extractKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp [gb, extractKeys]
      rw [this, Finset.mem_union]; exact Or.inl hx
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : extractKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = extractKeys (gb c1 u ctr).1
            ∪ extractKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp [gb, extractKeys]
      rw [this, Finset.mem_union]; exact Or.inr hx
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : extractKeys (gb (Circuit.FirstC c wb) (u1, u2) ctr).1
          = extractKeys (gb c u1 ctr).1 := by simp [gb, extractKeys]
      rw [this]; exact hx
/--
  `Sim` differs from `Gb` only in the *garbled tables* it emits: the output labels and the
  counter are threaded identically in every case.  Hence one `GbStage` relation describes
  the stages of both, which is what lets Lemma 8 be stated over the same relation as
  Lemma 7.
-/
theorem sim_snd_eq_gb_snd : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    (sim c u ctr).2 = (gb c u ctr).2 := by
  intro s t c
  induction c with
  | SwapC x y => rintro ⟨i1, i2⟩ ctr; rfl
  | AssocC x y z => rintro ⟨i1, i2, i3⟩ ctr; rfl
  | UnAssocC x y z => rintro ⟨⟨i1, i2⟩, i3⟩ ctr; rfl
  | DupC => intro l ctr; rfl
  | NandC => rintro ⟨li, lj⟩ ctr; rfl
  | FirstC c wb ih =>
      rintro ⟨b1, b2⟩ ctr
      simp only [sim, gb, Prod.mk.injEq]
      exact ⟨by rw [congrArg Prod.fst (ih b1 ctr)], congrArg Prod.snd (ih b1 ctr)⟩
  | ComposeC c1 c2 ih1 ih2 =>
      intro b ctr
      simp only [sim, gb]
      have h1 := ih1 b ctr
      have e1 : (sim c1 b ctr).2.1 = (gb c1 b ctr).2.1 := congrArg Prod.fst h1
      have e2 : (sim c1 b ctr).2.2 = (gb c1 b ctr).2.2 := congrArg Prod.snd h1
      rw [e1, e2]; exact ih2 _ _
lemma GbStage.exprKeys_subset_sim {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s}
    {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') :
    exprKeys (sim c' u' ctr').1 ⊆ exprKeys (sim c u ctr).1 := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @composeL a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : exprKeys (sim (Circuit.ComposeC c1 c2) u ctr).1
          = exprKeys (sim c1 u ctr).1
            ∪ exprKeys (sim c2 (sim c1 u ctr).2.1 (sim c1 u ctr).2.2).1 := by simp [sim, exprKeys]
      rw [this, Finset.mem_union]; exact Or.inl hx
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      have e1 : (sim c1 u ctr).2.1 = (gb c1 u ctr).2.1 := congrArg Prod.fst (sim_snd_eq_gb_snd c1 u ctr)
      have e2 : (sim c1 u ctr).2.2 = (gb c1 u ctr).2.2 := congrArg Prod.snd (sim_snd_eq_gb_snd c1 u ctr)
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : exprKeys (sim (Circuit.ComposeC c1 c2) u ctr).1
          = exprKeys (sim c1 u ctr).1
            ∪ exprKeys (sim c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp only [sim, exprKeys, e1, e2]
      rw [this, Finset.mem_union]; exact Or.inr hx
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro x hx
      have : exprKeys (sim (Circuit.FirstC c wb) (u1, u2) ctr).1 = exprKeys (sim c u1 ctr).1 := by
        simp [sim]
      rw [this]; exact hx
/--
  The label invariant propagates along a stage: it is enough to know that one `gb` step
  preserves it (Lemma 7's content) to get it at *every* stage of the garbling.
  Stated for an abstract step hypothesis so that Lemmas 7 and 8 can both use it.
-/
lemma gbStage_invariant {U S : Finset (Expression Shape.KeyS)}
    (step : ∀ {a b : WireBundle} (d : Circuit a b) (v : labelType a) (n : ℕ),
        LabelInvariantIn U S v → LabelInvariantIn U S (gb d v n).2.1) :
    ∀ {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
      {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ},
      GbStage c u ctr c' u' ctr' → LabelInvariantIn U S u → LabelInvariantIn U S u' := by
  intro s t s' t' c u ctr c' u' ctr' h
  induction h with
  | refl => exact fun hu => hu
  | composeL _ ih => exact ih
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' _ ih => exact fun hu => ih (step c1 u ctr hu)
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih => exact fun hu => ih hu.1
/-- A stage is in particular a sub-circuit. -/
lemma GbStage.subCircuit {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') : SubCircuit c' c := by
  induction h with
  | refl c u ctr => exact SubCircuit.refl c
  | composeL _ ih => exact SubCircuit.composeL ih
  | composeR _ ih => exact SubCircuit.composeR ih
  | first _ ih => exact SubCircuit.first ih
/-! ## The remaining obligations, restated over `GbStage` -/
/--
  **LM18 Lemma 7.**  `Gb` preserves the label invariant: if the labels at a stage of
  garbling `C` have exactly one key of each pair in `S = Fix(𝓕_{Garble C x})`, so do the
  output labels of that stage.

  `S` is *not* arbitrary, and neither are `u'`/`ctr'`: they are the ones the garbling of
  `C` actually produces, which is what `GbStage` records.  The `Dup` case needs this — it
  argues that `G^h(k^{1-z}) ∉ S` via Lemma 6 applied to the *whole* garbled circuit, which
  has no counterpart for an unconstrained `S`.

  `LabelInvariantIn` is relativised to `U = keySubterms (Garble c x)` because the
  formalisation's `prgClosure` is bounded by the ambient key subterms; keys outside `U` are
  simply not tested.  See `PRGExtension-Analysis.md` §4.7.
-/
def Lemma7 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (x : bundleBool s),
    ∀ {s' t' : WireBundle} (c' : Circuit s' t') (u' : labelType s') (ctr' : ℕ),
      GbStage c (makeLabels s 0).1 (makeLabels s 0).2 c' u' ctr' →
      LabelInvariantIn (keySubterms (Garble c x)) (adversaryKeys (Garble c x)) u' →
      LabelInvariantIn (keySubterms (Garble c x)) (adversaryKeys (Garble c x))
        (gb c' u' ctr').2.1
/--
  **LM18 Lemma 8.**  The same for the simulator, with `T = Fix(𝓕_f)` for
  `f = Simulate(C, C(x))`.  `Sim` threads labels and counters exactly as `Gb` does
  (`sim_snd_eq_gb_snd`), so the very same stage relation applies.
-/
def Lemma8 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (y : bundleBool t),
    ∀ {s' t' : WireBundle} (c' : Circuit s' t') (u' : labelType s') (ctr' : ℕ),
      GbStage c (makeLabels s 0).1 (makeLabels s 0).2 c' u' ctr' →
      LabelInvariantIn (keySubterms (Simulate c y)) (adversaryKeys (Simulate c y)) u' →
      LabelInvariantIn (keySubterms (Simulate c y)) (adversaryKeys (Simulate c y))
        (sim c' u' ctr').2.1
/--
  **LM18 Theorem 5**, the goal these lemmas serve:
  `Pattern(Garble(C,x)) ≈ Pattern(Simulate(C,C(x)))`.
-/
def Theorem5 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (x : bundleBool s),
    symIndistinguishable (Garble c x) (Simulate c (evalCircuit c x))
/--
  Given Lemma 7, the invariant holds at *every* stage once it holds at the input labels —
  this is the form Theorem 5 consumes.  (`gbStage_invariant` specialised; the `step`
  hypothesis is Lemma 7 with its `GbStage` premise discharged by the stage being extended,
  so we state it directly in the unquantified form.)
-/
lemma lemma7_propagates {U S : Finset (Expression Shape.KeyS)}
    (step : ∀ {a b : WireBundle} (d : Circuit a b) (v : labelType a) (n : ℕ),
        LabelInvariantIn U S v → LabelInvariantIn U S (gb d v n).2.1)
    {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') (hu : LabelInvariantIn U S u) :
    LabelInvariantIn U S u' ∧ LabelInvariantIn U S (gb c' u' ctr').2.1 :=
  let hu' := gbStage_invariant step h hu
  ⟨hu', step c' u' ctr' hu'⟩

end PRG
