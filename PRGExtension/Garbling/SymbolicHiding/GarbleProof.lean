import PRGExtension.Garbling.SymbolicHiding.Lemmas

/-!
# Characterising `adversaryKeys (Garble C x)`

LM18 Lemmas 5 and 6, then their consequences for the whole garbled expression.

* `lemma5` — `Gb` preserves strong independence of the label expressions, and every key of
  the output labels is freshly minted and yielded by something the garbling reveals.
* `lemma6` — every key used as an *encryption* key has no strict PRG-descendant occurring in
  the garbled circuit, does not yield any output-label key, and is itself yielded by
  something revealed.
* `lemma4_garble` / `lemma4_adversaryView` — every key appearing as a *part* of the garbled
  expression is atomic.
* `lemma6_garble_cond1`, `adversaryKeys_G0_seed`, `adversaryKeys_G1_seed` — the fixpoint of
  `keyRecovery` on `Garble C x` knows a derived key only if it knows the seed.
-/

set_option maxHeartbeats 2000000

namespace PRG

lemma sy_G0_self (k : Expression Shape.KeyS) : strictYields k (Expression.G0 k) = true := by
  simp [strictYields]
lemma sy_G1_self (k : Expression Shape.KeyS) : strictYields k (Expression.G1 k) = true := by
  simp [strictYields]
lemma sy_of_G0_left {x y : Expression Shape.KeyS} (h : strictYields (Expression.G0 x) y = true) :
    strictYields x y = true := strictYields_trans x _ (sy_G0_self x) y h
lemma sy_of_G1_left {x y : Expression Shape.KeyS} (h : strictYields (Expression.G1 x) y = true) :
    strictYields x y = true := strictYields_trans x _ (sy_G1_self x) y h
lemma sy_G0_k {a b : Expression Shape.KeyS} (h : strictYields a b = false) :
    strictYields (Expression.G0 a) b = false := by
  cases hb : strictYields (Expression.G0 a) b
  · rfl
  · rw [sy_of_G0_left hb] at h; exact Bool.noConfusion h
lemma sy_G1_k {a b : Expression Shape.KeyS} (h : strictYields a b = false) :
    strictYields (Expression.G1 a) b = false := by
  cases hb : strictYields (Expression.G1 a) b
  · rfl
  · rw [sy_of_G1_left hb] at h; exact Bool.noConfusion h
/-- If `a ⊀ b` then no `G`-child of `a` yields any `G`-child of `b`. -/
lemma sy_GG4 {a b : Expression Shape.KeyS} (h : strictYields a b = false) :
    strictYields (Expression.G0 a) (Expression.G0 b) = false ∧
    strictYields (Expression.G0 a) (Expression.G1 b) = false ∧
    strictYields (Expression.G1 a) (Expression.G0 b) = false ∧
    strictYields (Expression.G1 a) (Expression.G1 b) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · cases hb : strictYields _ _
    · rfl
    · exfalso
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with hb | hb
      · subst hb
        first
          | (rw [sy_G0_self a] at h; exact Bool.noConfusion h)
          | (rw [sy_G1_self a] at h; exact Bool.noConfusion h)
      · first
          | (rw [sy_of_G0_left hb] at h; exact Bool.noConfusion h)
          | (rw [sy_of_G1_left hb] at h; exact Bool.noConfusion h)
/-- A fresh key variable cannot yield anything built only from older variables. -/
lemma sy_varK_of_below {k : Expression Shape.KeyS} {n m : ℕ}
    (hk : keyVarsBelow n k) (hm : n ≤ m) : strictYields (Expression.VarK m) k = false := by
  cases hb : strictYields (Expression.VarK m) k
  · rfl
  · exact absurd (hk m (strictYields_mem_keySubterms _ _ hb)) (by omega)
lemma sy_to_varK (x : Expression Shape.KeyS) (n : ℕ) :
    strictYields x (Expression.VarK n) = false := by simp [strictYields]
lemma keySubterms_linear : ∀ (c a b : Expression Shape.KeyS),
    a ∈ keySubterms c → b ∈ keySubterms c → a ∈ keySubterms b ∨ b ∈ keySubterms a
  | Expression.VarK n, a, b, ha, hb => by
      simp only [keySubterms, Finset.mem_singleton] at ha hb
      subst ha; subst hb; exact Or.inl (by simp [keySubterms])
  | Expression.G0 sd, a, b, ha, hb => by
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at ha hb
      rcases ha with rfl | ha
      · exact Or.inr (by rcases hb with rfl | hb
                         · simp [keySubterms]
                         · simp [keySubterms, hb])
      · rcases hb with rfl | hb
        · exact Or.inl (by simp [keySubterms, ha])
        · exact keySubterms_linear sd a b ha hb
  | Expression.G1 sd, a, b, ha, hb => by
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at ha hb
      rcases ha with rfl | ha
      · exact Or.inr (by rcases hb with rfl | hb
                         · simp [keySubterms]
                         · simp [keySubterms, hb])
      · rcases hb with rfl | hb
        · exact Or.inl (by simp [keySubterms, ha])
        · exact keySubterms_linear sd a b ha hb
lemma keySubterms_subset_of_mem : ∀ (b a : Expression Shape.KeyS),
    a ∈ keySubterms b → keySubterms a ⊆ keySubterms b
  | Expression.VarK n, a, h => by
      simp only [keySubterms, Finset.mem_singleton] at h; subst h; exact Finset.Subset.refl _
  | Expression.G0 sd, a, h => by
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at h
      rcases h with rfl | h
      · exact Finset.Subset.refl _
      · exact Finset.Subset.trans (keySubterms_subset_of_mem sd a h)
          (by intro x hx; simp [keySubterms, hx])
  | Expression.G1 sd, a, h => by
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at h
      rcases h with rfl | h
      · exact Finset.Subset.refl _
      · exact Finset.Subset.trans (keySubterms_subset_of_mem sd a h)
          (by intro x hx; simp [keySubterms, hx])
lemma yields_mem_keySubterms {a b : Expression Shape.KeyS} (h : yields a b) :
    a ∈ keySubterms b := by
  rcases h with rfl | h
  · cases a <;> simp [keySubterms]
  · exact strictYields_mem_keySubterms _ _ h
lemma labelKeys_below : ∀ {bd : WireBundle} {ctr : ℕ} (u : labelType bd),
    LabelsBelow ctr u → ∀ k ∈ labelKeys u, keyVarsBelow (2*ctr) k
  | WireBundle.SimpleB, ctr, l, h, k, hk => by
      simp only [labelKeys, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl; exacts [h.2.1, h.2.2]
  | WireBundle.PairB o1 o2, ctr, (l1, l2), h, k, hk => by
      simp only [labelKeys, Finset.mem_union] at hk
      rcases hk with hk | hk
      · exact labelKeys_below l1 h.1 k hk
      · exact labelKeys_below l2 h.2 k hk
lemma exprKeys_gbEntry (ko ki kp : Expression Shape.KeyS) (b : BitExpr) :
    exprKeys (gbEntry ko ki kp b) = {ko, ki, kp} := by
  simp [gbEntry, exprKeys, exprKeys_key, Finset.insert_eq]
lemma extractKeys_gbEntry (ko ki kp : Expression Shape.KeyS) (b : BitExpr) :
    extractKeys (gbEntry ko ki kp b) = {kp} := by
  simp [gbEntry, extractKeys, extractKeys_key]
lemma inter_empty_of {A B : Finset (Expression Shape.KeyS)}
    (h : ∀ x, x ∈ A → x ∈ B → False) : A ∩ B = ∅ :=
  Finset.eq_empty_of_forall_not_mem
    (fun x hx => h x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2)
lemma mem_of_inter_empty {A B : Finset (Expression Shape.KeyS)} (h : A ∩ B = ∅)
    {x : Expression Shape.KeyS} (ha : x ∈ A) (hb : x ∈ B) : False := by
  have hx : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, hb⟩
  rw [h] at hx; simp at hx
lemma IndependentKeys.subset {A B : Finset (Expression Shape.KeyS)} (h : IndependentKeys B)
    (hs : A ⊆ B) : IndependentKeys A := fun k1 hk1 k2 hk2 => h k1 (hs hk1) k2 (hs hk2)
/-- Lemma 5 together with Lemma 6's condition (3).  The two must be proved by one
    induction: Lemma 5's `First` case needs (3) for the sub-circuit, and (3)'s `Compose`
    case needs Lemma 5's condition (2). -/
def L5core {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ) : Prop :=
  StronglyIndependent (gb c u ctr).2.1 ∧
  (∀ k ∈ labelKeys (gb c u ctr).2.1,
    (∀ k' ∈ exprKeys (gb c u ctr).1 ∪ labelKeys u, strictYields k k' = false) ∧
    (∃ k' ∈ extractKeys (gb c u ctr).1 ∪ labelKeys u, yields k' k)) ∧
  (∀ k ∈ exprKeys (gb c u ctr).1,
    ∃ k' ∈ extractKeys (gb c u ctr).1 ∪ labelKeys u, yields k' k)
/-- The `ε`-garbling cases (Swap/Assoc/UnAssoc): the circuit contributes no expression and
    the output labels are a rearrangement of the input labels. -/
lemma lemma5_rearrange {s t : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    (hE : exprKeys (gb c u ctr).1 = ∅)
    (hK : labelKeys (gb c u ctr).2.1 = labelKeys u)
    (hI : IndependentKeys (labelKeys u))
    (hD : DistinctLabels (gb c u ctr).2.1) :
    L5core c u ctr := by
  refine ⟨⟨by rw [hK]; exact hI, hD⟩, fun k hk => ?_,
    fun k hk => absurd hk (by rw [hE]; simp)⟩
  rw [hK] at hk
  refine ⟨fun k' hk' => ?_, ⟨k, by rw [Finset.mem_union]; exact Or.inr hk, yields_refl k⟩⟩
  rw [Finset.mem_union, hE] at hk'
  rcases hk' with h | h
  · exact absurd h (by simp)
  · exact hI k hk k' h
theorem lemma5core : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    StronglyIndependent u → LabelsBelow ctr u → L5core c u ctr := by
  intro s t c
  induction c with
  | SwapC x y =>
      rintro ⟨i1, i2⟩ ctr ⟨hind, hdist⟩ _
      refine lemma5_rearrange (by simp [gb, exprKeys]) ?_ hind ?_
      · simp only [gb, labelKeys]; exact Finset.union_comm _ _
      · exact ⟨hdist.2.1, hdist.1, by rw [Finset.inter_comm]; exact hdist.2.2⟩
  | AssocC x y z =>
      rintro ⟨i1, i2, i3⟩ ctr ⟨hind, hdist⟩ _
      obtain ⟨d1, ⟨d2, d3, h23⟩, h1_23⟩ := hdist
      simp only [labelKeys] at h1_23
      have h12 : labelKeys i1 ∩ labelKeys i2 = ∅ :=
        inter_empty_of (fun x ha hb => mem_of_inter_empty h1_23 ha (Finset.mem_union_left _ hb))
      have h13 : labelKeys i1 ∩ labelKeys i3 = ∅ :=
        inter_empty_of (fun x ha hb => mem_of_inter_empty h1_23 ha (Finset.mem_union_right _ hb))
      refine lemma5_rearrange (by simp [gb, exprKeys]) ?_ hind ?_
      · simp only [gb, labelKeys]; exact Finset.union_assoc _ _ _
      · refine ⟨⟨d1, d2, h12⟩, d3, inter_empty_of (fun x ha hb => ?_)⟩
        simp only [labelKeys, Finset.mem_union] at ha
        rcases ha with h | h
        · exact mem_of_inter_empty h13 h hb
        · exact mem_of_inter_empty h23 h hb
  | UnAssocC x y z =>
      rintro ⟨⟨i1, i2⟩, i3⟩ ctr ⟨hind, hdist⟩ _
      obtain ⟨⟨d1, d2, h12⟩, d3, h12_3⟩ := hdist
      simp only [labelKeys] at h12_3
      have h13 : labelKeys i1 ∩ labelKeys i3 = ∅ :=
        inter_empty_of (fun x ha hb => mem_of_inter_empty h12_3 (Finset.mem_union_left _ ha) hb)
      have h23 : labelKeys i2 ∩ labelKeys i3 = ∅ :=
        inter_empty_of (fun x ha hb => mem_of_inter_empty h12_3 (Finset.mem_union_right _ ha) hb)
      refine lemma5_rearrange (by simp [gb, exprKeys]) ?_ hind ?_
      · simp only [gb, labelKeys]; exact (Finset.union_assoc _ _ _).symm
      · refine ⟨d1, ⟨d2, d3, h23⟩, inter_empty_of (fun x ha hb => ?_)⟩
        simp only [labelKeys, Finset.mem_union] at hb
        rcases hb with h | h
        · exact mem_of_inter_empty h12 ha h
        · exact mem_of_inter_empty h13 ha h
  | DupC =>
      intro l ctr hSI _
      obtain ⟨hind, hdist⟩ := hSI
      simp only [labelKeys] at hind
      have hm0 : l.key0 ∈ labelKeys (b := WireBundle.SimpleB) l := by simp [labelKeys]
      have hm1 : l.key1 ∈ labelKeys (b := WireBundle.SimpleB) l := by simp [labelKeys]
      have h00 : strictYields l.key0 l.key0 = false := strictYields_irrefl _
      have h11 : strictYields l.key1 l.key1 = false := strictYields_irrefl _
      have h01 : strictYields l.key0 l.key1 = false := hind _ hm0 _ hm1
      have h10 : strictYields l.key1 l.key0 = false := hind _ hm1 _ hm0
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, fun k hk => absurd hk (by simp [gb, exprKeys])⟩
      · -- IndependentKeys of the four derived keys
        intro x hx y hy
        simp only [gb, labelKeys, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton] at hx hy
        rcases hx with (rfl | rfl) | (rfl | rfl) <;> rcases hy with (rfl | rfl) | (rfl | rfl) <;>
          first
          | exact (sy_GG4 h00).1 | exact (sy_GG4 h00).2.1
          | exact (sy_GG4 h00).2.2.1 | exact (sy_GG4 h00).2.2.2
          | exact (sy_GG4 h01).1 | exact (sy_GG4 h01).2.1
          | exact (sy_GG4 h01).2.2.1 | exact (sy_GG4 h01).2.2.2
          | exact (sy_GG4 h10).1 | exact (sy_GG4 h10).2.1
          | exact (sy_GG4 h10).2.2.1 | exact (sy_GG4 h10).2.2.2
          | exact (sy_GG4 h11).1 | exact (sy_GG4 h11).2.1
          | exact (sy_GG4 h11).2.2.1 | exact (sy_GG4 h11).2.2.2
      · simpa [gb, DistinctLabels] using hdist
      · simpa [gb, DistinctLabels] using hdist
      · simp [gb, labelKeys, inter_empty_of]
      · -- the two conditions
        intro k hk
        simp only [gb, labelKeys, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton] at hk
        refine ⟨fun k' hk' => ?_, ?_⟩
        · rw [Finset.mem_union] at hk'
          rcases hk' with h | h
          · exact absurd h (by simp [gb, exprKeys])
          · simp only [labelKeys, Finset.mem_insert, Finset.mem_singleton] at h
            rcases hk with (rfl | rfl) | (rfl | rfl) <;> rcases h with rfl | rfl <;>
              first
              | exact sy_G0_k h00 | exact sy_G0_k h01 | exact sy_G0_k h10 | exact sy_G0_k h11
              | exact sy_G1_k h00 | exact sy_G1_k h01 | exact sy_G1_k h10 | exact sy_G1_k h11
        · rcases hk with (rfl | rfl) | (rfl | rfl)
          · exact ⟨l.key0, by rw [Finset.mem_union]; exact Or.inr hm0, Or.inr (sy_G0_self _)⟩
          · exact ⟨l.key1, by rw [Finset.mem_union]; exact Or.inr hm1, Or.inr (sy_G0_self _)⟩
          · exact ⟨l.key0, by rw [Finset.mem_union]; exact Or.inr hm0, Or.inr (sy_G1_self _)⟩
          · exact ⟨l.key1, by rw [Finset.mem_union]; exact Or.inr hm1, Or.inr (sy_G1_self _)⟩
  | NandC =>
      rintro ⟨li, lj⟩ ctr ⟨_, _⟩ hbelow
      simp only [LabelsBelow] at hbelow
      obtain ⟨⟨_, hi0, hi1⟩, ⟨_, hj0, hj1⟩⟩ := hbelow
      -- the output label consists of the two fresh atomic keys
      have hkeys : labelKeys (gb Circuit.NandC (li, lj) ctr).2.1
          = {Expression.VarK (2*ctr), Expression.VarK (2*ctr+1)} := by simp [gb, labelKeys]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · intro x _ y hy
        rw [hkeys, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> exact sy_to_varK _ _
      · simp [gb, DistinctLabels]
      · intro k hk
        rw [hkeys, Finset.mem_insert, Finset.mem_singleton] at hk
        -- every old key is below 2*ctr, and the fresh keys are atomic
        have hC : ∀ k' ∈ exprKeys (gb Circuit.NandC (li, lj) ctr).1,
            k' = li.key0 ∨ k' = li.key1 ∨ k' = lj.key0 ∨ k' = lj.key1 ∨
            k' = Expression.VarK (2*ctr) ∨ k' = Expression.VarK (2*ctr+1) := by
          intro k' h
          simp [gb, gbEntry, exprKeys, exprKeys_key] at h
          tauto
        have hL : ∀ k' ∈ labelKeys (b := WireBundle.PairB WireBundle.SimpleB WireBundle.SimpleB)
            (li, lj), k' = li.key0 ∨ k' = li.key1 ∨ k' = lj.key0 ∨ k' = lj.key1 := by
          intro k' h
          simp [labelKeys] at h
          tauto
        have hold : ∀ (m : ℕ), 2*ctr ≤ m → ∀ k' ∈ exprKeys (gb Circuit.NandC (li, lj) ctr).1
            ∪ labelKeys (b := WireBundle.PairB WireBundle.SimpleB WireBundle.SimpleB) (li, lj),
            strictYields (Expression.VarK m) k' = false := by
          intro m hm k' hk'
          have hlab : ∀ kk : Expression Shape.KeyS, keyVarsBelow (2*ctr) kk →
              strictYields (Expression.VarK m) kk = false := fun kk hkk => sy_varK_of_below hkk hm
          rw [Finset.mem_union] at hk'
          rcases hk' with h | h
          · rcases hC k' h with rfl|rfl|rfl|rfl|rfl|rfl <;>
              first | exact hlab _ hi0 | exact hlab _ hi1 | exact hlab _ hj0 | exact hlab _ hj1
                    | exact sy_to_varK _ _
          · rcases hL k' h with rfl|rfl|rfl|rfl <;>
              first | exact hlab _ hi0 | exact hlab _ hi1 | exact hlab _ hj0 | exact hlab _ hj1
        have hpart : ∀ (k0 : Expression Shape.KeyS),
            k0 = Expression.VarK (2*ctr) ∨ k0 = Expression.VarK (2*ctr+1) →
            k0 ∈ extractKeys (gb Circuit.NandC (li, lj) ctr).1 := by
          intro k0 h
          rcases h with rfl | rfl <;> simp [gb, gbEntry, extractKeys, extractKeys_key]
        rcases hk with rfl | rfl
        · exact ⟨hold _ (by omega), _, Finset.mem_union_left _ (hpart _ (Or.inl rfl)),
            yields_refl _⟩
        · exact ⟨hold _ (by omega), _, Finset.mem_union_left _ (hpart _ (Or.inr rfl)),
            yields_refl _⟩
      · -- every key used by the table is a label key or one of the two fresh keys
        intro k hk
        have hC : ∀ k' ∈ exprKeys (gb Circuit.NandC (li, lj) ctr).1,
            k' = li.key0 ∨ k' = li.key1 ∨ k' = lj.key0 ∨ k' = lj.key1 ∨
            k' = Expression.VarK (2*ctr) ∨ k' = Expression.VarK (2*ctr+1) := by
          intro k' h
          simp [gb, gbEntry, exprKeys, exprKeys_key] at h
          tauto
        have hpart : ∀ (k0 : Expression Shape.KeyS),
            k0 = Expression.VarK (2*ctr) ∨ k0 = Expression.VarK (2*ctr+1) →
            k0 ∈ extractKeys (gb Circuit.NandC (li, lj) ctr).1 := by
          intro k0 h
          rcases h with rfl | rfl <;> simp [gb, gbEntry, extractKeys, extractKeys_key]
        have hlab : ∀ k0 : Expression Shape.KeyS,
            (k0 = li.key0 ∨ k0 = li.key1 ∨ k0 = lj.key0 ∨ k0 = lj.key1) →
            k0 ∈ labelKeys (b := WireBundle.PairB WireBundle.SimpleB WireBundle.SimpleB)
              (li, lj) := by
          intro k0 h; simp only [labelKeys, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton]; tauto
        rcases hC k hk with h|h|h|h|h|h
        · exact ⟨k, Finset.mem_union_right _ (hlab k (by tauto)), yields_refl _⟩
        · exact ⟨k, Finset.mem_union_right _ (hlab k (by tauto)), yields_refl _⟩
        · exact ⟨k, Finset.mem_union_right _ (hlab k (by tauto)), yields_refl _⟩
        · exact ⟨k, Finset.mem_union_right _ (hlab k (by tauto)), yields_refl _⟩
        · exact ⟨k, Finset.mem_union_left _ (hpart k (Or.inl h)), yields_refl _⟩
        · exact ⟨k, Finset.mem_union_left _ (hpart k (Or.inr h)), yields_refl _⟩
  | ComposeC c1 c2 ih1 ih2 =>
      intro u ctr hSI hbelow
      obtain ⟨hSIw, hw, hL3w⟩ := ih1 u ctr hSI hbelow
      have hbw : LabelsBelow (gb c1 u ctr).2.2 (gb c1 u ctr).2.1 := gb_labels_below c1 u ctr hbelow
      obtain ⟨hSIv, hv, hL3v⟩ := ih2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2 hSIw hbw
      have hE : exprKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = exprKeys (gb c1 u ctr).1
            ∪ exprKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by simp [gb, exprKeys]
      have hX : extractKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = extractKeys (gb c1 u ctr).1
            ∪ extractKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by simp [gb, extractKeys]
      have hV : (gb (Circuit.ComposeC c1 c2) u ctr).2.1
          = (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).2.1 := by simp [gb]
      refine ⟨by rw [hV]; exact hSIv, ?_, ?_⟩
      ·
        intro k hk
        rw [hV] at hk
        obtain ⟨hQ1, hQ2⟩ := hv k hk
        -- the common argument: an "old" key cannot be a descendant of `k`
        have key : ∀ k'' : Expression Shape.KeyS, keyVarsBelow (2*(gb c1 u ctr).2.2) k'' →
            (∀ k0 ∈ labelKeys (gb c1 u ctr).2.1, strictYields k0 k'' = false) →
            strictYields k k'' = false := by
          intro k'' hb'' hlab
          cases hb : strictYields k k''
          · rfl
          · exfalso
            obtain ⟨k0, hk0, hy0⟩ := hQ2
            rw [Finset.mem_union] at hk0
            rcases hk0 with h0 | h0
            · obtain ⟨m, hmeq, hm1, _⟩ := gb_parts_fresh c2 _ _ _ h0
              subst hmeq
              have hmem : Expression.VarK m ∈ keySubterms k'' :=
                keySubterms_subset_of_mem k'' k (strictYields_mem_keySubterms _ _ hb)
                  (yields_mem_keySubterms hy0)
              exact absurd (hb'' m hmem) (by omega)
            · have hcon := hlab k0 h0
              rw [yields_strictYields_trans hy0 hb] at hcon
              exact Bool.noConfusion hcon
        refine ⟨fun k' hk' => ?_, ?_⟩
        · simp only [hE, Finset.mem_union] at hk'
          rcases hk' with (h | h) | h
          · refine key k' (fun m hm => ?_) (fun k0 hk0 => (hw k0 hk0).1 k' ?_)
            · exact gb_circuit_below c1 u ctr hbelow m
                (keySubterms_subset_of_mem_exprKeys _ k' h hm)
            · rw [Finset.mem_union]; exact Or.inl h
          · exact hQ1 k' (by rw [Finset.mem_union]; exact Or.inl h)
          · refine key k' (fun m hm => ?_) (fun k0 hk0 => (hw k0 hk0).1 k' ?_)
            · have := labelKeys_below u hbelow k' h m hm
              have hmono := gb_ctr_mono c1 u ctr
              omega
            · rw [Finset.mem_union]; exact Or.inr h
        · obtain ⟨k0, hk0, hy0⟩ := hQ2
          rw [Finset.mem_union] at hk0
          rcases hk0 with h0 | h0
          · exact ⟨k0, by simp only [hX, Finset.mem_union]; exact Or.inl (Or.inr h0), hy0⟩
          · obtain ⟨k1, hk1, hy1⟩ := (hw k0 h0).2
            rw [Finset.mem_union] at hk1
            rcases hk1 with h1 | h1
            · exact ⟨k1, by simp only [hX, Finset.mem_union]; exact Or.inl (Or.inl h1),
                yields_trans hy1 hy0⟩
            · exact ⟨k1, by simp only [hX, Finset.mem_union]; exact Or.inr h1,
                yields_trans hy1 hy0⟩
      ·
          intro k hk
          simp only [hE, Finset.mem_union] at hk
          rcases hk with h | h
          · obtain ⟨k', hk', hy⟩ := hL3w k h
            rw [Finset.mem_union] at hk'
            rcases hk' with h' | h'
            · exact ⟨k', by simp only [hX, Finset.mem_union]; exact Or.inl (Or.inl h'), hy⟩
            · exact ⟨k', by simp only [hX, Finset.mem_union]; exact Or.inr h', hy⟩
          · obtain ⟨k', hk', hy⟩ := hL3v k h
            rw [Finset.mem_union] at hk'
            rcases hk' with h' | h'
            · exact ⟨k', by simp only [hX, Finset.mem_union]; exact Or.inl (Or.inr h'), hy⟩
            · obtain ⟨k'', hk'', hy'⟩ := (hw k' h').2
              rw [Finset.mem_union] at hk''
              rcases hk'' with h'' | h''
              · exact ⟨k'', by simp only [hX, Finset.mem_union]; exact Or.inl (Or.inl h''),
                  yields_trans hy' hy⟩
              · exact ⟨k'', by simp only [hX, Finset.mem_union]; exact Or.inr h'',
                  yields_trans hy' hy⟩
  | FirstC c wb ih =>
      rintro ⟨u1, u2⟩ ctr ⟨hindU, hd1, hd2, hdisj⟩ ⟨hb1, hb2⟩
      have hSI1 : StronglyIndependent u1 :=
        ⟨hindU.subset (by intro x hx; simp only [labelKeys, Finset.mem_union]; exact Or.inl hx), hd1⟩
      obtain ⟨hSIv, hv, hL3⟩ := ih u1 ctr hSI1 hb1
      have hE : exprKeys (gb (Circuit.FirstC c wb) (u1, u2) ctr).1
          = exprKeys (gb c u1 ctr).1 := by simp [gb]
      have hX : extractKeys (gb (Circuit.FirstC c wb) (u1, u2) ctr).1
          = extractKeys (gb c u1 ctr).1 := by simp [gb]
      have hV : (gb (Circuit.FirstC c wb) (u1, u2) ctr).2.1 = ((gb c u1 ctr).2.1, u2) := by
        simp [gb]
      have hmemU : ∀ x, x ∈ labelKeys u1 ∨ x ∈ labelKeys u2 →
          x ∈ labelKeys (b := WireBundle.PairB _ _) (u1, u2) := by
        intro x h; simp only [labelKeys, Finset.mem_union]; exact h
      -- a key of `u2` cannot contain a fresh variable
      have hfresh : ∀ x ∈ labelKeys u2, ∀ m, 2*ctr ≤ m → Expression.VarK m ∉ keySubterms x := by
        intro x hx m hm hc
        exact absurd (labelKeys_below u2 hb2 x hx m hc) (by omega)
      -- Fact X : nothing in `v₁` yields anything in `u₂`
      have factX : ∀ k ∈ labelKeys (gb c u1 ctr).2.1, ∀ k' ∈ labelKeys u2,
          strictYields k k' = false := by
        intro k hk k' hk'
        cases hb : strictYields k k'
        · rfl
        · exfalso
          obtain ⟨k0, hk0, hy0⟩ := (hv k hk).2
          rw [Finset.mem_union] at hk0
          rcases hk0 with h0 | h0
          · obtain ⟨m, rfl, hm1, _⟩ := gb_parts_fresh c u1 ctr _ h0
            exact hfresh k' hk' m hm1
              (keySubterms_subset_of_mem k' k (strictYields_mem_keySubterms _ _ hb)
                (yields_mem_keySubterms hy0))
          · have := hindU k0 (hmemU _ (Or.inl h0)) k' (hmemU _ (Or.inr hk'))
            rw [yields_strictYields_trans hy0 hb] at this; exact Bool.noConfusion this
      -- Fact Y : nothing in `u₂` yields anything in `v₁`
      have factY : ∀ k ∈ labelKeys (gb c u1 ctr).2.1, ∀ k' ∈ labelKeys u2,
          strictYields k' k = false := by
        intro k hk k' hk'
        cases hb : strictYields k' k
        · rfl
        · exfalso
          obtain ⟨k0, hk0, hy0⟩ := (hv k hk).2
          rw [Finset.mem_union] at hk0
          rcases hk0 with h0 | h0
          · obtain ⟨m, rfl, hm1, _⟩ := gb_parts_fresh c u1 ctr _ h0
            rcases keySubterms_linear k _ k' (yields_mem_keySubterms hy0)
              (strictYields_mem_keySubterms _ _ hb) with hL | hL
            · exact hfresh k' hk' m hm1 hL
            · simp only [keySubterms, Finset.mem_singleton] at hL
              exact hfresh k' hk' m hm1 (by rw [hL]; simp [keySubterms])
          · rcases hy0 with rfl | hy0
            · have hcon := hindU k' (hmemU _ (Or.inr hk')) _ (hmemU _ (Or.inl h0))
              rw [hb] at hcon; exact Bool.noConfusion hcon
            · rcases strictYields_comparable k k0 k' hy0 hb with heq | hc | hc
              · subst heq; exact mem_of_inter_empty hdisj h0 hk'
              · have := hindU k0 (hmemU _ (Or.inl h0)) k' (hmemU _ (Or.inr hk'))
                rw [hc] at this; exact Bool.noConfusion this
              · have := hindU k' (hmemU _ (Or.inr hk')) k0 (hmemU _ (Or.inl h0))
                rw [hc] at this; exact Bool.noConfusion this
      have factZ : labelKeys (gb c u1 ctr).2.1 ∩ labelKeys u2 = ∅ := by
        refine inter_empty_of (fun x hx1 hx2 => ?_)
        obtain ⟨k0, hk0, hy0⟩ := (hv x hx1).2
        rw [Finset.mem_union] at hk0
        rcases hk0 with h0 | h0
        · obtain ⟨m, rfl, hm1, _⟩ := gb_parts_fresh c u1 ctr _ h0
          exact hfresh x hx2 m hm1 (yields_mem_keySubterms hy0)
        · rcases hy0 with rfl | hy0
          · exact mem_of_inter_empty hdisj h0 hx2
          · have hcon := hindU k0 (hmemU _ (Or.inl h0)) x (hmemU _ (Or.inr hx2))
            rw [hy0] at hcon; exact Bool.noConfusion hcon
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hV]
        intro x hx y hy
        simp only [labelKeys, Finset.mem_union] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact hSIv.1 x hx y hy
        · exact factX x hx y hy
        · exact factY y hy x hx
        · exact hindU x (hmemU _ (Or.inr hx)) y (hmemU _ (Or.inr hy))
      · rw [hV]; exact ⟨hSIv.2, hd2, factZ⟩
      · intro k hk
        rw [hV] at hk
        simp only [labelKeys, Finset.mem_union] at hk
        rcases hk with hk | hk
        · refine ⟨fun k' hk' => ?_, ?_⟩
          · simp only [hE, labelKeys, Finset.mem_union] at hk'
            rcases hk' with h | h | h
            · exact (hv k hk).1 k' (by rw [Finset.mem_union]; exact Or.inl h)
            · exact (hv k hk).1 k' (by rw [Finset.mem_union]; exact Or.inr h)
            · exact factX k hk k' h
          · obtain ⟨k', hk', hy⟩ := (hv k hk).2
            rw [Finset.mem_union] at hk'
            rcases hk' with h | h
            · exact ⟨k', by rw [hX, Finset.mem_union]; exact Or.inl h, hy⟩
            · exact ⟨k', by rw [hX]; simp only [Finset.mem_union, labelKeys]; tauto, hy⟩
        · refine ⟨fun k' hk' => ?_,
            ⟨k, by simp only [Finset.mem_union, labelKeys]; tauto, yields_refl k⟩⟩
          simp only [hE, labelKeys, Finset.mem_union] at hk'
          rcases hk' with h | h | h
          · -- `k` comes from `u₂`, `k'` from the garbled sub-circuit
            cases hb : strictYields k k'
            · rfl
            · exfalso
              obtain ⟨r, hr, hyr⟩ := hL3 k' h
              rw [Finset.mem_union] at hr
              rcases hr with hr | hr
              · obtain ⟨m, rfl, hm1, _⟩ := gb_parts_fresh c u1 ctr _ hr
                rcases keySubterms_linear k' _ k (yields_mem_keySubterms hyr)
                  (strictYields_mem_keySubterms _ _ hb) with hL | hL
                · exact hfresh k hk m hm1 hL
                · simp only [keySubterms, Finset.mem_singleton] at hL
                  exact hfresh k hk m hm1 (by rw [hL]; simp [keySubterms])
              · rcases hyr with rfl | hyr
                · have hcon := hindU k (hmemU _ (Or.inr hk)) _ (hmemU _ (Or.inl hr))
                  rw [hb] at hcon; exact Bool.noConfusion hcon
                · rcases strictYields_comparable k' r k hyr hb with heq | hc | hc
                  · subst heq; exact mem_of_inter_empty hdisj hr hk
                  · have hcon := hindU r (hmemU _ (Or.inl hr)) k (hmemU _ (Or.inr hk))
                    rw [hc] at hcon; exact Bool.noConfusion hcon
                  · have hcon := hindU k (hmemU _ (Or.inr hk)) r (hmemU _ (Or.inl hr))
                    rw [hc] at hcon; exact Bool.noConfusion hcon
          · exact hindU k (hmemU _ (Or.inr hk)) k' (hmemU _ (Or.inl h))
          · exact hindU k (hmemU _ (Or.inr hk)) k' (hmemU _ (Or.inr h))
      · intro k hk
        rw [hE] at hk
        obtain ⟨k', hk', hy⟩ := hL3 k hk
        rw [Finset.mem_union] at hk'
        rcases hk' with h' | h'
        · exact ⟨k', by rw [hX, Finset.mem_union]; exact Or.inl h', hy⟩
        · exact ⟨k', by rw [hX]; simp only [Finset.mem_union, labelKeys]; tauto, hy⟩
/-- **LM18 Lemma 5.** -/
theorem lemma5 : Lemma5 := by
  intro s t c u ctr hSI hb
  exact ⟨(lemma5core c u ctr hSI hb).1, (lemma5core c u ctr hSI hb).2.1⟩
/-- **LM18 Lemma 6, condition (3):** every key a garbled circuit uses is yielded by one
    that appears as a part of `(C̃, u)`.  Conditions (1) and (2) of Lemma 6 need their own
    induction and are still open. -/
theorem lemma6_cond3 {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ)
    (hSI : StronglyIndependent u) (hb : LabelsBelow ctr u) :
    ∀ k ∈ encKeys (gb c u ctr).1,
      ∃ k' ∈ extractKeys (gb c u ctr).1 ∪ labelKeys u, yields k' k := by
  intro k hk
  refine (lemma5core c u ctr hSI hb).2.2 k ?_
  rw [exprKeys_eq_extractKeys_union_encKeys, Finset.mem_union]
  exact Or.inr hk

/-! ## LM18 Lemma 6 -/

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

/-! ## Keys of the whole garbled expression -/

lemma extractKeys_bit : ∀ e : Expression Shape.BitS, extractKeys e = ∅
  | Expression.BitE _ => rfl
lemma extractKeys_maskedLabelToExpr : ∀ {b : WireBundle} (m : maskedLabelType b),
    extractKeys (maskedLabelToExpr m) = ∅
  | WireBundle.SimpleB, m => extractKeys_bit m
  | WireBundle.PairB o1 o2, (m1, m2) => by
      simp only [maskedLabelToExpr, extractKeys]
      rw [extractKeys_maskedLabelToExpr m1, extractKeys_maskedLabelToExpr m2]
      simp
lemma extractKeys_gEnc : ∀ {b : WireBundle} (u : labelType b) (x : bundleBool b),
    extractKeys (encodedLabelToExpr (gEnc u x)) ⊆ labelKeys u
  | WireBundle.SimpleB, l, x => by
      cases x <;>
        simp [gEnc, encodedLabelToExpr, extractKeys, extractKeys_key, labelKeys]
  | WireBundle.PairB o1 o2, (l1, l2), (x1, x2) => by
      simp only [gEnc, encodedLabelToExpr, extractKeys, labelKeys]
      exact Finset.union_subset_union (extractKeys_gEnc l1 x1) (extractKeys_gEnc l2 x2)
lemma makeLabels_atomic : ∀ (b : WireBundle) (i : ℕ),
    ∀ k ∈ labelKeys (makeLabels b i).1, isAtomicKey k = true
  | WireBundle.SimpleB, i, k, hk => by
      simp only [makeLabels, labelKeys, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> rfl
  | WireBundle.PairB o1 o2, i, k, hk => by
      simp only [makeLabels, labelKeys, Finset.mem_union] at hk
      rcases hk with h | h
      · exact makeLabels_atomic o1 i k h
      · exact makeLabels_atomic o2 (makeLabels o1 i).2 k h
/-- **LM18 Lemma 4, for the whole garbled expression.**  Every key appearing as a *part* of
    `Garble(C,x)` is atomic: the garbled tables contribute only the fresh `NAnd` output
    keys (`lemma4`), the encoded input contributes input-wire label keys (atomic by
    `makeLabels`), and the output masks contribute no keys at all. -/
theorem lemma4_garble {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    ∀ k ∈ extractKeys (Garble c x), isAtomicKey k = true := by
  intro k hk
  simp only [Garble, extractKeys, Finset.mem_union] at hk
  rcases hk with h | h | h
  · exact lemma4 c _ _ k h
  · exact makeLabels_atomic s 0 k (extractKeys_gEnc _ x h)
  · exact absurd h (by rw [extractKeys_maskedLabelToExpr]; simp)
/-- The same for the adversary's views, which only hide more. -/
theorem lemma4_adversaryView {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    ∀ k ∈ extractKeys (adversaryView (Garble c x)), isAtomicKey k = true := by
  intro k hk
  exact lemma4_garble c x k
    (keyPartsMonotone _ _ (hideEncryptedSmallerValue _ _) hk)

/-! ## The garbled expression's fixpoint -/

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

/-! ## Stage-wise consequences of Lemmas 5 and 6 -/
/-- The hypotheses Lemmas 5 and 6 need are inherited by every stage. -/
lemma GbStage.hyps {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') (hSI : StronglyIndependent u) (hb : LabelsBelow ctr u) :
    StronglyIndependent u' ∧ LabelsBelow ctr' u' := by
  induction h with
  | refl => exact ⟨hSI, hb⟩
  | composeL _ ih => exact ih hSI hb
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' hh ih =>
      exact ih (lemma5core c1 u ctr hSI hb).1 (gb_labels_below c1 u ctr hb)
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih =>
      refine ih ⟨hSI.1.subset ?_, hSI.2.1⟩ hb.1
      intro x hx; simp only [labelKeys, Finset.mem_union]; exact Or.inl hx
/-- Every key of a stage's input labels is yielded by a key that appears as a *part* of the
    global garbling, or by one of the global input labels.  (LM18 Lemma 5(2), propagated.) -/
lemma GbStage.labelKeys_yielded {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s}
    {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') (hSI : StronglyIndependent u) (hb : LabelsBelow ctr u) :
    ∀ k ∈ labelKeys u', ∃ r ∈ extractKeys (gb c u ctr).1 ∪ labelKeys u, yields r k := by
  induction h with
  | refl => exact fun k hk => ⟨k, Finset.mem_union_right _ hk, yields_refl k⟩
  | @composeL a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      intro k hk
      obtain ⟨r, hr, hy⟩ := ih hSI hb k hk
      rw [Finset.mem_union] at hr
      refine ⟨r, ?_, hy⟩
      have he : extractKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = extractKeys (gb c1 u ctr).1
            ∪ extractKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp [gb, extractKeys]
      simp only [he, Finset.mem_union]
      tauto
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      intro k hk
      obtain ⟨r, hr, hy⟩ := ih (lemma5core c1 u ctr hSI hb).1 (gb_labels_below c1 u ctr hb) k hk
      rw [Finset.mem_union] at hr
      have he : extractKeys (gb (Circuit.ComposeC c1 c2) u ctr).1
          = extractKeys (gb c1 u ctr).1
            ∪ extractKeys (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp [gb, extractKeys]
      rcases hr with hr | hr
      · exact ⟨r, by simp only [he, Finset.mem_union]; tauto, hy⟩
      · obtain ⟨r2, hr2, hy2⟩ := ((lemma5core c1 u ctr hSI hb).2.1 r hr).2
        exact ⟨r2, by simp only [he, Finset.mem_union] at hr2 ⊢; tauto, yields_trans hy2 hy⟩
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih =>
      intro k hk
      obtain ⟨r, hr, hy⟩ := ih ⟨hSI.1.subset (by
        intro x hx; simp only [labelKeys, Finset.mem_union]; exact Or.inl hx), hSI.2.1⟩ hb.1 k hk
      rw [Finset.mem_union] at hr
      have he : extractKeys (gb (Circuit.FirstC c wb) (u1, u2) ctr).1
          = extractKeys (gb c u1 ctr).1 := by simp [gb, extractKeys]
      refine ⟨r, ?_, hy⟩
      simp only [he, Finset.mem_union, labelKeys]
      tauto

end PRG
