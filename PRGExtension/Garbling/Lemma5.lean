import PRGExtension.Garbling.Independence

/-!
# LM18 Lemma 5 (and Lemma 6's condition (3))

`Gb` turns strongly independent input labels into strongly independent output labels, and
every output key (1) has no strict PRG-descendant among the keys of `(C̃, u)` and (2) is
yielded by some key appearing as a *part* of `(C̃, u)`.

Lemma 5 and Lemma 6's condition (3) are proved by a **single** induction (`lemma5core`):
Lemma 5's `First` case needs (3) for the sub-circuit, and (3)'s `Compose` case needs
Lemma 5's condition (2).  They cannot be separated.
-/

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

end PRG
