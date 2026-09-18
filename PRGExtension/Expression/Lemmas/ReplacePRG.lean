import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Lemmas.HideEncrypted

/-!
# Idealising one PRG node

`replacePRG (K_t) i j` identifies `G0(K_t)` and `G1(K_t)` with two fresh independent key
variables.  LM18 uses this (Lemma 2 / [Mic09, Cor. 1]) to move a key expression with
non-atomic roots to one with atomic roots, which is what makes the IND-CPA reduction
applicable.  This file collects the symbolic bookkeeping.

`exprKeys` and `extractKeys` transport as images; `keySubterms` only shrinks (a subterm
`K_t` disappears).  `unrp` is a left inverse on keys avoiding the two fresh variables,
which gives injectivity, and injectivity in turn gives two things the hop needs:
idealisation never *creates* an ancestor relation (`strictYields_rp_reflect`), and it
commutes with hiding one key (`rp_hideSelected`).  `keySize_rp` is the termination
measure: each hop shortens the chain of the key being hidden by exactly one.
-/

namespace PRG

open Expression

/-- Abbreviation: idealising the PRG node above the atomic seed `K_t`. -/
abbrev rp (t i j : ℕ) {s : Shape} (e : Expression s) : Expression s :=
  replacePRG (Expression.VarK t) (i) (j) e

@[simp] lemma rp_varK (t i j n : ℕ) : rp t i j (Expression.VarK n) = Expression.VarK n := rfl

lemma rp_G0 (t i j : ℕ) (c : Expression Shape.KeyS) :
    rp t i j (Expression.G0 c)
      = if c = Expression.VarK t then Expression.VarK i else Expression.G0 (rp t i j c) := by
  simp only [rp, replacePRG, beq_iff_eq]

lemma rp_G1 (t i j : ℕ) (c : Expression Shape.KeyS) :
    rp t i j (Expression.G1 c)
      = if c = Expression.VarK t then Expression.VarK j else Expression.G1 (rp t i j c) := by
  simp only [rp, replacePRG, beq_iff_eq]

/-- `Keys` transports as an image. -/
lemma exprKeys_rp (t i j : ℕ) : ∀ {s : Shape} (e : Expression s),
    exprKeys (rp t i j e) = (exprKeys e).image (rp t i j) := by
  intro s e
  induction e with
  | VarK n => simp [exprKeys]
  | G0 c _ =>
      rw [rp_G0]; split_ifs with h
      · subst h; simp [exprKeys, rp_G0]
      · simp [exprKeys, rp_G0, h]
  | G1 c _ =>
      rw [rp_G1]; split_ifs with h
      · subst h; simp [exprKeys, rp_G1]
      · simp [exprKeys, rp_G1, h]
  | Pair p1 p2 ih1 ih2 => simp [replacePRG, exprKeys, ih1, ih2, Finset.image_union]
  | Perm b p1 p2 _ ih1 ih2 => simp [replacePRG, exprKeys, ih1, ih2, Finset.image_union]
  | Enc k e ihk ihe => simp [replacePRG, exprKeys, ihk, ihe, Finset.image_union]
  | Hidden k ih => simp [replacePRG, exprKeys, ih]
  | BitE b => simp [replacePRG, exprKeys]
  | Eps => simp [replacePRG, exprKeys]

/-- `Parts` transports as an image. -/
lemma extractKeys_rp (t i j : ℕ) : ∀ {s : Shape} (e : Expression s),
    extractKeys (rp t i j e) = (extractKeys e).image (rp t i j) := by
  intro s e
  induction e with
  | VarK n => simp [extractKeys]
  | G0 c _ =>
      rw [rp_G0]; split_ifs with h
      · subst h; simp [extractKeys, rp_G0]
      · simp [extractKeys, rp_G0, h]
  | G1 c _ =>
      rw [rp_G1]; split_ifs with h
      · subst h; simp [extractKeys, rp_G1]
      · simp [extractKeys, rp_G1, h]
  | Pair p1 p2 ih1 ih2 => simp [replacePRG, extractKeys, ih1, ih2, Finset.image_union]
  | Perm b p1 p2 _ ih1 ih2 => simp [replacePRG, extractKeys, ih1, ih2, Finset.image_union]
  | Enc k e _ ihe => simp [replacePRG, extractKeys, ihe]
  | Hidden k ih => simp [replacePRG, extractKeys]
  | BitE b => simp [replacePRG, extractKeys]
  | Eps => simp [replacePRG, extractKeys]

/-- Hiding never creates key subterms, and neither does idealisation. -/
lemma keySubterms_rp (t i j : ℕ) : ∀ {s : Shape} (e : Expression s),
    keySubterms (rp t i j e) ⊆ (keySubterms e).image (rp t i j) := by
  intro s e
  induction e with
  | VarK n => simp [keySubterms]
  | G0 c ih =>
      rw [rp_G0]; split_ifs with h
      · subst h
        intro x hx
        simp only [keySubterms, Finset.mem_singleton] at hx
        subst hx
        simp only [Finset.mem_image]
        exact ⟨Expression.G0 (Expression.VarK t), by simp [keySubterms], by simp [rp_G0]⟩
      · intro x hx
        simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hx
        simp only [Finset.mem_image]
        rcases hx with hx | hx
        · exact ⟨Expression.G0 c, by simp [keySubterms], by rw [hx, rp_G0, if_neg h]⟩
        · obtain ⟨y, hy, hy2⟩ := Finset.mem_image.mp (ih hx)
          exact ⟨y, by simp [keySubterms, hy], hy2⟩
  | G1 c ih =>
      rw [rp_G1]; split_ifs with h
      · subst h
        intro x hx
        simp only [keySubterms, Finset.mem_singleton] at hx
        subst hx
        simp only [Finset.mem_image]
        exact ⟨Expression.G1 (Expression.VarK t), by simp [keySubterms], by simp [rp_G1]⟩
      · intro x hx
        simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hx
        simp only [Finset.mem_image]
        rcases hx with hx | hx
        · exact ⟨Expression.G1 c, by simp [keySubterms], by rw [hx, rp_G1, if_neg h]⟩
        · obtain ⟨y, hy, hy2⟩ := Finset.mem_image.mp (ih hx)
          exact ⟨y, by simp [keySubterms, hy], hy2⟩
  | Pair p1 p2 ih1 ih2 =>
      simp only [replacePRG, keySubterms, Finset.image_union]
      exact Finset.union_subset_union ih1 ih2
  | Perm b p1 p2 _ ih1 ih2 =>
      simp only [replacePRG, keySubterms, Finset.image_union]
      exact Finset.union_subset_union ih1 ih2
  | Enc k e ihk ihe =>
      simp only [replacePRG, keySubterms, Finset.image_union]
      exact Finset.union_subset_union ihk ihe
  | Hidden k ih => simp only [replacePRG, keySubterms]; exact ih
  | BitE b => simp [replacePRG, keySubterms]
  | Eps => simp [replacePRG, keySubterms]

/-- A left inverse of `rp` on keys that avoid the two fresh variables. -/
def unrp (t i j : ℕ) : Expression Shape.KeyS → Expression Shape.KeyS
  | Expression.VarK n =>
      if n = i then Expression.G0 (Expression.VarK t)
      else if n = j then Expression.G1 (Expression.VarK t)
      else Expression.VarK n
  | Expression.G0 c => Expression.G0 (unrp t i j c)
  | Expression.G1 c => Expression.G1 (unrp t i j c)

lemma unrp_rp (t i j : ℕ) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t) :
    ∀ k : Expression Shape.KeyS, Expression.VarK i ∉ keySubterms k →
      Expression.VarK j ∉ keySubterms k → unrp t i j (rp t i j k) = k
  | Expression.VarK n, hi, hj => by
      simp only [keySubterms, Finset.mem_singleton] at hi hj
      have hni : n ≠ i := fun h => hi (by rw [h])
      have hnj : n ≠ j := fun h => hj (by rw [h])
      simp [rp, replacePRG, unrp, hni, hnj]
  | Expression.G0 c, hi, hj => by
      simp only [keySubterms, Finset.mem_union, not_or] at hi hj
      rw [rp_G0]
      split_ifs with h
      · subst h; simp [unrp, hit]
      · rw [unrp, unrp_rp t i j hij hit hjt c hi.2 hj.2]
  | Expression.G1 c, hi, hj => by
      simp only [keySubterms, Finset.mem_union, not_or] at hi hj
      rw [rp_G1]
      split_ifs with h
      · subst h; simp [unrp, hjt, Ne.symm hij]
      · rw [unrp, unrp_rp t i j hij hit hjt c hi.2 hj.2]

lemma rp_inj (t i j : ℕ) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    {a b : Expression Shape.KeyS}
    (hai : Expression.VarK i ∉ keySubterms a) (haj : Expression.VarK j ∉ keySubterms a)
    (hbi : Expression.VarK i ∉ keySubterms b) (hbj : Expression.VarK j ∉ keySubterms b)
    (h : rp t i j a = rp t i j b) : a = b := by
  rw [← unrp_rp t i j hij hit hjt a hai haj, ← unrp_rp t i j hij hit hjt b hbi hbj, h]

/-- Idealisation can break a `G`-chain but never creates one: an ancestor relation in the
    idealised expression was already there. -/
lemma strictYields_rp_reflect (t i j : ℕ) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (a : Expression Shape.KeyS)
    (hai : Expression.VarK i ∉ keySubterms a) (haj : Expression.VarK j ∉ keySubterms a) :
    ∀ b : Expression Shape.KeyS, Expression.VarK i ∉ keySubterms b →
      Expression.VarK j ∉ keySubterms b →
      strictYields (rp t i j a) (rp t i j b) = true → strictYields a b = true
  | Expression.VarK n, _, _, h => by simp [rp, replacePRG, strictYields] at h
  | Expression.G0 c, hi, hj, h => by
      simp only [keySubterms, Finset.mem_union, not_or] at hi hj
      rw [rp_G0] at h
      split_ifs at h with hc
      · simp [strictYields] at h
      · simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h ⊢
        rcases h with h | h
        · exact Or.inl (rp_inj t i j hij hit hjt hi.2 hj.2 hai haj h)
        · exact Or.inr (strictYields_rp_reflect t i j hij hit hjt a hai haj c hi.2 hj.2 h)
  | Expression.G1 c, hi, hj, h => by
      simp only [keySubterms, Finset.mem_union, not_or] at hi hj
      rw [rp_G1] at h
      split_ifs at h with hc
      · simp [strictYields] at h
      · simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h ⊢
        rcases h with h | h
        · exact Or.inl (rp_inj t i j hij hit hjt hi.2 hj.2 hai haj h)
        · exact Or.inr (strictYields_rp_reflect t i j hij hit hjt a hai haj c hi.2 hj.2 h)

/-- The atomic variable at the bottom of a key's `G`-chain. -/
def baseVar : Expression Shape.KeyS → ℕ
  | Expression.VarK n => n
  | Expression.G0 c => baseVar c
  | Expression.G1 c => baseVar c

@[simp] lemma baseVar_VarK (n : ℕ) : baseVar (Expression.VarK n) = n := by simp [baseVar]
@[simp] lemma baseVar_G0 (c : Expression Shape.KeyS) :
    baseVar (Expression.G0 c) = baseVar c := by simp [baseVar]
@[simp] lemma baseVar_G1 (c : Expression Shape.KeyS) :
    baseVar (Expression.G1 c) = baseVar c := by simp [baseVar]

lemma strictYields_baseVar : ∀ k : Expression Shape.KeyS, isAtomicKey k = false →
    strictYields (Expression.VarK (baseVar k)) k = true
  | Expression.VarK _, h => by simp [isAtomicKey] at h
  | Expression.G0 c, _ => by
      cases hc : isAtomicKey c
      · rw [baseVar_G0]
        simp only [strictYields, Bool.or_eq_true]
        exact Or.inr (strictYields_baseVar c hc)
      · cases c with
        | VarK m => simp [strictYields]
        | G0 _ => simp [isAtomicKey] at hc
        | G1 _ => simp [isAtomicKey] at hc
  | Expression.G1 c, _ => by
      cases hc : isAtomicKey c
      · rw [baseVar_G1]
        simp only [strictYields, Bool.or_eq_true]
        exact Or.inr (strictYields_baseVar c hc)
      · cases c with
        | VarK m => simp [strictYields]
        | G0 _ => simp [isAtomicKey] at hc
        | G1 _ => simp [isAtomicKey] at hc

/-- Each hop shortens the chain of the key being hidden by exactly one. -/
lemma keySize_rp (i j : ℕ) : ∀ k : Expression Shape.KeyS, isAtomicKey k = false →
    keySize (rp (baseVar k) i j k) + 1 = keySize k
  | Expression.VarK _, h => by simp [isAtomicKey] at h
  | Expression.G0 c, _ => by
      cases hc : isAtomicKey c
      · have hne : c ≠ Expression.VarK (baseVar c) := by
          cases c with
          | VarK _ => simp [isAtomicKey] at hc
          | G0 _ => simp
          | G1 _ => simp
        rw [baseVar_G0, rp_G0, if_neg hne, keySize, keySize, keySize_rp i j c hc]
      · cases c with
        | VarK m => simp [rp_G0, keySize]
        | G0 _ => simp [isAtomicKey] at hc
        | G1 _ => simp [isAtomicKey] at hc
  | Expression.G1 c, _ => by
      cases hc : isAtomicKey c
      · have hne : c ≠ Expression.VarK (baseVar c) := by
          cases c with
          | VarK _ => simp [isAtomicKey] at hc
          | G0 _ => simp
          | G1 _ => simp
        rw [baseVar_G1, rp_G1, if_neg hne, keySize, keySize, keySize_rp i j c hc]
      · cases c with
        | VarK m => simp [rp_G1, keySize]
        | G0 _ => simp [isAtomicKey] at hc
        | G1 _ => simp [isAtomicKey] at hc

lemma rp_pair (t i j : ℕ) {s1 s2 : Shape} (p1 : Expression s1) (p2 : Expression s2) :
    rp t i j (Expression.Pair p1 p2) = Expression.Pair (rp t i j p1) (rp t i j p2) := rfl

lemma rp_perm (t i j : ℕ) {s1 : Shape} (b : Expression Shape.BitS) (p1 p2 : Expression s1) :
    rp t i j (Expression.Perm b p1 p2) = Expression.Perm b (rp t i j p1) (rp t i j p2) := rfl

lemma rp_enc (t i j : ℕ) {s1 : Shape} (k : Expression Shape.KeyS) (m : Expression s1) :
    rp t i j (Expression.Enc k m) = Expression.Enc (rp t i j k) (rp t i j m) := rfl

lemma rp_hidden (t i j : ℕ) {s1 : Shape} (k : Expression Shape.KeyS) :
    rp t i j (Expression.Hidden (s := s1) k) = Expression.Hidden (rp t i j k) := rfl

lemma keySubterms_trans : ∀ (b a : Expression Shape.KeyS),
    a ∈ keySubterms b → keySubterms a ⊆ keySubterms b
  | Expression.VarK n, a, h => by
      simp only [keySubterms, Finset.mem_singleton] at h; subst h; exact Finset.Subset.refl _
  | Expression.G0 sd, a, h => by
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at h
      rcases h with rfl | h
      · exact Finset.Subset.refl _
      · exact Finset.Subset.trans (keySubterms_trans sd a h)
          (by intro x hx; simp [keySubterms, hx])
  | Expression.G1 sd, a, h => by
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at h
      rcases h with rfl | h
      · exact Finset.Subset.refl _
      · exact Finset.Subset.trans (keySubterms_trans sd a h)
          (by intro x hx; simp [keySubterms, hx])

/-- Idealisation commutes with hiding one key. -/
lemma rp_hideSelected (t i j : ℕ) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (k : Expression Shape.KeyS)
    (hki : Expression.VarK i ∉ keySubterms k) (hkj : Expression.VarK j ∉ keySubterms k) :
    ∀ {s : Shape} (e : Expression s), Expression.VarK i ∉ keySubterms e →
      Expression.VarK j ∉ keySubterms e →
      rp t i j (hideSelectedS {k} e) = hideSelectedS {rp t i j k} (rp t i j e) := by
  intro s e
  induction e with
  | VarK n => intro _ _; simp [hideSelectedS, hideEncryptedS_K]
  | G0 c _ => intro _ _; simp only [hideSelectedS, hideEncryptedS_K]
  | G1 c _ => intro _ _; simp only [hideSelectedS, hideEncryptedS_K]
  | BitE b => intro _ _; simp [hideSelectedS, hideEncryptedS, replacePRG]
  | Eps => intro _ _; simp [hideSelectedS, hideEncryptedS, replacePRG]
  | Hidden c _ =>
      intro _ _
      simp only [hideSelectedS, hideEncryptedS, rp_hidden]
  | Pair p1 p2 ih1 ih2 =>
      intro hi hj
      simp only [keySubterms, Finset.mem_union, not_or] at hi hj
      simp only [hideSelectedS, hideEncryptedS, rp_pair] at *
      rw [ih1 hi.1 hj.1, ih2 hi.2 hj.2]
  | Perm b p1 p2 _ ih1 ih2 =>
      intro hi hj
      simp only [keySubterms, Finset.mem_union, not_or] at hi hj
      simp only [hideSelectedS, hideEncryptedS, rp_perm] at *
      rw [ih1 hi.1 hj.1, ih2 hi.2 hj.2]
  | Enc c m _ ihm =>
      intro hi hj
      simp only [keySubterms, Finset.mem_union, not_or] at hi hj
      have hiff : (c ∈ ({k} : Set (Expression Shape.KeyS))ᶜ)
          ↔ (rp t i j c ∈ ({rp t i j k} : Set (Expression Shape.KeyS))ᶜ) := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_iff_not]
        exact ⟨fun h => by rw [h], fun h => rp_inj t i j hij hit hjt hi.1 hj.1 hki hkj h⟩
      simp only [hideSelectedS, hideEncryptedS, hideEncryptedS_K, rp_enc]
      by_cases hc : c ∈ ({k} : Set (Expression Shape.KeyS))ᶜ
      · rw [if_pos hc, if_pos (hiff.mp hc), rp_enc]
        exact congrArg _ (ihm hi.2 hj.2)
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h)), rp_hidden]

/-- A finite set of keys leaves infinitely many variable indices unused. -/
lemma exists_fresh_index (S : Finset (Expression Shape.KeyS)) :
    ∃ N : ℕ, ∀ m, N ≤ m → Expression.VarK m ∉ S := by
  obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range (S.image baseVar)
  refine ⟨N, fun m hm hmem => ?_⟩
  have h1 : m ∈ S.image baseVar := Finset.mem_image.mpr ⟨Expression.VarK m, hmem, by simp⟩
  have h2 := hN h1
  rw [Finset.mem_range] at h2
  omega

/-! ## Generic `keySubterms` facts, shared by both layers -/

/-- Every key expression is one of its own key subterms. -/
lemma keySubterms_self : ∀ k : Expression Shape.KeyS, k ∈ keySubterms k
  | Expression.VarK _ => by simp [keySubterms]
  | Expression.G0 _ => by simp [keySubterms]
  | Expression.G1 _ => by simp [keySubterms]
/-- `keySubterms` is subterm-closed through `G0`/`G1`. -/
lemma keySubterms_of_G0 {s : Shape} {p : Expression s} {k : Expression Shape.KeyS}
    (h : Expression.G0 k ∈ keySubterms p) : k ∈ keySubterms p := by
  induction p with
  | Pair p1 p2 ih1 ih2 =>
      simp only [keySubterms, Finset.mem_union] at h ⊢; exact h.imp ih1 ih2
  | Perm bb p1 p2 _ ih1 ih2 =>
      simp only [keySubterms, Finset.mem_union] at h ⊢; exact h.imp ih1 ih2
  | Enc kk e ih1 ih2 =>
      simp only [keySubterms, Finset.mem_union] at h ⊢; exact h.imp ih1 ih2
  | Hidden kk ih => simp only [keySubterms] at h ⊢; exact ih h
  | G0 e ih =>
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · right; rw [Expression.G0.injEq] at h; rw [← h]; exact keySubterms_self k
      · exact Or.inr (ih h)
  | G1 e ih =>
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact absurd h (by simp)
      · exact Or.inr (ih h)
  | _ => simp [keySubterms] at h ⊢

lemma keySubterms_of_G1 {s : Shape} {p : Expression s} {k : Expression Shape.KeyS}
    (h : Expression.G1 k ∈ keySubterms p) : k ∈ keySubterms p := by
  induction p with
  | Pair p1 p2 ih1 ih2 =>
      simp only [keySubterms, Finset.mem_union] at h ⊢; exact h.imp ih1 ih2
  | Perm bb p1 p2 _ ih1 ih2 =>
      simp only [keySubterms, Finset.mem_union] at h ⊢; exact h.imp ih1 ih2
  | Enc kk e ih1 ih2 =>
      simp only [keySubterms, Finset.mem_union] at h ⊢; exact h.imp ih1 ih2
  | Hidden kk ih => simp only [keySubterms] at h ⊢; exact ih h
  | G0 e ih =>
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact absurd h (by simp)
      · exact Or.inr (ih h)
  | G1 e ih =>
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · right; rw [Expression.G1.injEq] at h; rw [← h]
        cases k <;> simp [keySubterms]
      · exact Or.inr (ih h)
  | _ => simp [keySubterms] at h ⊢

end PRG
