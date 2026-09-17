import PRGExtension.Garbling.Lemma6

/-!
# Keys of the whole garbled / simulated expression

LM18 Lemma 4 says every key appearing as a *part* of a garbled circuit is atomic.  Here it
is lifted from `gb`'s output to the complete `Garble c x` (and `Simulate c y`) expression,
and to the adversary's view of it.

This is what rules out the `extractKeys` branch of `adversaryKeys_reflects_G0`: a
PRG-derived key such as `G0 k` is never a part, so it can only be in `adversaryKeys` via
the ancestor clause (killed by Lemma 6(1)) or because its seed is.
-/

namespace PRG


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

/-- LM18 Lemma 4 for the simulator: `Sim`'s `NAnd` case always carries `K_h⁰`. -/
theorem lemma4_sim : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    ∀ k ∈ extractKeys (sim c u ctr).1, isAtomicKey k = true := by
  intro s t c
  induction c with
  | NandC =>
      rintro ⟨li, lj⟩ ctr k hk
      simp [sim, gbEntry, extractKeys] at hk
      simp [hk, isAtomicKey]
  | AssocC _ _ _ => rintro ⟨i1, i2, i3⟩ ctr k hk; simp [sim, extractKeys] at hk
  | UnAssocC _ _ _ => rintro ⟨⟨i1, i2⟩, i3⟩ ctr k hk; simp [sim, extractKeys] at hk
  | SwapC _ _ => rintro ⟨i1, i2⟩ ctr k hk; simp [sim, extractKeys] at hk
  | DupC => intro l ctr k hk; simp [sim, extractKeys] at hk
  | ComposeC c1 c2 ih1 ih2 =>
      intro u ctr k hk
      simp only [sim, extractKeys, Finset.mem_union] at hk
      rcases hk with h | h
      · exact ih1 _ _ _ h
      · exact ih2 _ _ _ h
  | FirstC c w ih =>
      rintro ⟨u1, u2⟩ ctr k hk
      simp only [sim] at hk
      exact ih _ _ _ hk

lemma extractKeys_sEnc : ∀ {b : WireBundle} (u : labelType b),
    extractKeys (encodedLabelToExpr (sEnc u)) ⊆ labelKeys u
  | WireBundle.SimpleB, l => by
      simp [sEnc, encodedLabelToExpr, extractKeys, extractKeys_key, labelKeys]
  | WireBundle.PairB o1 o2, (l1, l2) => by
      simp only [sEnc, encodedLabelToExpr, extractKeys, labelKeys]
      exact Finset.union_subset_union (extractKeys_sEnc l1) (extractKeys_sEnc l2)

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

/-- The same for the simulated expression. -/
theorem lemma4_simulate {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    ∀ k ∈ extractKeys (Simulate c y), isAtomicKey k = true := by
  intro k hk
  simp only [Simulate, extractKeys, Finset.mem_union] at hk
  rcases hk with h | h | h
  · exact lemma4_sim c _ _ k h
  · exact makeLabels_atomic s 0 k (extractKeys_sEnc _ h)
  · exact absurd h (by rw [extractKeys_maskedLabelToExpr]; simp)

/-- The same for the adversary's views, which only hide more. -/
theorem lemma4_adversaryView {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    ∀ k ∈ extractKeys (adversaryView (Garble c x)), isAtomicKey k = true := by
  intro k hk
  exact lemma4_garble c x k
    (keyPartsMonotone _ _ (hideEncryptedSmallerValue _ _) hk)

theorem lemma4_simulate_adversaryView {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    ∀ k ∈ extractKeys (adversaryView (Simulate c y)), isAtomicKey k = true := by
  intro k hk
  exact lemma4_simulate c y k
    (keyPartsMonotone _ _ (hideEncryptedSmallerValue _ _) hk)

end PRG
