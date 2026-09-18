import PRGExtension.Garbling.SymbolicHiding.GarbleProof

/-!
# Characterising `adversaryView (Garble C x)`

What the adversary can actually read out of a garbled circuit, and LM18 Lemma 7.

Two facts do the work.  `atomic_recovered_garble`: an atomic key is recovered **only by
decrypting something** — `keyRecovery`'s other source, the ancestor clause of LM18
Definition 3, is vacuous on encryption keys by Lemma 6, and the PRG closure on top adds only
derived keys.  `GbStage.view_extract_iso`: a key whose index lies in a stage's counter range
was read out of *that* stage and nowhere else, because `Compose` splits the counter range at
an even endpoint so a `{2n, 2n+1}` pair never straddles the two halves.

Together they make `lemma7`'s `NAnd` case local: exactly one of the four rows decrypts, so
exactly one of the gate's two fresh keys is revealed, and nothing elsewhere in the circuit
could have supplied the other.  `lemma7_value` sharpens this to say *which* key that is.
-/

namespace PRG

/-- `prgStep` never introduces an atomic key: it only ever adds `G0`/`G1` applications. -/
lemma atomic_mem_prgStep {U known : Finset (Expression Shape.KeyS)}
    {k : Expression Shape.KeyS} (hat : isAtomicKey k = true) (h : k ∈ prgStep U known) :
    k ∈ known := by
  simp only [prgStep, Finset.mem_union, Finset.mem_filter] at h
  rcases h with h | ⟨_, hd⟩
  · exact h
  · cases k with
    | VarK n => simp [isDerived] at hd
    | G0 _ => simp [isAtomicKey] at hat
    | G1 _ => simp [isAtomicKey] at hat
/-- Hence an atomic key is in the PRG closure only if it was in the base set.  This is the
    formal counterpart of "`𝖦*(S)` adds only derived keys". -/
lemma atomic_mem_prgClosure {U base : Finset (Expression Shape.KeyS)}
    {k : Expression Shape.KeyS} (hat : isAtomicKey k = true) (h : k ∈ prgClosure U base) :
    k ∈ base := by
  rw [prgClosure_eq_iterate] at h
  generalize U.card + 1 = n at h
  induction n with
  | zero => simpa using h
  | succ m ih =>
      rw [Function.iterate_succ_apply'] at h
      exact ih (atomic_mem_prgStep hat h)
/-- On a pure key expression `hideEncrypted` is the identity: there is nothing to hide. -/
lemma hideEncrypted_key (keys : Finset (Expression Shape.KeyS)) :
    ∀ k : Expression Shape.KeyS, hideEncrypted keys k = k
  | Expression.VarK _ => rfl
  | Expression.G0 e => by rw [hideEncrypted, hideEncrypted_key keys e]
  | Expression.G1 e => by rw [hideEncrypted, hideEncrypted_key keys e]
/-- `hideEncrypted` never invents an encryption key. -/
lemma encKeys_hideEncrypted {s : Shape} (keys : Finset (Expression Shape.KeyS))
    (p : Expression s) : encKeys (hideEncrypted keys p) ⊆ encKeys p := by
  induction p with
  | Pair p1 p2 ih1 ih2 =>
      simp only [hideEncrypted, encKeys]; exact Finset.union_subset_union ih1 ih2
  | Perm bb p1 p2 _ ih1 ih2 =>
      simp only [hideEncrypted, encKeys]; exact Finset.union_subset_union ih1 ih2
  | Enc k e ihk ihe =>
      simp only [hideEncrypted]
      by_cases hk : k ∈ keys
      · simp only [hk, if_true, encKeys]
        refine Finset.union_subset_union ?_ ihe
        intro x hx
        simp only [Finset.mem_singleton] at hx ⊢
        subst hx
        exact hideEncrypted_key keys k
      · simp only [hk, if_false, encKeys]
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        simp only [Finset.mem_union, Finset.mem_singleton]
        exact Or.inl (hideEncrypted_key keys k)
  | Hidden k ih =>
      simp only [hideEncrypted, encKeys]
      intro x hx
      simp only [Finset.mem_singleton] at hx ⊢
      subst hx; exact hideEncrypted_key keys k
  | _ => simp [hideEncrypted, encKeys]
lemma encKeys_gEnc : ∀ {b : WireBundle} (u : labelType b) (x : bundleBool b),
    encKeys (encodedLabelToExpr (gEnc u x)) = ∅ := by
  intro b
  induction b with
  | SimpleB => intro l x; cases x <;> simp [gEnc, encodedLabelToExpr, encKeys]
  | PairB b1 b2 ih1 ih2 =>
      rintro ⟨l1, l2⟩ ⟨x1, x2⟩
      simp [gEnc, encodedLabelToExpr, encKeys, ih1, ih2]
lemma encKeys_maskedLabelToExpr : ∀ {b : WireBundle} (m : maskedLabelType b),
    encKeys (maskedLabelToExpr m) = ∅ := by
  intro b
  induction b with
  | SimpleB => intro m; cases m <;> simp [maskedLabelToExpr, encKeys]
  | PairB b1 b2 ih1 ih2 => rintro ⟨m1, m2⟩; simp [maskedLabelToExpr, encKeys, ih1, ih2]
/-- **LM18 Lemma 6(1) for the whole garbled expression, keyed on encryption keys.**
    Generalises `lemma6_garble_cond1`, which only covered non-atomic keys. -/
theorem lemma6_garble_enc {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    {k : Expression Shape.KeyS} (hk : k ∈ encKeys (Garble c x)) :
    ∀ k' ∈ exprKeys (Garble c x), strictYields k k' = false := by
  intro k' hk'
  have henc : k ∈ encKeys (gb c (makeLabels s 0).1 (makeLabels s 0).2).1 := by
    simp only [Garble, encKeys, Finset.mem_union] at hk
    rcases hk with h | h | h
    · exact h
    · exact absurd h (by rw [encKeys_gEnc]; simp)
    · exact absurd h (by rw [encKeys_maskedLabelToExpr]; simp)
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
/-- The keys the adversary can read off the view are certainly recovered. -/
lemma extractKeys_adversaryView_subset {s : Shape} (e : Expression s) :
    extractKeys (adversaryView e) ⊆ adversaryKeys e := by
  have hfix : keyRecovery e (adversaryKeys e) = adversaryKeys e := adversaryKeysIsFix e
  intro k hk
  rw [← hfix]
  simp only [keyRecovery]
  rw [adversaryKeys_prgClosed]
  refine subset_prgClosure _ _ ?_
  simp only [Finset.mem_union]
  exact Or.inl hk
/-- **An atomic key is recovered only by decryption.**  `keyRecovery` has two sources —
    `extractKeys` of the view and the ancestor clause — and the PRG closure on top adds only
    derived keys (`atomic_mem_prgClosure`).  For the garbled expression the ancestor clause
    can only fire on a key that occurs in the view; if that key is an *encryption* key,
    LM18 Lemma 6 forbids a strict descendant of it from occurring, so the clause is vacuous
    and the key must have come from `extractKeys`. -/
theorem atomic_recovered_garble {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    {k : Expression Shape.KeyS} (hat : isAtomicKey k = true)
    (h : k ∈ adversaryKeys (Garble c x)) :
    k ∈ extractKeys (adversaryView (Garble c x)) := by
  set e := Garble c x with he
  have hfix : keyRecovery e (adversaryKeys e) = adversaryKeys e := adversaryKeysIsFix e
  have h' : k ∈ keyRecovery e (adversaryKeys e) := by rw [hfix]; exact h
  simp only [keyRecovery] at h'
  rw [adversaryKeys_prgClosed] at h'
  have hview : hideEncrypted (adversaryKeys e) e = adversaryView e := rfl
  rw [hview] at h'
  have h'' := atomic_mem_prgClosure hat h'
  rw [Finset.mem_union] at h''
  rcases h'' with h'' | h''
  · exact h''
  · obtain ⟨hmem, k', hk', hy⟩ := mem_ancestorKeys.mp h''
    rw [exprKeys_eq_extractKeys_union_encKeys, Finset.mem_union] at hmem
    rcases hmem with hmem | hmem
    · exact hmem
    · exfalso
      have hke : k ∈ encKeys e := encKeys_hideEncrypted _ _ hmem
      have hsub : exprKeys (adversaryView e) ⊆ exprKeys e :=
        exprKeysMonotone _ _ (hideEncryptedSmallerValue _ _)
      rw [lemma6_garble_enc c x hke k' (hsub hk')] at hy
      exact Bool.noConfusion hy
/-- Reading a garbled-table entry: the payload is recovered exactly when both the outer and
    the inner encryption key are known. -/
lemma extractKeys_view_gbEntry (S : Finset (Expression Shape.KeyS))
    (ko ki kp : Expression Shape.KeyS) (b : BitExpr) :
    extractKeys (hideEncrypted S (gbEntry ko ki kp b))
      = if ko ∈ S ∧ ki ∈ S then extractKeys kp else ∅ := by
  simp only [gbEntry, hideEncrypted]
  by_cases hko : ko ∈ S
  · by_cases hki : ki ∈ S
    · simp only [hko, hki, if_true, extractKeys, hideEncrypted, and_self]
      simp only [hideEncrypted_key, extractKeys]
      simp
    · simp only [hko, hki, if_true, if_false, extractKeys, and_false, if_false]
  · simp only [hko, if_false, extractKeys, false_and, if_false]
/-- Every key the adversary reads out of a garbled circuit is one of the payload key
    variables minted by a `NAnd` gate *inside that circuit*. -/
theorem extractKeys_view_range (S : Finset (Expression Shape.KeyS)) :
    ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
      ∀ K ∈ extractKeys (hideEncrypted S (gb c u ctr).1),
        ∃ j, 2 * ctr ≤ j ∧ j < 2 * (gb c u ctr).2.2 ∧ K = Expression.VarK j := by
  intro s t c
  induction c with
  | SwapC x y => rintro ⟨i1, i2⟩ ctr K hK; simp [gb, hideEncrypted, extractKeys] at hK
  | AssocC x y z => rintro ⟨i1, i2, i3⟩ ctr K hK; simp [gb, hideEncrypted, extractKeys] at hK
  | UnAssocC x y z => rintro ⟨⟨i1, i2⟩, i3⟩ ctr K hK; simp [gb, hideEncrypted, extractKeys] at hK
  | DupC => intro l ctr K hK; simp [gb, hideEncrypted, extractKeys] at hK
  | NandC =>
      rintro ⟨li, lj⟩ ctr K hK
      have hfin : (gb Circuit.NandC (li, lj) ctr).2.2 = ctr + 1 := rfl
      rw [hfin]
      have key : ∀ (P : Prop) [Decidable P] (m : ℕ),
          K ∈ (if P then extractKeys (Expression.VarK m) else (∅ : Finset (Expression Shape.KeyS))) →
          K = Expression.VarK m := by
        intro P _ m hm
        split_ifs at hm
        · simpa [extractKeys] using hm
        · simp at hm
      simp only [gb, hideEncrypted, extractKeys, Finset.mem_union,
        extractKeys_view_gbEntry] at hK
      rcases hK with ((h | h) | (h | h))
      · exact ⟨2*ctr+1, by omega, by omega, key _ _ h⟩
      · exact ⟨2*ctr+1, by omega, by omega, key _ _ h⟩
      · exact ⟨2*ctr+1, by omega, by omega, key _ _ h⟩
      · exact ⟨2*ctr, by omega, by omega, key _ _ h⟩
  | FirstC c wb ih =>
      rintro ⟨b1, b2⟩ ctr K hK
      simp only [gb] at hK ⊢
      exact ih b1 ctr K hK
  | ComposeC c1 c2 ih1 ih2 =>
      intro b ctr K hK
      have hfin : (gb (Circuit.ComposeC c1 c2) b ctr).2.2
          = (gb c2 (gb c1 b ctr).2.1 (gb c1 b ctr).2.2).2.2 := rfl
      rw [hfin]
      simp only [gb, hideEncrypted, extractKeys, Finset.mem_union] at hK
      have hm1 := gb_ctr_mono c1 b ctr
      have hm2 := gb_ctr_mono c2 (gb c1 b ctr).2.1 (gb c1 b ctr).2.2
      rcases hK with hK | hK
      · obtain ⟨j, h1, h2, h3⟩ := ih1 b ctr K hK; exact ⟨j, h1, by omega, h3⟩
      · obtain ⟨j, h1, h2, h3⟩ := ih2 (gb c1 b ctr).2.1 (gb c1 b ctr).2.2 K hK
        exact ⟨j, by omega, h2, h3⟩
lemma GbStage.final_le {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') : (gb c' u' ctr').2.2 ≤ (gb c u ctr).2.2 := by
  induction h with
  | refl => exact le_refl _
  | @composeL a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      simp only [gb]
      exact le_trans ih (gb_ctr_mono c2 _ _)
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' _ ih => simp only [gb]; exact ih
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih => simp only [gb]; exact ih
/--
  **No interference between stages.**  A key read out of the whole garbled circuit whose
  index lies in a stage's counter range must have been read out of *that stage*.  This is
  what lets the `NAnd` case of Lemma 7 reason locally about its own two fresh keys: nothing
  elsewhere in the circuit can contribute them.
-/
theorem GbStage.view_extract_iso (S : Finset (Expression Shape.KeyS))
    {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') {j : ℕ}
    (hlo : 2 * ctr' ≤ j) (hhi : j < 2 * (gb c' u' ctr').2.2)
    (hK : Expression.VarK j ∈ extractKeys (hideEncrypted S (gb c u ctr).1)) :
    Expression.VarK j ∈ extractKeys (hideEncrypted S (gb c' u' ctr').1) := by
  induction h with
  | refl => exact hK
  | @composeL a b d s' t' c1 c2 u ctr c'' u'' ctr'' hst ih =>
      simp only [gb, hideEncrypted, extractKeys, Finset.mem_union] at hK
      refine ih hlo hhi ?_
      rcases hK with hK | hK
      · exact hK
      · exfalso
        obtain ⟨j', hj1, hj2, hj3⟩ := extractKeys_view_range S c2 _ _ _ hK
        have hfe : (gb c'' u'' ctr'').2.2 ≤ (gb c1 u ctr).2.2 := hst.final_le
        rw [Expression.VarK.injEq] at hj3
        subst hj3
        have hstep : 2 * (gb c'' u'' ctr'').2.2 ≤ 2 * (gb c1 u ctr).2.2 := by omega
        exact absurd (lt_of_lt_of_le hhi hstep) (not_lt.mpr hj1)
  | @composeR a b d s' t' c1 c2 u ctr c'' u'' ctr'' hst ih =>
      simp only [gb, hideEncrypted, extractKeys, Finset.mem_union] at hK
      refine ih hlo hhi ?_
      rcases hK with hK | hK
      · exfalso
        obtain ⟨j', hj1, hj2, hj3⟩ := extractKeys_view_range S c1 u ctr _ hK
        have hcl : (gb c1 u ctr).2.2 ≤ ctr'' := hst.ctr_le
        rw [Expression.VarK.injEq] at hj3
        subst hj3
        have hstep : 2 * (gb c1 u ctr).2.2 ≤ 2 * ctr'' := by omega
        exact absurd (lt_of_lt_of_le hj2 hstep) (not_lt.mpr hlo)
      · exact hK
  | @first v1 v2 wb s' t' c u1 u2 ctr c'' u'' ctr'' _ ih =>
      simp only [gb] at hK
      exact ih hlo hhi hK
lemma GbStage.trans {s t s' t' s'' t'' : WireBundle} {c : Circuit s t} {u : labelType s}
    {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    {c'' : Circuit s'' t''} {u'' : labelType s''} {ctr'' : ℕ}
    (h1 : GbStage c u ctr c' u' ctr') (h2 : GbStage c' u' ctr' c'' u'' ctr'') :
    GbStage c u ctr c'' u'' ctr'' := by
  induction h1 with
  | refl => exact h2
  | composeL _ ih => exact GbStage.composeL (ih h2)
  | composeR _ ih => exact GbStage.composeR (ih h2)
  | first _ ih => exact GbStage.first (ih h2)
lemma GbStage.keySubterms_subset {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s}
    {ctr : ℕ} {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') :
    keySubterms (gb c' u' ctr').1 ⊆ keySubterms (gb c u ctr).1 := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @composeL a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      have : keySubterms (gb (Circuit.ComposeC c1 c2) u ctr).1
          = keySubterms (gb c1 u ctr).1
            ∪ keySubterms (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp [gb, keySubterms]
      rw [this, Finset.mem_union]; exact Or.inl hy
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      have : keySubterms (gb (Circuit.ComposeC c1 c2) u ctr).1
          = keySubterms (gb c1 u ctr).1
            ∪ keySubterms (gb c2 (gb c1 u ctr).2.1 (gb c1 u ctr).2.2).1 := by
        simp [gb, keySubterms]
      rw [this, Finset.mem_union]; exact Or.inr hy
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      have : keySubterms (gb (Circuit.FirstC c wb) (u1, u2) ctr).1
          = keySubterms (gb c u1 ctr).1 := by simp [gb]
      rw [this]; exact hy
lemma GbStage.view_extract_mono (S : Finset (Expression Shape.KeyS))
    {s t s' t' : WireBundle} {c : Circuit s t} {u : labelType s} {ctr : ℕ}
    {c' : Circuit s' t'} {u' : labelType s'} {ctr' : ℕ}
    (h : GbStage c u ctr c' u' ctr') :
    extractKeys (hideEncrypted S (gb c' u' ctr').1)
      ⊆ extractKeys (hideEncrypted S (gb c u ctr).1) := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @composeL a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      simp only [gb, hideEncrypted, extractKeys, Finset.mem_union]; exact Or.inl hy
  | @composeR a b d s' t' c1 c2 u ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy
      simp only [gb, hideEncrypted, extractKeys, Finset.mem_union]; exact Or.inr hy
  | @first v1 v2 wb s' t' c u1 u2 ctr c' u' ctr' _ ih =>
      refine Finset.Subset.trans ih ?_
      intro y hy; simp only [gb]; exact hy
/-- Reading the encoded input labels gives back label keys and nothing else. -/
lemma extractKeys_view_gEnc (S : Finset (Expression Shape.KeyS)) :
    ∀ {b : WireBundle} (u : labelType b) (x : bundleBool b),
      extractKeys (hideEncrypted S (encodedLabelToExpr (gEnc u x))) ⊆ labelKeys u := by
  intro b
  induction b with
  | SimpleB =>
      intro l x
      cases x
      · have he : hideEncrypted S (encodedLabelToExpr (gEnc (b := WireBundle.SimpleB) l false))
            = Expression.Pair (Expression.BitE l.bitE) l.key0 := by
          simp only [gEnc, encodedLabelToExpr, cond_false, hideEncrypted, hideEncrypted_key]
        rw [he]
        simp [extractKeys, extractKeys_key, labelKeys]
      · have he : hideEncrypted S (encodedLabelToExpr (gEnc (b := WireBundle.SimpleB) l true))
            = Expression.Pair (Expression.BitE (BitExpr.Not l.bitE)) l.key1 := by
          simp only [gEnc, encodedLabelToExpr, cond_true, hideEncrypted, hideEncrypted_key]
        rw [he]
        simp [extractKeys, extractKeys_key, labelKeys]
  | PairB b1 b2 ih1 ih2 =>
      rintro ⟨l1, l2⟩ ⟨x1, x2⟩
      simp only [gEnc, encodedLabelToExpr, hideEncrypted, extractKeys, labelKeys]
      exact Finset.union_subset_union (ih1 l1 x1) (ih2 l2 x2)

/-! ## LM18 Lemma 7 -/

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

/-! ## Lemma 7, tracking the wire values -/
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

end PRG
