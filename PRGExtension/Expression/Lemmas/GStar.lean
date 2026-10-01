import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.Expression.Lemmas.ReplacePRG

/-!
# The bounded closure is LM18's `𝖦*`, restricted

LM18 Definition 3 closes the recovered key set under PRG derivation with `𝖦*`, which is
infinite: `𝖦*({K}) = {K, G0 K, G1 K, G0 (G0 K), …}`.  The formalisation instead uses
`prgClosure (keySubterms p) ·`, bounded by the keys that syntactically occur in `p`.

That is not a shortcut, it is forced.  `adversaryKeys` is a `greatestFixpoint`, and
`greatestFixpoint` (`Core/Fixpoints.lean`) is a *constructive* Knaster–Tarski: it iterates
downward from the bound with `termination_by S.card`.  So `keyRecovery` must be
`Finset → Finset`, and an unbounded closure cannot be typed there at all.  (Computability
and `#eval` are consequences of that, not the motivation.)

This file discharges the two claims that were previously only argued in prose:

* **`prgClosure_eq_gStar_inter`** — for a chain-closed bound `U`,
  `prgClosure U base = 𝖦*(base) ∩ U`, exactly.  `keySubterms p` is chain-closed
  (`keySubterms_closed`), so `prgClosure_keySubterms_eq_gStar` is the instance the
  development uses.
* **`hideEncrypted_prgClosure_eq_gStar`** and **`adversaryView_eq_gStar`** — hiding with the
  bounded closure yields *the same expression* as hiding with the unbounded `𝖦*`.  So the
  pattern, which is all that `symIndistinguishable` compares, is the paper's.

What remains genuinely different is membership for keys that do **not** occur in `p`, and
that difference is real rather than hypothetical: `scratch/probes/DupTrailing.lean` computes
`Garble Dup true`, whose `keySubterms` is `{K₁}` while its output labels are
`(b, G0 K₀, G0 K₁)` and `(b, G1 K₀, G1 K₁)`.  LM18 recovers exactly one key of each pair;
the bounded closure recovers neither.  That is why `LabelInvariant S` had to be relativised
to `LabelInvariantIn U S`, guarded by `key0 ∈ U ∧ key1 ∈ U` — a key occurring nowhere
affects no pattern, so the guard costs nothing.
-/

namespace PRG

/-- **LM18's `𝖦*(S)`**: the closure of `S` under PRG derivation.  Genuinely unbounded —
    `GStar {K}` contains `K, G0 K, G1 K, G0 (G0 K), …` — so it is a `Prop`-valued predicate
    rather than a `Finset`. -/
inductive GStar (S : Set (Expression Shape.KeyS)) : Expression Shape.KeyS → Prop
  | base {k} : k ∈ S → GStar S k
  | g0 {k} : GStar S k → GStar S (Expression.G0 k)
  | g1 {k} : GStar S k → GStar S (Expression.G1 k)

/-- `keySubterms` is chain-closed: it contains every key subterm of every key it contains. -/
lemma keySubterms_closed : ∀ {s : Shape} (p : Expression s),
    ∀ k ∈ keySubterms p, keySubterms k ⊆ keySubterms p := by
  intro s p
  induction p with
  | VarK n =>
      intro k hk
      simp only [keySubterms, Finset.mem_singleton] at hk
      subst hk; exact Finset.Subset.refl _
  | G0 c ih =>
      intro k hk
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hk
      rcases hk with rfl | hk
      · exact Finset.Subset.refl _
      · exact Finset.Subset.trans (ih k hk) (by intro x hx; simp [keySubterms, hx])
  | G1 c ih =>
      intro k hk
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hk
      rcases hk with rfl | hk
      · exact Finset.Subset.refl _
      · exact Finset.Subset.trans (ih k hk) (by intro x hx; simp [keySubterms, hx])
  | Pair a b ih1 ih2 =>
      intro k hk
      simp only [keySubterms, Finset.mem_union] at hk
      rcases hk with hk | hk
      · exact Finset.Subset.trans (ih1 k hk) Finset.subset_union_left
      · exact Finset.Subset.trans (ih2 k hk) Finset.subset_union_right
  | Perm b a c _ ih1 ih2 =>
      intro k hk
      simp only [keySubterms, Finset.mem_union] at hk
      rcases hk with hk | hk
      · exact Finset.Subset.trans (ih1 k hk) Finset.subset_union_left
      · exact Finset.Subset.trans (ih2 k hk) Finset.subset_union_right
  | Enc kk m ihk ihm =>
      intro k hk
      simp only [keySubterms, Finset.mem_union] at hk
      rcases hk with hk | hk
      · exact Finset.Subset.trans (ihk k hk) Finset.subset_union_left
      · exact Finset.Subset.trans (ihm k hk) Finset.subset_union_right
  | Hidden kk ih => intro k hk; simp only [keySubterms] at hk ⊢; exact ih k hk
  | BitE b => intro k hk; simp [keySubterms] at hk
  | Eps => intro k hk; simp [keySubterms] at hk

/-- The bounded closure only ever produces PRG derivatives of the base set. -/
lemma prgClosure_subset_gStar (U base : Finset (Expression Shape.KeyS)) :
    ∀ k ∈ prgClosure U base, GStar (↑base) k := by
  rw [prgClosure_eq_iterate]
  generalize U.card + 1 = n
  induction n with
  | zero => intro k hk; simpa using GStar.base (S := (↑base : Set _)) (by simpa using hk)
  | succ m ih =>
      intro k hk
      rw [Function.iterate_succ_apply'] at hk
      simp only [prgStep, Finset.mem_union, Finset.mem_filter] at hk
      rcases hk with hk | ⟨_, hd⟩
      · exact ih k hk
      · cases k with
        | VarK n => simp [isDerived] at hd
        | G0 c => exact GStar.g0 (ih c (by simpa [isDerived] using hd))
        | G1 c => exact GStar.g1 (ih c (by simpa [isDerived] using hd))

/-- Conversely, every derivative that stays inside the (chain-closed) bound is produced. -/
lemma gStar_inter_subset_prgClosure (U base : Finset (Expression Shape.KeyS))
    (hchain : ∀ k ∈ U, keySubterms k ⊆ U) :
    ∀ k, GStar (↑base) k → k ∈ U → k ∈ prgClosure U base := by
  intro k hg
  induction hg with
  | base h => intro _; exact subset_prgClosure U base (by simpa using h)
  | @g0 c hc ih =>
      intro hU
      have hmem : c ∈ keySubterms (Expression.G0 c) := by
        simp only [keySubterms, Finset.mem_union, Finset.mem_singleton]
        exact Or.inr (keySubterms_self c)
      exact G0_mem_prgClosure (ih (hchain _ hU hmem)) hU
  | @g1 c hc ih =>
      intro hU
      have hmem : c ∈ keySubterms (Expression.G1 c) := by
        simp only [keySubterms, Finset.mem_union, Finset.mem_singleton]
        exact Or.inr (keySubterms_self c)
      exact G1_mem_prgClosure (ih (hchain _ hU hmem)) hU

/--
  **The bounded closure is exactly LM18's `𝖦*`, restricted to the bound.**

  This is what licenses the formalisation's use of a `Finset`-valued `prgClosure`: the
  `greatestFixpoint` construction is a terminating recursion on `Finset.card`, so
  `keyRecovery` *must* return a `Finset`, and `𝖦*({k})` is infinite.  The bound loses
  nothing that occurs.
-/
theorem prgClosure_eq_gStar_inter (U base : Finset (Expression Shape.KeyS))
    (hbase : base ⊆ U) (hchain : ∀ k ∈ U, keySubterms k ⊆ U) :
    (↑(prgClosure U base) : Set (Expression Shape.KeyS)) = {k | GStar (↑base) k} ∩ ↑U := by
  ext k
  simp only [Finset.mem_coe, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro hk
    exact ⟨prgClosure_subset_gStar U base k hk, prgClosureContained U base hbase hk⟩
  · rintro ⟨hg, hU⟩
    exact gStar_inter_subset_prgClosure U base hchain k hg hU

/-- Specialised to the bound the development actually uses. -/
theorem prgClosure_keySubterms_eq_gStar {s : Shape} (p : Expression s)
    (base : Finset (Expression Shape.KeyS)) (hbase : base ⊆ keySubterms p) :
    (↑(prgClosure (keySubterms p) base) : Set (Expression Shape.KeyS))
      = {k | GStar (↑base) k} ∩ ↑(keySubterms p) :=
  prgClosure_eq_gStar_inter _ _ hbase (keySubterms_closed p)

/-- Two key sets that agree on the *parts* of `p` hide the same way. -/
lemma hideEncryptedS_congr_allParts {s : Shape} (A B : Set (Expression Shape.KeyS))
    (p : Expression s) (h : A ∩ ↑(allParts p) = B ∩ ↑(allParts p)) :
    hideEncryptedS A p = hideEncryptedS B p := by
  rw [hideEncryptedUnivAux A (↑(allParts p)) p (Set.Subset.refl _),
    hideEncryptedUnivAux B (↑(allParts p)) p (Set.Subset.refl _), h]

/--
  **The bound changes nothing observable.**

  Hiding with the bounded `prgClosure` produces *the same expression* as hiding with LM18's
  unbounded `𝖦*`.  So `adversaryView` — the pattern, which is all that symbolic
  indistinguishability compares — is the paper's, and the divergence between the two closures
  is confined to membership queries about keys that do not occur in `p`.

  (Those queries are not vacuous: `scratch/probes/DupTrailing.lean` exhibits a trailing `Dup` whose
  output-label keys occur nowhere, so LM18 recovers one key of each pair and the bounded
  closure recovers neither.  That is why `LabelInvariant` had to be relativised to
  `LabelInvariantIn U S`.)
-/
theorem hideEncrypted_prgClosure_eq_gStar {s : Shape} (p : Expression s)
    (base : Finset (Expression Shape.KeyS)) (hbase : base ⊆ keySubterms p) :
    hideEncrypted (prgClosure (keySubterms p) base) p
      = hideEncryptedS {k | GStar (↑base) k} p := by
  rw [← hideEncryptedEqS]
  refine hideEncryptedS_congr_allParts _ _ p ?_
  ext k
  simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, hp⟩
    refine ⟨?_, hp⟩
    have := prgClosure_keySubterms_eq_gStar p base hbase
    rw [Set.ext_iff] at this
    exact ((this k).mp (by simpa using hk)).1
  · rintro ⟨hg, hp⟩
    refine ⟨?_, hp⟩
    have hkU : k ∈ keySubterms p := allParts_subset_keySubterms p (by simpa using hp)
    have := prgClosure_keySubterms_eq_gStar p base hbase
    rw [Set.ext_iff] at this
    exact (this k).mpr ⟨hg, by simpa using hkU⟩

/-- The same statement for `adversaryView`: the recovered pattern is LM18's. -/
theorem adversaryView_eq_gStar {s : Shape} (e : Expression s) :
    adversaryView e
      = hideEncryptedS {k | GStar (↑(adversaryKeys e)) k} e := by
  have hsub : adversaryKeys e ⊆ keySubterms e := by
    have := adversaryKeysIsFix e
    intro x hx
    exact keyRecoveryContained e (adversaryKeys e) (by rw [this]; exact hx)
  have h1 : adversaryView e = hideEncrypted (prgClosure (keySubterms e) (adversaryKeys e)) e := by
    rw [adversaryKeys_prgClosed]; rfl
  rw [h1, hideEncrypted_prgClosure_eq_gStar e (adversaryKeys e) hsub]

end PRG
