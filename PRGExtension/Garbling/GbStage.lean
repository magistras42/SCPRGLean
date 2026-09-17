import PRGExtension.Garbling.GarbleFixpoint

/-!
# Garbling stages

LM18's Lemmas 7 and 8 read "for every sub-circuit `C'` of `C` and every label expression
`u` …".  Taken literally with `SubCircuit` that is false in this formalisation: `gb` takes
the input labels `u` and the key counter `ctr` as *independent* arguments, so for arbitrary
`u`/`ctr` the garbling of `C'` has nothing to do with the garbling of `C` — in particular
the fresh keys `K_{2ctr}, K_{2ctr+1}` that `NAnd` creates need not be keys of
`Garble C x` at all, and the `Dup` case of Lemma 7 argues about membership in
`Fix(𝓕_{Garble C x})`.

What the paper means is the labels and counter that *actually arise* while garbling `C`.
`GbStage c u ctr c' u' ctr'` says exactly that: garbling `c` from `(u, ctr)` performs, as a
sub-computation, the garbling of `c'` from `(u', ctr')`.  It refines `SubCircuit`
(`GbStage.subCircuit`) and carries the structural facts the later proofs need.
-/

namespace PRG

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
