import PRGExtension.Garbling.GarblingDef

/-!
# LM18 Lemmas 4-8: the independence invariants of the garbling scheme

These are the structural facts about `Gb`/`Sim` that LM18 §5 uses to prove Theorem 5
(`Pattern(Garble(C,x)) ≈ Pattern(Simulate(C,C(x)))`).  They are *purely symbolic*: no
cryptography, only key bookkeeping.

Lemma 4 is proved below.  Lemmas 5-8 are written down as named propositions rather than
as `theorem … := by sorry`, so that the library stays `sorry`-free while the remaining
obligations are explicit and type-checked.  Discharging them is a structural induction on
circuits in each case (LM18 proves 5 and 6 in the appendix, 7 and 8 in §5).
-/

namespace PRG

/-- `Keys(u)` for a label expression. -/
def labelKeys : {b : WireBundle} -> labelType b -> Finset (Expression Shape.KeyS)
  | WireBundle.SimpleB, l => {l.key0, l.key1}
  | WireBundle.PairB _ _, (l1, l2) => labelKeys l1 ∪ labelKeys l2

/--
  LM18 §5: a label expression `w` is *strongly independent* when `Keys(w)` is an
  independent set of keys, a single label `(b,(k⁰,k¹))` has `k⁰ ≠ k¹`, and the two halves
  of a pair use disjoint key sets.
-/
def StronglyIndependent : {b : WireBundle} -> labelType b -> Prop
  | WireBundle.SimpleB, l => IndependentKeys {l.key0, l.key1} ∧ l.key0 ≠ l.key1
  | WireBundle.PairB _ _, (l1, l2) =>
      StronglyIndependent l1 ∧ StronglyIndependent l2 ∧ labelKeys l1 ∩ labelKeys l2 = ∅

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
-/
def Lemma5 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    StronglyIndependent u →
    StronglyIndependent (gb c u ctr).2.1 ∧
    ∀ k ∈ labelKeys (gb c u ctr).2.1,
      (∀ k' ∈ exprKeys (garbledWithLabels c (gb c u ctr).1 u), strictYields k k' = false) ∧
      (∃ k' ∈ extractKeys (garbledWithLabels c (gb c u ctr).1 u), yields k' k)

/--
  **LM18 Lemma 6.**  For every key `k` used as an *encryption* key inside a garbled
  circuit `C̃`:

  1. `𝖦⁺(k) ∩ Keys(C̃) = ∅`;
  2. `𝖦*(k) ∩ Keys(v) = ∅` for the output labels `v`;
  3. some key that appears as a part of `(C̃, u)` yields `k`.

  Together with Lemma 5 this is what rules out the key cycles that would otherwise break
  the IND-CPA reduction: (1) says no descendant of an encrypting key is ever visible, which
  is exactly the `seedFree` side condition of `symbolicToSemanticIndistinguishabilityHidingOneKey`.
-/
def Lemma6 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    StronglyIndependent u →
    ∀ k ∈ encKeys (gb c u ctr).1,
      (∀ k' ∈ exprKeys (gb c u ctr).1, strictYields k k' = false) ∧
      (∀ k' ∈ labelKeys (gb c u ctr).2.1, ¬ yields k k') ∧
      (∃ k' ∈ extractKeys (garbledWithLabels c (gb c u ctr).1 u), yields k' k)

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

/--
  **LM18 Lemma 7.**  `Gb` preserves the label invariant: if every input label has exactly
  one of its keys in `S`, so does every output label.

  `S` is *not* arbitrary — it is `Fix(𝓕_e) = adversaryKeys e` for the ambient garbled
  expression `e = Garble(C,x)`, and the lemma ranges over the sub-circuits of `C`.  The
  `Dup` case genuinely needs this: it argues that `G^h(k^{1-z}) ∉ S` using Lemma 6 applied
  to the whole garbled circuit, which has no counterpart for an unconstrained `S`.
-/
def Lemma7 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (x : bundleBool s),
    ∀ {s' t' : WireBundle} (c' : Circuit s' t'), SubCircuit c' c →
    ∀ (u : labelType s') (ctr : ℕ),
      LabelInvariant (adversaryKeys (Garble c x)) u →
      LabelInvariant (adversaryKeys (Garble c x)) (gb c' u ctr).2.1

/--
  **LM18 Lemma 8.**  The same for the simulator, with `T = Fix(𝓕_f)` for
  `f = Simulate(C, C(x))`.  There every label's actual value is `0`, because `Sim` always
  encodes with `k⁰`.
-/
def Lemma8 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (y : bundleBool t),
    ∀ {s' t' : WireBundle} (c' : Circuit s' t'), SubCircuit c' c →
    ∀ (u : labelType s') (ctr : ℕ),
      LabelInvariant (adversaryKeys (Simulate c y)) u →
      LabelInvariant (adversaryKeys (Simulate c y)) (sim c' u ctr).2.1

/--
  **LM18 Theorem 5**, the goal these lemmas serve:
  `Pattern(Garble(C,x)) ≈ Pattern(Simulate(C,C(x)))`, i.e. the garbled circuit and the
  simulated one have symbolically indistinguishable adversary views.
-/
def Theorem5 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (x : bundleBool s),
    symIndistinguishable (Garble c x) (Simulate c (evalCircuit c x))

end PRG
