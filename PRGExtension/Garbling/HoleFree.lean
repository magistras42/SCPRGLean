import PRGExtension.Expression.HoleFree
import PRGExtension.Garbling.Simulate

/-!
# `Garble` and `Simulate` produce no holes

The invariant LM18 gets from its types (`𝙶𝚋 : … → 𝐄𝐱𝐩`, and the hole lives only in `𝐏𝐚𝐭`),
recovered here as two theorems.  See `Expression/HoleFree.lean` for why it is worth stating
and `FUTURE-WORK.md` (cost C2) for what it replaces.

Before this file the fact was a grep result — `Simulate.lean` contains no `Hidden`, and
`GarblingDef.lean`'s single occurrence is `decrypt`'s failure arm.  Now an edit that starts
emitting holes from `Gb` or `Sim` breaks the build instead of silently desynchronising the
symbolic evaluator (which would refuse, `decrypt` returning `none` on a hole) from the
computational one (which is total, and by `evalExpr_hidden_decrypt` would return `ones` —
a wrong wire label rather than a failure).

Holes enter the development only through `hideEncrypted` and `adversaryView`, which is
exactly where LM18 puts them: the pattern of an expression, on the soundness side.  Nothing
on the garbling side produces one.
-/

namespace PRG

/-! ### Hole-freeness of the pieces `Garble` assembles -/

theorem holeFree_encodedLabelToExpr : ∀ {b : WireBundle} (i : encodedLabelType b),
    HoleFree (encodedLabelToExpr i)
  | WireBundle.SimpleB, i => holeFree_encLabel i
  | WireBundle.PairB _ _, (i1, i2) =>
      ⟨holeFree_encodedLabelToExpr i1, holeFree_encodedLabelToExpr i2⟩

theorem holeFree_maskedLabelToExpr : ∀ {b : WireBundle} (m : maskedLabelType b),
    HoleFree (maskedLabelToExpr m)
  | WireBundle.SimpleB, m => holeFree_bit m
  | WireBundle.PairB _ _, (m1, m2) =>
      ⟨holeFree_maskedLabelToExpr m1, holeFree_maskedLabelToExpr m2⟩

/-- A garbled-table entry is hole-free: it is `Enc` of `Enc` of a `(bit, key)` pair, and
key positions are hole-free by `holeFree_key`. -/
theorem holeFree_gbEntry (kOuter kInner kPayload : Expression Shape.KeyS) (b : BitExpr) :
    HoleFree (gbEntry kOuter kInner kPayload b) :=
  ⟨holeFree_key kOuter, holeFree_key kInner, trivial, holeFree_key kPayload⟩

/-! ### The two theorems -/

/-- **`Gb` never emits a hole.** -/
theorem gb_holeFree : ∀ {inp out : WireBundle} (c : Circuit inp out) (l : labelType inp) (ctr : ℕ),
    HoleFree (gb c l ctr).1 := by
  intro inp out c
  induction c with
  | NandC => intro l ctr; exact ⟨⟨holeFree_gbEntry .., holeFree_gbEntry ..⟩,
      holeFree_gbEntry .., holeFree_gbEntry ..⟩
  | SwapC _ _ => intro l ctr; exact trivial
  | AssocC _ _ _ => intro l ctr; exact trivial
  | UnAssocC _ _ _ => intro l ctr; exact trivial
  | DupC => intro l ctr; exact trivial
  | FirstC c u ih => intro l ctr; exact ih l.1 ctr
  | ComposeC c1 c2 ih1 ih2 =>
      intro l ctr
      exact ⟨ih1 l ctr, ih2 (gb c1 l ctr).2.1 (gb c1 l ctr).2.2⟩

/-- **`Sim` never emits a hole.** -/
theorem sim_holeFree : ∀ {inp out : WireBundle} (c : Circuit inp out) (l : labelType inp) (ctr : ℕ),
    HoleFree (sim c l ctr).1 := by
  intro inp out c
  induction c with
  | NandC => intro l ctr; exact ⟨⟨holeFree_gbEntry .., holeFree_gbEntry ..⟩,
      holeFree_gbEntry .., holeFree_gbEntry ..⟩
  | SwapC _ _ => intro l ctr; exact trivial
  | AssocC _ _ _ => intro l ctr; exact trivial
  | UnAssocC _ _ _ => intro l ctr; exact trivial
  | DupC => intro l ctr; exact trivial
  | FirstC c u ih => intro l ctr; exact ih l.1 ctr
  | ComposeC c1 c2 ih1 ih2 =>
      intro l ctr
      exact ⟨ih1 l ctr, ih2 (sim c1 l ctr).2.1 (sim c1 l ctr).2.2⟩

/-- **A garbled circuit contains no holes.**  In LM18 this is a typing fact; here it is a
theorem, and `gEvComp_sim`'s `gEv c g i = some ov` hypothesis is the place it was doing
unrecorded work. -/
theorem garble_holeFree {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    HoleFree (Garble c x) :=
  ⟨gb_holeFree c _ _, holeFree_encodedLabelToExpr _, holeFree_maskedLabelToExpr _⟩

/-- **A simulated garbled circuit contains no holes either.**  The simulator is what security
compares against, so it has to sit in the same grammar. -/
theorem simulate_holeFree {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    HoleFree (Simulate c y) :=
  ⟨sim_holeFree c _ _, holeFree_encodedLabelToExpr _, holeFree_maskedLabelToExpr _⟩

end PRG
