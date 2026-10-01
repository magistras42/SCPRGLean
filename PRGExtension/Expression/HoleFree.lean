import PRGExtension.Expression.Defs

/-!
# Hole-freeness

`Expression` merges LM18's two grammars — `𝐄𝐱𝐩(s)`, the expression algebra, and `𝐏𝐚𝐭(s)`,
that algebra plus the hole `⦃s⦄_{𝐄𝐱𝐩(𝕂)}` — into one shape-indexed type with `Hidden` as an
ordinary constructor.  `FUTURE-WORK.md` weighs that merge and keeps it: the shape index then
makes `Expression 𝕂 = Pattern 𝕂` definitional, one `ExpressionInclusion` replaces three
relations, and `normalizeExpr` / `applyVarRenaming` are defined once rather than twice.

What the merge loses is a *typing* fact: in LM18 `𝙶𝚋` has codomain `𝐄𝐱𝐩`, so "a garbled
circuit contains no holes" is true by construction and never worth stating.  Here it is a
property of the definitions that happens to hold, and nothing stops a later edit from breaking
it silently.  `HoleFree` writes that invariant down; `Garbling/HoleFree.lean` proves it of
`Garble` and `Simulate`.

Why it matters rather than merely tidies.  Symbolic `gEv` is partial *partly because*
`decrypt` returns `none` on a hole (`holeFree_enc_exists` is exactly that dependence, stated
positively); computational `gEvComp` is total, and `evalExpr_hidden_decrypt` says a hole's bits
decrypt to `ones` — garbage, not failure.  A hole reaching a garbled circuit would therefore
make the symbolic evaluator refuse and the computational one return a wrong wire label.
`gEvComp_sim` is sound only because it is conditioned on `gEv c g i = some ov`; that hypothesis
is doing work a type could have done, and `garble_holeFree` is the machine-checked substitute.

Note `holeFree_key`: *every* `Expression 𝕂` is hole-free, because `Hidden`'s index is always
`EncS s`.  That is `FUTURE-WORK.md`'s benefit B1 paying for part of the cost of C2 — key
positions need no side conditions at all.
-/

namespace PRG

/-- No `Hidden` node occurs anywhere in the expression. -/
def HoleFree : {s : Shape} → Expression s → Prop
  | _, .BitE _ => True
  | _, .VarK _ => True
  | _, .Eps => True
  | _, .G0 k => HoleFree k
  | _, .G1 k => HoleFree k
  | _, .Pair a b => HoleFree a ∧ HoleFree b
  | _, .Perm _ a b => HoleFree a ∧ HoleFree b
  | _, .Enc k m => HoleFree k ∧ HoleFree m
  | _, .Hidden _ => False

/-- Hole-freeness is a structural syntactic check, so it decides. -/
instance decidableHoleFree : {s : Shape} → (e : Expression s) → Decidable (HoleFree e)
  | _, .BitE _ => isTrue trivial
  | _, .VarK _ => isTrue trivial
  | _, .Eps => isTrue trivial
  | _, .G0 k => decidableHoleFree k
  | _, .G1 k => decidableHoleFree k
  | _, .Pair a b => @instDecidableAnd _ _ (decidableHoleFree a) (decidableHoleFree b)
  | _, .Perm _ a b => @instDecidableAnd _ _ (decidableHoleFree a) (decidableHoleFree b)
  | _, .Enc k m => @instDecidableAnd _ _ (decidableHoleFree k) (decidableHoleFree m)
  | _, .Hidden _ => isFalse id

/-! ### The shapes that carry no holes by construction -/

/-- **Every key expression is hole-free.**  `Expression 𝕂` has only `VarK`, `G0`, `G1` —
`Hidden` produces `EncS s`.  (Structural recursion rather than `induction`: the `Shape` index
is fixed at `𝕂`.) -/
theorem holeFree_key : (k : Expression Shape.KeyS) → HoleFree k
  | .VarK _ => trivial
  | .G0 k => holeFree_key k
  | .G1 k => holeFree_key k

/-- Every bit expression is hole-free: `Expression 𝔹` has only `BitE`. -/
theorem holeFree_bit : (b : Expression Shape.BitS) → HoleFree b
  | .BitE _ => trivial

/-- Every `(bit, key)` payload is hole-free. -/
theorem holeFree_encLabel : (e : Expression (Shape.PairS Shape.BitS Shape.KeyS)) → HoleFree e
  | .Pair (.BitE _) k => ⟨trivial, holeFree_key k⟩

/-! ### What hole-freeness buys at the ciphertext shape -/

/-- **A hole-free ciphertext is a real `Enc`.**  This is the whole point of the predicate:
`decrypt`'s failure arm (`GarblingDef.lean`) is `Hidden`, so on hole-free input the symbolic
evaluator can only fail by *key mismatch*, never by meeting a hole. -/
theorem holeFree_enc_exists {s : Shape} :
    ∀ (e : Expression (Shape.EncS s)), HoleFree e →
      ∃ (k : Expression Shape.KeyS) (p : Expression s), e = Expression.Enc k p
  | .Enc k p, _ => ⟨k, p, rfl⟩
  | .Hidden _, h => absurd h id

end PRG
