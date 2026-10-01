import PRGExtension.Garbling.Correctness.ComputationalCorrectness
import PRGExtension.Garbling.HoleFree

/-!
# The symbolic evaluator never fails on a genuine garbling

`gEv` is partial: it returns `Option`, and `gEvComp_sim` is conditioned on
`gEv c g i = some ov`.  `FUTURE-WORK.md` (cost C2) flags that hypothesis as "doing work a type
could have done" — in LM18 the garbled circuit lives in a grammar where the failure cases cannot
arise.  This file discharges it.

Two separate reasons `gEv` could fail, and both are now closed:

* **A hole.**  `decrypt` returns `none` on `Hidden`.  Ruled out by `garble_holeFree`
  (`Garbling/HoleFree.lean`): nothing on the garbling side ever emits one.  This is the
  soundness-adjacent half, because the computational evaluator does *not* fail there — by
  `evalExpr_hidden_decrypt` it would return `ones`, a wrong wire label.
* **Wrong structure.**  `extractPair` on a `Perm`, `extractPerm` on a `Pair`, a key that does not
  match the ciphertext it is used on.  Hole-freeness cannot rule these out; what does is being a
  genuine garbling, and `gEvCorrect` (`Garbling/Correctness/Correctness.lean`) already says exactly that.

So the invariant that replaces the hypothesis is "is in the image of `gb`", as predicted — and
it was already proved, as part of symbolic correctness.  What this file adds is the statements
that consume it, in which no `Option` and no symbolic evaluator appear.

`garbleCorrectComp` was already free of the hypothesis; these are the intermediate results,
which were not.
-/

namespace PRG

variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}
  {kVars : ℕ → BitVector κ} {bVars : ℕ → Bool}

/-- **`gEv` never fails on a genuine garbling.**  The totality the `gEv c g i = some ov`
hypothesis was standing in for. -/
theorem gEv_isSome_of_gb {inp out : WireBundle} (c : Circuit inp out) (inlbl : labelType inp)
    (i : ℕ) (x : bundleBool inp) :
    (gEv c (gb c inlbl i).1 (gEnc inlbl x)).isSome := by
  rw [gEvCorrect c inlbl i x]
  rfl

/-- **The computational simulation lemma, without the side condition.**  On a genuine garbling
the computational evaluator computes the encoded output labels of `C(x)` — no `gEv`, no
`Option`, no hypothesis. -/
theorem gEvComp_of_gb {inp out : WireBundle} (c : Circuit inp out) (inlbl : labelType inp)
    (i : ℕ) (x : bundleBool inp)
    (gv : BitVector (shapeLength κ enc (garbledShape c)))
    (hgv : gv ∈ (evalExpr enc prg kVars bVars (gb c inlbl i).1).support) :
    gEvComp enc prg c gv (encodedLabelVal prg kVars bVars (gEnc inlbl x))
      = encodedLabelVal prg kVars bVars (gEnc (gb c inlbl i).2.1 (evalCircuit c x)) :=
  gEvComp_sim c _ _ _ (gEvCorrect c inlbl i x) gv hgv

/-- **The two evaluators agree.**  On every bit vector a garbled circuit can take, symbolic
evaluation succeeds and returns what computational evaluation computes.  The symbolic
evaluator's partiality never bites, and the computational evaluator's totality never lies —
which is the property the merged grammar put at risk, since the two disagree exactly at a hole
(`evalExpr_hidden_decrypt`) and `garble_holeFree` is why no garbling contains one. -/
theorem GEvalExpr_eq_EvaluateComp {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    (v : BitVector (shapeLength κ enc (garbleShapeFull c)))
    (hv : v ∈ (evalExpr enc prg kVars bVars (Garble c x)).support) :
    GEvalExpr c (Garble c x) = some (EvaluateComp enc prg c v) := by
  rw [garbleCorrectComp c x v hv]
  exact garbleCorrect c x

end PRG
