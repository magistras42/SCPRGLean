import PRGExtension.Expression.ComputationalSemantics.Efficiency.CostModel

/-!
# The F4 loophole, and its closure

**Historical record.**  This file used to construct `constEnc`, a scheme whose ciphertext
ignores the message, and prove `constEnc_indCpa`: that it is IND-CPA secure against *every*
adversary class, including the trivial one.  That showed IND-CPA on its own constrained
nothing, and that the non-vacuity question was carried entirely by PRG security.

It was legal because `encryptionFunctions` related `encrypt` and `decrypt` by nothing.
**Adding `decrypt_encrypt` (F9, 2026-09-21g) closed the loophole**: the scheme is no longer
constructible, because its obligation reduces to `ones = msg` for every message.

Run with `lake env lean scratch/archive/DegenerateEnc.lean`.
-/

namespace PRG

/-- The obligation the degenerate scheme would now have to discharge, and why it cannot.
`encrypt key msg = pure ⟨true⟩` and `decrypt key c = ones` force `ones = msg` for every `msg`,
which fails as soon as a message has one bit that is not `true`. -/
theorem degenerateScheme_obligation_false :
    ¬ ∀ (msg : BitVector 1), (ones : BitVector 1) = msg := by
  intro h
  have := h (List.Vector.cons false List.Vector.nil)
  simp only [ones, List.Vector.replicate, List.Vector.cons] at this
  exact absurd (congrArg Subtype.val this) (by simp)

/-- What survives: the length requirement is orthogonal to correctness, so a scheme may still
have trivial ciphertext *length* — `LengthPoly` is about growth, not about hiding. -/
example : PolyLength (fun _ => 1) := PolyLength.const 1

end PRG
