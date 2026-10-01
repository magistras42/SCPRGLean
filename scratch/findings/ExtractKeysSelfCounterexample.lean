import PRGExtension.Expression.SymbolicIndistinguishability

/-!
# `extractKeys_hideEncrypted_self` is false

The inherited development carried a lemma of the shape

```
keys ⊆ extractKeys (hideEncrypted keys e)
```

("hiding under a key set leaves that key set visible") and used it to close a case of the
adversary-view argument.  It is false.  This file is the witness.  The lemma was removed from
`Expression/SymbolicIndistinguishability.lean` (CHANGELOG 2026-09-16) and the case it was
closing is now discharged directly in `SoundnessProof/AdversaryView.lean`.

**Why it fails.**  The two operations are not adjoint.  `extractKeys` collects the keys a term
*carries* — for a ciphertext, the plaintext keys, not the encrypting key.  `hideEncrypted keys e`
replaces by a `Hidden` node every subterm the adversary cannot open given `keys`, and
`extractKeys` does not descend into a hole.  So the keys fed in can be destroyed rather than
preserved: one round of hiding turns the visible key set into a *different* set, and the second
round then blanks the term entirely.

This file was rewritten on 2026-09-29 from `#eval` prints to kernel-checked theorems, after
`Finset.toList` became noncomputable and broke the prints.  Nothing below is printed; it is all
decided.
-/

open PRG

/-- `Enc (VarK 0) (VarK 1)`: key `1` encrypted under key `0`. -/
def e : Expression (⦃𝕂⦄) := Expression.Enc (.VarK 0) (.VarK 1)

def keys : Finset (Expression 𝕂) := {Expression.VarK 0}

/-- The keys visible after hiding under `keys`. -/
def Y := extractKeys (hideEncrypted keys e)

/-- Holding key `0` opens the ciphertext, so one round of hiding changes nothing. -/
theorem hide_keys_e : hideEncrypted keys e = e := by decide

/-- What is then visible is the *plaintext* key, `VarK 1` — not the key we started from.  This
is the step that breaks the claim: `keys ⊄ Y` already. -/
theorem Y_eq : Y = {Expression.VarK 1} := by decide

/-- Hiding under `Y = {VarK 1}` does not open the ciphertext, which collapses to a hole. -/
theorem hide_Y_e : hideEncrypted Y e = Expression.Hidden (Expression.VarK 0) := by decide

/-- And `extractKeys` sees nothing inside a hole. -/
theorem extractKeys_hide_Y_e : extractKeys (hideEncrypted Y e) = ∅ := by decide

/-- **The refutation at `Y`.** -/
theorem extractKeys_hideEncrypted_self_false :
    ¬ (Y ⊆ extractKeys (hideEncrypted Y e)) := by decide

/-- **The refutation of the lemma as stated**, with the quantifier explicit: no such lemma can
hold at every shape, expression and key set. -/
theorem not_forall_extractKeys_hideEncrypted_self :
    ¬ (∀ {s : Shape} (e : Expression s) (keys : Finset (Expression 𝕂)),
        keys ⊆ extractKeys (hideEncrypted keys e)) := by
  intro h; exact extractKeys_hideEncrypted_self_false (h e Y)
