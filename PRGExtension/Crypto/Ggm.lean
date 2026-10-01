import PRGExtension.Crypto.StreamCipher

/-!
# GGM: a keystream generator from the length-doubling PRG alone

`Crypto/StreamCipher.lean` builds a randomised cipher from a `prfFunctions` — a keyed generator
with a *nonce* input.  That is strictly more than `prgFunctions` offers, so a cipher built that
way rests on an assumption about the keystream generator, not about the PRG.

This file closes the gap in the construction direction.  **Goldreich–Goldwasser–Micali** builds a
pseudorandom function from a length-doubling pseudorandom generator by making the generator's two
outputs the two children of a binary tree and reading the input as a path:

```
    F_k(x₁ … x_d)  =  prg_{x_d} ( … prg_{x₂} ( prg_{x₁} (k) ) … )
```

`prgFunctions` is *exactly* this interface — `prg0` and `prg1` are the left and right child
functions — which is almost certainly why LM18 specifies a length-doubling generator rather than
a PRF.  Composing with `prfExecEnc` gives `ggmEnc`: an encryption scheme whose only ingredient is
the PRG.

**What this file does and does not establish.**  The construction is here, it is computable, and
the cipher it yields inherits `decrypt_encrypt` from `prfXor_prfXor` — correctness is a property
of the mode and needs nothing from GGM.  The *security* statement — that `ggmPrf prg` is a
pseudorandom function whenever `prg` is a pseudorandom generator — is **not** proved here, and
cannot even be stated yet: it needs the PRF game, which is blocked on the `Fintype` seed
obstruction recorded at the bottom of `Crypto/StreamCipher.lean`.  See `FUTURE-WORK.md`.

Nothing here is an assumption and nothing here replaces anything.  `chacha20Enc` remains the
witness for the direct route (`chacha20Enc_eq`), and the two-primitive theorems are untouched.
-/

namespace PRG

variable {κ : ℕ}

/-! ## The tree -/

/-- **The GGM tree.**  Walk down from the key, branching on each input bit: `false` takes
`prg0`, `true` takes `prg1`.  The result is the label of the leaf at that path.

Computable, and genuinely runnable — the recursion is structural in the path. -/
def ggm (prg : prgFunctions κ) (k : BitVector κ) : List Bool → BitVector κ
  | [] => k
  | b :: bs => ggm prg (if b then prg.prg1 k else prg.prg0 k) bs

@[simp] theorem ggm_nil (prg : prgFunctions κ) (k : BitVector κ) : ggm prg k [] = k := rfl

@[simp] theorem ggm_cons (prg : prgFunctions κ) (k : BitVector κ) (b : Bool) (bs : List Bool) :
    ggm prg k (b :: bs) = ggm prg (if b then prg.prg1 k else prg.prg0 k) bs := rfl

/-- Walking a concatenated path is walking one path and then the other: the tree really is a
tree, and `ggm` is the action of the free monoid on paths. -/
theorem ggm_append (prg : prgFunctions κ) (k : BitVector κ) (xs ys : List Bool) :
    ggm prg k (xs ++ ys) = ggm prg (ggm prg k xs) ys := by
  induction xs generalizing k with
  | nil => simp
  | cons b bs ih => simp [ih]

/-! ## The keystream generator -/

/-- `i` as `w` bits, least significant first.  The block counter of counter mode. -/
def natBits (w i : ℕ) : BitVector w := bvOfFn fun j => Nat.testBit i j.val

/-- **The GGM keystream generator.**  The PRF input is the nonce followed by a block counter, so
the tree has depth `ν + cw`; successive leaves, concatenated, are the keystream.  This is
ordinary counter mode with GGM in place of a block cipher.

`cw` bounds the stream at `2 ^ cw` blocks, i.e. `κ * 2 ^ cw` bits.  That bound is not an
artefact of the formalisation — ChaCha20-CTR has one too — and it is the same bound the
eventual security statement will have to carry. -/
def ggmPrf (prg : prgFunctions κ) (ν cw : ℕ) : prfFunctions κ where
  nonceLen := ν
  stream k r n :=
    (List.range ((n + κ - 1) / κ)).foldl
      (fun acc i => acc ++ (ggm prg k (r.toList ++ (natBits cw i).toList)).toList.toArray) #[]

/-- **The cipher built from the PRG alone.**  `prfExecEnc` over `ggmPrf`: computable, and its
`decrypt_encrypt` comes from `prfXor_prfXor`, which uses nothing about the generator. -/
def ggmExecEnc (prg : prgFunctions κ) (ν cw : ℕ) : ExecEnc κ :=
  prfExecEnc (ggmPrf prg ν cw)

/-- The specification it denotes — an `encryptionFunctions` whose only ingredient is `prg`. -/
noncomputable def ggmEnc (prg : prgFunctions κ) (ν cw : ℕ) : encryptionFunctions κ :=
  prfEnc (ggmPrf prg ν cw)

/-- Correctness of the GGM cipher, spelled out: decryption inverts encryption whatever coins were
drawn.  Inherited, not re-proved — the point being that **no** property of GGM is involved. -/
theorem ggmExecEnc_dec_run (prg : prgFunctions κ) (ν cw : ℕ) {n : ℕ}
    (k : BitVector κ) (m : BitVector n) (r : BitVector (ggmExecEnc prg ν cw).randLen) :
    (ggmExecEnc prg ν cw).dec k ((ggmExecEnc prg ν cw).run k m r) = m :=
  (ggmExecEnc prg ν cw).dec_run k m r

/-! ## Families -/

/-- The generator at every security parameter. -/
def ggmPrfScheme (prg : prgScheme) (ν cw : ℕ → ℕ) : prfScheme :=
  fun κ => ggmPrf (prg κ) (ν κ) (cw κ)

/-- **The single-primitive encryption scheme.**  This is the object the one-assumption mode would
be stated over: an `encryptionScheme` constructed from a `prgScheme` and nothing else, so that
`encryptionSchemeIndCpa` applied to it would follow from `prgSchemeSecure` alone — via the GGM
theorem, which is the piece that remains. -/
noncomputable def ggmEncScheme (prg : prgScheme) (ν cw : ℕ → ℕ) : encryptionScheme :=
  prfEncScheme (ggmPrfScheme prg ν cw)

/-! ## What remains

Two statements, in order:

1. **GGM.**  `prg` pseudorandom ⟹ `ggmPrf prg ν cw` pseudorandom.  A hybrid over the `ν + cw`
   levels of the tree, with a loss of `q · (ν + cw)` for `q` queries.  Blocked on stating the
   PRF game at all; see the design note in `Crypto/StreamCipher.lean`.
2. **Counter mode.**  `prf` pseudorandom ⟹ `prfEnc prf` IND-CPA.  A hybrid over queries plus a
   birthday term for nonce collisions, which needs `ν` to grow with `κ` for `q² / 2 ^ ν` to be
   negligible.

Together they would give `prgSchemeSecure A prg → encryptionSchemeIndCpa A (ggmEncScheme prg ν cw)`,
collapsing the ledger to a single primitive assumption.  The cost of that route, recorded so it
is not discovered later: the cipher is then a GGM tree, so `chacha20Enc` no longer instantiates
it — the witness for the single-assumption mode would be a GGM tree over the ChaCha20 block
function, correct but far too slow to run.  The direct route of `Crypto/StreamCipher.lean` keeps
the fast witness and pays with a second primitive assumption.  Both are worth having, which is
why neither replaces the other. -/

end PRG
