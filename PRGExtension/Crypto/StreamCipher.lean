import PRGExtension.Crypto.ChaCha20

/-!
# A keyed keystream generator, and the stream cipher it builds

**What this is for.**  The assumption ledger currently carries `encryptionSchemeIndCpa` as a
hypothesis about a whole *scheme*, independent of `prgSchemeSecure`.  But the only concrete
encryption scheme in the development, `chacha20Enc`, is not an independent object: it is counter
mode over the same ChaCha20 block function the PRG uses.  Stating its security as a scheme-level
assumption hides that, and hides the fact that the two assumptions are about one primitive.

This file takes the first step toward replacing the scheme-level assumption by a primitive-level
one: it isolates the *keystream generator* `prfFunctions` that the cipher is built from, and
exhibits `chacha20Enc` as an instance of a generic construction over it (`chacha20Enc_eq`, by
`rfl`).  The security statement — a PRF game, and the reduction
`prfSchemeSecure → encryptionSchemeIndCpa (prfEnc prf)` — is **not** in this file; see the
design note at the bottom for the obstruction that shapes it.

Nothing here is an assumption, and nothing here changes an existing statement.  The two-primitive
theorems (`garblingSecure` and its relatives, which take `enc` and `prg` as independent
parameters) are untouched and remain the general form: they hold for *any* IND-CPA scheme,
including ones with no PRG inside.  What this adds is the construction a narrower, single-
primitive corollary would be stated over.
-/

namespace PRG

/-! ## The primitive -/

/-- **A keyed keystream generator.**  `stream k r n` is `n` bits of keystream (as a bit array —
the caller indexes it) for key `k` and nonce `r`.

The nonce is what makes this stronger than `prgFunctions`, and the strengthening is forced:
`prgFunctions` offers `prg0, prg1 : BitVector κ → BitVector κ` and nothing else, so a scheme
built from it has one keystream per key and encryption is deterministic — which is not IND-CPA
secure, since equal messages give equal ciphertexts.  Randomised encryption needs the keystream
to depend on per-message randomness, and that randomness is the nonce.

No laws.  Like `prgFunctions`, every obligation is in the security game, not here; what this
structure must support is the *construction* below, and that needs only a function. -/
structure prfFunctions (κ : ℕ) where
  /-- Nonce width, in bits. -/
  nonceLen : ℕ
  /-- `n` bits of keystream for a key and a nonce. -/
  stream : BitVector κ → BitVector nonceLen → ℕ → Array Bool

/-- A family of keystream generators, one per security parameter — the shape `negl` needs. -/
def prfScheme : Type := (κ : ℕ) → prfFunctions κ

/-! ## The construction -/

/-- XOR a message against the keystream for `(key, nonce)`.  Encryption *and* decryption; this
is the generic form of `ChaCha20.xorStream`. -/
def prfXor {κ n : ℕ} (prf : prfFunctions κ)
    (k : BitVector κ) (r : BitVector prf.nonceLen) (m : BitVector n) : BitVector n :=
  let ks := prf.stream k r n
  ⟨m.1.mapIdx fun i b => xor b (ks.getD i false), by rw [List.length_mapIdx]; exact m.2⟩

/-- Xoring twice against the same keystream is the identity.  As with `xorStream_xorStream`,
this uses **nothing** about the generator: correctness is a property of the mode.  The keystream
is a function of key, nonce and length, and `prfXor` preserves length. -/
theorem prfXor_prfXor {κ n : ℕ} (prf : prfFunctions κ)
    (k : BitVector κ) (r : BitVector prf.nonceLen) (m : BitVector n) :
    prfXor prf k r (prfXor prf k r m) = m := by
  apply Subtype.ext
  simp only [prfXor]
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.getElem_mapIdx, Bool.xor_assoc]

/-- **The stream cipher.**  Nonce-prefixed counter mode: draw a nonce as the coins, send it in
clear alongside the message xored with the keystream it selects.

This is an `ExecEnc`, hence computable, and `ExecEnc.spec` turns it into the
`encryptionFunctions` the computational semantics consumes — with `encrypt` *by construction*
the push-forward of the uniform distribution on nonces, which is the law the distributional
refinement of `ExecutableDistribution.lean` needs.  `decrypt_encrypt` comes free from
`prfXor_prfXor`. -/
def prfExecEnc {κ : ℕ} (prf : prfFunctions κ) : ExecEnc κ where
  encryptLength n := prf.nonceLen + n
  randLen := prf.nonceLen
  run k m r := r.append (prfXor prf k r m)
  dec k c := prfXor prf k (vecTake (n := prf.nonceLen) c) (vecDrop (n := prf.nonceLen) c)
  dec_run k m r := by simp [vecTake_append, vecDrop_append, prfXor_prfXor]

/-- The specification the stream cipher denotes: the `encryptionFunctions` that `evalExpr`,
`encryptionSchemeIndCpa` and the garbling theorems all speak about. -/
noncomputable def prfEnc {κ : ℕ} (prf : prfFunctions κ) : encryptionFunctions κ :=
  (prfExecEnc prf).spec

/-- The same, at every security parameter. -/
noncomputable def prfEncScheme (prf : prfScheme) : encryptionScheme :=
  fun κ => prfEnc (prf κ)

/-! ## The witness

ChaCha20 is not *like* an instance of the construction; it **is** one, definitionally. -/

/-- ChaCha20's keystream, as a keyed generator.  No construction — `keystream` already takes a
key, a nonce and a length, and already runs the block function in counter mode. -/
def chacha20Prf : prfFunctions 256 where
  nonceLen := 96
  stream := ChaCha20.keystream

/-- **The identification**, by `rfl`: the concrete cipher the development runs and extracts to C
is exactly the generic construction applied to ChaCha20's keystream.

This is the point of the file.  It means a reduction
`prfSchemeSecure → encryptionSchemeIndCpa (prfEnc prf)` would apply to `chacha20Enc` itself, not
to a differently-shaped cipher that merely resembles it — so the witness survives the move from
a scheme-level assumption to a primitive-level one. -/
theorem chacha20Enc_eq : chacha20Enc = prfExecEnc chacha20Prf := rfl

/-- The same identification one level up, at the specification the semantics consumes. -/
theorem chacha20Enc_spec_eq : chacha20Enc.spec = prfEnc chacha20Prf := rfl

/-! ## The relationship between the two interfaces

Is the development still a *PRG*-based one after this?  At the level of the running code, yes —
and that is a theorem, not a reading. -/

/-- The all-zero nonce. -/
def zeroNonce {κ : ℕ} (prf : prfFunctions κ) : BitVector prf.nonceLen :=
  List.Vector.replicate prf.nonceLen false

/-- **A keystream generator gives a length-doubling PRG for free**: fix the nonce, take `2 κ`
bits, split them in half.  No assumption is involved — this is a construction, the trivial
direction of the relationship between the two interfaces. -/
def prgOfPrf {κ : ℕ} (prf : prfFunctions κ) : prgFunctions κ where
  prg0 s := bvOfFn fun i => (prf.stream s (zeroNonce prf) (2 * κ)).getD i.val false
  prg1 s := bvOfFn fun i => (prf.stream s (zeroNonce prf) (2 * κ)).getD (κ + i.val) false

/-- `nonceWords` of the all-zero nonce is the all-zero nonce block. -/
theorem nonceWords_zero : ChaCha20.nonceWords (zeroNonce chacha20Prf) = #[0, 0, 0] := by
  decide

/-- At nonce zero and length `2 κ`, the keystream *is* the PRG's block. -/
theorem keystream_zeroNonce (s : BitVector 256) :
    ChaCha20.keystream s (zeroNonce chacha20Prf) 512 = prgBlock s := by
  have hr : List.range 1 = [0] := rfl
  have h0 : UInt32.ofNat 0 = 0 := rfl
  simp [ChaCha20.keystream, prgBlock, nonceWords_zero, hr, h0, Array.empty_append]

/-- **One primitive, two uses.**  ChaCha20's length-doubling PRG is exactly its keystream
generator at nonce zero: `chacha20Prg` and `chacha20Prf` are not two primitives that happen to
share an implementation, they are one primitive seen through two interfaces.

So the answer to "is this still a PRG-based implementation" is yes, and in the strongest sense:
the binary contains one block function.  What the PRF interface adds is not a second primitive
but *more access* to the same one — a nonce input and arbitrary output length.  That extra
access is exactly what `prgFunctions` cannot express, and exactly what randomised encryption
needs; closing the gap in the other direction is what `Crypto/Ggm.lean` is for. -/
theorem chacha20Prg_eq : prgOfPrf chacha20Prf = chacha20Prg := by
  have h : ∀ s : BitVector 256,
      (chacha20Prf.stream s (zeroNonce chacha20Prf) (2 * 256)) = prgBlock s :=
    keystream_zeroNonce
  simp only [prgOfPrf, chacha20Prg, h]

/-! ## Design note: why the security game is not here

The PRF game needs an **ideal** oracle that is a *random function*: querying the same nonce twice
must give the same answer, or the game is trivially winnable — the same defect that made the
first `prgSchemeSecure` unsatisfiable (`CHANGELOG.md [2026-09-16]`).

`famSeededOracle` is stateless, with all randomness in the seed.  So the random function has to
*be* the seed, and `seedDistr` is `PMF.uniformOfFintype`, so the seed type must be a `Fintype`.
That rules out the obvious domain:

* `BitVector ν → BitVector L` — fine, a `Fintype`.
* `BitVector ν × ℕ → BitVector L` — not a `Fintype`; `ℕ` is infinite.
* `(n : ℕ) → BitVector ν → BitVector n` — an infinite dependent product, the same obstruction
  recorded for `randLen` in `Executable.lean` and `writeup.md` §7.1.

So the game must be stated over a **finite** PRF domain: a nonce and a *bounded* counter, with
the generator above refined to a block function.  That bound is not an artefact — ChaCha20-CTR
has a genuine `2 ^ 32` block limit — but it means the eventual reduction carries a message-length
side condition, and the statement has to say so.  The construction in this file is deliberately
independent of that choice: it takes a variable-length `stream`, so it stands whichever way the
game is formulated. -/

end PRG
