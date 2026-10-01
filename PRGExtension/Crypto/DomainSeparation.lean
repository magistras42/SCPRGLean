import PRGExtension.Crypto.StreamCipher

/-!
# Domain separation between the two uses of one keystream generator

**The problem this closes.**  The assumption ledger carries `encryptionSchemeIndCpa A enc` and
`prgSchemeSecure A prg` as hypotheses about *separate* objects.  But `Crypto/StreamCipher.lean`
proves they are not separate in the only instantiation the development offers:

* `chacha20Prg_eq : prgOfPrf chacha20Prf = chacha20Prg` — the PRG *is* the cipher's keystream
  generator seen through a narrower interface, and
* `keystream_zeroNonce` — at nonce zero, that keystream is exactly `prgBlock`, i.e.
  `prg0 k ‖ prg1 k`.

The garbling scheme uses the same key both as a PRG seed (to derive child labels at `Dup`) and as
an encryption key (to encrypt a `NAnd` row).  And `chacha20Enc` has `randLen = 96 = nonceLen`, so
its coins range over *all* nonces — the PRG's nonce among them, with probability `2⁻⁹⁶` per
encryption.  Nothing is unsound: each game hop reduces to one game, and the hybrid chains
indistinguishability relations transitively (`writeup.md` §13).  But a reader who wants to
*believe* the two assumptions jointly must supply a domain-separation argument, and the
development did not contain one.

**What this file does.**  It reserves one bit of the nonce.  Encryption draws `ν` bits of coins
and runs at the nonce `false ‖ r`; the generator runs at `true ‖ 0…0`.  `dsNonceDisjoint` is then a
theorem: no nonce the cipher can draw is the nonce the generator uses.  That is exactly the
hypothesis a PRF-based reduction needs — the two uses query the underlying function at **disjoint
inputs** — and it is an equality-level fact, not a new assumption.

**What it does not do.**  It does not prove the keystreams differ.  Two distinct nonces could in
principle give the same keystream; ruling that out *is* PRF security, which is the assumption
being set up rather than something to discharge here.  The honest scope is separation at the
query points.  See `FUTURE-WORK.md` R2.

**Nothing is replaced.**  `chacha20Enc`, `chacha20Prg` and every theorem about them are untouched,
and the extracted binary still runs on them.  This file adds the separated pair alongside, and
`oldNonceSpacesOverlap` records the gap in the original as a one-line witness so it cannot be
quietly forgotten.
-/

namespace PRG

variable {κ ν : ℕ}

/-! ## The nonce split -/

/-- A nonce built from a reserved tag bit and a body.  `false` is the cipher's half of the nonce
space, `true` the generator's. -/
def dsNonce {ν : ℕ} (tag : Bool) (r : BitVector ν) : BitVector (ν + 1) :=
  List.Vector.cons tag r

@[simp] theorem dsNonce_head {ν : ℕ} (tag : Bool) (r : BitVector ν) :
    (dsNonce tag r).head = tag := by
  simp [dsNonce]

/-- **The separation.**  A nonce tagged `false` is never a nonce tagged `true`, whatever the two
bodies are.  One line, and it is the whole content of the file: the reserved bit is readable from
the nonce, so the two halves of the space cannot meet. -/
theorem dsNonce_ne_of_tag {ν : ℕ} (r r' : BitVector ν) :
    dsNonce false r ≠ dsNonce true r' := by
  intro h
  have : (dsNonce false r).head = (dsNonce true r').head := by rw [h]
  simp at this

/-- The nonce the generator runs at: tag set, body zero. -/
def dsPrgNonce (ν : ℕ) : BitVector (ν + 1) :=
  dsNonce true (List.Vector.replicate ν false)

/-- **The theorem the ledger wanted.**  No coins the cipher can draw produce the generator's
nonce, so the two uses of one keystream generator query it at disjoint inputs. -/
theorem dsNonceDisjoint (r : BitVector ν) : dsNonce false r ≠ dsPrgNonce ν :=
  dsNonce_ne_of_tag r _

/-- The same, as a statement about the whole coin space rather than one draw. -/
theorem dsPrgNonce_not_mem_range : dsPrgNonce ν ∉ Set.range (dsNonce (ν := ν) false) := by
  rintro ⟨r, hr⟩
  exact dsNonceDisjoint r hr

/-! ## The construction

Taking the generator as a bare function rather than a `prfFunctions` keeps `nonceLen` equal to
`ν + 1` *by definition*, so nothing below needs a cast. -/

/-- The keystream generator, packaged at the split nonce width. -/
def dsPrfFns (stream : BitVector κ → BitVector (ν + 1) → ℕ → Array Bool) : prfFunctions κ where
  nonceLen := ν + 1
  stream := stream

/-- **The domain-separated cipher.**  Coins are `ν` bits; the nonce used is those bits tagged
`false`.  The ciphertext carries the full tagged nonce, so decryption needs to know nothing about
the convention — it reads the tag back off the wire.

`decrypt_encrypt` comes from `prfXor_prfXor` exactly as it does for `prfExecEnc`: correctness is a
property of the mode and uses nothing about the generator, nor about the separation. -/
def dsExecEnc (stream : BitVector κ → BitVector (ν + 1) → ℕ → Array Bool) : ExecEnc κ where
  encryptLength n := (ν + 1) + n
  randLen := ν
  run k m r := (dsNonce false r).append (prfXor (dsPrfFns stream) k (dsNonce false r) m)
  dec k c := prfXor (dsPrfFns stream) k (vecTake (n := ν + 1) c) (vecDrop (n := ν + 1) c)
  dec_run k m r := by simp [vecTake_append, vecDrop_append, prfXor_prfXor]

/-- The specification it denotes — what `evalExpr` and the IND-CPA game consume. -/
noncomputable def dsEnc (stream : BitVector κ → BitVector (ν + 1) → ℕ → Array Bool) :
    encryptionFunctions κ :=
  (dsExecEnc stream).spec

/-- **The domain-separated generator.**  The same keystream generator, at the reserved nonce. -/
def dsPrg (stream : BitVector κ → BitVector (ν + 1) → ℕ → Array Bool) : prgFunctions κ where
  prg0 s := bvOfFn fun i => (stream s (dsPrgNonce ν) (2 * κ)).getD i.val false
  prg1 s := bvOfFn fun i => (stream s (dsPrgNonce ν) (2 * κ)).getD (κ + i.val) false

/-- Correctness of the separated cipher, spelled out.  Inherited, not re-proved. -/
theorem dsExecEnc_dec_run (stream : BitVector κ → BitVector (ν + 1) → ℕ → Array Bool) {n : ℕ}
    (k : BitVector κ) (m : BitVector n) (r : BitVector (dsExecEnc stream).randLen) :
    (dsExecEnc stream).dec k ((dsExecEnc stream).run k m r) = m :=
  (dsExecEnc stream).dec_run k m r

/-- The coins of the separated cipher really are one bit narrower than its nonce: this is the
type-level record of what was given up, and it is all that was given up. -/
theorem dsExecEnc_randLen (stream : BitVector κ → BitVector (ν + 1) → ℕ → Array Bool) :
    (dsExecEnc stream).randLen + 1 = (dsPrgNonce ν).length := rfl

/-! ## Families -/

/-- The separated cipher at every security parameter. -/
noncomputable def dsEncScheme (ν : ℕ → ℕ)
    (stream : (κ : ℕ) → BitVector κ → BitVector (ν κ + 1) → ℕ → Array Bool) : encryptionScheme :=
  fun κ => dsEnc (stream κ)

/-- The separated generator at every security parameter. -/
def dsPrgScheme (ν : ℕ → ℕ)
    (stream : (κ : ℕ) → BitVector κ → BitVector (ν κ + 1) → ℕ → Array Bool) : prgScheme :=
  fun κ => dsPrg (stream κ)

/-! ## The ChaCha20 instance

`ν = 95`: a 95-bit coin space and a 96-bit nonce, which is still RFC 8439 counter mode — the
cipher is unchanged, only the set of nonces it draws from is halved. -/

/-- ChaCha20 CTR with the top nonce bit reserved. -/
def chacha20EncDS : ExecEnc 256 := dsExecEnc (ν := 95) ChaCha20.keystream

/-- ChaCha20's length-doubling generator at the reserved nonce. -/
def chacha20PrgDS : prgFunctions 256 := dsPrg (ν := 95) ChaCha20.keystream

/-- **The instantiated separation.**  This is the fact the ledger needs in order to read
`encryptionSchemeIndCpa` and `prgSchemeSecure` as assumptions about one primitive used twice at
disjoint inputs, rather than as two assumptions whose conjunction is weaker than it looks. -/
theorem chacha20_ds_nonce_disjoint (r : BitVector 95) :
    dsNonce false r ≠ dsPrgNonce 95 :=
  dsNonceDisjoint r

/-- Correctness survives the separation, by `rfl` on the mode. -/
theorem chacha20EncDS_dec_run {n : ℕ} (k : BitVector 256) (m : BitVector n)
    (r : BitVector chacha20EncDS.randLen) :
    chacha20EncDS.dec k (chacha20EncDS.run k m r) = m :=
  chacha20EncDS.dec_run k m r

/-- **The gap in the unseparated pair, recorded.**  `chacha20Enc.randLen = 96 = nonceLen`, so the
cipher's coin space is *all* of `BitVector 96`, and the old PRG's nonce — all-zero, by
`keystream_zeroNonce` — is one of the values it can draw.  The witness is `rfl`, which is the
point: there was nothing to prove, because nothing separated them. -/
theorem oldNonceSpacesOverlap :
    ∃ r : BitVector chacha20Enc.randLen, r = zeroNonce chacha20Prf :=
  ⟨zeroNonce chacha20Prf, rfl⟩

/-! ## What remains

Domain separation is a *hypothesis-shaping* result, not a security theorem.  With it, the
statement a PRF-based reduction would prove becomes sayable:

> `stream` a pseudorandom function  ⟹  `encryptionSchemeIndCpa A (dsEncScheme …)` **and**
> `prgSchemeSecure A (dsPrgScheme …)`, jointly, from the single assumption.

The joint form is the one worth having, and it is what the unseparated pair could not support.
Proving it is still blocked on stating the PRF game at all — the `Fintype` obstruction recorded at
the bottom of `Crypto/StreamCipher.lean` — so this file deliberately stops at the disjointness
fact, which needs no game and no assumption.

Two smaller consequences worth noting before anyone switches the binary over:

* The coin space halves, `2⁹⁶ → 2⁹⁵`.  For a nonce-respecting CTR mode the birthday term in the
  IND-CPA bound goes from `q²/2⁹⁶` to `q²/2⁹⁵` — one bit, and negligible either way.
* `chacha20Enc_eq`'s analogue does *not* hold for `chacha20EncDS`: it is not `prfExecEnc` of
  anything, because its `randLen` and `nonceLen` differ.  That is why `dsExecEnc` is a separate
  construction rather than a special case, and why the original is kept.
-/

end PRG
