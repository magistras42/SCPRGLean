import PRGExtension.Expression.ComputationalSemantics.Executable.Executable

/-!
# ChaCha20, and the primitives the framework needs

A concrete instantiation of both primitives, so that `ExecEnc` and `prgFunctions` are inhabited
by something other than a toy: ChaCha20 (RFC 8439) in pure Lean, a stream cipher built from it,
and the length-doubling PRG it gives for free.

**Why ChaCha20 rather than AES.**  Three reasons, all of them about proof burden rather than
taste.  It is ARX — add, rotate, xor on `UInt32` — so there is no S-box and no `GF(2⁸)` layer to
formalise.  It is natively a *stream* cipher, so the mode is not a construction wrapped around a
block cipher, and `dec_run` (decryption inverts encryption) reduces to **xor involution**,
needing no property of the cipher at all: `xorStream_xorStream` below is three lines and would
hold just as well if `keystream` were nonsense.  And it is natively the PRG this development
wants: `prg0`/`prg1` are the two halves of a single keystream block, so LM18's length-doubling
generator is one block call rather than a construction.

**What is proved and what is not.**  Proved: `decrypt` inverts `encrypt` (hence
`ExecEnc.dec_run`, hence `encryptionFunctions.decrypt_encrypt` for the denoted specification),
which is everything correctness needs.  Not proved, and not provable here: that this *is*
ChaCha20 — that is a claim about agreement with RFC 8439, validated by test vectors
(`scratch/checks/ChaCha20Kat.lean`, checked against OpenSSL), exactly as `libcrux` and `lean-crypto`
validate theirs.  Also not proved: security.  `encryptionSchemeIndCpa` and `prgSchemeSecure`
remain assumptions, and at a *fixed* key size they are asymptotically false for the reasons
`FUTURE-WORK.md` records — a κ-indexed family whose members stop depending on κ has
non-vanishing distinguishing advantage.  This file supplies a real implementation, not a
security proof.

**Bit order.**  A `BitVector n` here is LSB-first within each 32-bit word, words in order, which
is the same thing as RFC 8439's little-endian byte serialisation with LSB-first bits inside each
byte.  The convention is internal: it is fixed once in `bitOfWords` / `bitsToWords`.  Those two
are mutually inverse, but that is *not proved here* — nothing depends on it, since the two are
used in opposite directions and never composed in anything correctness rests on.  It is checked
end to end by the test vectors, which is where a transcription error in either would show.
-/

namespace PRG
namespace ChaCha20

/-! ## The block function (RFC 8439 §2.3) -/

/-- 32-bit left rotation. -/
def rotl32 (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- The quarter round `QUARTERROUND(a, b, c, d)` (RFC 8439 §2.1), in place. -/
def qr (s : Array UInt32) (a b c d : Nat) : Array UInt32 :=
  let A := s[a]!; let B := s[b]!; let C := s[c]!; let D := s[d]!
  let A := A + B; let D := rotl32 (D ^^^ A) 16
  let C := C + D; let B := rotl32 (B ^^^ C) 12
  let A := A + B; let D := rotl32 (D ^^^ A) 8
  let C := C + D; let B := rotl32 (B ^^^ C) 7
  (((s.set! a A).set! b B).set! c C).set! d D

/-- One double round: four column rounds, then four diagonal rounds. -/
def doubleRound (s : Array UInt32) : Array UInt32 :=
  let s := qr s 0 4 8 12
  let s := qr s 1 5 9 13
  let s := qr s 2 6 10 14
  let s := qr s 3 7 11 15
  let s := qr s 0 5 10 15
  let s := qr s 1 6 11 12
  let s := qr s 2 7 8 13
  let s := qr s 3 4 9 14
  s

/-- The initial state: the constants `"expand 32-byte k"`, the key, the counter, the nonce. -/
def initState (key : Array UInt32) (ctr : UInt32) (nonce : Array UInt32) : Array UInt32 :=
  #[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574] ++ key ++ #[ctr] ++ nonce

/-- **The ChaCha20 block function**: twenty rounds, then add the initial state. -/
def block (key : Array UInt32) (ctr : UInt32) (nonce : Array UInt32) : Array UInt32 :=
  let init := initState key ctr nonce
  let s := (List.range 10).foldl (fun acc _ => doubleRound acc) init
  Array.ofFn (n := 16) fun i => s[i.val]! + init[i.val]!

/-! ## Bits in, bits out

The framework speaks `BitVector n = List.Vector Bool n`; ChaCha20 speaks 32-bit words.  These
two conversions are inverse by construction: local bit `t` of a word is its bit at shift `t`.
-/

/-- Bit `i` of a word array, LSB-first within each word. -/
def bitOfWords (ws : Array UInt32) (i : ℕ) : Bool :=
  ((ws[i / 32]! >>> UInt32.ofNat (i % 32)) &&& 1) == 1

/-- Pack a bit array into `nwords` words, LSB-first within each word. -/
def bitsToWords (bs : Array Bool) (nwords : ℕ) : Array UInt32 :=
  Array.ofFn (n := nwords) fun w =>
    (List.range 32).foldl
      (fun acc t => if bs.getD (32 * w.val + t) false then acc ||| (1 <<< UInt32.ofNat t) else acc)
      0

/-- A 256-bit key as eight words. -/
def keyWords (k : BitVector 256) : Array UInt32 := bitsToWords k.toList.toArray 8
/-- A 96-bit nonce as three words. -/
def nonceWords (r : BitVector 96) : Array UInt32 := bitsToWords r.toList.toArray 3

/-- `n` bits of keystream: as many blocks as needed, counters `0, 1, 2, …`. -/
def keystream (k : BitVector 256) (r : BitVector 96) (n : ℕ) : Array Bool :=
  let key := keyWords k
  let nonce := nonceWords r
  (List.range ((n + 511) / 512)).foldl
    (fun acc b =>
      let blk := block key (UInt32.ofNat b) nonce
      acc ++ Array.ofFn (n := 512) fun i => bitOfWords blk i.val)
    #[]

/-! ## The stream cipher -/

/-- XOR a message against the keystream for `(key, nonce)`.  Encryption *and* decryption.

`List.mapIdx` over the underlying list rather than `ofFn`+`get`: the message is a cons list, so
indexing it per bit would be quadratic.  This is the innermost loop of both garbling and
evaluation. -/
def xorStream {n : ℕ} (k : BitVector 256) (r : BitVector 96) (m : BitVector n) : BitVector n :=
  let ks := keystream k r n
  ⟨m.1.mapIdx fun i b => xor b (ks.getD i false), by rw [List.length_mapIdx]; exact m.2⟩

/-- **The only cryptographic fact correctness needs**, and it is not about ChaCha20: xoring
twice against the same keystream is the identity.  The keystream is a function of key, nonce and
length, all three of which are unchanged between the two applications — the length because
`xorStream` preserves it. -/
theorem xorStream_xorStream {n : ℕ} (k : BitVector 256) (r : BitVector 96) (m : BitVector n) :
    xorStream k r (xorStream k r m) = m := by
  apply Subtype.ext
  simp only [xorStream]
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [List.getElem_mapIdx, Bool.xor_assoc]

end ChaCha20

/-! ## The two primitives -/

open ChaCha20

/-- **ChaCha20 as an executable encryption scheme.**  The nonce *is* the coins: `randLen = 96`,
and the ciphertext carries it, so `encryptLength n = 96 + n`.  A caller must supply distinct
coins per encryption — `evalExprExecOn` threads a counter that never repeats, which is what that
requirement is for.

Note what `dec_run` does *not* need: nothing about `block`.  Correctness here is a property of
the mode, and security is where the cipher would have to earn its keep. -/
def chacha20Enc : ExecEnc 256 where
  encryptLength n := 96 + n
  randLen := 96
  run k m r := r.append (xorStream k r m)
  dec k c := xorStream k (vecTake (n := 96) c) (vecDrop (n := 96) c)
  dec_run k m r := by simp [vecTake_append, vecDrop_append, xorStream_xorStream]

/-- One keystream block of a seed, as bits: 512 of them, which is exactly two κ = 256 keys. -/
def prgBlock (s : BitVector 256) : Array Bool :=
  let ws := block (keyWords s) 0 #[0, 0, 0]
  Array.ofFn (n := 512) fun i => bitOfWords ws i.val

/-- **The length-doubling PRG**, LM18's `G`, as the two halves of one ChaCha20 block.  No
construction: `prgFunctions` asks for two functions `BitVector κ → BitVector κ` and imposes no
law, so this is complete as it stands.  Everything of substance lives in `prgSchemeSecure`,
which is an assumption. -/
def chacha20Prg : prgFunctions 256 where
  prg0 s := let b := prgBlock s; bvOfFn fun i => b.getD i.val false
  prg1 s := let b := prgBlock s; bvOfFn fun i => b.getD (256 + i.val) false

end PRG
