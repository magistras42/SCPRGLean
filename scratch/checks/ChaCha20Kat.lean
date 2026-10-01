import PRGExtension.Crypto.ChaCha20

/-!
# ChaCha20 known-answer tests

`PRGExtension/Crypto/ChaCha20.lean` proves that decryption inverts encryption, which is all
*correctness* needs and which would hold for any keystream whatsoever.  What it cannot prove is
that the keystream is ChaCha20's — that is a claim about agreement with RFC 8439, and like
`libcrux` and `lean-crypto` it is established by test vectors against an independent
implementation.

**Why eleven and not two.**  Until 2026-10-01 this file carried two vectors, and a review pointed
out that two known-answer tests cannot catch an error conditional on a particular counter or key
pattern (`FUTURE-WORK.md` R5).  The suite below is chosen so that each vector can fail
independently of the others:

| | what it exercises |
|---|---|
| A | the all-zero input, one block via the `keystream` path |
| B | two blocks via `keystream`, so the counter increment inside the fold |
| C | RFC 8439 §2.4.2's published block, reached through `block` at an explicit counter |
| D | all-ones key *and* nonce — the complement of A |
| E | counter `255`, the last value inside one byte |
| F | counter `256`, so the carry out of the low counter byte |
| G | counter `2³² − 1`, the top of the counter's range |
| H | key `80 00 … 00` — one set bit, in the first byte: bit *and* byte order of `keyWords` |
| I | nonce `80 00 … 00` — the same for `nonceWords`, and the top nonce bit that
      `Crypto/DomainSeparation.lean` reserves |
| J | 100 bytes — not a block multiple, so the truncation at the tail of `keystream` |
| K | 320 bytes — five blocks, so counters 0–4 and a long fold |

E, F, G, H and I are block-level: they call `block` with an explicit counter, which is the only
way to reach counter 255 or `2³² − 1` without generating gigabytes of keystream.

All eleven were produced with OpenSSL 3.0.13, whose `-iv` is the 16-byte
`counter (little-endian) ‖ nonce`:

```
le32() { printf '%08x' "$1" | sed 's/\(..\)\(..\)\(..\)\(..\)/\4\3\2\1/'; }
head -c <nbytes> /dev/zero | openssl enc -chacha20 -K <key-hex> -iv "$(le32 <ctr>)<nonce-hex>" \
  | xxd -p -c 1000
```

Encrypting zeros yields the keystream.  Vector C's value also appears as the second block of
vector B, which is a cross-check between the `block` and `keystream` paths.

This is **testing, not proof**, and it stays that way until an independent RFC 8439 specification
exists in Lean; `writeup.md` §8.5 scopes that and explains why it is the one piece of this
development's engineering that is tested where it could be proved.

Run with `lake env lean scratch/checks/ChaCha20Kat.lean`.
-/

namespace PRG
namespace ChaCha20Kat

open ChaCha20

/-! ## Plumbing: hex in, hex out -/

def bytesToBitArray (bs : List UInt8) : Array Bool :=
  bs.foldl (fun acc b => acc ++ Array.ofFn (n := 8) fun t => ((b >>> UInt8.ofNat t.val) &&& 1) == 1) #[]

def mkBits (n : ℕ) (bs : List UInt8) : BitVector n :=
  let a := bytesToBitArray bs
  List.Vector.ofFn fun i => a.getD i.val false

def hexVal (c : Char) : ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 55
  else 0

/-- Parse a hex string into bytes.  Odd trailing digits are dropped. -/
def bytesOfHex : List Char → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * hexVal a + hexVal b) :: bytesOfHex rest
  | _ => []

def keyOf (h : String) : BitVector 256 := mkBits 256 (bytesOfHex h.toList)
def nonceOf (h : String) : BitVector 96 := mkBits 96 (bytesOfHex h.toList)

def hexDigit (n : ℕ) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def byteAt (a : Array Bool) (j : ℕ) : ℕ :=
  (List.range 8).foldl (fun acc t => acc + (if a.getD (8 * j + t) false then 2 ^ t else 0)) 0

def hexOfBits (a : Array Bool) (nbytes : ℕ) : String :=
  (List.range nbytes).foldl
    (fun s j => let b := byteAt a j; s.push (hexDigit (b / 16)) |>.push (hexDigit (b % 16))) ""

/-- One ChaCha20 block at an explicit counter, as hex.  The only route to counters the
`keystream` fold would take gigabytes to reach. -/
def blockHex (k : BitVector 256) (ctr : ℕ) (r : BitVector 96) : String :=
  let ws := block (keyWords k) (UInt32.ofNat ctr) (nonceWords r)
  hexOfBits ((List.range 512).map (bitOfWords ws)).toArray 64

/-- `n` bytes of keystream from counter 0, as hex — the path the cipher actually uses. -/
def streamHex (k : BitVector 256) (r : BitVector 96) (nbytes : ℕ) : String :=
  hexOfBits (keystream k r (8 * nbytes)) nbytes

/-! ## The keys and nonces -/

def zeroKey : String := "0000000000000000000000000000000000000000000000000000000000000000"
def zeroNonce : String := "000000000000000000000000"
/-- `00 01 02 … 1f`, RFC 8439's running example key. -/
def key1f : String := "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
def ffKey : String := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
def ffNonce : String := "ffffffffffffffffffffffff"
/-- RFC 8439 §2.4.2's nonce. -/
def nonceRfc : String := "000000090000004a00000000"
/-- A key with no structure, so a vector that depends on key bits cannot pass by accident. -/
def keyStr : String := "0b30557a9fc4e90e33587da2c7ec11365b80a5caef14395e83a8cdf2173c6186"
/-- One set bit, in the first byte of the key. -/
def key80 : String := "8000000000000000000000000000000000000000000000000000000000000000"
/-- One set bit, in the top position of the nonce — the bit `Crypto/DomainSeparation.lean`
reserves for the PRG. -/
def nonce80 : String := "800000000000000000000000"

/-! ## The suite -/

structure Kat where
  name : String
  got  : String
  want : String

def kats : List Kat :=
  [ { name := "A  keystream, zero key/nonce, 1 block"
    , got  := streamHex (keyOf zeroKey) (nonceOf zeroNonce) 64
    , want := "76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7" ++
              "da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586" }
  , { name := "B  keystream, key 00..1f, RFC nonce, 2 blocks"
    , got  := streamHex (keyOf key1f) (nonceOf nonceRfc) 128
    , want := "8adc91fd9ff4f0f51b0fad50ff15d637e40efda206cc52c783a74200503c1582" ++
              "cd9833367d0a54d57d3c9e998f490ee69ca34c1ff9e939a75584c52d690a35d4" ++
              -- RFC 8439 §2.4.2's published counter-1 output
              "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4e" ++
              "d2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e" }
  , { name := "C  block, counter 1, RFC 8439 2.4.2"
    , got  := blockHex (keyOf key1f) 1 (nonceOf nonceRfc)
    , want := "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4e" ++
              "d2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e" }
  , { name := "D  block, all-ones key and nonce"
    , got  := blockHex (keyOf ffKey) 0 (nonceOf ffNonce)
    , want := "d6e63495eafed7fc3bf8e7c419fa77be8234a6a49df517ebab06c8f65d9f7a17" ++
              "d3a64d4b97c911e6995b65c79336220cb63b703e25d3d45f5fee90a37bbe0535" }
  , { name := "E  block, counter 255"
    , got  := blockHex (keyOf key1f) 255 (nonceOf nonceRfc)
    , want := "77ef613261a22aa6669404c2bfc3b736b10ca7d512d9a1f8f845112747d1e4f4" ++
              "6e5c8d61fe0954fe11f1b04cd7bd6bf5e763d18a64da5b91b58e52c85827ec3c" }
  , { name := "F  block, counter 256 (carry out of the low byte)"
    , got  := blockHex (keyOf key1f) 256 (nonceOf nonceRfc)
    , want := "cb694b7f060fd78bee7ef785bfa6925f95dec3287e29129bee662ba853c9259a" ++
              "1bba981fb9b3a1ab544e70fc113b49d3f320957608c99a243f8518c9cd9a78ae" }
  , { name := "G  block, counter 2^32-1"
    , got  := blockHex (keyOf key1f) 4294967295 (nonceOf nonceRfc)
    , want := "ff2941b8d740f6cbb50936bf997ebd5218cb108dc53f41c64841d0218167430c" ++
              "a03b770ca74ccb642a28194d1dedd2ed13151e25ec5d7faeb6d060bfb7e6b146" }
  , { name := "H  block, key 80 00..00 (key bit/byte order)"
    , got  := blockHex (keyOf key80) 0 (nonceOf zeroNonce)
    , want := "e29edae0466dea17f2576ce95025dd2db2d34fc81b5153f1b70a87f315a35286" ++
              "fb56db91e8dbf0a93faaa25777aad63450dae65ce3eae7fc210f54cc8f77df86" }
  , { name := "I  block, nonce 80 00..00 (nonce bit/byte order)"
    , got  := blockHex (keyOf zeroKey) 0 (nonceOf nonce80)
    , want := "fc63f996e15577c8bffcf526ab4b1a4126b13d638b21cda6e205626e5609a316" ++
              "0462f8598db94871852aae71b1bb1b9ee693f83fec57499ff9052b1f6bb41f71" }
  , { name := "J  keystream, 100 bytes (not a block multiple)"
    , got  := streamHex (keyOf keyStr) (nonceOf nonceRfc) 100
    , want := "d7cb79baaad7e6e19740a23177ce949f98190507e1d903b1cc2c95a0742319dc" ++
              "fd2927fe14438d43689bf9a31642db43452fddc5c77e54c526c6f787e65d0c13" ++
              "ae999a0d4deba460c16d80bc579f8d0763f6c07bd0b5dbf41a9f7f8fe9c907d2" ++
              "7b3681e9" }
  , { name := "K  keystream, 320 bytes (five blocks)"
    , got  := streamHex (keyOf keyStr) (nonceOf zeroNonce) 320
    , want := "ca8348f60d11e1c03bf26a9f9ad08d890e1610ec83a938bc446579d4a0daf482" ++
              "edf28be06e6e8a10fed8772883a4b6729eed2372f752a207a7838f611804a74b" ++
              "a09feda09fd3ea9312f7d400fc538f67432b7538457b59e7bac641da793ce9eb" ++
              "83f6d08aec1620292845cc90b9fe0c92b333a8cafebe50fd4f1e68bb0812f9d7" ++
              "5ac5dfaabad7a5fc189bb19b6eab26545ff88225aa678637fbc6ef8dac34c6ee" ++
              "1d2c7b72be1d96294f6ebef0905a2257098ca8813915b988ec0ab41ed1482e24" ++
              "33851ee9199f2c312659fc638a64adb476639ed1c9c8ecc3f628e2bc14786127" ++
              "b85d0cbd9745f21842efa4494eda26c1caff6da667bfd304713aa399e582d70a" ++
              "d58ad26321ae69835ad7928754e8c8eb481aba5221bcf0038caccfbd5626eb64" ++
              "624f56a73da701c1ef932667fe08b858b7a106e6bb6bbccd70233c009d83119c" }
  ]

/-! ## The checks

`failures` must print `[]` and `allPass` must print `true`. -/

#eval kats.length
#eval kats.filter (fun k => k.got != k.want) |>.map Kat.name
#eval kats.all (fun k => k.got == k.want)

/-! ## Cross-checks between the two paths

Properties rather than vectors: these must hold for *any* key, and they tie the `block` route
used by E–I to the `keystream` route the cipher actually runs on. -/

-- The PRG's two halves are the two halves of one block at counter 0 and nonce 0.
#eval decide
  ((chacha20Prg.prg0 (keyOf key1f)).toList
      = (List.range 256).map (fun i => (keystream (keyOf key1f) (nonceOf zeroNonce) 512).getD i false)
   ∧ (chacha20Prg.prg1 (keyOf key1f)).toList
      = (List.range 256).map
          (fun i => (keystream (keyOf key1f) (nonceOf zeroNonce) 512).getD (256 + i) false))

-- `keystream`'s first block is `block` at counter 0, and its second is `block` at counter 1:
-- the fold's counter really is the block counter.
#eval decide (streamHex (keyOf keyStr) (nonceOf nonceRfc) 64 = blockHex (keyOf keyStr) 0 (nonceOf nonceRfc))
#eval decide (streamHex (keyOf keyStr) (nonceOf nonceRfc) 128
  = blockHex (keyOf keyStr) 0 (nonceOf nonceRfc) ++ blockHex (keyOf keyStr) 1 (nonceOf nonceRfc))

-- Truncation is a prefix: 100 bytes agrees with the first 100 bytes of 128.
#eval decide ((streamHex (keyOf keyStr) (nonceOf nonceRfc) 100).toList
  = (streamHex (keyOf keyStr) (nonceOf nonceRfc) 128).toList.take 200)

end ChaCha20Kat
end PRG
