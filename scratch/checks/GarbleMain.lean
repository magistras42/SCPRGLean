import PRGExtension.Crypto.ChaCha20
import PRGExtension.Garbling.Correctness.ExecutableCorrectness
import PRGExtension.Expression.ComputationalSemantics.Executable.ExecutableDistribution

/-!
# A garbling driver, compiled to a native binary

Used by `scratch/checks/extract-c/build.sh` to extract a standalone C implementation.  Garbles and
evaluates `notC`, `NAnd`, `andC` and `orC` over ChaCha20, checking every answer against
`evalCircuit`.

## Three randomness modes, and why the difference matters

**Default — every wire key, mask bit and nonce is drawn from `IO.getRandomBytes`.**  This is the
mode that matches the theorems: `execToDistr` (`ComputationalSemantics/ExecutableDistribution.lean`)
samples the environment from `uniformOfFintype`, and `execToDistr_eq` says what the code then
produces *is* `exprToDistr` of the specification.  Drawing each key independently from the OS is
an instance of that sampling, so nothing extra is assumed beyond the OS being a good source.

**`--seeded` — a 256-bit seed from the OS, expanded with ChaCha20.**  What a real deployment
does; nobody reads 20 KB from `/dev/urandom` per circuit.  Covered by
**`garblingSecureExecSeeded`** (`Garbling/Security/ExecutableSecurity.lean`), which is a *different*
theorem from `garblingSecureExec`: expanded keys are not uniform, only computationally
indistinguishable from uniform, so this mode additionally assumes PRG security for the expansion
and a poly-time expansion reduction.  The default mode assumes neither.

**`--fixed-seed` — the same expansion from a hardcoded seed.**  Reproducible, for demos.  The
expansion is covered as above, but a *fixed* seed is not: the security statement quantifies over
a uniformly drawn one, and with a known seed the keys are recomputable.  Demonstration only.

Note what does **not** vary between the modes: ChaCha20 is the encryption of every garbled table
entry in all three, and `chacha20Prg` is LM18's `G` at every `Dup` gate in all three.  Only the
source of the initial environment changes.

The two modes are the same code path apart from how `kVars`, `bVars` and `coins` are built —
which is the point: `garbleExecCorrect` holds for *both*, since correctness quantifies over every
environment and coin supply.  Only the security statement cares about the distribution.

Key material is never printed, even in fixed-seed mode.
-/

namespace PRG
namespace GarbleDriver

open ChaCha20

/-! ## Reading an environment out of raw bytes -/

/-- `n` bits taken from `bs`, starting at byte `byteOff`, LSB-first within each byte.  Out of
range reads as zero rather than panicking. -/
def bitsAt (bs : ByteArray) (byteOff : ℕ) (n : ℕ) : BitVector n :=
  bvOfFn fun i => ((bs.data.getD (byteOff + i.val / 8) 0 >>> UInt8.ofNat (i.val % 8)) &&& 1) == 1

/-- Raw entropy for one garbling: a 32-byte key per key variable, a byte per mask bit, a 12-byte
nonce per encryption node. -/
structure Entropy where
  keys : ByteArray
  masks : ByteArray
  nonces : ByteArray

/-- Draw the whole environment from the OS.  This is the mode the theorems cover. -/
def osEntropy (nKeys nNonces : ℕ) : IO Entropy := do
  let keys ← IO.getRandomBytes (USize.ofNat (32 * nKeys + 32))
  let masks ← IO.getRandomBytes (USize.ofNat (nKeys + 8))
  let nonces ← IO.getRandomBytes (USize.ofNat (12 * nNonces + 12))
  pure ⟨keys, masks, nonces⟩

def Entropy.kVars (e : Entropy) : ℕ → BitVector 256 := fun v => bitsAt e.keys (32 * v) 256
def Entropy.bVars (e : Entropy) : ℕ → Bool := fun v => ((e.masks.data.getD v 0) &&& 1) == 1
def Entropy.coins (e : Entropy) : ℕ → BitVector chacha20Enc.randLen :=
  fun j => bitsAt e.nonces (12 * j) 96

/-! ## Expanding one seed with ChaCha20

What a deployment does: draw a short seed, expand it.  Used by two modes — `--seeded` takes the
seed from the OS, `--fixed-seed` hardcodes it — which is deliberate, because **the fixedness is
not what puts these outside the theorem**.  The expansion is.  `--seeded` is as unproved as
`--fixed-seed`; it is merely also unpredictable.
-/

def expandedKVars (seed : BitVector 256) : ℕ → BitVector 256 := fun v =>
  let ws := block (keyWords seed) (UInt32.ofNat (v + 1)) #[0, 0, 0]
  bvOfFn fun i => bitOfWords ws i.val
def expandedBVars (seed : BitVector 256) : ℕ → Bool := fun v =>
  bitOfWords (block (keyWords seed) 0 #[0, 0, 0]) v
def expandedCoins : ℕ → BitVector chacha20Enc.randLen := fun j =>
  bvOfFn fun i => decide ((j >>> i.val) % 2 = 1)

def fixedSeed : BitVector 256 := bvOfFn fun i => decide ((i.val * 7 + 3) % 5 < 2)

/-! ## Garbling, parameterised by the environment -/

def run1 (kV : ℕ → BitVector 256) (bV : ℕ → Bool) (co : ℕ → BitVector chacha20Enc.randLen)
    (c : Circuit o o) (x : Bool) : Bool :=
  chacha20Enc.EvaluateExec chacha20Prg c (chacha20Enc.GarbleExec chacha20Prg kV bV co c x)

def run2 (kV : ℕ → BitVector 256) (bV : ℕ → Bool) (co : ℕ → BitVector chacha20Enc.randLen)
    (c : Circuit (WireBundle.PairB o o) o) (x : Bool × Bool) : Bool :=
  chacha20Enc.EvaluateExec chacha20Prg c (chacha20Enc.GarbleExec chacha20Prg kV bV co c x)

def size2 (kV : ℕ → BitVector 256) (bV : ℕ → Bool) (co : ℕ → BitVector chacha20Enc.randLen)
    (c : Circuit (WireBundle.PairB o o) o) (x : Bool × Bool) : ℕ :=
  (chacha20Enc.GarbleExec chacha20Prg kV bV co c x).toList.length

/-- Hamming weight of the garbled circuit — a cheap fingerprint of the *bits*, which vary with
the randomness even though the evaluated output does not.  That invariance is exactly what
`garbleExecCorrect` asserts: it quantifies over every environment and every coin supply. -/
def fingerprint2 (kV : ℕ → BitVector 256) (bV : ℕ → Bool)
    (co : ℕ → BitVector chacha20Enc.randLen)
    (c : Circuit (WireBundle.PairB o o) o) (x : Bool × Bool) : ℕ :=
  (chacha20Enc.GarbleExec chacha20Prg kV bV co c x).toList.foldl
    (fun acc b => if b then acc + 1 else acc) 0

/-- How much entropy the largest circuit here needs. -/
def keyCount : ℕ := getMaxVar (Garble orC (Prod.mk true true)) + 1
def nonceCount : ℕ := encCount (Garble orC (Prod.mk true true))

def report (kV : ℕ → BitVector 256) (bV : ℕ → Bool)
    (co : ℕ → BitVector chacha20Enc.randLen) : IO Unit := do
  let mut ok := true
  for x in [false, true] do
    let got := run1 kV bV co notC x
    let want : Bool := evalCircuit notC x
    ok := ok && got == want
    IO.println s!"  notC {x} -> {got}  (expected {want})"
  for p in [(false, false), (false, true), (true, false), (true, true)] do
    let q : Bool × Bool := p
    let gN := run2 kV bV co Circuit.NandC q
    let gA := run2 kV bV co andC q
    let gO := run2 kV bV co orC q
    let wN : Bool := evalCircuit Circuit.NandC q
    let wA : Bool := evalCircuit andC q
    let wO : Bool := evalCircuit orC q
    ok := ok && gN == wN && gA == wA && gO == wO
    IO.println s!"  {q.1},{q.2} -> nand {gN}  and {gA}  or {gO}"
  IO.println s!"  garbled orC: {size2 kV bV co orC (Prod.mk true true)} bits, Hamming weight {fingerprint2 kV bV co orC (Prod.mk true true)}"
  IO.println (if ok then "  all outputs match evalCircuit" else "  MISMATCH")

/-- The three modes differ *only* in how the environment is produced.  The scheme itself uses
ChaCha20 throughout in all of them: as the encryption of every garbled table entry, and as
LM18's `G` at every `Dup` gate, deriving both child wire keys from the parent. -/
def main (args : List String) : IO Unit := do
  if args.contains "--fixed-seed" then
    IO.println "randomness: ChaCha20 expansion of a FIXED 256-bit seed (reproducible)"
    IO.println "  demonstration only: the theorems quantify over a uniformly drawn seed"
    report (expandedKVars fixedSeed) (expandedBVars fixedSeed) expandedCoins
  else if args.contains "--seeded" then
    IO.println "randomness: 256-bit seed from IO.getRandomBytes, expanded with ChaCha20"
    IO.println "  what a deployment does; covered by garblingSecureExecSeeded, which assumes"
    IO.println "  PRG security for the expansion on top of what the default mode needs"
    let sb ← IO.getRandomBytes 32
    let seed := bitsAt sb 0 256
    report (expandedKVars seed) (expandedBVars seed) expandedCoins
  else
    IO.println s!"randomness: {keyCount} keys, {keyCount} mask bits and {nonceCount} nonces \
from IO.getRandomBytes"
    IO.println "  the sampling the theorems quantify over -- no expansion, nothing assumed"
    let e ← osEntropy keyCount nonceCount
    report e.kVars e.bVars e.coins

end GarbleDriver
end PRG

def main (args : List String) : IO Unit := PRG.GarbleDriver.main args
