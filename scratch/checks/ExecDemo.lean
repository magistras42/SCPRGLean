import PRGExtension.Crypto.ChaCha20
import PRGExtension.Garbling.Correctness.ExecutableCorrectness

/-!
# Running the garbling scheme, with real crypto

Garbling and evaluation, `#eval`'d end to end on ChaCha20 at κ = 256.  Not part of the library.
Run with `lake env lean scratch/checks/ExecDemo.lean` (a couple of seconds, elaboration included).

Each line below builds the symbolic `Garble c x`, evaluates it into an actual bit vector —
sampling wire keys, XORing against ChaCha20 keystream once per encryption node, with a fresh
nonce per node — then evaluates the garbled circuit: selecting rows by point-and-permute,
decrypting twice per NAND gate, and decoding against the output mask.  The answers are
`garbleExecCorrect`'s, computed rather than assumed.

Three things make this possible, all of them recent:

* `ExecEnc` (`ComputationalSemantics/Executable.lean`) is an implementation with the
  specification *derived* from it, so no `encryptionFunctions` — which is necessarily
  `noncomputable`, since `PMF.pure` has no executable code — appears in any position the
  compiler sees.
* `shapeLengthOn` (`ComputationalSemantics/Def.lean`) computes the bit-vector lengths from the
  ciphertext-length function alone.  `vecTake` / `vecDrop` consume those lengths as *data*, so
  that is what the earlier version actually foundered on.
* ChaCha20 (`Crypto/ChaCha20.lean`) instantiates the primitives: the cipher in CTR form, and the
  length-doubling PRG as the two halves of one keystream block.

**Correctness is proved; security is assumed.**  The last `example` is the general theorem, for
every circuit and every input.  `encryptionSchemeIndCpa` and `prgSchemeSecure` are not
discharged here and cannot be at a fixed key size — see `FUTURE-WORK.md`.
-/

namespace PRG
namespace ExecDemo

open ChaCha20

/-! ## An environment and a coin supply

An implementation draws these from real randomness.  Here they are derived deterministically
from a seed so the output is reproducible; `garbleExecCorrect` holds for *every* choice, so
fixing them costs nothing.  What does matter is that the coins differ per encryption node —
`evalExprExecOn` threads a counter that never repeats, and `coinsEnv` turns it into a distinct
nonce.
-/

/-- A demo seed. -/
def seed : BitVector 256 :=
  bvOfFn fun i => decide ((i.val * 7 + 3) % 5 < 2)

/-- Wire keys: block `v+1` of ChaCha20 under the seed. -/
def kEnv : ℕ -> BitVector 256 := fun v =>
  let ws := block (keyWords seed) (UInt32.ofNat (v + 1)) #[0, 0, 0]
  bvOfFn fun i => bitOfWords ws i.val

/-- Mask bits, from block 0 of the same stream. -/
def bEnv : ℕ -> Bool := fun v => bitOfWords (block (keyWords seed) 0 #[0, 0, 0]) v

/-- A fresh nonce per encryption node: the node counter, little-endian. -/
def coinsEnv : ℕ -> BitVector chacha20Enc.randLen := fun j =>
  bvOfFn fun i => decide ((j >>> i.val) % 2 = 1)

/-! ## Garble, then evaluate -/

/-- The whole pipeline: `Evaluate(Garble(C, x))`, computably. -/
def runCircuit {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) : bundleBool t :=
  chacha20Enc.EvaluateExec chacha20Prg c
    (chacha20Enc.GarbleExec chacha20Prg kEnv bEnv coinsEnv c x)

/-- How many bits the garbled circuit actually occupies. -/
def garbledSize {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) : ℕ :=
  (chacha20Enc.GarbleExec chacha20Prg kEnv bEnv coinsEnv c x).toList.length

/-! ## The runs -/

#eval (runCircuit notC true, runCircuit notC false)

#eval (runCircuit Circuit.NandC (Prod.mk false false),
       runCircuit Circuit.NandC (Prod.mk false true),
       runCircuit Circuit.NandC (Prod.mk true false),
       runCircuit Circuit.NandC (Prod.mk true true))

#eval (runCircuit andC (Prod.mk false true), runCircuit andC (Prod.mk true true))

#eval (runCircuit orC (Prod.mk false false), runCircuit orC (Prod.mk true false))

-- every answer agrees with the circuit's own semantics.  (`bundleBool o` is `Bool`, but only
-- definitionally, so the ascriptions are needed for `BEq` to be found.)
def agrees1 (c : Circuit o o) (x : Bool) : Bool :=
  let got : Bool := runCircuit c x
  let want : Bool := evalCircuit c x
  got == want

def agrees2 (c : Circuit (WireBundle.PairB o o) o) (x : Bool × Bool) : Bool :=
  let got : Bool := runCircuit c x
  let want : Bool := evalCircuit c x
  got == want

#eval [false, true].all (agrees1 notC)

#eval [Prod.mk false false, Prod.mk false true, Prod.mk true false, Prod.mk true true].all
  fun x => agrees2 Circuit.NandC x && agrees2 andC x && agrees2 orC x

-- sizes, in bits
#eval (garbledSize notC true, garbledSize Circuit.NandC (Prod.mk true true),
       garbledSize orC (Prod.mk true true))

/-- And the general statement: no `#eval`, no literals, every circuit and every input. -/
example {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    runCircuit c x = evalCircuit c x :=
  chacha20Enc.garbleExecCorrect chacha20Prg kEnv bEnv coinsEnv c x

end ExecDemo
end PRG
