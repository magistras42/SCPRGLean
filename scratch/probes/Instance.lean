import PRGExtension

/-! Can a concrete garbling instance be built and the security theorem applied?

Answer: yes, and this file is the check — every hypothesis of `garblingSecureGenerated` that can
be supplied concretely is supplied, leaving exactly three (poly-time closure, IND-CPA, PRG
security), all of them genuine.

Repointed 2026-09-29 from the encryption-only root `SymbolicGarbledCircuitsInLean` to
`PRGExtension`, which is where `decrypt_encrypt` and `LengthPoly` live; it had stopped building
when those were added.

Two caveats on what this demonstrates.  `demoEnc` is **not** a secure scheme — it is a concrete
*inhabitant*, enough to show the statement is not vacuous, not enough to discharge `HEncIndCpa`.
And `garblingSecureGenerated` states security against `GenPolyTime demoEnc demoPrg`, a generated
class narrower than one would want (`FUTURE-WORK.md` F8); for a citable security statement use
`garblingSecure`, which quantifies over the class.  For a scheme that is actually implementable,
see `scratch/checks/ExecDemo.lean` and `PRGExtension/Crypto/ChaCha20.lean`.
-/

namespace PRG
open Shape

/-- A concrete encryption scheme: ciphertexts are the same length as plaintexts. -/
noncomputable def demoEnc : encryptionScheme := fun _ =>
  { encryptLength := fun n => n
    encrypt := fun {_} _ msg => PMF.pure msg      -- NOT secure; a concrete inhabitant
    decrypt := fun {_} _ c => c
    decrypt_encrypt := fun {_} _ msg c hc => by simpa using hc }

/-- A concrete PRG. -/
def demoPrg : prgScheme := fun _ => { prg0 := id, prg1 := id }

theorem demoEnc_lengthPoly : LengthPoly demoEnc :=
  ⟨Polynomial.X, fun κ n => by simp [demoEnc]⟩

/-- A concrete circuit: one NAND gate. -/
def demoCircuit : Circuit (o, o) o := Circuit.NandC

/-- **The instance closes.**  Everything but the three assumptions is supplied concretely. -/
theorem demoSecure
    (HPolyTime : PolyTimeClosedUnderComposition
      (fun {_ _ _} => GenPolyTime demoEnc demoPrg))
    (HEncIndCpa : encryptionSchemeIndCpa
      (fun {_ _ _} => GenPolyTime demoEnc demoPrg) demoEnc)
    (HPrgSecure : prgSchemeSecure
      (fun {_ _ _} => GenPolyTime demoEnc demoPrg) demoPrg) :
    CompIndistinguishabilityDistr (fun {_ _ _} => GenPolyTime demoEnc demoPrg)
      (famDistrLift (exprToFamDistr demoEnc demoPrg (Garble demoCircuit (true, false))))
      (famDistrLift (exprToFamDistr demoEnc demoPrg
        (Simulate demoCircuit (evalCircuit demoCircuit (true, false))))) :=
  garblingSecureGenerated demoEnc demoPrg demoEnc_lengthPoly HPolyTime HEncIndCpa HPrgSecure
    demoCircuit (true, false)

end PRG

namespace PRG

/-! ### How many of the assumptions can actually be discharged?

Before F9 this section built a degenerate scheme whose IND-CPA assumption was dischargeable
against *every* class.  `encryptionFunctions.decrypt_encrypt` has since made that scheme
illegal — see `scratch/archive/DegenerateEnc.lean` — so IND-CPA is no longer trivially satisfiable and
all the remaining hypotheses are genuine. -/

-- Is any of this executable?  The symbolic layer always was: `Garble` builds a real
-- `Expression` and `evalCircuit` runs, as below.  The computational layer is not —
-- `exprToFamDistr` is `PMF`-valued and therefore `noncomputable`.  That gap has since been
-- closed from the other side by `ExecEnc`
-- (`Expression/ComputationalSemantics/Executable/Executable.lean`), which runs and whose induced
-- distribution is *proved* equal to `exprToFamDistr` (`execToDistr_eq`); `chacha20Enc` is a
-- real instance of it.  So the answer is now "yes, via `ExecEnc`", not "no".
#eval (getMaxVar (Garble demoCircuit (true, false)))
#eval (evalCircuit demoCircuit (true, false))

end PRG
