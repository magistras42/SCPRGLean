import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.ComputationalIndistinguishability.Def

import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.OracleSpec
import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.OracleComp
import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ

namespace PRG

-- The oracle takes a Unit (no meaningful input) and returns a pair of κ-bit strings
def oracleSpecPrg (κ : ℕ) : OracleSpec Unit :=
  fun _ => (Unit, BitVector κ × BitVector κ)

-- Real World (Seeded Oracle)
noncomputable
def prgRealOracleImpl (κ : ℕ) (prg : prgFunctions κ) (seed : BitVector κ) : QueryImpl (oracleSpecPrg κ) (OptionT PMF) := {
  impl
  | OracleSpec.OracleQuery.query _ _ =>
    pure (prg.prg0 seed, prg.prg1 seed)
}

-- Wrap it in the framework's seeded oracle structure
noncomputable
def seededPrgRealOracle (prg : prgScheme) : famSeededOracle (fun κ ↦ oracleSpecPrg κ) := {
  Seed := fun κ => BitVector κ
  seedDistr := fun κ => PMF.uniformOfFintype (BitVector κ)
  queryImpl := fun κ seed => prgRealOracleImpl κ (prg κ) seed
}

-- Ideal World (Random Oracle)
noncomputable
def prgIdealOracleImpl (κ : ℕ) : QueryImpl (oracleSpecPrg κ) (OptionT PMF) := {
  impl
  | OracleSpec.OracleQuery.query _ _ => do
    let r0 ← liftM (PMF.uniformOfFintype (BitVector κ))
    let r1 ← liftM (PMF.uniformOfFintype (BitVector κ))
    return (r0, r1)
}

-- Wrap it in the framework's seeded oracle structure (with a dummy Unit seed)
noncomputable
def seededPrgIdealOracle : famSeededOracle (fun κ ↦ oracleSpecPrg κ) := {
  Seed := fun _ => Unit
  seedDistr := fun _ => PMF.pure ()
  queryImpl := fun κ _ => prgIdealOracleImpl κ
}

-- A PRG scheme is secure if its real distribution is computationally
-- indistinguishable from the ideal random distribution.
def prgSchemeSecure (IsPolyTime : PolyFamOracleCompPred) (prg : prgScheme) : Prop :=
  CompIndistinguishabilitySeededOracle IsPolyTime (seededPrgRealOracle prg) seededPrgIdealOracle

end PRG
