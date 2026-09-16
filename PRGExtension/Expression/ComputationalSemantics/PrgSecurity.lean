import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.ComputationalIndistinguishability.Def
import PRGExtension.Expression.SymbolicIndistinguishability

import VCVio2.VCVio.OracleComp.OracleSpec
import VCVio2.VCVio.OracleComp.OracleComp
import VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ

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
--
-- NOTE (fix, see CHANGELOG 2026-09-16): the randomness MUST live in the seed, not in
-- the query implementation.  `famSeededOracle` samples `Seed` once and then runs a
-- *stateless* `queryImpl` on every query.  The previous version sampled fresh `(r0,r1)`
-- inside `impl`, so the ideal oracle answered two queries with independent values while
-- the real oracle answered both with the same `(prg0 seed, prg1 seed)`.  A distinguisher
-- that queries twice and compares therefore won with probability `1 - 2^(-2κ)`, making
-- `prgSchemeSecure` unsatisfiable and every theorem assuming it vacuous.
noncomputable
def prgIdealOracleImpl (κ : ℕ) (r : BitVector κ × BitVector κ) :
    QueryImpl (oracleSpecPrg κ) (OptionT PMF) := {
  impl
  | OracleSpec.OracleQuery.query _ _ => pure r
}

-- Wrap it in the framework's seeded oracle structure.  The seed is the pair of answers,
-- drawn uniformly once, exactly mirroring `seededPrgRealOracle` which draws one seed once.
noncomputable
def seededPrgIdealOracle : famSeededOracle (fun κ ↦ oracleSpecPrg κ) := {
  Seed := fun κ => BitVector κ × BitVector κ
  seedDistr := fun κ => PMF.uniformOfFintype (BitVector κ × BitVector κ)
  queryImpl := fun κ r => prgIdealOracleImpl κ r
}

-- A PRG scheme is secure if its real distribution is computationally
-- indistinguishable from the ideal random distribution.
def prgSchemeSecure (IsPolyTime : PolyFamOracleCompPred) (prg : prgScheme) : Prop :=
  CompIndistinguishabilitySeededOracle IsPolyTime (seededPrgRealOracle prg) seededPrgIdealOracle

-- REMOVED (see CHANGELOG 2026-09-16): `axiom idealize_PRG_soundness`.
-- It was dead (referenced only from a comment in HidingOnePrgSeed.lean) and it asserted,
-- as an axiom, precisely the theorem that
-- `symbolicToSemanticIndistinguishabilityPrgIdealization` is supposed to prove.

end PRG
