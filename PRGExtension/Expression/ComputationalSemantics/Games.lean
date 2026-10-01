import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.ComputationalIndistinguishability.Def
import PRGExtension.Expression.SymbolicIndistinguishability

import VCVio2.VCVio.OracleComp.OracleSpec
import VCVio2.VCVio.OracleComp.OracleComp
import VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# The two primitive security games

`encryptionSchemeIndCpa` and `prgSchemeSecure`: the only two cryptographic assumptions the
development makes.  Both are stated in the same shape — a pair of seeded oracles that the
ambient adversary class cannot tell apart — and both place their randomness in the **seed**
rather than in the query implementation, for the reason recorded under the PRG game below.

They were two files (`EncryptionIndCpa.lean`, `PrgSecurity.lean`) until they were merged here:
144 lines between them, always imported together, and the seed-placement argument is one
argument told twice.
-/

namespace PRG

/-!
## IND-CPA security for the encryption scheme

The left-or-right formulation, as a seeded oracle.  `oracleSpecIndCpa` indexes queries by
message length; a query carries a *pair* of messages and the oracle answers with an
encryption of one of them under a key drawn once and held in the seed.
`encryptionSchemeIndCpa` says the `Side.L` and `Side.R` oracles are indistinguishable to the
ambient adversary class.

`indCpaOracleImpl` is stateless by construction, with the key in `famSeededOracle.Seed`.  That
placement matters: an implementation sampling fresh randomness per query would answer repeated
queries independently and be trivially distinguishable.  See `CHANGELOG.md [2026-09-16]` for
exactly that bug in the PRG oracle below.
-/

def oracleSpecIndCpa (κ : ℕ) (enc : encryptionFunctions κ) : OracleSpec ℕ :=
  fun n => ((BitVector n)×(BitVector n), BitVector (enc.encryptLength n))

inductive Side : Type
  | L
  | R

def choose (w : Side) (x : X × X) : X :=
  match w with
  | Side.L => x.1
  | Side.R => x.2

noncomputable
def indCpaOracleImpl (w : Side) (κ : ℕ) (enc : encryptionFunctions κ)  (key : BitVector κ) : QueryImpl (oracleSpecIndCpa κ enc) (OptionT PMF) := {
  impl query :=
  let OracleSpec.query msg_len ⟨msg₁, msg₂⟩ := query
  enc.encrypt key (choose w (msg₁, msg₂))
}

noncomputable
def seededIndCpaOracleImpl (w : Side) (enc : encryptionScheme) : famSeededOracle (fun κ ↦ oracleSpecIndCpa κ (enc κ)) := {
  Seed κ := BitVector κ,
  seedDistr κ := PMF.uniformOfFintype (BitVector κ),
  queryImpl κ key := indCpaOracleImpl w κ (enc κ) key
}

def encryptionSchemeIndCpa (IsPolyTime : PolyFamOracleCompPred) (enc : encryptionScheme)  : Prop :=
  CompIndistinguishabilitySeededOracle IsPolyTime (seededIndCpaOracleImpl Side.L enc) (seededIndCpaOracleImpl Side.R enc)

/-!
## PRG security

The real-versus-ideal formulation, as a seeded oracle.  The real oracle draws a κ-bit seed and
answers every query with `(prg0 seed, prg1 seed)`; the ideal oracle draws a uniform 2κ-bit
pair and answers every query with that.  `prgSchemeSecure` says the two are indistinguishable.

Both oracles are stateless, with the randomness in the **seed**.  That is a fix, not an
accident: an earlier version sampled inside the query implementation, so the ideal oracle
answered two queries independently while the real one repeated itself, and a two-query
distinguisher won with probability `1 - 2 ^ (-2 κ)` — making `prgSchemeSecure` unsatisfiable
and every theorem assuming it vacuous.  See `CHANGELOG.md [2026-09-16]`.

Worth knowing: PRG security, not IND-CPA, is the hypothesis that actually constrains the
adversary class.  It is information-theoretically false against unbounded adversaries, since
`(prg0 s, prg1 s)` covers at most `2 ^ κ` of `2 ^ (2 * κ)` points.  IND-CPA is not — a
degenerate scheme satisfies it against *every* class (`scratch/archive/DegenerateEnc.lean`).
-/

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
  -- written as two independent draws (rather than `uniformOfFintype` on the product) so
  -- that it matches the shape of the reduction's own sampling; the distribution is the same
  seedDistr := fun κ => do
    let r0 ← PMF.uniformOfFintype (BitVector κ)
    let r1 ← PMF.uniformOfFintype (BitVector κ)
    PMF.pure (r0, r1)
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
