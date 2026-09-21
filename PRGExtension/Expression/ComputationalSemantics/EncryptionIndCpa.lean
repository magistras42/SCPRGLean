import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.ComputationalIndistinguishability.Def
import VCVio2.VCVio.OracleComp.OracleSpec
import VCVio2.VCVio.OracleComp.OracleComp
import VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# IND-CPA security for the encryption scheme

The left-or-right formulation, as a seeded oracle.  `oracleSpecIndCpa` indexes queries by
message length; a query carries a *pair* of messages and the oracle answers with an
encryption of one of them under a key drawn once and held in the seed.
`encryptionSchemeIndCpa` says the `Side.L` and `Side.R` oracles are indistinguishable to the
ambient adversary class.

`indCpaOracleImpl` is stateless by construction, with the key in `famSeededOracle.Seed`.  That
placement matters: an implementation sampling fresh randomness per query would answer repeated
queries independently and be trivially distinguishable.  See `CHANGELOG.md [2026-09-16]` for
exactly that bug in `PrgSecurity.lean`.
-/

-- defines the notion of IND-CPA security for encryption schemes.
namespace PRG

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

end PRG
