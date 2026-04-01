import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.Def
import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Def
import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.OracleSpec
import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.OracleComp
import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ

-- defines the notion of IND-CPA security for encryption schemes.

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
