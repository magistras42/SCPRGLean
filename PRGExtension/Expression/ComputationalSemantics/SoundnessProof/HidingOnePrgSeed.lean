import PRGExtension.Expression.Defs
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.EncryptionIndCpa
import PRGExtension.Expression.ComputationalSemantics.PrgSecurity

namespace PRG

/--
  The Reduction:
  We query the provided PRG oracle (which is either Real or Ideal).
  It gives us two strings (val0, val1). We then evaluate the modified expression
  (where G0/G1 are replaced by VarK idx0/idx1), binding those variables to val0 and val1.
-/
noncomputable
def reductionToPrgOracle (enc : encryptionScheme) (prg : prgScheme)
  {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ)
  (κ : ℕ) : OracleComp (withRandom (oracleSpecPrg κ)) (BitVector (shapeLength κ (enc κ) s)) := do

  -- Use `withRandom` and pass `Sum.inr ()` to route the query to the PRG oracle!
  let (val0, val1) ← (withRandom (oracleSpecPrg κ)).query (Sum.inr ()) ()

  -- 3. Evaluate the replaced expression, forcing idx0 to val0 and idx1 to val1 in the environment.
  sorry


/--
  Real World Equivalence:
  If the oracle is the REAL PRG oracle (computing prg0(seed) and prg1(seed)),
  our reduction perfectly perfectly simulates the evaluation of the original expression.
-/
lemma reductionToPrgOracleRealEq (enc : encryptionScheme) (prg : prgScheme)
  {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ) :
  compToDistrGen (seededPrgRealOracle prg) (fun κ => reductionToPrgOracle enc prg expr targetSeed idx0 idx1 κ) =
  famDistrLift (exprToFamDistr enc prg expr) := by
  sorry

/--
  Ideal World Equivalence:
  If the oracle is the IDEAL PRG oracle (returning truly random strings),
  our reduction perfectly perfectly simulates the evaluation of `replacePRG` with fresh indices.
-/
lemma reductionToPrgOracleIdealEq (enc : encryptionScheme) (prg : prgScheme)
  {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ)
  (H_diff : idx0 ≠ idx1)
  (H_fresh0 : Expression.VarK idx0 ∉ keySubterms expr)
  (H_fresh1 : Expression.VarK idx1 ∉ keySubterms expr) :
  compToDistrGen seededPrgIdealOracle (fun κ => reductionToPrgOracle enc prg expr targetSeed idx0 idx1 κ) =
  famDistrLift (exprToFamDistr enc prg (replacePRG targetSeed idx0 idx1 expr)) := by
  sorry

/--
  The Core PRG Idealization Theorem.
  Replaces `idealize_PRG_soundness` axiom using standard computational indistinguishability hops.
-/
theorem symbolicToSemanticIndistinguishabilityPrgIdealization
  (IsPolyTime : PolyFamOracleCompPred)
  -- FIX: Provide strict, explicit types for every binder inside Hreduction!
  (Hreduction : ∀ (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape)
    (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
  (enc : encryptionScheme)
  (prg : prgScheme)
  (HPrgSecure : prgSchemeSecure (fun {I Spec Output} => IsPolyTime) prg)
  {shape : Shape} (expr : Expression shape) (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ)
  (H_no_seed : targetSeed ∉ adversaryKeys expr)
  (H_diff : idx0 ≠ idx1)
  (H_fresh0 : Expression.VarK idx0 ∉ keySubterms expr)
  (H_fresh1 : Expression.VarK idx1 ∉ keySubterms expr) :
  CompIndistinguishabilityDistr (fun {I Spec Output} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg expr))
    (famDistrLift (exprToFamDistr enc prg (replacePRG targetSeed idx0 idx1 expr))) := by

  -- Rewrite the goal to be in terms of our reduction and the two seeded oracles
  rw [← reductionToPrgOracleRealEq enc prg expr targetSeed idx0 idx1]
  rw [← reductionToPrgOracleIdealEq enc prg expr targetSeed idx0 idx1 H_diff H_fresh0 H_fresh1]

  -- Apply the framework's Oracle Indistinguishability lemma here
  sorry

end PRG
