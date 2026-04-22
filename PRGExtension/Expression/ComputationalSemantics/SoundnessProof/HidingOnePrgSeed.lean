import PRGExtension.Expression.Defs
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.EncryptionIndCpa
import PRGExtension.Expression.ComputationalSemantics.PrgSecurity

namespace PRG

/-
Part 1: Theorems for reductionHidingOnePrgSeed.lean

To replace the idealize_PRG_soundness axiom from PrgSecurity.lean, you need to build a reduction
that acts as the adversary against the PRG oracle.

1. The Reduction Function
You need a function that queries the PRG oracle exactly once to get a pair
of strings (val0, val1). Then, it traverses the expression. Whenever it sees G0 targetSeed,
it substitutes val0. When it sees G1 targetSeed, it substitutes val1.

2. The Real World Equivalence
You must prove that if your reduction interacts with the Real PRG oracle (which outputs prg0(seed),
prg1(seed)), the resulting distribution perfectly matches standard evaluation of the original expression.

3. The Ideal World Equivalence
You must prove that if your reduction interacts with the Ideal PRG oracle (which outputs two
completely independent, truly random strings), the resulting distribution perfectly matches
the evaluation of replacePRG (which uses fresh VarK idx0 and VarK idx1).

4. The PRG Idealization Theorem
Combine the two lemmas above with IndistinguishabilityByReduction (just like you did for IND-CPA)
to prove the final PRG hop. This replaces the axiom.
-/

def reductionToPrgOracle (enc : encryptionScheme) (prg : prgScheme)
  {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS) :
  OracleComp (oracleSpecPrg κ) (BitVector ...)


lemma reductionToPrgOracleRealEq :
  OracleComp.simulateQ (prgRealOracleImpl κ prg targetSeed) (reductionToPrgOracle enc prg expr targetSeed) =
  liftM (exprToFamDistr enc prg expr) := by sorry


lemma reductionToPrgOracleIdealEq (idx0 idx1 : ℕ) (H_diff : idx0 ≠ idx1) (H_fresh0 : ...) (H_fresh1 : ...) :
  OracleComp.simulateQ (prgIdealOracleImpl κ) (reductionToPrgOracle enc prg expr targetSeed) =
  liftM (exprToFamDistr enc prg (replacePRG targetSeed idx0 idx1 expr)) := by sorry

theorem symbolicToSemanticIndistinguishabilityPrgIdealization
  (IsPolyTime : PolyFamOracleCompPred)
  (Hreduction : forall enc prg shape expr targetSeed, IsPolyTime (reductionToPrgOracle enc prg expr targetSeed))
  (enc : encryptionScheme) (prg : prgScheme) (HPrgSecure : prgSchemeSecure IsPolyTime prg)
  {shape : Shape} (expr : Expression shape) (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ)
  (H_no_seed : targetSeed ∉ adversaryKeys expr)
  (H_diff : idx0 ≠ idx1)
  (H_fresh0 : Expression.VarK idx0 ∉ keySubterms expr)
  (H_fresh1 : Expression.VarK idx1 ∉ keySubterms expr) :
  CompIndistinguishabilityDistr IsPolyTime
    (famDistrLift (exprToFamDistr enc prg expr))
    (famDistrLift (exprToFamDistr enc prg (replacePRG targetSeed idx0 idx1 expr))) := by sorry

end PRG
