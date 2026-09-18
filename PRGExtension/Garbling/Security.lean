import PRGExtension.Garbling.SymbolicHiding.GarbleHoleBitSwap
import PRGExtension.Expression.ComputationalSemantics.Soundness

/-!
# Computational security of the PRG-based garbling scheme

The payoff.  LM18 Theorem 5 (`theorem5`) says the garbled circuit and the simulated one are
*symbolically* indistinguishable; LM18 Theorem 1 (`symbolicToSemanticSoundness`) says
symbolic indistinguishability implies computational indistinguishability.  Composing them
gives simulation security of the garbling scheme from IND-CPA security of the encryption
scheme and security of the PRG — with no side conditions.
-/

open PRG
namespace PRG

/-- **The garbling scheme is computationally secure.** -/
theorem garblingSecure
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
  (enc : encryptionScheme) (prg : prgScheme)
  (Hreduction : EncReductionPolyTime IsPolyTime enc prg)
  (HreductionPrg : PrgReductionPolyTime IsPolyTime enc prg)
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
  {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
  CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg (Garble c x)))
    (famDistrLift (exprToFamDistr enc prg (Simulate c (evalCircuit c x)))) :=
  symbolicToSemanticSoundness IsPolyTime HPolyTime enc prg Hreduction HreductionPrg
    HEncIndCpa HPrgSecure _ _ (theorem5 c x)

end PRG
