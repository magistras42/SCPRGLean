import PRGExtension.Garbling.Theorem5
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
  (Hreduction : ∀ (enc : encryptionScheme) (prg : prgScheme) (shape : Shape)
    (expr : Expression shape) (key₀ : ℕ), IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (HreductionPrg : ∀ (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape)
    (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
  (enc : encryptionScheme) (prg : prgScheme)
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
  {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
  CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg (Garble c x)))
    (famDistrLift (exprToFamDistr enc prg (Simulate c (evalCircuit c x)))) :=
  symbolicToSemanticSoundness IsPolyTime HPolyTime Hreduction HreductionPrg enc prg
    HEncIndCpa HPrgSecure _ _ (theorem5 c x)

end PRG
