import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef
import SymbolicGarbledCircuitsInLean.Expression.Renamings
import SymbolicGarbledCircuitsInLean.Expression.Lemmas.NormalizeIdempotent
import SymbolicGarbledCircuitsInLean.Garbling.Simulate
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleProof
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleHole
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.SimulateProof
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleHoleBitSwap
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.Soundness

-- This file proves the security of the garbling scheme. Thanks to the soundness theorem, the main goal here is to prove symbolic indistinguishability. The main lemma is `garblingSecure`.

def stronglyIndistinguishable {s : Shape} (e1 e2 : Expression s) : Prop :=
  ∃ (r : varRenaming), validVarRenaming r /\
   normalizeExpr (applyVarRenaming r (adversaryView e1)) = (adversaryView e2)



lemma garblingSecureAux : ∀ {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle),
  let garbled : Expression (garbleOutputShape c) := Garble c input
  let simulated : Expression (garbleOutputShape c) := SimulateG c (evalCircuit c input)
  stronglyIndistinguishable (garbled) (simulated) := by
  intro inputBundle outputBundle c input
  simp [stronglyIndistinguishable, adversaryView, GarbleExprNoProjection]
  generalize Hkeys : adversaryKeys (GarbleNoProjection c input) = keys
  rw [GarbleExprHoleCorrect]
  · rw [simulateExprHoleCorrect]
    · let inputLabel := makeLabelExp inputBundle 0
      let e0 := input2f input (fun _x ↦ false) 0
      let e1 :=(evalTotal c inputLabel.1 e0.1 inputLabel.2)
      exists (bitPerm e1.1, makeKeySwap e1.1)
      constructor
      · simp [validVarRenaming]
        constructor
        · apply bitPermInjective e1.1
        · simp [validKeyRenaming]
          exact keySwapBijective e1.1
      apply (simToGarble c input)
    · apply adversaryKeysIsFix
  · rw [<-Hkeys]
    apply adversaryKeysIsFix

lemma indistinguishableOfStronglyIndistinguishable {s : Shape} (e1 e2 : Expression s) :
  stronglyIndistinguishable e1 e2 -> symIndistinguishable e1 e2 := by
  intro H
  simp [symIndistinguishable, stronglyIndistinguishable] at *
  have ⟨r, H₁, H₂⟩ := H
  exists r
  constructor <;> try assumption
  rw [← H₂, normalizeIdempotent]

lemma garblingSecureSymbolic : ∀ {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle),
  let garbled : Expression (garbleOutputShape c) := Garble c input
  let simulated : Expression (garbleOutputShape c) := SimulateG c (evalCircuit c input)
  symIndistinguishable (garbled) (simulated) := by
    intro x y c input
    simp
    apply indistinguishableOfStronglyIndistinguishable
    apply garblingSecureAux

def exprCompIndistinguishabilityDistr  (IsPolyTime : PolyFamOracleCompPred) (enc : encryptionScheme)
  {shape : Shape} (e1 e2 : Expression shape) :=
  CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc e1)) (famDistrLift (exprToFamDistr enc e2))



theorem garblingSecure : ∀
  (IsPolyTime : PolyFamOracleCompPred) (_HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (_Hreduction : forall enc shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc expr key₀))
  (enc : encryptionScheme) (_HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle),
  let garbled : Expression (garbleOutputShape c) := Garble c input
  let simulated : Expression (garbleOutputShape c) := SimulateG c (evalCircuit c input)
  exprCompIndistinguishabilityDistr IsPolyTime enc garbled simulated :=
  by
    intro IsPolyTime HPolyTime Hreduction enc HEncIndCpa
    intro inputBundle outputBundle c input
    simp [exprCompIndistinguishabilityDistr]
    apply symbolicToSemanticIndistinguishability <;> try assumption
    apply garblingSecureSymbolic
