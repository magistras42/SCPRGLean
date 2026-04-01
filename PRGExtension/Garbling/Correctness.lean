import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef

-- This file proves the correctness of the garbling scheme at the symbolic level. The main lemma is `garbleCorrect`.

  lemma parseEncodeBundleCorrect {u : WireBundle} (x : encodedLabelType u) : parseEncodedBundle (encodedLabelToExpr x) = some x := by
    induction u <;> try (simp at x; simp [parseEncodedBundle, encodedLabelToExpr, extractPair])
    case PairB v w Hv Hw =>
      simp [Hv, Hw]

  lemma parseMaskedBundleCorrect {u : WireBundle} (x : maskedLabelType u) : parseMaskedBundle (maskedLabelToExpr x) = some x := by
    induction u <;> (simp at x;  simp [maskedLabelToExpr, parseMaskedBundle, extractPair])
    case PairB v w Hv Hw =>
    simp [Hv, Hw]

  lemma gEvCorrect {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (inputVal : bundleBool input) :
  let g := gb c inlbl i
  gEv c g.1 (gEnc inlbl inputVal) = some (gEnc g.2.1 (evalCircuit c inputVal)) := by
    induction c generalizing i <;> (simp; simp at inlbl inputVal)
    case NandC =>
      simp [gb, gEv, evalCircuit, gEnc, extractPair, extractPerm, xorVarB, exprToVarOrNegVar, normalizeB, negatedBit, exprToVarOrNegVar2, makeEntryForWire]
      cases inputVal.1 <;> cases inputVal.2 <;> simp [normalizeB, condSwap, decrypt, gb_entry, makeKey, castVarOrNegVar, castVarOrNegVar2Bool, exprToVarOrNegVar2]
    case ComposeC c1 c2 Hc1 Hc2 =>
      simp [gb, gEv, evalCircuit, gEnc, Hc1, Hc2, extractPair]
    case FirstC v w c u Hc =>
      simp [gb, gEv, evalCircuit, gEnc, Hc]
    repeat simp [gb, gEv, evalCircuit, gEnc]

  lemma decodeCorrect {bundle : WireBundle} (output : bundleBool bundle) (lbl : labelType bundle): decode (gEnc lbl output) (gMask bundle lbl) = some output
   := by
    induction bundle
    case SimpleB =>
      simp [gEnc, gMask, decode]
      cases output <;> simp [makeEntryForWire, negatedBit, xorVarB, exprToVarOrNegVar, normalizeB, castVarOrNegVar, castVarOrNegVar2Bool, exprToVarOrNegVar2, decode]
    case PairB u v Hu Hv =>
      simp at lbl output
      simp [gEnc, gMask, decode, Hu, Hv]

  lemma garbleCorrect {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle) :
    testGarbleEval c input = some (evalCircuit c input) := by
      simp [GarbleExprNoProjection, testGarbleEval, GarbleNoProjection, GEvalExpr, garbleOutputToExpr, parseGarbleOutput, extractPair]
      simp [parseEncodeBundleCorrect, parseMaskedBundleCorrect]
      generalize _Hinlbl : makeLabelExp inputBundle 0 = inlbl
      generalize Hgb : gb c inlbl.1 inlbl.2 = g
      simp [GEval]
      have := gEvCorrect c inlbl.1 inlbl.2 input
      rw [Hgb] at this
      simp at this
      rw [this]
      simp [decodeCorrect]
