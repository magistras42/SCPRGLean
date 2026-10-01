import PRGExtension.Garbling.GarblingDef

/-!
# Correctness of the garbling scheme

`garbleCorrect`: evaluating `Garble(C, x)` symbolically returns `C(x)`.  This is LM18
Theorem 4 (`theorem4_holds`).
-/

namespace PRG

lemma parseEncodedBundleCorrect {u : WireBundle} (x : encodedLabelType u) :
    parseEncodedBundle (encodedLabelToExpr x) = some x := by
  induction u <;> try (simp at x; simp [parseEncodedBundle, encodedLabelToExpr, extractPair])
  case PairB v w Hv Hw => simp [Hv, Hw]
lemma parseMaskedBundleCorrect {u : WireBundle} (x : maskedLabelType u) :
    parseMaskedBundle (maskedLabelToExpr x) = some x := by
  induction u <;> (simp at x; simp [parseMaskedBundle, maskedLabelToExpr, extractPair])
  case PairB v w Hv Hw => simp [Hv, Hw]
/-- Evaluating the garbled circuit on the encoded input yields the encoded output. -/
lemma gEvCorrect {input output : WireBundle} (c : Circuit input output)
    (inlbl : labelType input) (i : ℕ) (inputVal : bundleBool input) :
    let g := gb c inlbl i
    gEv c g.1 (gEnc inlbl inputVal) = some (gEnc g.2.1 (evalCircuit c inputVal)) := by
  induction c generalizing i <;> (simp; simp at inlbl inputVal)
  case NandC =>
    simp [gb, gEv, evalCircuit, gEnc, extractPair, extractPerm, xorVarB, exprToVarOrNegVar,
      normalizeB, exprToVarOrNegVar2, gbEntry]
    cases inputVal.1 <;> cases inputVal.2 <;>
      simp [gEv, normalizeB, condSwap, decrypt, gbEntry, castVarOrNegVar, castVarOrNegVar2Bool,
        exprToVarOrNegVar2, extractPerm, xorVarB, exprToVarOrNegVar, WireLabel.bitE]
  case DupC =>
    -- the PRG case: `Gb` derives (G0 k⁰, G0 k¹) / (G1 k⁰, G1 k¹) and `GEv` re-derives
    -- G0 k / G1 k from the single encoded key k, so the two agree on either input bit
    cases inputVal <;> simp [gb, gEv, evalCircuit, gEnc, WireLabel.bitE]
  case ComposeC c1 c2 Hc1 Hc2 =>
    simp [gb, gEv, evalCircuit, gEnc, Hc1, Hc2, extractPair]
  case FirstC v w c u Hc =>
    simp [gb, gEv, evalCircuit, gEnc, Hc]
  repeat simp [gb, gEv, evalCircuit, gEnc]
lemma decodeCorrect {bundle : WireBundle} (output : bundleBool bundle) (lbl : labelType bundle) :
    decode (gEnc lbl output) (gMask lbl) = some output := by
  induction bundle
  case SimpleB =>
    simp [gEnc, gMask, decode]
    cases output <;>
      simp [xorVarB, exprToVarOrNegVar, normalizeB, castVarOrNegVar, castVarOrNegVar2Bool,
        exprToVarOrNegVar2, decode, WireLabel.bitE]
  case PairB u v Hu Hv =>
    simp at lbl output
    simp [gEnc, gMask, decode, Hu, Hv]
/-- **LM18 Theorem 4.** -/
theorem garbleCorrect {s t : WireBundle} (c : Circuit s t) (input : bundleBool s) :
    testGarbleEval c input = some (evalCircuit c input) := by
  simp [testGarbleEval, GEvalExpr, Garble, parseGarbleOutput, extractPair]
  simp [parseEncodedBundleCorrect, parseMaskedBundleCorrect]
  generalize _Hinlbl : makeLabels s 0 = inlbl
  generalize Hgb : gb c inlbl.1 inlbl.2 = g
  simp [GEval]
  have := gEvCorrect c inlbl.1 inlbl.2 input
  rw [Hgb] at this
  simp at this
  rw [this]
  simp [decodeCorrect]
/-- `Theorem4` (the named obligation) is discharged. -/
theorem theorem4_holds : Theorem4 := fun c x => garbleCorrect c x

end PRG
