import PRGExtension.Garbling.SymbolicHiding.GarbleProof
open PRG
-- a circuit ending in Dup: do the output-label keys occur in the expression at all?
def e := Garble Circuit.DupC true
def cands : List (Expression Shape.KeyS) :=
  [.VarK 0, .VarK 1, .G0 (.VarK 0), .G1 (.VarK 0), .G0 (.VarK 1), .G1 (.VarK 1)]
def nm : Expression Shape.KeyS → String
  | .VarK n => s!"K{n}" | .G0 k => s!"G0({nm k})" | .G1 k => s!"G1({nm k})"
def lst (T : Finset (Expression Shape.KeyS)) := (cands.filter (fun k => decide (k ∈ T))).map nm
#eval ("keySubterms (Garble Dup true)", lst (keySubterms e))
#eval ("adversaryKeys", lst (adversaryKeys e))
#eval ("output labels are (b,(G0 K0, G0 K1)) and (b,(G1 K0, G1 K1))")
#eval ("G0 K0 in keySubterms?", decide (Expression.G0 (.VarK 0) ∈ keySubterms e))
