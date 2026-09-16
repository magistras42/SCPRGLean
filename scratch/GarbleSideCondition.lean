import PRGExtension.Garbling.Independence
import PRGExtension.Expression.Lemmas.HideEncrypted
open PRG

-- andC = NAnd >>> (Dup >>> NAnd): the Dup's PRG-derived keys are used as encryption
-- keys by the second NAnd, which is the configuration that matters.
def e := Garble andC (true, true)

def cands : List (Expression Shape.KeyS) :=
  (List.range 10).map Expression.VarK ++
  [Expression.G0 (.VarK 4), Expression.G1 (.VarK 4),
   Expression.G0 (.VarK 5), Expression.G1 (.VarK 5)]
def nm : Expression Shape.KeyS → String
  | .VarK n => s!"K{n}" | .G0 k => s!"G0({nm k})" | .G1 k => s!"G1({nm k})"
def lst (T : Finset (Expression Shape.KeyS)) : List String :=
  (cands.filter (fun k => decide (k ∈ T))).map nm

def U := keySubterms e
def S1 := keyRecovery e U
def S2 := keyRecovery e S1
def S3 := keyRecovery e S2
def S4 := keyRecovery e S3
def S5 := keyRecovery e S4

#eval ("cards", U.card, S1.card, S2.card, S3.card, S4.card, S5.card)
#eval ("fixpoint at S4?", decide (S5 = S4))
#eval ("keySubterms e  ", lst U)
#eval ("adversaryKeys e", lst S4)
def view := hideEncrypted S4 e
#eval ("hidden keys = allParts(view) \\ extractKeys(view)", lst (allParts view \ extractKeys view))
#eval ("hidingSideCondition part 1 (all hidden keys atomic)?",
        decide (∀ k ∈ (allParts view \ extractKeys view), isAtomicKey k = true))
