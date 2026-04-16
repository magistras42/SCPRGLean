import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.Expression.Lemmas.NormalizeIdempotent


open PRG

lemma getMaxVarNormalizeBI (i : ℕ): forall e, lengthOfBit e <= i -> getMaxVarBExpr (normalizeB e) = getMaxVarBExpr e := by
  induction i using Nat.strongRecOn
  case ind i Hi =>
    intro e Hl
    cases e <;> simp [normalizeB, getMaxVarBExpr]
    case Not z =>

      cases z <;> simp [normalizeB, getMaxVarBExpr]
      case Not r =>
        simp [normalizeB, getMaxVarBExpr] at Hi
        apply Hi (lengthOfBit r) _ r
        · simp []
        · simp [lengthOfBit] at Hl; omega


lemma getMaxVarNormalizeB {e : BitExpr} : getMaxVarBExpr (normalizeB e) = getMaxVarBExpr e := by
  apply getMaxVarNormalizeBI (lengthOfBit e)
  exact Nat.le_refl (lengthOfBit e)

-- lemma getMaxVarNormalize {e : Expression s} : getMaxVar (normalizeExpr e) = getMaxVar e := by
--   induction e <;> try simp [normalizeExpr, getMaxVarNormalizeB, getMaxVar]
--   case Pair s1 s2 a b Ha Hb =>
--     rw [Ha, Hb]
--   case Enc s2 a b Ha Hb =>
--     rw [Hb]
--   case Perm s1 s2 a b Ha Hb Hc =>
--     cases s2 with | BitE x =>
--     simp [normalizeExpr]
--     simp [getMaxVar]
--     generalize Hb' : normalizeB x = x'
--     rw [<-getMaxVarNormalizeB]
--     cases x'
--     case Bit d =>
--       cases d <;> rw [Hb'] <;> simp [normalizeB, getMaxVarBExpr, getMaxVar] <;> try rw [Hb, Hc] <;> simp [Nat.max_comm]
--     case VarB d =>
--       rw [Hb']
--       simp [normalizeB, getMaxVarBExpr, getMaxVar]
--       rw [Hb, Hc]
--     case Not d =>
--       rw [Hb']
--       apply normalizeBitLemma at Hb'
--       have ⟨z, hz⟩ := Hb'
--       rw [hz]
--       simp [getMaxVar, getMaxVarBExpr]
--       rw [Hb, Hc]
--       simp [Nat.max_comm]

lemma getMaxVarNormalize {e : Expression s} : getMaxVar (normalizeExpr e) = getMaxVar e := by
  induction e <;> try simp [normalizeExpr, getMaxVarNormalizeB, getMaxVar]
  case Pair s1 s2 a b Ha Hb =>
    rw [Ha, Hb]
  case Enc k e Hk He =>
    rw [He]
  case Perm s1 s2 a b Ha Hb Hc =>
    cases s2 with | BitE x =>
    simp [normalizeExpr]
    simp [getMaxVar]
    generalize Hb' : normalizeB x = x'
    rw [<-getMaxVarNormalizeB]
    cases x'
    case Bit d =>
      cases d <;> rw [Hb'] <;> simp [normalizeB, getMaxVarBExpr, getMaxVar] <;> try rw [Hb, Hc] <;> simp [Nat.max_comm]
    case VarB d =>
      rw [Hb']
      simp [normalizeB, getMaxVarBExpr, getMaxVar]
      rw [Hb, Hc]
    case Not d =>
      rw [Hb']
      apply normalizeBitLemma at Hb'
      have ⟨z, hz⟩ := Hb'
      rw [hz]
      simp [getMaxVar, getMaxVarBExpr]
      rw [Hb, Hc]
      simp [Nat.max_comm]



lemma normalizeEvalBitExprInter (bVars : ℕ -> Bool) (n : ℕ) : forall e : BitExpr, lengthOfBit e <= n -> evalBitExpr bVars e = evalBitExpr bVars (normalizeB e) := by
  induction n
  case zero =>
    intro e
    cases e <;> simp [evalBitExpr, normalizeB, lengthOfBit]
  case succ n Hn =>
    intro e
    cases e <;> simp [evalBitExpr, normalizeB, lengthOfBit]
    case Not e2 =>
      cases e2 <;> simp [evalBitExpr, normalizeB, lengthOfBit]
      intro Hi
      apply Hn
      omega


lemma normalizeEvalBitExpr (bVars : ℕ -> Bool) (e : BitExpr) : evalBitExpr bVars e = evalBitExpr bVars (normalizeB e) := by
  apply normalizeEvalBitExprInter _ (lengthOfBit e)
  omega


def finToACast {n m : ℕ} (h : n = m) : (Fin n -> a) -> (Fin m -> a) :=
  fun f x => f (Fin.cast h.symm x)

-- instance {n m : ℕ} (h : n = m) : isomp :=
--   ⟨fun f => finToACast rfl f⟩


lemma normalizeEvalExpr {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool) (e : Expression s) :
  evalExpr enc prg kVars bVars e = evalExpr enc prg kVars bVars (normalizeExpr e) := by
  induction e <;> try simp[normalizeExpr, evalExpr]
  case BitE b =>
    rw [normalizeEvalBitExpr]
  case Pair e₁ e₂ ih₁ ih₂ =>
    simp [ih₁, ih₂]
  case Enc k e ihk ihe =>
    simp [evalExpr, normalizeExpr, ihk, ihe]
  case Perm e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
    cases e₁ with | BitE a =>
    simp [evalExpr]
    rw [normalizeEvalBitExpr]
    simp [normalizeExpr]
    cases (normalizeB a)
    case BitE b =>
      simp [normalizeB, evalExpr]
      cases b <;> simp [evalBitExpr, evalExpr, ih₂, ih₃]
      conv =>
        lhs
        congr
        · skip
        · intro e
          congr
          · skip
          · skip
      simp [Bind.bind]
      rw [PMF.bind_comm]
    case VarB v =>
      simp [normalizeB, evalBitExpr, evalExpr, ih₂, ih₃]
    case Not a =>
      simp [normalizeB, evalExpr, evalBitExpr]
      cases (evalBitExpr bVars a) <;> simp [evalBitExpr, evalExpr, ih₂, ih₃]
      · simp [Bind.bind]
        rw [PMF.bind_comm]
      · simp [Bind.bind]
        rw [PMF.bind_comm]


lemma normalizeExprEvalWithVars {κ :ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (e : Expression s) :
  exprToDistr enc prg e = exprToDistr enc prg (normalizeExpr e) := by
  nth_rw 2 [exprToDistr]
  simp [evalExprVarsL]
  simp [<-normalizeEvalExpr]
  simp [exprToDistr]
  rw [<-evalExprVarsNoMatter enc prg (getMaxVar (normalizeExpr e) + 1)]
  simp [evalExprVarsL]
  simp [getMaxVarNormalize]
  omega

lemma normalizeExprToDistr (enc : encryptionScheme) (prg : prgScheme) (e : Expression s) :
  exprToFamDistr enc prg e = exprToFamDistr enc prg (normalizeExpr e) := by
  ext1 κ
  rw [exprToFamDistr]
  apply normalizeExprEvalWithVars
