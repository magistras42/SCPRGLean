import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability


lemma normalize_renameK_commute (p : Expression s) (f : KeyRenaming) :
  normalizeExpr (applyKeyRenamingP f p) = applyKeyRenamingP f (normalizeExpr p) := by
  induction p <;> simp [normalizeExpr, applyKeyRenamingP]
  case Pair p1 p2 ih1 ih2 => simp [normalizeExpr, applyKeyRenamingP, ih1, ih2]
  case Perm s x' a p1 p2 ih1 ih2 =>
    cases x'
    case BitE x' =>
    simp [normalizeExpr, applyKeyRenamingP]
    generalize hn : normalizeB x' = a'
    cases a' <;> (simp [normalizeB, normalizeExpr, applyKeyRenamingP, ih1, ih2])
    case Bit a'' =>
      cases a'' <;> (simp [normalizeB, normalizeExpr, applyKeyRenamingP, ih1, ih2])
  case Enc s k p ih => apply ih

lemma renameB_renameK_commute (p : Expression s) (fk : KeyRenaming) (fb : BitRenaming) :
  applyBitRenaming fb (applyKeyRenamingP fk p) = applyKeyRenamingP fk (applyBitRenaming fb p) := by
  induction p <;> simp [applyBitRenaming, applyKeyRenamingP]
  case Pair p1 p2 ih1 ih2 => simp [applyBitRenaming, applyKeyRenamingP, ih1, ih2]
  case Enc s k p ih => apply ih
  case Perm a p1 p2 ih1 ih2 => simp [ih1, ih2]
