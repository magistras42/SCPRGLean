import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability

def lengthOfBit : BitExpr -> Nat
| BitExpr.Not x =>
  1+lengthOfBit x
| BitExpr.Bit _ => 0
| BitExpr.VarB _ => 0


lemma normalizeBitLemmaStrong (n : ℕ):
    (x' y : BitExpr) ->
    lengthOfBit x' <= n ->
    normalizeB x' = BitExpr.Not y ->
    exists z, y = BitExpr.VarB z
  := by
  induction n <;> (try simp)
  case zero =>
    intro x' Hx' y
    cases x' <;> simp [lengthOfBit, normalizeB] at *
  case succ x Hind =>
    intro x' y Hx' Heq
    simp at Hind
    cases x' <;> try simp [normalizeB] at *
    case Not w =>
    cases w <;> try simp [normalizeB] at *
    case VarB z =>
      exists z
      exact id (Eq.symm Heq)
    case Not z =>
      apply Hind z <;> try assumption
      simp [lengthOfBit] at Hx'
      omega

lemma normalizeBitLemma (x y : BitExpr):
  normalizeB x = BitExpr.Not y ->
  exists z, y = BitExpr.VarB z
  := by
  apply normalizeBitLemmaStrong (lengthOfBit x) x
  exact Nat.le_refl (lengthOfBit x)


lemma normalizeIdempotent {s : Shape} (x : Expression s):
  normalizeExpr (normalizeExpr x) = (normalizeExpr x)
  := by
  induction x <;> try simp [normalizeExpr]
  case BitE b =>
    generalize Hb' : normalizeB b = b'
    cases b' <;> try simp [normalizeB]
    case Not b =>
      apply normalizeBitLemma at Hb'
      have ⟨z, hz⟩ := Hb'
      simp [hz]
      rfl
  case Perm x b y p1 p2 ih1 ih2 =>
    cases b
    case BitE b =>
      --simp[normalizeB, normalizeExpr]
      generalize Hb' : normalizeB b = b'
      cases b' <;> try simp [Hb', normalizeB, normalizeExpr, ih1, ih2]
      case Not r =>
        apply normalizeBitLemma at Hb'
        have ⟨z, hz⟩ := Hb'
        simp [normalizeExpr, normalizeB, ih1, ih2, Hb', hz]
      case Bit x =>
        cases x <;> simp [Hb', normalizeB, normalizeExpr, ih1, ih2]
  case Pair s1 s2 p1 p2 ih1 ih2 =>
    simp [normalizeB, normalizeExpr, ih1, ih2]
  case Enc s p1 ih1 =>
    simp [normalizeB, normalizeExpr, ih1]
