import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability

-- In this module we define some lemmas (mostly about adversary's view)

noncomputable
def hideEncryptedS {s : Shape} (keys : Set (Expression Shape.KeyS)) (p : Expression s) : Expression s :=
  match p with
  | Expression.Pair e1 e2 => Expression.Pair (hideEncryptedS keys e1) (hideEncryptedS keys e2)
  | Expression.Perm b e1 e2 => Expression.Perm b (hideEncryptedS keys e1) (hideEncryptedS keys e2)
  | Expression.Enc k e =>
    open Classical in
    if k ∈ keys
    then Expression.Enc k (hideEncryptedS keys e)
    else  Expression.Hidden k
  | p => p

noncomputable
def hideSelectedS {s : Shape} (keys : Set  (Expression Shape.KeyS)) (p : Expression s) :=
  hideEncryptedS keysᶜ p

lemma hideEncryptedSUniv {s : Shape} (p : Expression s) :
  hideEncryptedS Set.univ p = p := by
  induction p <;> simp [hideEncryptedS] <;> try tauto

lemma emptyHide {s : Shape} (p : Expression s) : hideSelectedS ∅ p = p := by
  induction p <;> simp [hideSelectedS, hideEncryptedS, hideEncryptedSUniv]

def allParts {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  match p with
  | Expression.VarK e => {Expression.VarK e}
  | Expression.Pair p1 p2 => (allParts p1) ∪ (allParts p2)
  | Expression.Perm _ p1 p2 => (allParts p1) ∪ (allParts p2)
  | Expression.Enc x e => (allParts e) ∪ allParts x
  | Expression.Hidden _ => {}
  | _ => {}

def allPartsKEq (p :  Expression Shape.KeyS) :
  allParts p = {p} := by
  cases p
  simp [allParts]

lemma hideEncryptedEqS {s : Shape} (keys : Finset (Expression Shape.KeyS)) (p : Expression s) :
  hideEncryptedS keys p = hideEncrypted keys p := by
  induction p <;> simp [hideEncryptedS, hideEncrypted]
  case Pair e1 e2 ih1 ih2 =>
    simp [ih1, ih2]
  case Perm b e1 e2 ih1 ih2 =>
    simp [ih1, ih2]
  case Enc k e ih1 ih2 =>
    split <;> simp [ih1, ih2]

lemma hideEncryptedUnivAux {s : Shape} (keys Z : Set (Expression Shape.KeyS)) (p : Expression s) :
  (↑(allParts p) ⊆ Z) ->
  hideEncryptedS keys p = hideEncryptedS (keys ∩ Z) p := by
  induction p <;> simp [hideEncryptedS, hideEncrypted, allParts] <;> try tauto
  case Enc e1 e2 ih1 ih2 =>
    intro h₁ h₂
    split
    next heq =>
      have h := heq
      rw [ite_cond_eq_true] <;> simp
      rw [ih2]
      assumption
      constructor <;> try assumption
      simp [allPartsKEq] at h₂
      assumption
    next hn =>
      rw [ite_cond_eq_false] ; simp
      tauto

lemma hideEncryptedUniv {s : Shape} (keys : Set (Expression Shape.KeyS)) (p : Expression s) :
  hideEncryptedS  (keys ∩ allParts p) p = hideEncryptedS keys p := by
  rw [hideEncryptedUnivAux keys (allParts p) p]
  tauto

lemma hideKeysUniv {s : Shape} (keys : Finset (Expression Shape.KeyS)) (p : Expression s):
  hideSelectedS (allParts p \ keys) p = hideEncrypted (keys) p := by
    simp [hideSelectedS]
    rw [←hideEncryptedEqS]
    simp [Set.compl_diff, Set.compl_union]
    rw [←hideEncryptedUniv, Set.union_inter_distrib_right]
    rw [Set.compl_inter_self, Set.union_empty]
    rw [hideEncryptedUniv]

def hideEncryptedPush {shape : Shape} (e1 e2 : Expression shape) (eb : Expression Shape.BitS) (keys : Finset (Expression Shape.KeyS)):
  hideEncrypted keys (Expression.Perm eb e1 e2) = Expression.Perm eb (hideEncrypted keys e1) (hideEncrypted keys e2)
  := by simp [hideEncrypted]

def recoveryPush {shape : Shape} (e1 e2 : Expression shape) (eb : Expression Shape.BitS) (keys : Finset (Expression Shape.KeyS)):
  keyRecovery (Expression.Perm eb e1 e2) keys = keyRecovery e1 keys ∪ keyRecovery e2 keys := by
    simp [keyRecovery, keyRecovery, hideEncrypted, extractKeys, extractKeys]

def keyRecoveryOnPair {s1 s2 : Shape} (kh : Expression s1) (eb : Expression s2) (keys : Finset (Expression Shape.KeyS)) :
  keyRecovery (Expression.Pair kh eb) keys = keyRecovery kh keys ∪ keyRecovery eb keys  := by
  simp [keyRecovery, keyRecovery, hideEncrypted, extractKeys, extractKeys]

-- upper bound
def keyRecoveryUpperBound {shape : Shape} (p : Expression shape) (keys : Finset (Expression Shape.KeyS)) :
  keyRecovery p keys ⊆ extractKeys p := by
    induction p <;> simp [keyRecovery, extractKeys, extractKeys, hideEncrypted]
    case Pair p1 p2 IH1 IH2 =>
      apply Finset.union_subset_union <;> try assumption
    case Perm p1 p2 IH1 IH2 =>
      apply Finset.union_subset_union <;> try assumption
    case Enc p1 s e IH1 =>
      rw [apply_ite extractKeys]
      split <;> try assumption
      simp [extractKeys]

lemma hideEncryptedSSmallerValue {s : Shape} (keys : Set (Expression Shape.KeyS)) (p : Expression s) : hideEncryptedS keys p ⊆ p := by
  induction p <;> simp [hideEncryptedS, ExpressionInclusion]
  case Pair p1 p2 hp1 hp2 => simp [hp1, hp2]
  case Perm b p1 p2 hp1 hp2 =>
    simp [p2, hp1, hp2, ExpressionInclusionRfl]
  case Enc k p hp =>
    rw [apply_ite ExpressionInclusion]
    split <;> simp [ExpressionInclusion, hp]

lemma hideKeys2SmallerValue {s : Shape} (keys : Set (Expression Shape.KeyS)) (p : Expression s) : hideSelectedS keys p ⊆ p := by
  simp [hideSelectedS]
  apply hideEncryptedSSmallerValue

lemma keyPartsMonotoneP {s : Shape} (p1 p2 : Expression s) (h : p1 ⊆ p2) :
  extractKeys p1 ⊆ extractKeys p2 := by
  apply keyPartsMonotone
  assumption
