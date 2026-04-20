import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability

-- In this module we define some lemmas (mostly about adversary's view)
open PRG

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
  | Expression.G0 k =>
    open Classical in
    if k ∈ keys
    then Expression.G0 k
    else Expression.HiddenG0 k
  | Expression.G1 k =>
    open Classical in
    if k ∈ keys
    then Expression.G1 k
    else Expression.HiddenG1 k
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
  | Expression.G0 e => {Expression.G0 e} ∪ allParts e
  | Expression.G1 e => {Expression.G1 e} ∪ allParts e
  | Expression.Pair p1 p2 => (allParts p1) ∪ (allParts p2)
  | Expression.Perm _ p1 p2 => (allParts p1) ∪ (allParts p2)
  | Expression.Enc x e => (allParts e) ∪ allParts x
  | Expression.Hidden _ => {}
  | Expression.HiddenG0 e => {Expression.HiddenG0 e}
  | Expression.HiddenG1 e => {Expression.HiddenG1 e}
  | _ => {}

-- obsolete because keys are recursive due to PRG trees
-- def allPartsKEq (p :  Expression Shape.KeyS) :
--   allParts p = {p} := by
--   cases p <;> simp [allParts]

lemma self_in_allParts (p : Expression Shape.KeyS) : p ∈ allParts p := by
  cases p <;> simp [allParts]

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
      exact h₂ (self_in_allParts e1)
    next hn =>
      rw [ite_cond_eq_false] ; simp
      tauto
  case G0 k ih =>
    intro hZ
    have hk_in_Z : k ∈ Z := by
      apply hZ
      simp [allParts]
      exact Or.inr (self_in_allParts k)

    -- Bypass `simp` struggling with `ite` conditions by using explicit branching:
    by_cases h_keys : k ∈ keys
    · -- True branch: we know k ∈ keys, and we know k ∈ Z.
      have h_inter : k ∈ keys ∩ Z := ⟨h_keys, hk_in_Z⟩
      simp [h_keys, h_inter]
    · -- False branch: we know k ∉ keys. Thus it cannot be in the intersection.
      have h_not_inter : ¬ (k ∈ keys ∩ Z) := fun h_contra => h_keys h_contra.1
      simp [h_keys, h_not_inter]

  case G1 k ih =>
    intro hZ
    have hk_in_Z : k ∈ Z := by
      apply hZ
      simp [allParts]
      exact Or.inr (self_in_allParts k)

    by_cases h_keys : k ∈ keys
    · have h_inter : k ∈ keys ∩ Z := ⟨h_keys, hk_in_Z⟩
      simp [h_keys, h_inter]
    · have h_not_inter : ¬ (k ∈ keys ∩ Z) := fun h_contra => h_keys h_contra.1
      simp [h_keys, h_not_inter]

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

-- The following defs are obsolete and already replaced in SymbolicIndistinguishability.lean, but we keep them here for reference. They are not used in the proof of the main theorem, but they are useful for reasoning about the adversary's view and key recovery.
-- def recoveryPush {shape : Shape} (e1 e2 : Expression shape) (eb : Expression Shape.BitS) (keys : Finset (Expression Shape.KeyS)):
--   keyRecovery (Expression.Perm eb e1 e2) keys = keyRecovery e1 keys ∪ keyRecovery e2 keys := by
--     simp [keyRecovery, keyRecovery, hideEncrypted, extractKeys, extractKeys]

-- def keyRecoveryOnPair {s1 s2 : Shape} (kh : Expression s1) (eb : Expression s2) (keys : Finset (Expression Shape.KeyS)) :
--   keyRecovery (Expression.Pair kh eb) keys = keyRecovery kh keys ∪ keyRecovery eb keys  := by
--   simp [keyRecovery, keyRecovery, hideEncrypted, extractKeys, extractKeys]

-- -- upper bound
-- def keyRecoveryUpperBound {shape : Shape} (p : Expression shape) (keys : Finset (Expression Shape.KeyS)) :
--   keyRecovery p keys ⊆ extractKeys p := by
--     induction p <;> simp [keyRecovery, extractKeys, extractKeys, hideEncrypted]
--     case Pair p1 p2 IH1 IH2 =>
--       apply Finset.union_subset_union <;> try assumption
--     case Perm p1 p2 IH1 IH2 =>
--       apply Finset.union_subset_union <;> try assumption
--     case Enc p1 s e IH1 =>
--       rw [apply_ite extractKeys]
--       split <;> try assumption
--       simp [extractKeys]

lemma hideEncryptedSSmallerValue {s : Shape} (keys : Set (Expression Shape.KeyS)) (p : Expression s) : hideEncryptedS keys p ⊆ p := by
  induction p <;> simp [hideEncryptedS, ExpressionInclusion]
  case Pair p1 p2 hp1 hp2 => simp [hp1, hp2]
  case Perm b p1 p2 hp1 hp2 =>
    simp [p2, hp1, hp2, ExpressionInclusionRfl]
  case Enc k p hp =>
    rw [apply_ite ExpressionInclusion]
    split <;> simp [ExpressionInclusion, hp]
  case G0 k ih =>
    -- Split the `if k ∈ keys` statement into its True and False realities
    split
    · -- True branch: The 'if' evaluates to k.G0.
      -- We now need to prove `ExpressionInclusion k.G0 k.G0 = true`, which is reflexive!
      exact ExpressionInclusionRfl _
    · -- False branch: The 'if' evaluates to k.HiddenG0.
      -- We need to prove `ExpressionInclusion k.HiddenG0 k.G0 = true`.
      -- This should be true by the very definition of your inclusion function.
      simp [ExpressionInclusion]

  case G1 k ih =>
    split
    · exact ExpressionInclusionRfl _
    · simp [ExpressionInclusion]

lemma hideKeys2SmallerValue {s : Shape} (keys : Set (Expression Shape.KeyS)) (p : Expression s) : hideSelectedS keys p ⊆ p := by
  simp [hideSelectedS]
  apply hideEncryptedSSmallerValue

lemma keyPartsMonotoneP {s : Shape} (p1 p2 : Expression s) (h : p1 ⊆ p2) :
  extractKeys p1 ⊆ extractKeys p2 := by
  apply keyPartsMonotone
  assumption
