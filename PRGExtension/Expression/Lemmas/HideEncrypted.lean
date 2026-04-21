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
    let k' := hideEncryptedS keys k
    if k ∈ keys
    then Expression.Enc k' (hideEncryptedS keys e)
    else Expression.Hidden k'
  -- G0 and G1 no longer have "Hidden" counterparts.
  -- They simply evaluate to themselves!
  -- | Expression.G0 k => Expression.G0 k
  -- | Expression.G1 k => Expression.G1 k
  | Expression.G0 e => Expression.G0 (hideEncryptedS keys e)
  | Expression.G1 e => Expression.G1 (hideEncryptedS keys e)
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
  case G0 e ih =>
    rw [ih]
    simp [hideEncrypted]
  case G1 e ih =>
    rw [ih]
    simp [hideEncrypted]

lemma hideEncryptedUnivAux {s : Shape} (keys Z : Set (Expression Shape.KeyS)) (p : Expression s) :
  (↑(allParts p) ⊆ Z) ->
  hideEncryptedS keys p = hideEncryptedS (keys ∩ Z) p := by
  induction p <;> simp [hideEncryptedS, hideEncrypted, allParts] <;> try tauto
  case G0 e ih =>
    intro h
    -- Explicitly prove the subset condition for the inner expression
    have h_sub : ↑(allParts e) ⊆ Z := by
      intro x hx
      apply h
      -- simp knows that if x ∈ A, then x ∈ insert y A
      simp [hx]
    -- Use it to rewrite with the induction hypothesis
    rw [ih h_sub]
  case G1 e ih =>
    intro h
    have h_sub : ↑(allParts e) ⊆ Z := by
      intro x hx
      apply h
      simp [hx]
    rw [ih h_sub]
  case Enc e1 e2 ih1 ih2 =>
    intro h₁ h₂
    -- Extract the fact that e1 is in Z (since all parts of e1 are in Z)
    have he1_Z : e1 ∈ Z := h₂ (self_in_allParts e1)
    split
    next heq =>
      -- We are in the branch where e1 ∈ keys.
      -- We explicitly prove the right-hand side's `if` condition is true!
      have h_intersect : e1 ∈ keys ∩ Z := ⟨heq, he1_Z⟩
      -- simp sees the proof, collapses the `if`, and splits the Enc equality into an ∧
      simp [h_intersect]
      -- Our two induction hypotheses perfectly solve the left and right children!
      rw [ih1 h₂, ih2 h₁]
      exact ⟨rfl, rfl⟩
    next hn =>
      -- We are in the branch where e1 ∉ keys.
      -- We prove the right-hand side's `if` condition is false!
      have h_intersect : ¬(e1 ∈ keys ∩ Z) := fun h => hn h.1
      simp [h_intersect]
      rw [ih1 h₂]

  -- Commented Out -  artifact from trying to prove an overly strong assumption
  -- case G0 k ih =>
  --   intro hZ
  --   have hk_in_Z : k ∈ Z := by
  --     apply hZ
  --     simp [allParts]
  --     exact Or.inr (self_in_allParts k)

  --   -- Bypass `simp` struggling with `ite` conditions by using explicit branching:
  --   by_cases h_keys : k ∈ keys
  --   · -- True branch: we know k ∈ keys, and we know k ∈ Z.
  --     have h_inter : k ∈ keys ∩ Z := ⟨h_keys, hk_in_Z⟩
  --     simp [h_keys, h_inter]
  --   · -- False branch: we know k ∉ keys. Thus it cannot be in the intersection.
  --     have h_not_inter : ¬ (k ∈ keys ∩ Z) := fun h_contra => h_keys h_contra.1
  --     simp [h_keys, h_not_inter]

  -- case G1 k ih =>
  --   intro hZ
  --   have hk_in_Z : k ∈ Z := by
  --     apply hZ
  --     simp [allParts]
  --     exact Or.inr (self_in_allParts k)

  --   by_cases h_keys : k ∈ keys
  --   · have h_inter : k ∈ keys ∩ Z := ⟨h_keys, hk_in_Z⟩
  --     simp [h_keys, h_inter]
  --   · have h_not_inter : ¬ (k ∈ keys ∩ Z) := fun h_contra => h_keys h_contra.1
  --     simp [h_keys, h_not_inter]

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
  case Pair p1 p2 hp1 hp2 =>
    simp [hp1, hp2]
  case Perm b p1 p2 hp1 hp2 =>
    simp [p2, hp1, hp2, ExpressionInclusionRfl]
  case G0 e ih =>
    exact ih
  case G1 e ih =>
    simp [ih]
  case Enc k e ih_k ih_e =>
    split
    ·
      have heq : hideEncryptedS keys k = k := shape_K_eq ih_k
      rw [heq]
      simp [ExpressionInclusion, ih_e]

    ·
      have heq : hideEncryptedS keys k = k := shape_K_eq ih_k
      rw [heq]
      simp [ExpressionInclusion, ih_e]

lemma hideEncryptedS_K (keys : Set (Expression 𝕂)) (k : Expression 𝕂) :
  hideEncryptedS keys k = k := by
  -- hideEncryptedSSmallerValue proves structural inclusion (⊆).
  -- shape_K_eq promotes that structural inclusion to strict equality for Keys!
  exact shape_K_eq (hideEncryptedSSmallerValue keys k)

lemma hideKeys2SmallerValue {s : Shape} (keys : Set (Expression Shape.KeyS)) (p : Expression s) : hideSelectedS keys p ⊆ p := by
  simp [hideSelectedS]
  apply hideEncryptedSSmallerValue

lemma keyPartsMonotoneP {s : Shape} (p1 p2 : Expression s) (h : p1 ⊆ p2) :
  extractKeys p1 ⊆ extractKeys p2 := by
  apply keyPartsMonotone
  assumption
