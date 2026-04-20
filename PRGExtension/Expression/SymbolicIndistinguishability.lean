import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card


import PRGExtension.Expression.Defs
import PRGExtension.Core.Fixpoints

-- The definition of symbolic indistinguishability consists of 3 parts
-- (i) Normalization, i.e. performing simple computations on the expressions
-- (ii) Variable renaming -- both key and bit variables.
-- (iii) Adversary view, i.e. hiding the parts of the expression that are not accessible to the adversary.

-- First, we define all those three parts, and then we combine them into the definition of symbolic indistinguishability.

-- Part i.  Normalization

namespace PRG

def normalizeB (p : BitExpr) : BitExpr :=
  match p with
  | BitExpr.Not (BitExpr.Not e) => normalizeB e
  | BitExpr.Not (BitExpr.Bit b) => BitExpr.Bit (not b)
  | e => e

def normalizeExpr {s : Shape} (p : Expression s) : Expression s :=
  match p with
  | Expression.BitE p => Expression.BitE (normalizeB p)
  | Expression.Perm (Expression.BitE b) p1 p2 =>
    let b' :=  normalizeB b
    let p1' := normalizeExpr p1
    let p2' := normalizeExpr p2
    match b' with
    | BitExpr.Bit b'' =>
      if b''
      then Expression.Pair p2' p1'
      else Expression.Pair p1' p2'
    | BitExpr.Not b'' =>
      Expression.Perm (Expression.BitE b'') p2' p1'
    | BitExpr.VarB k => Expression.Perm (Expression.BitE (BitExpr.VarB k)) p1' p2'
  | Expression.Pair p1 p2 => Expression.Pair  (normalizeExpr p1) (normalizeExpr p2)
  | Expression.Enc k e => Expression.Enc k (normalizeExpr e)
  | p => p

-- Part ii. Variable renaming

-- We start with key-variable renaming, which is a bijection of type ℕ → ℕ.

def KeyRenaming : Type := ℕ → ℕ

def validKeyRenaming (r : KeyRenaming) : Prop := Function.Bijective r

-- In order to apply the renaming to an expression, we apply it to each variable.
def applyKeyRenamingP {s : Shape} (r : KeyRenaming) (e : Expression s) : Expression s :=
  match e with
  | Expression.VarK n => Expression.VarK (r n)
  | Expression.Pair e1 e2 => Expression.Pair (applyKeyRenamingP r e1) (applyKeyRenamingP r e2)
  | Expression.Perm b e1 e2 => Expression.Perm b (applyKeyRenamingP r e1) (applyKeyRenamingP r e2)
  | Expression.Enc e1 e2 => Expression.Enc (applyKeyRenamingP r e1) (applyKeyRenamingP r e2)
  | Expression.Hidden e => Expression.Hidden (applyKeyRenamingP r e)
  | Expression.G0 e => Expression.G0 (applyKeyRenamingP r e)
  | Expression.G1 e => Expression.G1 (applyKeyRenamingP r e)
  | Expression.HiddenG0 e => Expression.HiddenG0 (applyKeyRenamingP r e)
  | Expression.HiddenG1 e => Expression.HiddenG1 (applyKeyRenamingP r e)
  | e => e

-- Next, we define bit-variable, which is a bit complicated.

-- A bit renaming maps each variable `i` either to another variable `j` or to a negation of another variable `¬j`.

inductive VarOrNegVar : Type
| Var : Nat → VarOrNegVar
| NegVar : Nat → VarOrNegVar

instance : Nonempty VarOrNegVar :=
  ⟨VarOrNegVar.Var 0⟩

def BitRenaming := Nat → VarOrNegVar

-- A bit renaming is valid, if after casting it to a function ℕ → ℕ, it is a bijection.

def castVarOrNegVar (v : VarOrNegVar) : Nat :=
  match v with
  | VarOrNegVar.Var n => n
  | VarOrNegVar.NegVar n => n

def validBitRenaming (r : BitRenaming) : Prop :=
  Function.Bijective (castVarOrNegVar ∘ r)

-- Finally, we show how to apply the bit renaming to an expression.

def varOrNegVarToExpr (v : VarOrNegVar) : BitExpr :=
  match v with
  | VarOrNegVar.Var n => BitExpr.VarB n
  | VarOrNegVar.NegVar n => BitExpr.Not (BitExpr.VarB n)

def applyBitRenamingB (r : BitRenaming) (e : BitExpr) : BitExpr :=
  match e with
  | BitExpr.VarB n => varOrNegVarToExpr (r n)
  | BitExpr.Not e' => BitExpr.Not (applyBitRenamingB r e')
  | e => e

def applyBitRenaming {s : Shape} (r : BitRenaming) (p : Expression s) : Expression s :=
  match p with
  | Expression.BitE e => Expression.BitE (applyBitRenamingB r e)
  | Expression.Pair p1 p2 => Expression.Pair (applyBitRenaming r p1) (applyBitRenaming r p2)
  | Expression.Perm b p1 p2 => Expression.Perm (applyBitRenamingB r b) (applyBitRenaming r p1) (applyBitRenaming r p2)
  | Expression.Enc k e => Expression.Enc k (applyBitRenaming r e)
  | p => p

-- Finally, we are ready to define the total renaming which is a pair of bit and key renaming.

def varRenaming : Type := (BitRenaming × KeyRenaming)

def validVarRenaming (r : varRenaming) : Prop :=
  validBitRenaming r.1 ∧ validKeyRenaming r.2

def applyVarRenaming {s : Shape} (r : varRenaming) (e : Expression s) : Expression s :=
  applyKeyRenamingP r.2 (applyBitRenaming r.1 e)

-- Part iii. Adversary view

-- The goal of this section is defining adversary view, which is a function that hides
-- the parts of the expressions that are not accessible to the adversary.

-- This function traverses the expression to find all key-shaped subterms.
-- This provides the finite "universe" of keys that bounds the PRG derivation
-- and prevents infinite loops in Lean.
def keySubterms {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  match p with
  | Expression.VarK e => {Expression.VarK e}
  | Expression.G0 e => {Expression.G0 e} ∪ keySubterms e
  | Expression.G1 e => {Expression.G1 e} ∪ keySubterms e
  | Expression.Pair p1 p2 => keySubterms p1 ∪ keySubterms p2
  | Expression.Perm _ p1 p2 => keySubterms p1 ∪ keySubterms p2
  | Expression.Enc k e => keySubterms k ∪ keySubterms e
  | Expression.Hidden k => keySubterms k
  | Expression.HiddenG0 k => keySubterms k
  | Expression.HiddenG1 k => keySubterms k
  | _ => ∅

-- Lean doesn't like anonymous match statements inside lambdas,
-- so we need to define a helper function that returns a Bool.
-- When we extract it, Lean no longer has to guess how to push the
-- Decidable typeclass through the branches :)
def isDerived (known : Finset (Expression Shape.KeyS)) (k : Expression Shape.KeyS) : Bool :=
  match k with
  | Expression.G0 seed => decide (seed ∈ known)
  | Expression.G1 seed => decide (seed ∈ known)
  | _ => false

-- A single step of derivation: Adds G0(k) or G1(k) if 'k' is currently known
def prgStep (univKeys : Finset (Expression Shape.KeyS)) (known : Finset (Expression Shape.KeyS)) : Finset (Expression Shape.KeyS) :=
  known ∪ univKeys.filter (fun k => isDerived known k)

-- The bounded equivalent of G*(S) from Li's paper
def prgClosure (univKeys : Finset (Expression Shape.KeyS)) (S : Finset (Expression Shape.KeyS)) : Finset (Expression Shape.KeyS) :=
  -- We fold (iterate) prgStep over the set `S`, bounded by the size of the universe
  (List.range (univKeys.card + 1)).foldl (fun currentS _ => prgStep univKeys currentS) S

-- We start by defining a function `hideEncrypted` which hides all parts of the expression
-- that cannot be decrypted using the available keys.
-- This is the function 'p' from the paper.
def hideEncrypted {s : Shape} (keys : Finset (Expression Shape.KeyS)) (p : Expression s) : Expression s :=
  match p with
  | Expression.Pair e1 e2 => Expression.Pair (hideEncrypted keys e1) (hideEncrypted keys e2)
  | Expression.Perm b e1 e2 => Expression.Perm b (hideEncrypted keys e1) (hideEncrypted keys e2)
  | Expression.Enc k e =>
    if k ∈ keys
    then Expression.Enc k (hideEncrypted keys e)
    else  Expression.Hidden k
  | Expression.G0 k =>
    if k ∈ keys
    then Expression.G0 k
    else Expression.HiddenG0 k
  | Expression.G1 k =>
    if k ∈ keys
    then Expression.G1 k
    else Expression.HiddenG1 k
  | p => p

-- Next, we define a function that only extracts those keys that are actually present in the expression
-- (and are are not merely used to encrypt the data)
def extractKeys {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  match p with
  | Expression.VarK e => {Expression.VarK e}
  | Expression.Pair p1 p2 => (extractKeys p1) ∪ (extractKeys p2)
  | Expression.Perm _ p1 p2 => (extractKeys p1) ∪ (extractKeys p2)
  -- We omit the key used for encryption
  | Expression.Enc _ e => (extractKeys e)
  | Expression.Hidden _ => ∅
  -- The adversary learns the PRG output, but cannot extract the underlying seed
  | Expression.G0 e => {Expression.G0 e}
  | Expression.G1 e => {Expression.G1 e}
  | Expression.HiddenG0 _ => ∅
  | Expression.HiddenG1 _ => ∅
  | _ => ∅

-- Next, we define the 'key recovery operator (𝓕ₑ from the paper), that given a set of keys,
-- hides the encrypted parts of the expression and computes `extractKeys` from the resulting expressions.
def keyRecovery {s : Shape} (p : Expression s) (S : Finset (Expression Shape.KeyS)) : Finset (Expression Shape.KeyS) :=
  -- Determine the finite universe of sub-keys in the expression
  let univKeys := keySubterms p

  -- The adversary computes all PRG derivations for current keys
  let expandedS := prgClosure univKeys S

  -- The adversary attempts to decrypt the expression using these expanded keys
  let view := hideEncrypted expandedS p

  -- The adversary extracts whatever new plaintext keys are revealed
  let extracted := extractKeys view

  -- The adversary computes all PRG derivations for newly extracted keys
  prgClosure univKeys extracted



-- In order to compute the adversary view, we need to compute the greatest fix point of the `keyRecovery`.
-- For this, we need to prove that the `keyRecovery` is monotone, i.e. if `S ⊆ T`, then `keyRecovery p S ⊆ keyRecovery p T`.

-- We start by defining an auxiliary order on the expressions,
-- based on the assertion that Hidden should be smaller than Enc.
def ExpressionInclusion :  {s : Shape} -> (p1 : Expression s) -> (p2 : Expression s) -> Bool
| .(_), Expression.BitE e1, Expression.BitE e2 => e1 == e2
| .(_), Expression.VarK e1, Expression.VarK  e2 => e1 == e2
| .(_), Expression.Pair p1 p2, Expression.Pair p1' p2' => ExpressionInclusion p1 p1' ∧ ExpressionInclusion p2 p2'
| .(_), Expression.Perm z p1 p2, Expression.Perm z' p1' p2' =>  ExpressionInclusion p1 p1' ∧ ExpressionInclusion p2 p2' ∧ ExpressionInclusion z z'
| .(_), Expression.Eps , Expression.Eps => true
| .(_), Expression.Hidden k, Expression.Hidden k' => k == k'
| .(_), Expression.Enc k e, Expression.Enc k' e' => k == k' ∧ ExpressionInclusion e e'
| .(_), Expression.Hidden k, Expression.Enc k' _ => k == k'
-- undo if this breaks anything
| .(_), Expression.G0 k1, Expression.G0 k2 => k1 == k2
| .(_), Expression.G1 k1, Expression.G1 k2 => k1 == k2
-- A redacted PRG is included in a real PRG if their underlying seeds match
| .(_), Expression.HiddenG0 k1, Expression.G0 k2 => k1 == k2
| .(_), Expression.HiddenG1 k1, Expression.G1 k2 => k1 == k2
  -- A redacted PRG is included in another redacted PRG if the seeds match
| .(_), Expression.HiddenG0 k1, Expression.HiddenG0 k2 => k1 == k2
| .(_), Expression.HiddenG1 k1, Expression.HiddenG1 k2 => k1 == k2
| .(_), _, _ => false

notation  p1 "⊆" p2 => (ExpressionInclusion p1 p2)

-- Next we introduce a block of lemmas about `ExpressionInclusion`, `hideEncrypted`, and `extractKeys`.

lemma ExpressionInclusionRfl (p : Expression s) : ExpressionInclusion p p :=
 by induction p <;>  simp [ExpressionInclusion] <;> try tauto

lemma hideEncryptedMonotone {s : Shape} (keys1 keys2 : Finset (Expression Shape.KeyS)) (p : Expression s) (h : keys1 ⊆ keys2) :
  hideEncrypted keys1 p ⊆ hideEncrypted keys2 p := by
  induction p <;> try simp [ExpressionInclusion, hideEncrypted]
  case Pair e1 e2 ih1 ih2 =>
    constructor <;> assumption
  case Perm b e1 e2 ih1 ih2 =>
    constructor <;> try assumption
    constructor <;> try assumption
    apply ExpressionInclusionRfl
  case Enc k e ih_k ih_e =>
    by_cases hk1 : k ∈ keys1
    · have hk2 : k ∈ keys2 := h hk1
      simp [hk1, hk2, ExpressionInclusion]
      exact ih_e
    · simp [hk1, ExpressionInclusion]
      by_cases hk2 : k ∈ keys2 <;> simp [hk2, ExpressionInclusion]
  case G0 k =>
    split <;> rename_i h1
    · split <;> rename_i h2
      · exact ExpressionInclusionRfl _
      · -- The impossible branch: k ∈ keys1 but k ∉ keys2
        -- 'h h1' proves k ∈ keys2. 'h2' takes that and produces False!
        exact False.elim (h2 (h h1))
    · split <;> rename_i h2
      · -- HiddenG0 k ⊆ G0 k
        simp [ExpressionInclusion]
      · -- HiddenG0 k ⊆ HiddenG0 k
        exact ExpressionInclusionRfl _
  case G1 k =>
    split <;> rename_i h1
    · split <;> rename_i h2
      · exact ExpressionInclusionRfl _
      · -- The impossible branch:
        exact False.elim (h2 (h h1))
    · split <;> rename_i h2
      · -- HiddenG1 k ⊆ G1 k
        simp [ExpressionInclusion]
      · -- HiddenG1 k ⊆ HiddenG1 k
        exact ExpressionInclusionRfl _

-- No longer mathematically true - updated key eq defs
-- lemma eq_of_ExpressionInclusion_key : ∀ (k1 k2 : Expression 𝕂), ExpressionInclusion k1 k2 = true → k1 = k2
--   | Expression.VarK id, k2, h => by
--       cases k2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
--       exact congrArg _ (eq_of_beq h)

--   | Expression.G0 e, k2, h => by
--       cases k2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
--       exact congrArg _ (eq_of_ExpressionInclusion_key e _ h)

--   | Expression.G1 e, k2, h => by
--       cases k2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
--       exact congrArg _ (eq_of_ExpressionInclusion_key e _ h)

lemma keyPartsMonotone {s : Shape} (p1 p2 : Expression s) (h : p1 ⊆ p2) :
  extractKeys p1 ⊆ extractKeys p2 := by
  induction p1 with
  | VarK k =>
      cases p2 <;> simp_all [ExpressionInclusion, extractKeys]
  | BitE b =>
      cases p2; simp_all [ExpressionInclusion, extractKeys]
  | Eps =>
      cases p2; simp_all [ExpressionInclusion, extractKeys]
  | Pair e1 e2 ih1 ih2 =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      -- Unwrap the decide coercion into a standard logical AND
      have ⟨h1, h2⟩ := of_decide_eq_true h
      simp [extractKeys]
      exact Finset.union_subset_union (ih1 _ h1) (ih2 _ h2)
  | Enc k e ih_k ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨hk_bool, he⟩ := of_decide_eq_true h
      -- hk_bool is (k == k') = true. We convert this to strict equality and substitute it.
      have hk : k = _ := eq_of_beq hk_bool
      subst hk
      simp [extractKeys]
      exact (ih_e _ he)
  | Hidden k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      · simp [extractKeys]
      · simp [extractKeys]
  | G0 e ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have heq : e = _ := eq_of_beq h
      subst heq
      simp [extractKeys]
  | G1 e ih =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have heq : e = _ := eq_of_beq h
      subst heq
      simp [extractKeys]
  | HiddenG0 k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      -- extractKeys of a HiddenG0 is empty, so it's a trivial subset of anything
      all_goals simp [extractKeys]
  | HiddenG1 k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      all_goals simp [extractKeys]
  | Perm z e1 e2 ih_z ih_e1 ih_e2 =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      -- The logical AND evaluates e1, then e2, then z
      have ⟨he1_incl, he2_incl, _hz_incl⟩ := of_decide_eq_true h
      simp only [extractKeys]
      -- extractKeys for Perm only unions e1 and e2, ignoring z
      exact Finset.union_subset_union (ih_e1 _ he1_incl) (ih_e2 _ he2_incl)

lemma hideEncryptedSmallerValue {s : Shape} (keys : Finset (Expression Shape.KeyS)) (p : Expression s) : hideEncrypted keys p ⊆ p := by
  induction p <;> try simp [ExpressionInclusion, hideEncrypted] <;> try tauto
  case Perm s eb e1 e2 ih1 ih2 ih3 =>
    constructor; assumption
    constructor; assumption
    apply ExpressionInclusionRfl
  case Enc s ek e ih1 ih2 =>
    split <;> try simp [ExpressionInclusion, hideEncrypted]
    assumption
  case G0 k =>
    split
    · -- Branch 1 (True): G0 k ⊆ G0 k
      exact ExpressionInclusionRfl _
    · -- Branch 2 (False): HiddenG0 k ⊆ G0 k
      simp [ExpressionInclusion]
  case G1 k =>
    split
    · -- Branch 1 (True): G1 k ⊆ G1 k
      exact ExpressionInclusionRfl _
    · -- Branch 2 (False): HiddenG1 k ⊆ G1 k
      simp [ExpressionInclusion]

-- Lemma 1: The universe of keys extracted from a smaller expression is a subset
-- of the universe extracted from a larger expression.
lemma keySubtermsMonotone {s : Shape} (p1 p2 : Expression s) (h : p1 ⊆ p2) :
  keySubterms p1 ⊆ keySubterms p2 := by
  induction p1 with
  | VarK k =>
      cases p2 <;> simp_all [ExpressionInclusion, keySubterms]
  | BitE b =>
      cases p2 ; simp_all [ExpressionInclusion, keySubterms]
  | Eps =>
      cases p2 ; simp_all [ExpressionInclusion, keySubterms]
  | Pair e1 e2 ih1 ih2 =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨h1, h2⟩ := of_decide_eq_true h
      simp [keySubterms]
      exact Finset.union_subset_union (ih1 _ h1) (ih2 _ h2)
  | Enc k e ih_k ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨hk_bool, he⟩ := of_decide_eq_true h
      have hk : k = _ := eq_of_beq hk_bool
      subst hk
      simp [keySubterms]
      exact Finset.union_subset_union (Finset.Subset.refl _) (ih_e _ he)
  | Hidden k ih_k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      -- Case 1: p2 is Enc (Enc is defined before Hidden in Defs.lean)
      · simp only [keySubterms]
        have hk : k = _ := eq_of_beq h
        subst hk
        exact @Finset.subset_union_left (Expression Shape.KeyS) _ _ _
      -- Case 2: p2 is Hidden
      · simp [keySubterms]
        have hk : k = _ := eq_of_beq h
        subst hk
        exact Finset.Subset.refl _
  | G0 e ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have heq : e = _ := eq_of_beq h
      subst heq
      simp [keySubterms]
  | G1 e ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have heq : e = _ := eq_of_beq h
      subst heq
      simp [keySubterms]
  | HiddenG0 k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      -- Handles both the case where p2 is G0 and p2 is HiddenG0
      all_goals
        have heq : k = _ := eq_of_beq h
        subst heq
        simp [keySubterms]
        try apply Finset.subset_union_left
        try apply Finset.subset_insert
  | HiddenG1 k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      all_goals
        have heq : k = _ := eq_of_beq h
        subst heq
        simp [keySubterms]
        try apply Finset.subset_union_left
        try apply Finset.subset_insert
  | Perm z e1 e2 ih_z ih_e1 ih_e2 =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨he1_incl, he2_incl, _hz_incl⟩ := of_decide_eq_true h
      simp [keySubterms]
      exact Finset.union_subset_union (ih_e1 _ he1_incl) (ih_e2 _ he2_incl)

-- Lemma 2: The cleartext keys are always a subset of the entire key universe.
lemma extractKeys_subset_keySubterms {s : Shape} (p : Expression s) :
  extractKeys p ⊆ keySubterms p := by
  induction p with
  | VarK k => simp [extractKeys, keySubterms]
  | BitE b => simp [extractKeys, keySubterms]
  | Eps => simp [extractKeys, keySubterms]
  | Pair e1 e2 ih1 ih2 =>
      simp [extractKeys, keySubterms]
      exact Finset.union_subset_union ih1 ih2
  | Enc k e ih_k ih_e =>
      simp [extractKeys, keySubterms]
      -- Goal is: extractKeys e ⊆ keySubterms k ∪ keySubterms e
      -- 1. We know from IH: extractKeys e ⊆ keySubterms e
      -- 2. We know: keySubterms e ⊆ keySubterms k ∪ keySubterms e (via subset_union_right)
      -- Use transitivity to connect them, being explicit about the element type
      apply @Finset.Subset.trans (Expression Shape.KeyS) _
      · exact ih_e
      · exact @Finset.subset_union_right (Expression Shape.KeyS) _ _ _
  | Hidden k =>
      simp [extractKeys, keySubterms]
  | G0 e ih =>
      simp [extractKeys, keySubterms]
  | G1 e ih =>
      simp [extractKeys, keySubterms]
  | HiddenG0 k =>
      simp [extractKeys, keySubterms]
  | HiddenG1 k =>
      simp [extractKeys, keySubterms]
  | Perm z e1 e2 ih_z ih_e1 ih_e2 =>
      simp [extractKeys, keySubterms]
      exact Finset.union_subset_union ih_e1 ih_e2

-- Lemma 3: prgStep preserves subset monotonicity.
lemma prgStepMonotone (U S1 S2 : Finset (Expression Shape.KeyS)) (h : S1 ⊆ S2) :
  prgStep U S1 ⊆ prgStep U S2 := by
  intro x hx
  simp only [prgStep, Finset.mem_union, Finset.mem_filter] at hx ⊢
  cases hx with
  | inl h_in_S1 =>
      exact Or.inl (h h_in_S1)
  | inr h_filter1 =>
      right
      refine ⟨h_filter1.1, ?_⟩
      -- If the term is a valid derived key (G0 or G1), extract the seed inclusion
      cases x <;> simp_all [isDerived]
      · exact h h_filter1.2
      · exact h h_filter1.2

-- Lemma 4: prgClosure preserves subset monotonicity
lemma prgClosureMonotone (U S1 S2 : Finset (Expression Shape.KeyS)) (h : S1 ⊆ S2) :
  prgClosure U S1 ⊆ prgClosure U S2 := by
  simp only [prgClosure]
  -- This replaces the specific range with a generic list 'l' in the goal
  generalize List.range (U.card + 1) = l
  -- Now we induct on 'l', generalizing S1 and S2 so the IH works for each step
  induction l generalizing S1 S2 with
  | nil =>
      -- Now simp works because the list is literally '[]'
      simp only [List.foldl_nil]
      exact h
  | cons hd tl ih =>
      -- Now simp works because the list is literally 'hd :: tl'
      simp only [List.foldl_cons]
      -- Goal: foldl ... (prgStep U S1) tl ⊆ foldl ... (prgStep U S2) tl
      apply ih
      exact prgStepMonotone U S1 S2 h

-- Helper to isolate the step containment for Lemma 5
lemma prgStepContained (U S : Finset (Expression Shape.KeyS)) (h : S ⊆ U) :
  prgStep U S ⊆ U := by
  intro x hx
  simp only [prgStep, Finset.mem_union, Finset.mem_filter] at hx
  cases hx with
  | inl h_in_S => exact h h_in_S
  | inr h_in_filter => exact h_in_filter.1

-- Lemma 5: If you start with a subset of the universe, prgClosure never exceeds the universe.
lemma prgClosureContained (U S : Finset (Expression Shape.KeyS)) (h : S ⊆ U) :
  prgClosure U S ⊆ U := by
  simp only [prgClosure]
  -- Replaces the specific range with a generic list 'l' to allow structural induction
  generalize List.range (U.card + 1) = l
  induction l generalizing S with
  | nil =>
      simp only [List.foldl_nil]
      exact h
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      -- Goal: foldl ... (prgStep U S) tl ⊆ U
      apply ih
      -- Prove that the state after one step is still a subset of U
      exact prgStepContained U S h

lemma keyRecoveryMonotone {s : Shape} (p : Expression s) (S1 S2 : Finset (Expression Shape.KeyS)) (h : S1 ⊆ S2) :
  keyRecovery p S1 ⊆ keyRecovery p S2 := by
  simp [keyRecovery]
  -- S1 ⊆ S2 implies prgClosure U S1 ⊆ prgClosure U S2
  have h_prg1 := prgClosureMonotone (keySubterms p) S1 S2 h
  -- which implies hideEncrypted (prg1) p ⊆ hideEncrypted (prg2) p
  have h_hide := hideEncryptedMonotone _ _ p h_prg1
  -- which implies extractKeys (hide1) ⊆ extractKeys (hide2)
  have h_ext := keyPartsMonotone _ _ h_hide
  -- which implies the final prgClosure is also a subset
  apply prgClosureMonotone
  assumption

lemma keyRecoveryContained {s : Shape} (p : Expression s) (S : Finset (Expression Shape.KeyS)) :
  keyRecovery p S ⊆ keySubterms p := by
  simp [keyRecovery]

  -- 1. hideEncrypted is structurally smaller than p
  have h_hide := hideEncryptedSmallerValue (prgClosure (keySubterms p) S) p

  -- 2. So the universe of the hidden view is a subset of the universe of p
  have h_univ := keySubtermsMonotone _ _ h_hide

  -- 3. The extracted keys of the view are a subset of the universe of the view
  have h_ext := extractKeys_subset_keySubterms (hideEncrypted (prgClosure (keySubterms p) S) p)

  -- 4. Therefore, the extracted keys are a subset of the main universe (keySubterms p)
  have h_ext_sub_univ : extractKeys (hideEncrypted (prgClosure (keySubterms p) S) p) ⊆ keySubterms p :=
    Finset.Subset.trans h_ext h_univ

  -- 5. Because the extracted keys are bounded by the universe, their PRG closure is also bounded by the universe
  apply prgClosureContained
  assumption

-- We are now ready to calculate the fixpoint.

def adversaryKeys {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  -- Notice the third argument is now 'keySubterms p' instead of 'extractKeys p'
  greatestFixpoint (keyRecovery p) (keyRecoveryMonotone p) (keySubterms p) (keyRecoveryContained p)

lemma adversaryKeysIsFix {s : Shape} (e : Expression s) :
  let keys := adversaryKeys e
  keyRecovery e keys = keys
  := by
  apply greatestFixpointIsFixpoint

def adversaryView {s : Shape} (e : Expression s) : Expression s :=
  hideEncrypted (adversaryKeys e) e

-- To conclude, we connect parts (i), (ii), and (iii) and define symbolic indistinguishability.

def symIndistinguishable {s : Shape} (e1 e2 : Expression s) : Prop :=
  ∃ (r : varRenaming), validVarRenaming r ∧
   normalizeExpr (applyVarRenaming r (adversaryView e1)) = normalizeExpr (adversaryView e2)

end PRG
