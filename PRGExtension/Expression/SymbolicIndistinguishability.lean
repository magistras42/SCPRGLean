import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union


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
  -- Recursing into the *key* positions as well.  On today's algebra this is a no-op —
  -- `Expression 𝕂` has only `VarK`, `G0`, `G1`, so a key contains no bit expression and
  -- `normalizeExpr_key` below shows normalising one is the identity.  It is written
  -- recursively anyway so that `symIndistinguishable` cannot silently become *too strong*
  -- if the language ever gains a key former that mentions bits: a pattern differing only by
  -- an unnormalised bit inside a key would then be judged distinguishable, which would break
  -- LM18 Theorem 5 rather than soundness.
  | Expression.G0 k => Expression.G0 (normalizeExpr k)
  | Expression.G1 k => Expression.G1 (normalizeExpr k)
  | Expression.Enc k e => Expression.Enc (normalizeExpr k) (normalizeExpr e)
  | Expression.Hidden k => Expression.Hidden (normalizeExpr k)
  | p => p

/-- Normalising a key expression is the identity: keys contain no bit expressions. -/
@[simp] lemma normalizeExpr_key : ∀ k : Expression Shape.KeyS, normalizeExpr k = k
  | Expression.VarK _ => rfl
  | Expression.G0 c => by rw [normalizeExpr, normalizeExpr_key c]
  | Expression.G1 c => by rw [normalizeExpr, normalizeExpr_key c]

/-- The equations as they read before the key positions became recursive, so that the
    downstream proofs are unaffected. -/
@[simp] lemma normalizeExpr_enc {s : Shape} (k : Expression Shape.KeyS) (e : Expression s) :
    normalizeExpr (Expression.Enc k e) = Expression.Enc k (normalizeExpr e) := by
  rw [normalizeExpr, normalizeExpr_key]

@[simp] lemma normalizeExpr_hidden {s : Shape} (k : Expression Shape.KeyS) :
    normalizeExpr (Expression.Hidden (s := s) k) = Expression.Hidden k := by
  rw [normalizeExpr, normalizeExpr_key]

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
  -- | Expression.HiddenG0 e => Expression.HiddenG0 (applyKeyRenamingP r e)
  -- | Expression.HiddenG1 e => Expression.HiddenG1 (applyKeyRenamingP r e)
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
  -- | Expression.HiddenG0 k => keySubterms k
  -- | Expression.HiddenG1 k => keySubterms k
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
  -- PRG Outputs: The adversary always sees the output string.
  -- We just recurse to hide anything that might be encrypted *inside* the seed formulation.
  | Expression.G0 e => Expression.G0 (hideEncrypted keys e)
  | Expression.G1 e => Expression.G1 (hideEncrypted keys e)
  | Expression.Enc k e =>
    let k' := hideEncrypted keys k
    if k ∈ keys then
      Expression.Enc k' (hideEncrypted keys e)
    else
      Expression.Hidden k'
  -- If we encounter an already hidden term, just recurse on the key.
  | Expression.Hidden k => Expression.Hidden (hideEncrypted keys k)
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
  -- | Expression.HiddenG0 _ => ∅
  -- | Expression.HiddenG1 _ => ∅
  | _ => ∅

-- LM18 `Keys(e)`: every key *as it is used*, without decomposing PRG applications.
-- This is deliberately different from both `extractKeys` (which drops encryption keys)
-- and `keySubterms` (which recurses into PRG seeds):
--   exprKeys (G0 k)      = {G0 k}                    -- NOT {G0 k} ∪ exprKeys k
--   exprKeys (Enc k e)   = exprKeys k ∪ exprKeys e    -- = {k} ∪ Keys(e)
--   exprKeys (Hidden k)  = exprKeys k                 -- = {k}, the pattern keeps its key
def exprKeys {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  match p with
  | Expression.VarK e => {Expression.VarK e}
  | Expression.G0 e => {Expression.G0 e}
  | Expression.G1 e => {Expression.G1 e}
  | Expression.Pair p1 p2 => exprKeys p1 ∪ exprKeys p2
  | Expression.Perm _ p1 p2 => exprKeys p1 ∪ exprKeys p2
  | Expression.Enc k e => exprKeys k ∪ exprKeys e
  | Expression.Hidden k => exprKeys k
  | _ => ∅

-- The keys an expression uses *as encryption keys* (including the keys of pattern holes).
-- LM18 splits `Keys(e)` into the keys that occur as parts and the keys that encrypt;
-- `extractKeys` is the former, `encKeys` the latter.  Lemma 6 is stated about the latter.
def encKeys {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  match p with
  | Expression.Pair p1 p2 => encKeys p1 ∪ encKeys p2
  | Expression.Perm _ p1 p2 => encKeys p1 ∪ encKeys p2
  | Expression.Enc k e => {k} ∪ encKeys e
  | Expression.Hidden k => {k}
  | _ => ∅

lemma exprKeys_eq_extractKeys_union_encKeys {s : Shape} (p : Expression s) :
  exprKeys p = extractKeys p ∪ encKeys p := by
  induction p with
  | VarK n => simp [exprKeys, extractKeys, encKeys]
  | BitE b => simp [exprKeys, extractKeys, encKeys]
  | Eps => simp [exprKeys, extractKeys, encKeys]
  | G0 e _ => simp [exprKeys, extractKeys, encKeys]
  | G1 e _ => simp [exprKeys, extractKeys, encKeys]
  | Pair e1 e2 ih1 ih2 =>
      simp only [exprKeys, extractKeys, encKeys, ih1, ih2]
      ac_rfl
  | Perm b e1 e2 _ ih1 ih2 =>
      simp only [exprKeys, extractKeys, encKeys, ih1, ih2]
      ac_rfl
  | Enc k e _ ihe =>
      simp only [exprKeys, extractKeys, encKeys, ihe]
      cases k <;> simp [exprKeys] <;> ac_rfl
  | Hidden k _ => cases k <;> simp [exprKeys, extractKeys, encKeys]

-- LM18 `k ≺ k'`: `k'` is a *strict* PRG-descendant of `k`, i.e. `k' ∈ 𝖦⁺(k)`.
def strictYields (k : Expression Shape.KeyS) : Expression Shape.KeyS → Bool
  | Expression.G0 seed => (seed == k) || strictYields k seed
  | Expression.G1 seed => (seed == k) || strictYields k seed
  | _ => false

-- ===================================================================================
-- LM18 §2.1 "Independence of pseudorandom keys": ⪯, ≺, independence, Roots.
-- These are the notions LM18 Lemmas 5-8 (and hence the garbled-circuit proof) are
-- stated in, so they live here rather than in the soundness proof.
-- ===================================================================================

def keySize : Expression Shape.KeyS → ℕ
  | Expression.VarK _ => 1
  | Expression.G0 k => keySize k + 1
  | Expression.G1 k => keySize k + 1

lemma strictYields_size : ∀ (k k' : Expression Shape.KeyS),
    strictYields k k' = true → keySize k < keySize k'
  | k, Expression.VarK n, h => by simp [strictYields] at h
  | k, Expression.G0 sd, h => by
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · subst h; simp [keySize]
      · have := strictYields_size k sd h; simp [keySize]; omega
  | k, Expression.G1 sd, h => by
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · subst h; simp [keySize]
      · have := strictYields_size k sd h; simp [keySize]; omega

lemma strictYields_irrefl (k : Expression Shape.KeyS) : strictYields k k = false := by
  cases hb : strictYields k k
  · rfl
  · exact absurd (strictYields_size k k hb) (by omega)

lemma strictYields_trans (a b : Expression Shape.KeyS) (hab : strictYields a b = true) :
    ∀ c : Expression Shape.KeyS, strictYields b c = true → strictYields a c = true
  | Expression.VarK n, h => by simp [strictYields] at h
  | Expression.G0 sd, h => by
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h ⊢
      rcases h with h | h
      · subst h; exact Or.inr hab
      · exact Or.inr (strictYields_trans a b hab sd h)
  | Expression.G1 sd, h => by
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h ⊢
      rcases h with h | h
      · subst h; exact Or.inr hab
      · exact Or.inr (strictYields_trans a b hab sd h)

lemma exprKeys_key : ∀ k : Expression Shape.KeyS, exprKeys k = {k}
  | Expression.VarK _ => rfl
  | Expression.G0 _ => rfl
  | Expression.G1 _ => rfl

lemma extractKeys_key : ∀ k : Expression Shape.KeyS, extractKeys k = {k}
  | Expression.VarK _ => rfl
  | Expression.G0 _ => rfl
  | Expression.G1 _ => rfl

/-- `k ≺ k'` means `k` occurs in `k'`'s chain. -/
lemma strictYields_mem_keySubterms : ∀ (a b : Expression Shape.KeyS),
    strictYields a b = true → a ∈ keySubterms b
  | a, Expression.VarK n, h => by simp [strictYields] at h
  | a, Expression.G0 sd, h => by
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h
      simp only [keySubterms, Finset.mem_union]
      rcases h with h | h
      · exact Or.inr (by subst h; cases sd <;> simp [keySubterms])
      · exact Or.inr (strictYields_mem_keySubterms a sd h)
  | a, Expression.G1 sd, h => by
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h
      simp only [keySubterms, Finset.mem_union]
      rcases h with h | h
      · exact Or.inr (by subst h; cases sd <;> simp [keySubterms])
      · exact Or.inr (strictYields_mem_keySubterms a sd h)

/-- Chains are linear: two keys that both yield `c` are comparable.
    (LM18 uses this repeatedly, e.g. "`k'' ⪯ k` or `k ≺ k''`".) -/
lemma strictYields_comparable : ∀ (c a b : Expression Shape.KeyS),
    strictYields a c = true → strictYields b c = true →
    a = b ∨ strictYields a b = true ∨ strictYields b a = true
  | Expression.VarK n, a, b, ha, _ => by simp [strictYields] at ha
  | Expression.G0 sd, a, b, ha, hb => by
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at ha hb
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact Or.inl (by rw [← ha, ← hb])
        · exact Or.inr (Or.inr (by rw [← ha]; exact hb))
      · rcases hb with hb | hb
        · exact Or.inr (Or.inl (by rw [← hb]; exact ha))
        · exact strictYields_comparable sd a b ha hb
  | Expression.G1 sd, a, b, ha, hb => by
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at ha hb
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact Or.inl (by rw [← ha, ← hb])
        · exact Or.inr (Or.inr (by rw [← ha]; exact hb))
      · rcases hb with hb | hb
        · exact Or.inr (Or.inl (by rw [← hb]; exact ha))
        · exact strictYields_comparable sd a b ha hb

/-- LM18 `k₁ ⪯ k₂`: `k₂ ∈ 𝖦*(k₁)`, i.e. `k₁` yields `k₂`. -/
def yields (k1 k2 : Expression Shape.KeyS) : Prop := k1 = k2 ∨ strictYields k1 k2 = true

lemma yields_refl (k : Expression Shape.KeyS) : yields k k := Or.inl rfl

lemma yields_trans {a b c : Expression Shape.KeyS} (hab : yields a b) (hbc : yields b c) :
    yields a c := by
  rcases hab with rfl | hab
  · exact hbc
  · rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (strictYields_trans a b hab c hbc)

lemma yields_strictYields_trans {a b c : Expression Shape.KeyS} (hab : yields a b)
    (hbc : strictYields b c = true) : strictYields a c = true := by
  rcases hab with rfl | hab
  · exact hbc
  · exact strictYields_trans a b hab c hbc

/-- LM18: a set of keys is independent when no member yields another.  (Reflexivity is
    free: `strictYields_irrefl`.) -/
def IndependentKeys (S : Finset (Expression Shape.KeyS)) : Prop :=
  ∀ k1 ∈ S, ∀ k2 ∈ S, strictYields k1 k2 = false

/-- `𝖦⁺(S) ∩ S`: the members of `S` that are strict PRG-descendants of some member. -/
def descendantKeys (S : Finset (Expression Shape.KeyS)) : Finset (Expression Shape.KeyS) :=
  S.biUnion (fun k' => S.filter (fun k => strictYields k' k))

/-- LM18 `Roots(S) = S ⧵ 𝖦⁺(S)`. -/
def rootsOf (S : Finset (Expression Shape.KeyS)) : Finset (Expression Shape.KeyS) :=
  S \ descendantKeys S

lemma mem_descendantKeys {S : Finset (Expression Shape.KeyS)} {k : Expression Shape.KeyS} :
  k ∈ descendantKeys S ↔ (k ∈ S ∧ ∃ k' ∈ S, strictYields k' k = true) := by
  simp only [descendantKeys, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨k', hk', hk, h⟩; exact ⟨hk, k', hk', h⟩
  · rintro ⟨hk, k', hk', h⟩; exact ⟨k', hk', hk, h⟩

lemma rootsOf_subset (S : Finset (Expression Shape.KeyS)) : rootsOf S ⊆ S :=
  Finset.sdiff_subset

lemma mem_rootsOf {S : Finset (Expression Shape.KeyS)} {k : Expression Shape.KeyS} :
  k ∈ rootsOf S ↔ (k ∈ S ∧ ∀ k' ∈ S, strictYields k' k = false) := by
  rw [rootsOf, Finset.mem_sdiff]
  constructor
  · rintro ⟨hk, hnd⟩
    refine ⟨hk, fun k' hk' => ?_⟩
    cases hb : strictYields k' k
    · rfl
    · exact absurd (mem_descendantKeys.mpr ⟨hk, k', hk', hb⟩) hnd
  · rintro ⟨hk, h⟩
    refine ⟨hk, fun hd => ?_⟩
    obtain ⟨_, k', hk', hy⟩ := mem_descendantKeys.mp hd
    rw [h k' hk'] at hy
    exact Bool.noConfusion hy

/-- LM18: `Roots(S)` is always an independent set. -/
lemma rootsOf_independent (S : Finset (Expression Shape.KeyS)) : IndependentKeys (rootsOf S) := by
  intro k1 hk1 k2 hk2
  exact (mem_rootsOf.mp hk2).2 k1 (rootsOf_subset S hk1)

/-- LM18: `S` is independent iff `S = Roots(S)`. -/
lemma independentKeys_iff_rootsOf (S : Finset (Expression Shape.KeyS)) :
  IndependentKeys S ↔ rootsOf S = S := by
  constructor
  · intro h
    apply Finset.Subset.antisymm (rootsOf_subset S)
    intro k hk
    exact mem_rootsOf.mpr ⟨hk, fun k' hk' => h k' hk' k hk⟩
  · intro h k1 hk1 k2 hk2
    rw [← h] at hk2
    exact (mem_rootsOf.mp hk2).2 k1 hk1

-- If `k` is not a strict PRG-ancestor of the key expression `e`, and is not `e` itself,
-- then `k` does not occur anywhere in `e`'s seed chain.
lemma strictYields_keySubterms : ∀ (k e : Expression Shape.KeyS),
    strictYields k e = false → e ≠ k → k ∉ keySubterms e
  | k, Expression.VarK n, _, hne => by
      simp only [keySubterms, Finset.mem_singleton]
      exact fun h => hne h.symm
  | k, Expression.G0 sd, h, hne => by
      simp only [strictYields, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨fun hc => hne hc.symm, strictYields_keySubterms k sd h.2 h.1⟩
  | k, Expression.G1 sd, h, hne => by
      simp only [strictYields, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨fun hc => hne hc.symm, strictYields_keySubterms k sd h.2 h.1⟩

-- LM18 Lemma 3, property 3: `𝖦⁺(VarK key₀) ∩ Keys(e) = ∅`, i.e. `key₀` is never used as a
-- PRG seed anywhere in `e`.  This is exactly what the IND-CPA reduction needs: the
-- reduction never learns the value of `key₀`, so it must never be required to compute
-- `prg0 key₀` or `prg1 key₀`.
def seedFree (key₀ : ℕ) {s : Shape} (e : Expression s) : Prop :=
  ∀ k ∈ exprKeys e, strictYields (Expression.VarK key₀) k = false

lemma seedFree_mono {key₀ : ℕ} {s t : Shape} {e : Expression s} {e' : Expression t}
  (hsub : exprKeys e' ⊆ exprKeys e) (h : seedFree key₀ e) : seedFree key₀ e' :=
  fun k hk => h k (hsub hk)

-- Destructuring `seedFree` along the constructors, for use inside inductions.
lemma seedFree_pair_left {key₀ : ℕ} {s₁ s₂ : Shape} {e1 : Expression s₁} {e2 : Expression s₂}
  (h : seedFree key₀ (Expression.Pair e1 e2)) : seedFree key₀ e1 :=
  fun k hk => h k (by simp [exprKeys, hk])

lemma seedFree_pair_right {key₀ : ℕ} {s₁ s₂ : Shape} {e1 : Expression s₁} {e2 : Expression s₂}
  (h : seedFree key₀ (Expression.Pair e1 e2)) : seedFree key₀ e2 :=
  fun k hk => h k (by simp [exprKeys, hk])

lemma seedFree_perm_left {key₀ : ℕ} {s : Shape} {b : Expression Shape.BitS} {e1 e2 : Expression s}
  (h : seedFree key₀ (Expression.Perm b e1 e2)) : seedFree key₀ e1 :=
  fun k hk => h k (by simp [exprKeys, hk])

lemma seedFree_perm_right {key₀ : ℕ} {s : Shape} {b : Expression Shape.BitS} {e1 e2 : Expression s}
  (h : seedFree key₀ (Expression.Perm b e1 e2)) : seedFree key₀ e2 :=
  fun k hk => h k (by simp [exprKeys, hk])

lemma seedFree_enc_key {key₀ : ℕ} {s : Shape} {k0 : Expression Shape.KeyS} {e : Expression s}
  (h : seedFree key₀ (Expression.Enc k0 e)) : seedFree key₀ k0 :=
  fun k hk => h k (by simp [exprKeys, hk])

lemma seedFree_enc_msg {key₀ : ℕ} {s : Shape} {k0 : Expression Shape.KeyS} {e : Expression s}
  (h : seedFree key₀ (Expression.Enc k0 e)) : seedFree key₀ e :=
  fun k hk => h k (by simp [exprKeys, hk])

lemma seedFree_hidden {key₀ : ℕ} {s : Shape} {k0 : Expression Shape.KeyS}
  (h : seedFree key₀ (Expression.Hidden (s := s) k0)) : seedFree key₀ k0 :=
  fun k hk => h k (by simp [exprKeys, hk])

-- On a `G`-node, seed-freeness of the node gives absence from the whole seed chain.
lemma seedFree_G_inner {key₀ : ℕ} {e : Expression Shape.KeyS}
  (h : strictYields (Expression.VarK key₀) e = false) (hne : e ≠ Expression.VarK key₀) :
  Expression.VarK key₀ ∉ keySubterms e :=
  strictYields_keySubterms _ _ h hne

lemma seedFree_G0_chain {key₀ : ℕ} {e : Expression Shape.KeyS}
  (h : seedFree key₀ (Expression.G0 e)) : Expression.VarK key₀ ∉ keySubterms e := by
  have h1 : strictYields (Expression.VarK key₀) (Expression.G0 e) = false :=
    h _ (by simp [exprKeys])
  simp only [strictYields, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h1
  exact seedFree_G_inner h1.2 h1.1

lemma seedFree_G1_chain {key₀ : ℕ} {e : Expression Shape.KeyS}
  (h : seedFree key₀ (Expression.G1 e)) : Expression.VarK key₀ ∉ keySubterms e := by
  have h1 : strictYields (Expression.VarK key₀) (Expression.G1 e) = false :=
    h _ (by simp [exprKeys])
  simp only [strictYields, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h1
  exact seedFree_G_inner h1.2 h1.1

def isAtomicKey : Expression Shape.KeyS → Bool
  | Expression.VarK _ => true
  | _ => false

-- The ancestor clause of LM18 Definition 3: `{k ∈ K | ∃ k' ∈ K. k ≺ k'}`.
-- If both a key and a strict PRG-descendant of it occur in the expression, the two are
-- not symbolically independent, so no reduction may treat the ancestor as an unknown
-- uniform key; it is conservatively declared recovered.
def ancestorKeys (K : Finset (Expression Shape.KeyS)) : Finset (Expression Shape.KeyS) :=
  K.biUnion (fun k' => K.filter (fun k => strictYields k k'))

lemma mem_ancestorKeys {K : Finset (Expression Shape.KeyS)} {k : Expression Shape.KeyS} :
  k ∈ ancestorKeys K ↔ (k ∈ K ∧ ∃ k' ∈ K, strictYields k k' = true) := by
  simp only [ancestorKeys, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨k', hk', hk, h⟩; exact ⟨hk, k', hk', h⟩
  · rintro ⟨hk, k', hk', h⟩; exact ⟨k', hk', hk, h⟩

lemma ancestorKeys_subset (K : Finset (Expression Shape.KeyS)) : ancestorKeys K ⊆ K := by
  intro k hk; exact (mem_ancestorKeys.mp hk).1

lemma ancestorKeysMonotone {K1 K2 : Finset (Expression Shape.KeyS)} (h : K1 ⊆ K2) :
  ancestorKeys K1 ⊆ ancestorKeys K2 := by
  intro k hk
  obtain ⟨hkK, k', hk', hyield⟩ := mem_ancestorKeys.mp hk
  exact mem_ancestorKeys.mpr ⟨h hkK, k', h hk', hyield⟩

/-- An expression with no PRG structure at all: every key subterm is an atomic variable.
    This is the shape an idealisation chain drives an expression towards, and it is also
    exactly the fragment the original encryption-only framework covers. -/
def AtomicKeys {s : Shape} (e : Expression s) : Prop :=
  ∀ k ∈ keySubterms e, isAtomicKey k = true

lemma atomicKeys_of_subset {s t : Shape} {e : Expression s} {e' : Expression t}
  (hsub : keySubterms e' ⊆ keySubterms e) (h : AtomicKeys e) : AtomicKeys e' :=
  fun k hk => h k (hsub hk)

/-- The bridge between LM18's independence and the ancestor clause of `keyRecovery`:
    the clause fires on exactly the non-independent key sets. -/
lemma ancestorKeys_eq_empty_iff (K : Finset (Expression Shape.KeyS)) :
  ancestorKeys K = ∅ ↔ IndependentKeys K := by
  constructor
  · intro h k1 hk1 k2 hk2
    cases hb : strictYields k1 k2
    · rfl
    · exact absurd (mem_ancestorKeys.mpr ⟨hk1, k2, hk2, hb⟩) (by simp [h])
  · intro h
    apply Finset.eq_empty_of_forall_not_mem
    intro k hk
    obtain ⟨hkK, k', hk', hy⟩ := mem_ancestorKeys.mp hk
    rw [h k hkK k' hk'] at hy
    exact Bool.noConfusion hy

-- Next, we define the 'key recovery operator (𝓕ₑ from the paper), that given a set of keys,
-- hides the encrypted parts of the expression and computes the recoverable keys of the result.
--
-- LM18 Definition 3:
--   r(e) = 𝖦*({ k ∈ Keys(e) | (k ⋐ e) ∨ (∃ k' ∈ Keys(e). k ≺ k') })
-- The first disjunct is `extractKeys view`; the second is `ancestorKeys (exprKeys view)`.
def keyRecovery {s : Shape} (p : Expression s) (S : Finset (Expression Shape.KeyS)) : Finset (Expression Shape.KeyS) :=
  -- Determine the finite universe of sub-keys in the expression
  let univKeys := keySubterms p
  -- The adversary computes all PRG derivations for current keys
  let expandedS := prgClosure univKeys S
  -- The adversary attempts to decrypt the expression using these expanded keys
  let view := hideEncrypted expandedS p
  -- The adversary extracts the keys it can read off directly ...
  -- ... together with every key that has a strict PRG-descendant in the view.
  let extracted := extractKeys view ∪ ancestorKeys (exprKeys view)
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
-- Encryption vs Hidden Blob inclusion
| .(_), Expression.Hidden k, Expression.Hidden k' => k == k'
| .(_), Expression.Enc k e, Expression.Enc k' e' => k == k' ∧ ExpressionInclusion e e'
| .(_), Expression.Hidden k, Expression.Enc k' _ => k == k'
-- PRG instances just match exactly with each other
| .(_), Expression.G0 e1, Expression.G0 e2 => ExpressionInclusion e1 e2
| .(_), Expression.G1 e1, Expression.G1 e2 => ExpressionInclusion e1 e2
-- Catch-all for non-matching shapes
| .(_), _, _ => false

notation  p1 "⊆" p2 => (ExpressionInclusion p1 p2)

def KeySetInclusion {s : Shape} (K1 K2 : Finset (Expression s)) : Prop :=
  ∀ k1 ∈ K1, ∃ k2 ∈ K2, ExpressionInclusion k1 k2 = true

-- Next we introduce a block of lemmas about `ExpressionInclusion`, `hideEncrypted`, and `extractKeys`.

-- Lemmas about prgClosure
-- 1. A single PRG step always contains the initial keys
lemma prgStep_extensive (univKeys S : Finset (Expression Shape.KeyS)) :
  S ⊆ prgStep univKeys S := by
  -- prgStep is defined as `S ∪ ...`, so the left side is trivially included
  simp [prgStep]

-- 2. Applying the step multiple times over any list maintains the subset
lemma foldl_prgStep_extensive (univKeys S : Finset (Expression Shape.KeyS)) (l : List ℕ) :
  S ⊆ l.foldl (fun currentS _ => prgStep univKeys currentS) S := by
  -- We prove this by induction on the length of the list!
  induction l generalizing S with
  | nil =>
    simp only [List.foldl_nil]
    -- Base case: S ⊆ S
    intro x hx
    exact hx
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    -- Inductive case: S ⊆ foldl ... (prgStep univKeys S) tl
    have H_step := prgStep_extensive univKeys S
    have H_fold := ih (prgStep univKeys S)
    exact Finset.Subset.trans H_step H_fold

-- 3. The final extensivity lemma for the full closure!
lemma subset_prgClosure (univKeys S : Finset (Expression Shape.KeyS)) :
  S ⊆ prgClosure univKeys S := by
  -- Simply unfold the closure definition and apply our list helper
  unfold prgClosure
  apply foldl_prgStep_extensive

lemma key_in_keySubterms (k : Expression Shape.KeyS) : k ∈ keySubterms k := by
  cases k <;> simp [keySubterms]

lemma hideEncrypted_superset_keySubterms {s : Shape} (keys : Finset (Expression Shape.KeyS)) (p : Expression s) (h : keySubterms p ⊆ keys) : hideEncrypted keys p = p := by
  induction p <;> try simp [hideEncrypted]
  case Pair e1 e2 ih1 ih2 =>
    have h1 : keySubterms e1 ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    have h2 : keySubterms e2 ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    exact ⟨ih1 h1, ih2 h2⟩
  case Perm b e1 e2 _ ih1 ih2 =>
    have h1 : keySubterms e1 ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    have h2 : keySubterms e2 ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    exact ⟨ih1 h1, ih2 h2⟩
  case Enc k e ih_k ih_e =>
    have hk : k ∈ keys := h (by simp [keySubterms, key_in_keySubterms])
    have h_k : keySubterms k ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    have h_e : keySubterms e ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    simp [hk]
    exact ⟨ih_k h_k, ih_e h_e⟩
  case G0 e ih =>
    have h_e : keySubterms e ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    exact ih h_e
  case G1 e ih =>
    have h_e : keySubterms e ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    exact ih h_e
  case Hidden k ih =>
    have h_k : keySubterms k ⊆ keys := fun x hx => h (by simp [keySubterms, hx])
    exact ih h_k

lemma hideEncrypted_keySubterms {s : Shape} (p : Expression s) : hideEncrypted (keySubterms p) p = p :=
  hideEncrypted_superset_keySubterms (keySubterms p) p (Finset.Subset.refl _)

lemma ExpressionInclusionRfl (p : Expression s) : ExpressionInclusion p p :=
 by induction p <;>  simp [ExpressionInclusion] <;> try tauto

@[simp]
lemma hideEncrypted_key_id (keys : Finset (Expression Shape.KeyS)) : (k : Expression 𝕂) → hideEncrypted keys k = k
| .VarK n => by rfl
| .G0 k' => by simp [hideEncrypted, hideEncrypted_key_id keys k']
| .G1 k' => by simp [hideEncrypted, hideEncrypted_key_id keys k']

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
      simp [hk1, hk2, ExpressionInclusion, hideEncrypted_key_id]
      exact ih_e
    · by_cases hk2 : k ∈ keys2
      · simp [hk1, hk2, ExpressionInclusion, hideEncrypted_key_id]
      · simp [hk1, hk2, ExpressionInclusion, hideEncrypted_key_id]
  case G0 k ih => exact ExpressionInclusionRfl k
  case G1 k ih => exact ExpressionInclusionRfl k

-- lemma hideEncryptedMonotone {s : Shape} (keys1 keys2 : Finset (Expression Shape.KeyS)) (p : Expression s) (h : keys1 ⊆ keys2) :
--   hideEncrypted keys1 p ⊆ hideEncrypted keys2 p := by
--   induction p <;> try simp [ExpressionInclusion, hideEncrypted]
--   case Pair e1 e2 ih1 ih2 =>
--     constructor <;> assumption
--   case Perm b e1 e2 ih1 ih2 =>
--     constructor <;> try assumption
--     constructor <;> try assumption
--     apply ExpressionInclusionRfl
--   case Enc k e ih_k ih_e =>
--     by_cases hk1 : k ∈ keys1
--     · have hk2 : k ∈ keys2 := h hk1
--       simp [hk1, hk2, ExpressionInclusion]
--       exact ih_e
--     · simp [hk1, ExpressionInclusion]
--       by_cases hk2 : k ∈ keys2 <;> simp [hk2, ExpressionInclusion]
--   case G0 k =>
--     split <;> rename_i h1
--     · split <;> rename_i h2
--       · exact ExpressionInclusionRfl _
--       · -- The impossible branch: k ∈ keys1 but k ∉ keys2
--         -- 'h h1' proves k ∈ keys2. 'h2' takes that and produces False!
--         exact False.elim (h2 (h h1))
--     · split <;> rename_i h2
--       · -- HiddenG0 k ⊆ G0 k
--         simp [ExpressionInclusion]
--       · -- HiddenG0 k ⊆ HiddenG0 k
--         exact ExpressionInclusionRfl _
--   case G1 k =>
--     split <;> rename_i h1
--     · split <;> rename_i h2
--       · exact ExpressionInclusionRfl _
--       · -- The impossible branch:
--         exact False.elim (h2 (h h1))
--     · split <;> rename_i h2
--       · -- HiddenG1 k ⊆ G1 k
--         simp [ExpressionInclusion]
--       · -- HiddenG1 k ⊆ HiddenG1 k
--         exact ExpressionInclusionRfl _

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

-- 1. A set is structurally included in itself (Base Cases)
lemma KeySetInclusion_refl {s : Shape} (K : Finset (Expression s)) : KeySetInclusion K K := by
  intro k hk
  exact ⟨k, hk, ExpressionInclusionRfl k⟩

-- 2. If A ⊆ C and B ⊆ D, then (A ∪ B) ⊆ (C ∪ D) (For Pair, Perm, Enc)
lemma KeySetInclusion_union {s : Shape} {A B C D : Finset (Expression s)}
  (h1 : KeySetInclusion A C) (h2 : KeySetInclusion B D) :
  KeySetInclusion (A ∪ B) (C ∪ D) := by
  intro k hk
  simp only [Finset.mem_union] at hk ⊢
  cases hk with
  | inl hA =>
      rcases h1 k hA with ⟨k2, hk2, hinc⟩
      exact ⟨k2, Or.inl hk2, hinc⟩
  | inr hB =>
      rcases h2 k hB with ⟨k2, hk2, hinc⟩
      exact ⟨k2, Or.inr hk2, hinc⟩

-- 3. If k1 ⊆ k2 and K1 ⊆ K2, then insert k1 K1 ⊆ insert k2 K2 (For G0, G1, Enc if using insert)
lemma KeySetInclusion_insert {s : Shape} {k1 k2 : Expression s} {K1 K2 : Finset (Expression s)}
  (h_k : ExpressionInclusion k1 k2 = true) (h_K : KeySetInclusion K1 K2) :
  KeySetInclusion (insert k1 K1) (insert k2 K2) := by
  intro k hk
  simp only [Finset.mem_insert] at hk ⊢
  cases hk with
  | inl heq =>
      subst heq
      exact ⟨k2, Or.inl rfl, h_k⟩
  | inr hmem =>
      rcases h_K k hmem with ⟨k_out, h_out_mem, hinc⟩
      exact ⟨k_out, Or.inr h_out_mem, hinc⟩

-- 4. If A ⊆ B, then A is included in (B ∪ C) (Crucial for proving Hidden ⊆ Enc)
lemma KeySetInclusion_subset_right {s : Shape} {A B C : Finset (Expression s)}
  (h : KeySetInclusion A B) : KeySetInclusion A (B ∪ C) := by
  intro k hk
  rcases h k hk with ⟨k2, hk2, hinc⟩
  exact ⟨k2, Finset.mem_union_left C hk2, hinc⟩

lemma KeySetInclusion_empty {s : Shape} (K : Finset (Expression s)) : KeySetInclusion ∅ K := by
  intro k hk
  simp at hk -- A contradiction, nothing is in the empty set

lemma KeySetInclusion_singleton {s : Shape} {e1 e2 : Expression s} (h : ExpressionInclusion e1 e2 = true) :
  KeySetInclusion {e1} {e2} := by
  intro k hk
  simp only [Finset.mem_singleton] at hk ⊢
  subst hk
  exact ⟨e2, rfl, h⟩

lemma keyPartsMonotone' {s : Shape} (p1 p2 : Expression s) (h : ExpressionInclusion p1 p2 = true) :
  KeySetInclusion (extractKeys p1) (extractKeys p2) := by
  induction p1 with
  -- Base Cases (Keys are identical, so apply reflexivity)
  | VarK k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      -- 'h' is (k == a✝) = true. Convert to strict equality.
      have heq : k = _ := eq_of_beq h
      subst heq
      simp [extractKeys]
      exact KeySetInclusion_refl _
  | BitE b =>
      cases p2 ; simp only [ExpressionInclusion] at h ; try contradiction
      simp [extractKeys]
      apply KeySetInclusion_refl
  | Eps =>
      cases p2 ; simp only [ExpressionInclusion] at h ; try contradiction
      simp [extractKeys]
      apply KeySetInclusion_refl
  -- Union Cases (Just swap Finset.union_subset_union for our new lemma)
  | Pair e1 e2 ih1 ih2 =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨h1, h2⟩ := of_decide_eq_true h
      simp [extractKeys]
      exact KeySetInclusion_union (ih1 _ h1) (ih2 _ h2)
  | Perm z e1 e2 ih_z ih_e1 ih_e2 =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨he1_incl, he2_incl, _hz_incl⟩ := of_decide_eq_true h
      simp only [extractKeys]
      exact KeySetInclusion_union (ih_e1 _ he1_incl) (ih_e2 _ he2_incl)

  | Enc k e ih_k ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨_hk, he⟩ := of_decide_eq_true h
      simp [extractKeys]
      -- Because extractKeys (Enc) only extracts from 'e', we only use ih_e
      exact ih_e _ he
  | Hidden k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      · simp [extractKeys]
        exact KeySetInclusion_empty _
      · simp [extractKeys]
        exact KeySetInclusion_empty _
  | G0 e ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      simp [extractKeys]
      -- h is exactly ExpressionInclusion e a✝ = true
      exact KeySetInclusion_singleton h
  | G1 e ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      simp [extractKeys]
      -- h is exactly ExpressionInclusion e a✝ = true
      exact KeySetInclusion_singleton h

lemma shape_K_eq {e a : Expression 𝕂} (h : ExpressionInclusion e a = true) : e = a :=
  match e with
  | .VarK n => by
      cases a <;> simp [ExpressionInclusion] at h ; try contradiction
      -- simp already proved n = a✝, so we just substitute it!
      subst h
      rfl
  | .G0 e_inner => by
      cases a <;> simp [ExpressionInclusion] at h ; try contradiction
      have heq : e_inner = _ := shape_K_eq h
      subst heq
      rfl
  | .G1 e_inner => by
      cases a <;> simp [ExpressionInclusion] at h ; try contradiction
      have heq : e_inner = _ := shape_K_eq h
      subst heq
      rfl

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
      have heq : e = _ := shape_K_eq h
      subst heq
      -- Now the goal is {G0 e} ⊆ {G0 e}, which is solved automatically by simp!
      simp [extractKeys]
  | G1 e ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have heq : e = _ := shape_K_eq h
      subst heq
      simp [extractKeys]
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
  case G0 k ih => exact ExpressionInclusionRfl k
  case G1 k ih => exact ExpressionInclusionRfl k

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
      have heq : e = _ := shape_K_eq h
      subst heq
      simp [keySubterms]
  | G1 e ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have heq : e = _ := shape_K_eq h
      subst heq
      simp [keySubterms]
  -- | HiddenG0 k =>
  --     cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
  --     -- Handles both the case where p2 is G0 and p2 is HiddenG0
  --     all_goals
  --       have heq : k = _ := eq_of_beq h
  --       subst heq
  --       simp [keySubterms]
  --       try apply Finset.subset_union_left
  --       try apply Finset.subset_insert
  -- | HiddenG1 k =>
  --     cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
  --     all_goals
  --       have heq : k = _ := eq_of_beq h
  --       subst heq
  --       simp [keySubterms]
  --       try apply Finset.subset_union_left
  --       try apply Finset.subset_insert
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
  -- | HiddenG0 k =>
  --     simp [extractKeys, keySubterms]
  -- | HiddenG1 k =>
  --     simp [extractKeys, keySubterms]
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

-- `exprKeys` (LM18 `Keys`) is monotone for the `Hidden ⊆ Enc` order, exactly like
-- `extractKeys`.  Needed because `keyRecovery` now consults it.
lemma exprKeysMonotone {s : Shape} (p1 p2 : Expression s) (h : p1 ⊆ p2) :
  exprKeys p1 ⊆ exprKeys p2 := by
  induction p1 with
  | VarK k =>
      cases p2 <;> simp_all [ExpressionInclusion, exprKeys]
  | BitE b =>
      cases p2; simp_all [ExpressionInclusion, exprKeys]
  | Eps =>
      cases p2; simp_all [ExpressionInclusion, exprKeys]
  | Pair e1 e2 ih1 ih2 =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨h1, h2⟩ := of_decide_eq_true h
      simp [exprKeys]
      exact Finset.union_subset_union (ih1 _ h1) (ih2 _ h2)
  | Perm z e1 e2 _ih_z ih_e1 ih_e2 =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨he1, he2, _hz⟩ := of_decide_eq_true h
      simp only [exprKeys]
      exact Finset.union_subset_union (ih_e1 _ he1) (ih_e2 _ he2)
  | Enc k e _ih_k ih_e =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have ⟨hk_bool, he⟩ := of_decide_eq_true h
      have hk : k = _ := eq_of_beq hk_bool
      subst hk
      simp [exprKeys]
      exact Finset.union_subset_union (Finset.Subset.refl _) (ih_e _ he)
  | Hidden k =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      -- p2 = Enc k' e' : exprKeys (Hidden k) = exprKeys k ⊆ exprKeys k' ∪ exprKeys e'
      · simp only [exprKeys]
        have hk : k = _ := eq_of_beq h
        subst hk
        exact @Finset.subset_union_left (Expression Shape.KeyS) _ _ _
      -- p2 = Hidden k'
      · simp only [exprKeys]
        have hk : k = _ := eq_of_beq h
        subst hk
        exact Finset.Subset.refl _
  | G0 e _ih =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have heq : e = _ := shape_K_eq h
      subst heq
      simp [exprKeys]
  | G1 e _ih =>
      cases p2 <;> simp only [ExpressionInclusion] at h <;> try contradiction
      have heq : e = _ := shape_K_eq h
      subst heq
      simp [exprKeys]

-- Every key *used* in an expression is one of its key subterms, so the ancestor clause
-- stays inside the finite universe that bounds the fixpoint.
lemma exprKeys_subset_keySubterms {s : Shape} (p : Expression s) :
  exprKeys p ⊆ keySubterms p := by
  induction p with
  | VarK k => simp [exprKeys, keySubterms]
  | BitE b => simp [exprKeys, keySubterms]
  | Eps => simp [exprKeys, keySubterms]
  | Pair e1 e2 ih1 ih2 =>
      simp [exprKeys, keySubterms]
      exact Finset.union_subset_union ih1 ih2
  | Perm z e1 e2 _ih_z ih1 ih2 =>
      simp [exprKeys, keySubterms]
      exact Finset.union_subset_union ih1 ih2
  | Enc k e ih_k ih_e =>
      simp only [exprKeys, keySubterms]
      exact Finset.union_subset_union ih_k ih_e
  | Hidden k ih_k =>
      simp only [exprKeys, keySubterms]
      exact ih_k
  | G0 e _ih => simp [exprKeys, keySubterms]
  | G1 e _ih => simp [exprKeys, keySubterms]

lemma seedFree_of_atomicKeys {s : Shape} {e : Expression s} (h : AtomicKeys e) (n : ℕ) :
  seedFree n e := by
  intro k hk
  have hat : isAtomicKey k = true := h k (exprKeys_subset_keySubterms e hk)
  cases k with
  | VarK m => simp [strictYields]
  | G0 _ => simp [isAtomicKey] at hat
  | G1 _ => simp [isAtomicKey] at hat

-- ===================================================================================
-- Atomicisation: LM18 Lemma 3, property 1.
--
--   "If `Roots(Keys(e)) ⊆ 𝐊` then every key the hiding step removes is atomic."
--
-- A non-atomic `k ∈ Keys(e)` cannot be a root, so some `k' ∈ Keys(e)` satisfies `k' ≺ k`;
-- that `k'` is caught by the ancestor clause of `keyRecovery`, and `k` lies in its PRG
-- closure, so `k` is *recovered* rather than hidden.
-- ===================================================================================

lemma keySize_le_of_mem_keySubterms : ∀ (k x : Expression Shape.KeyS),
    x ∈ keySubterms k → keySize x ≤ keySize k
  | Expression.VarK n, x, hx => by
      simp only [keySubterms, Finset.mem_singleton] at hx; subst hx; exact le_refl _
  | Expression.G0 sd, x, hx => by
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with h | h
      · subst h; exact le_refl _
      · have := keySize_le_of_mem_keySubterms sd x h; simp only [keySize]; omega
  | Expression.G1 sd, x, hx => by
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with h | h
      · subst h; exact le_refl _
      · have := keySize_le_of_mem_keySubterms sd x h; simp only [keySize]; omega

lemma G0_not_mem_keySubterms (sd : Expression Shape.KeyS) :
    Expression.G0 sd ∉ keySubterms sd := fun hc => by
  have := keySize_le_of_mem_keySubterms sd _ hc; simp only [keySize] at this; omega

lemma G1_not_mem_keySubterms (sd : Expression Shape.KeyS) :
    Expression.G1 sd ∉ keySubterms sd := fun hc => by
  have := keySize_le_of_mem_keySubterms sd _ hc; simp only [keySize] at this; omega

/-- The chain of a key expression has exactly `keySize k` distinct members. -/
lemma keySubterms_card : ∀ k : Expression Shape.KeyS, (keySubterms k).card = keySize k
  | Expression.VarK n => by simp [keySubterms, keySize]
  | Expression.G0 sd => by
      have h : keySubterms (Expression.G0 sd) = insert (Expression.G0 sd) (keySubterms sd) := by
        simp [keySubterms, Finset.insert_eq]
      rw [h, Finset.card_insert_of_not_mem (G0_not_mem_keySubterms sd), keySubterms_card sd]
      simp [keySize]
  | Expression.G1 sd => by
      have h : keySubterms (Expression.G1 sd) = insert (Expression.G1 sd) (keySubterms sd) := by
        simp [keySubterms, Finset.insert_eq]
      rw [h, Finset.card_insert_of_not_mem (G1_not_mem_keySubterms sd), keySubterms_card sd]
      simp [keySize]

/-- Every key *used* by an expression has its whole chain among the expression's subterms. -/
lemma keySubterms_subset_of_mem_exprKeys {s : Shape} (e : Expression s) :
    ∀ k ∈ exprKeys e, keySubterms k ⊆ keySubterms e := by
  induction e with
  | BitE b => intro k hk; simp [exprKeys] at hk
  | Eps => intro k hk; simp [exprKeys] at hk
  | VarK n => intro k hk; simp only [exprKeys, Finset.mem_singleton] at hk; subst hk; exact Finset.Subset.refl _
  | G0 sd _ => intro k hk; simp only [exprKeys, Finset.mem_singleton] at hk; subst hk; exact Finset.Subset.refl _
  | G1 sd _ => intro k hk; simp only [exprKeys, Finset.mem_singleton] at hk; subst hk; exact Finset.Subset.refl _
  | Pair e1 e2 ih1 ih2 =>
      intro k hk
      simp only [exprKeys, Finset.mem_union] at hk
      simp only [keySubterms]
      rcases hk with h | h
      · exact Finset.Subset.trans (ih1 k h) Finset.subset_union_left
      · exact Finset.Subset.trans (ih2 k h) Finset.subset_union_right
  | Perm b e1 e2 _ ih1 ih2 =>
      intro k hk
      simp only [exprKeys, Finset.mem_union] at hk
      simp only [keySubterms]
      rcases hk with h | h
      · exact Finset.Subset.trans (ih1 k h) Finset.subset_union_left
      · exact Finset.Subset.trans (ih2 k h) Finset.subset_union_right
  | Enc k0 e0 ihk ihe =>
      intro k hk
      simp only [exprKeys, Finset.mem_union] at hk
      simp only [keySubterms]
      rcases hk with h | h
      · exact Finset.Subset.trans (ihk k h) Finset.subset_union_left
      · exact Finset.Subset.trans (ihe k h) Finset.subset_union_right
  | Hidden k0 ihk =>
      intro k hk
      simp only [exprKeys] at hk
      simp only [keySubterms]
      exact ihk k hk

-- --- the PRG closure reaches a whole chain -----------------------------------------

lemma prgClosure_eq_iterate (U S : Finset (Expression Shape.KeyS)) :
    prgClosure U S = (prgStep U)^[U.card + 1] S := by
  simp only [prgClosure]
  generalize U.card + 1 = n
  induction n generalizing S with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ_apply']
      simp

lemma prgStep_iterate_extensive (U S : Finset (Expression Shape.KeyS)) (n : ℕ) :
    S ⊆ (prgStep U)^[n] S := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact Finset.Subset.trans ih (prgStep_extensive U _)

lemma prgStep_iterate_monotone (U : Finset (Expression Shape.KeyS)) (n : ℕ)
    {X Y : Finset (Expression Shape.KeyS)} (h : X ⊆ Y) :
    (prgStep U)^[n] X ⊆ (prgStep U)^[n] Y := by
  induction n generalizing X Y with
  | zero => simpa using h
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
                 exact ih (prgStepMonotone U X Y h)

lemma prgStep_iterate_mono_exp (U S : Finset (Expression Shape.KeyS)) {m n : ℕ} (h : m ≤ n) :
    (prgStep U)^[m] S ⊆ (prgStep U)^[n] S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact prgStep_iterate_monotone U m (prgStep_iterate_extensive U S d)

/-- If `k' ≺ k` and `k'` is known, then `k` is reached in `keySize k` derivation steps. -/
lemma mem_iterate_of_strictYields (U X : Finset (Expression Shape.KeyS)) :
    ∀ (k k' : Expression Shape.KeyS), strictYields k' k = true → k' ∈ X →
      (keySubterms k ⊆ U) → (k ∈ (prgStep U)^[keySize k] X)
  | Expression.VarK n, k', h, _, _ => by simp [strictYields] at h
  | Expression.G0 sd, k', h, hk', hU => by
      have hmemU : Expression.G0 sd ∈ U := hU (by simp [keySubterms])
      have hsdU : keySubterms sd ⊆ U :=
        Finset.Subset.trans (by intro x hx; simp [keySubterms, hx]) hU
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h
      rw [show keySize (Expression.G0 sd) = keySize sd + 1 from by simp [keySize],
        Function.iterate_succ_apply']
      have hsd : sd ∈ (prgStep U)^[keySize sd] X := by
        rcases h with h | h
        · subst h; exact prgStep_iterate_extensive U X _ hk'
        · exact mem_iterate_of_strictYields U X sd k' h hk' hsdU
      simp only [prgStep, Finset.mem_union, Finset.mem_filter]
      exact Or.inr ⟨hmemU, by simp [isDerived, hsd]⟩
  | Expression.G1 sd, k', h, hk', hU => by
      have hmemU : Expression.G1 sd ∈ U := hU (by simp [keySubterms])
      have hsdU : keySubterms sd ⊆ U :=
        Finset.Subset.trans (by intro x hx; simp [keySubterms, hx]) hU
      simp only [strictYields, Bool.or_eq_true, beq_iff_eq] at h
      rw [show keySize (Expression.G1 sd) = keySize sd + 1 from by simp [keySize],
        Function.iterate_succ_apply']
      have hsd : sd ∈ (prgStep U)^[keySize sd] X := by
        rcases h with h | h
        · subst h; exact prgStep_iterate_extensive U X _ hk'
        · exact mem_iterate_of_strictYields U X sd k' h hk' hsdU
      simp only [prgStep, Finset.mem_union, Finset.mem_filter]
      exact Or.inr ⟨hmemU, by simp [isDerived, hsd]⟩

lemma mem_prgClosure_of_strictYields {U X : Finset (Expression Shape.KeyS)}
    {k k' : Expression Shape.KeyS} (h : strictYields k' k = true) (hk' : k' ∈ X)
    (hU : (keySubterms k ⊆ U)) : (k ∈ prgClosure U X) := by
  rw [prgClosure_eq_iterate]
  refine prgStep_iterate_mono_exp U X ?_ (mem_iterate_of_strictYields U X k k' h hk' hU)
  have : keySize k = (keySubterms k).card := (keySubterms_card k).symm
  have hle : (keySubterms k).card ≤ U.card := Finset.card_le_card hU
  omega

/-- Once the derivation fold stops growing it stays put. -/
lemma prgStep_stable {U S : Finset (Expression Shape.KeyS)} {i : ℕ}
    (h : (prgStep U)^[i+1] S = (prgStep U)^[i] S) :
    ∀ j, i ≤ j → (prgStep U)^[j] S = (prgStep U)^[i] S := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [Function.iterate_succ_apply', ih, ← Function.iterate_succ_apply' (prgStep U) i S]
      exact h

/-- Each non-stabilising step adds at least one element of the universe. -/
lemma prgStep_card_growth (U S : Finset (Expression Shape.KeyS)) :
    ∀ i : ℕ, (∀ j, j < i → (prgStep U)^[j+1] S ≠ (prgStep U)^[j] S) →
      i ≤ ((prgStep U)^[i] S ∩ U).card := by
  intro i
  induction i with
  | zero => intro _; omega
  | succ m ih =>
      intro h
      have hm := ih (fun j hj => h j (by omega))
      have hne := h m (by omega)
      have hsub : (prgStep U)^[m] S ⊆ (prgStep U)^[m+1] S := by
        rw [Function.iterate_succ_apply']; exact prgStep_extensive U _
      obtain ⟨x, hx1, hx2⟩ : ∃ x, x ∈ (prgStep U)^[m+1] S ∧ x ∉ (prgStep U)^[m] S := by
        by_contra hc
        push_neg at hc
        exact hne (Finset.Subset.antisymm (fun y hy => hc y hy) hsub)
      have hxU : x ∈ U := by
        rw [Function.iterate_succ_apply'] at hx1
        simp only [prgStep, Finset.mem_union, Finset.mem_filter] at hx1
        rcases hx1 with h1 | h1
        · exact absurd h1 hx2
        · exact h1.1
      have hlt : ((prgStep U)^[m] S ∩ U).card < ((prgStep U)^[m+1] S ∩ U).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.inter_subset_inter hsub (Finset.Subset.refl U))]
        exact ⟨x, Finset.mem_inter.mpr ⟨hx1, hxU⟩,
          fun hc => hx2 (Finset.mem_of_mem_inter_left hc)⟩
      omega

lemma exists_prgStep_stable (U S : Finset (Expression Shape.KeyS)) :
    ∃ i, i ≤ U.card ∧ (prgStep U)^[i+1] S = (prgStep U)^[i] S := by
  by_contra hc
  push_neg at hc
  have hgrow := prgStep_card_growth U S (U.card + 1) (fun j hj => hc j (by omega))
  have hle : ((prgStep U)^[U.card+1] S ∩ U).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

/-- **The bounded `prgClosure` really is a closure**: one more derivation step adds nothing. -/
theorem prgStep_prgClosure (U S : Finset (Expression Shape.KeyS)) :
    prgStep U (prgClosure U S) = prgClosure U S := by
  obtain ⟨i, hi, hstable⟩ := exists_prgStep_stable U S
  rw [prgClosure_eq_iterate, prgStep_stable hstable (U.card+1) (by omega),
    ← Function.iterate_succ_apply' (prgStep U) i S]
  exact hstable

/-- The closure is closed under derivation (within the universe). -/
theorem G0_mem_prgClosure {U S : Finset (Expression Shape.KeyS)} {k : Expression Shape.KeyS}
    (hk : k ∈ prgClosure U S) (hU : Expression.G0 k ∈ U) :
    Expression.G0 k ∈ prgClosure U S := by
  have hstep : Expression.G0 k ∈ prgStep U (prgClosure U S) := by
    simp only [prgStep, Finset.mem_union, Finset.mem_filter]
    exact Or.inr ⟨hU, by simp [isDerived, hk]⟩
  rwa [prgStep_prgClosure] at hstep

theorem G1_mem_prgClosure {U S : Finset (Expression Shape.KeyS)} {k : Expression Shape.KeyS}
    (hk : k ∈ prgClosure U S) (hU : Expression.G1 k ∈ U) :
    Expression.G1 k ∈ prgClosure U S := by
  have hstep : Expression.G1 k ∈ prgStep U (prgClosure U S) := by
    simp only [prgStep, Finset.mem_union, Finset.mem_filter]
    exact Or.inr ⟨hU, by simp [isDerived, hk]⟩
  rwa [prgStep_prgClosure] at hstep

-- and the converse: a derived key is in the closure only if it was in the base, or its
-- seed is in the closure
lemma iterate_reflect_G0 (U S : Finset (Expression Shape.KeyS)) : ∀ (n : ℕ)
    (k : Expression Shape.KeyS), Expression.G0 k ∈ (prgStep U)^[n] S →
      Expression.G0 k ∈ S ∨ k ∈ (prgStep U)^[n] S := by
  intro n
  induction n with
  | zero => intro k h; exact Or.inl (by simpa using h)
  | succ m ih =>
      intro k h
      rw [Function.iterate_succ_apply'] at h
      simp only [prgStep, Finset.mem_union, Finset.mem_filter] at h
      rcases h with h | h
      · rcases ih k h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [Function.iterate_succ_apply']; exact prgStep_extensive U _ h')
      · right
        rw [Function.iterate_succ_apply']
        refine prgStep_extensive U _ ?_
        have h2 := h.2
        simp only [isDerived, decide_eq_true_eq] at h2
        exact h2

lemma iterate_reflect_G1 (U S : Finset (Expression Shape.KeyS)) : ∀ (n : ℕ)
    (k : Expression Shape.KeyS), Expression.G1 k ∈ (prgStep U)^[n] S →
      Expression.G1 k ∈ S ∨ k ∈ (prgStep U)^[n] S := by
  intro n
  induction n with
  | zero => intro k h; exact Or.inl (by simpa using h)
  | succ m ih =>
      intro k h
      rw [Function.iterate_succ_apply'] at h
      simp only [prgStep, Finset.mem_union, Finset.mem_filter] at h
      rcases h with h | h
      · rcases ih k h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by rw [Function.iterate_succ_apply']; exact prgStep_extensive U _ h')
      · right
        rw [Function.iterate_succ_apply']
        refine prgStep_extensive U _ ?_
        have h2 := h.2
        simp only [isDerived, decide_eq_true_eq] at h2
        exact h2

theorem prgClosure_reflects_G0 {U S : Finset (Expression Shape.KeyS)}
    {k : Expression Shape.KeyS} (h : Expression.G0 k ∈ prgClosure U S) :
    Expression.G0 k ∈ S ∨ k ∈ prgClosure U S := by
  rw [prgClosure_eq_iterate] at h ⊢
  exact iterate_reflect_G0 U S _ k h

theorem prgClosure_reflects_G1 {U S : Finset (Expression Shape.KeyS)}
    {k : Expression Shape.KeyS} (h : Expression.G1 k ∈ prgClosure U S) :
    Expression.G1 k ∈ S ∨ k ∈ prgClosure U S := by
  rw [prgClosure_eq_iterate] at h ⊢
  exact iterate_reflect_G1 U S _ k h


lemma iterate_of_stable {U X : Finset (Expression Shape.KeyS)} (h : prgStep U X = X) :
    ∀ n, (prgStep U)^[n] X = X := by
  intro n; induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, h]

theorem prgClosure_idem (U S : Finset (Expression Shape.KeyS)) :
    prgClosure U (prgClosure U S) = prgClosure U S := by
  rw [prgClosure_eq_iterate (S := prgClosure U S)]
  exact iterate_of_stable (prgStep_prgClosure U S) _

/-- LM18 `r(e)` (Definition 3) evaluated at a pattern directly, i.e. `keyRecovery` at a
    set large enough that nothing is hidden. -/
def rOf {s : Shape} (e : Expression s) : Finset (Expression Shape.KeyS) :=
  prgClosure (keySubterms e) (extractKeys e ∪ ancestorKeys (exprKeys e))

/--
  **LM18 Lemma 3, property 1 — the atomicisation lemma.**

  If the *roots* of `Keys(e)` are atomic, then every key of `Keys(e)` that is not recovered
  — i.e. every key the pattern function is about to hide behind — is itself atomic.

  This is what makes the IND-CPA reduction applicable: `reductionHidingOneKey` can only
  target a key *variable*, because the oracle's uniformly random key has to be identified
  with one.  The hypothesis `Roots(Keys(e)) ⊆ 𝐊` is discharged in LM18 by a pseudorandom
  key renaming (`PrgRenameRel` / `prgRename` here), which renames the roots to fresh atomic
  keys; the conclusion is then inherited through the renaming.
-/
theorem hiddenKeys_atomic_of_atomicRoots {s : Shape} (e : Expression s)
    (hroots : ∀ k ∈ rootsOf (exprKeys e), isAtomicKey k = true) :
    ∀ k ∈ exprKeys e, k ∉ rOf e → isAtomicKey k = true := by
  intro k hk hnr
  by_contra hat
  -- a non-atomic key cannot be a root of `Keys(e)` ...
  have hnotroot : k ∉ rootsOf (exprKeys e) := fun hc => hat (hroots k hc)
  -- ... so some `k' ∈ Keys(e)` strictly yields it
  have hex : ∃ k' ∈ exprKeys e, strictYields k' k = true := by
    by_contra hcon
    push_neg at hcon
    refine hnotroot (mem_rootsOf.mpr ⟨hk, fun k' hk' => ?_⟩)
    cases hb : strictYields k' k
    · rfl
    · exact absurd hb (hcon k' hk')
  obtain ⟨k', hk', hy⟩ := hex
  -- that `k'` is exactly what the ancestor clause of `keyRecovery` collects ...
  have hbase : k' ∈ extractKeys e ∪ ancestorKeys (exprKeys e) :=
    Finset.mem_union_right _ (mem_ancestorKeys.mpr ⟨hk', k, hk, hy⟩)
  -- ... and `k` lies in its PRG closure, so `k` is recovered.  Contradiction.
  exact hnr (mem_prgClosure_of_strictYields hy hbase (keySubterms_subset_of_mem_exprKeys e k hk))

/-- The hypothesis of the atomicisation lemma, named. -/
def AtomicRoots {s : Shape} (e : Expression s) : Prop :=
  ∀ k ∈ rootsOf (exprKeys e), isAtomicKey k = true

/-- PRG-free expressions trivially have atomic roots. -/
lemma atomicRoots_of_atomicKeys {s : Shape} {e : Expression s} (h : AtomicKeys e) :
    AtomicRoots e :=
  fun k hk => h k (exprKeys_subset_keySubterms e (rootsOf_subset _ hk))

lemma keyRecoveryMonotone {s : Shape} (p : Expression s) (S1 S2 : Finset (Expression Shape.KeyS)) (h : S1 ⊆ S2) :
  keyRecovery p S1 ⊆ keyRecovery p S2 := by
  simp only [keyRecovery]
  -- S1 ⊆ S2 implies prgClosure U S1 ⊆ prgClosure U S2
  have h_prg1 := prgClosureMonotone (keySubterms p) S1 S2 h
  -- which implies hideEncrypted (prg1) p ⊆ hideEncrypted (prg2) p
  have h_hide := hideEncryptedMonotone _ _ p h_prg1
  -- which implies extractKeys (hide1) ⊆ extractKeys (hide2)
  have h_ext := keyPartsMonotone _ _ h_hide
  -- and Keys(hide1) ⊆ Keys(hide2), hence the ancestor clause is monotone too
  have h_keys := exprKeysMonotone _ _ h_hide
  -- which implies the final prgClosure is also a subset
  apply prgClosureMonotone
  exact Finset.union_subset_union h_ext (ancestorKeysMonotone h_keys)

lemma keyRecoveryContained {s : Shape} (p : Expression s) (S : Finset (Expression Shape.KeyS)) :
  keyRecovery p S ⊆ keySubterms p := by
  simp only [keyRecovery]
  set view := hideEncrypted (prgClosure (keySubterms p) S) p with hview
  -- 1. hideEncrypted is structurally smaller than p
  have h_hide : view ⊆ p := hideEncryptedSmallerValue (prgClosure (keySubterms p) S) p
  -- 2. So the universe of the hidden view is a subset of the universe of p
  have h_univ := keySubtermsMonotone _ _ h_hide
  -- 3. Both halves of the recovery set are bounded by the universe of the view ...
  have h_ext : extractKeys view ⊆ keySubterms p :=
    Finset.Subset.trans (extractKeys_subset_keySubterms view) h_univ
  have h_anc : ancestorKeys (exprKeys view) ⊆ keySubterms p :=
    Finset.Subset.trans (ancestorKeys_subset _)
      (Finset.Subset.trans (exprKeys_subset_keySubterms view) h_univ)
  -- 4/5. Their union is bounded by the universe, hence so is its PRG closure.
  -- (NB: `⊆` is shadowed by `ExpressionInclusion` in this file, so we avoid the
  -- notation on the union and feed `Finset.union_subset` directly.)
  exact prgClosureContained _ _ (Finset.union_subset h_ext h_anc)

-- REMOVED (see CHANGELOG 2026-09-16): `extractKeys_hideEncrypted_self`.
--
-- It claimed `extractKeys (hide keys e) ⊆ extractKeys (hide (extractKeys (hide keys e)) e)`
-- and was the last `sorry` outside `HidingOnePrgSeed.lean`.  The statement is FALSE:
--
--     e = Enc (VarK 0) (VarK 1),  keys = {VarK 0}
--     hide keys e            = Enc (VarK 0) (VarK 1)
--     Y := extractKeys (…)   = {VarK 1}
--     hide Y e               = Hidden (VarK 0)        -- VarK 0 ∉ Y
--     extractKeys (hide Y e) = ∅          so  Y ⊆ ∅  fails.
--
-- (`scratch/ExtractKeysSelfCounterexample.lean` computes this.)  Its only consumer, the
-- fixpoint step of `symbolicToSemanticIndistinguishabilityAdversaryView`, no longer needs
-- it: that step now hides `z \ keyRecovery expr z` in one IND-CPA application instead of
-- routing through the (also false) `H_ext_eq`.

-- We are now ready to calculate the fixpoint.

def adversaryKeys {s : Shape} (p : Expression s) : Finset (Expression Shape.KeyS) :=
  -- Notice the third argument is now 'keySubterms p' instead of 'extractKeys p'
  greatestFixpoint (keyRecovery p) (keyRecoveryMonotone p) (keySubterms p) (keyRecoveryContained p)

lemma adversaryKeysIsFix {s : Shape} (e : Expression s) :
  let keys := adversaryKeys e
  keyRecovery e keys = keys
  := by
  apply greatestFixpointIsFixpoint

/-- `adversaryKeys e` is closed under PRG derivation (inside the expression's universe).
    This is one of the two facts LM18 Lemma 7's `Dup` case needs. -/
lemma adversaryKeys_G0_closed {s : Shape} (e : Expression s) {k : Expression Shape.KeyS}
    (hk : k ∈ adversaryKeys e) (hU : Expression.G0 k ∈ keySubterms e) :
    Expression.G0 k ∈ adversaryKeys e := by
  have hfix : keyRecovery e (adversaryKeys e) = adversaryKeys e := adversaryKeysIsFix e
  have hk' : k ∈ keyRecovery e (adversaryKeys e) := by rw [hfix]; exact hk
  have hres : Expression.G0 k ∈ keyRecovery e (adversaryKeys e) := by
    simp only [keyRecovery] at hk' ⊢
    exact G0_mem_prgClosure hk' hU
  rwa [hfix] at hres

lemma adversaryKeys_G1_closed {s : Shape} (e : Expression s) {k : Expression Shape.KeyS}
    (hk : k ∈ adversaryKeys e) (hU : Expression.G1 k ∈ keySubterms e) :
    Expression.G1 k ∈ adversaryKeys e := by
  have hfix : keyRecovery e (adversaryKeys e) = adversaryKeys e := adversaryKeysIsFix e
  have hk' : k ∈ keyRecovery e (adversaryKeys e) := by rw [hfix]; exact hk
  have hres : Expression.G1 k ∈ keyRecovery e (adversaryKeys e) := by
    simp only [keyRecovery] at hk' ⊢
    exact G1_mem_prgClosure hk' hU
  rwa [hfix] at hres

def adversaryView {s : Shape} (e : Expression s) : Expression s :=
  hideEncrypted (adversaryKeys e) e

-- To conclude, we connect parts (i), (ii), and (iii) and define symbolic indistinguishability.

lemma prgClosure_keyRecovery {s : Shape} (e : Expression s) (S : Finset (Expression Shape.KeyS)) :
    prgClosure (keySubterms e) (keyRecovery e S) = keyRecovery e S := by
  simp only [keyRecovery]
  exact prgClosure_idem _ _

lemma adversaryKeys_prgClosed {s : Shape} (e : Expression s) :
    prgClosure (keySubterms e) (adversaryKeys e) = adversaryKeys e := by
  have hfix : keyRecovery e (adversaryKeys e) = adversaryKeys e := adversaryKeysIsFix e
  conv_lhs => rw [← hfix]
  rw [prgClosure_keyRecovery]
  exact hfix

lemma adversaryView_eq_hideEncrypted_closure {s : Shape} (e : Expression s) :
    hideEncrypted (prgClosure (keySubterms e) (adversaryKeys e)) e = adversaryView e := by
  rw [adversaryKeys_prgClosed]; rfl

/-- `adversaryKeys e` also *reflects* derivation: a derived key is in it only because it is
    directly recoverable from the adversary view, or because its seed is.  This is the other
    fact LM18 Lemma 7's `Dup` case needs — Lemma 4 then kills the `extractKeys` branch and
    Lemma 6(1) the ancestor branch. -/
lemma adversaryKeys_reflects_G0 {s : Shape} (e : Expression s) {k : Expression Shape.KeyS}
    (h : Expression.G0 k ∈ adversaryKeys e) :
    Expression.G0 k ∈ extractKeys (adversaryView e) ∪ ancestorKeys (exprKeys (adversaryView e))
      ∨ k ∈ adversaryKeys e := by
  have hfix : keyRecovery e (adversaryKeys e) = adversaryKeys e := adversaryKeysIsFix e
  have h' : Expression.G0 k ∈ keyRecovery e (adversaryKeys e) := by rw [hfix]; exact h
  simp only [keyRecovery] at h'
  rcases prgClosure_reflects_G0 h' with hb | hc
  · left; rwa [adversaryView_eq_hideEncrypted_closure] at hb
  · right; rw [← hfix]; simp only [keyRecovery]; exact hc

lemma adversaryKeys_reflects_G1 {s : Shape} (e : Expression s) {k : Expression Shape.KeyS}
    (h : Expression.G1 k ∈ adversaryKeys e) :
    Expression.G1 k ∈ extractKeys (adversaryView e) ∪ ancestorKeys (exprKeys (adversaryView e))
      ∨ k ∈ adversaryKeys e := by
  have hfix : keyRecovery e (adversaryKeys e) = adversaryKeys e := adversaryKeysIsFix e
  have h' : Expression.G1 k ∈ keyRecovery e (adversaryKeys e) := by rw [hfix]; exact h
  simp only [keyRecovery] at h'
  rcases prgClosure_reflects_G1 h' with hb | hc
  · left; rwa [adversaryView_eq_hideEncrypted_closure] at hb
  · right; rw [← hfix]; simp only [keyRecovery]; exact hc

def symIndistinguishable {s : Shape} (e1 e2 : Expression s) : Prop :=
  ∃ (r : varRenaming), validVarRenaming r ∧
   normalizeExpr (applyVarRenaming r (adversaryView e1)) = normalizeExpr (adversaryView e2)

-- For PRGs, we need to define a new relation to simulate "Game Hops"
-- Helper to jointly replace G0(targetSeed) and G1(targetSeed) with distinct fresh variables
def replacePRG {s : Shape} (targetSeed : Expression 𝕂) (idx0 idx1 : ℕ) (p : Expression s) : Expression s :=
  match p with
  | Expression.BitE b => Expression.BitE b
  | Expression.VarK n => Expression.VarK n
  | Expression.Eps => Expression.Eps
  | Expression.Pair p1 p2 => Expression.Pair (replacePRG targetSeed idx0 idx1 p1) (replacePRG targetSeed idx0 idx1 p2)
  | Expression.Perm b p1 p2 => Expression.Perm b (replacePRG targetSeed idx0 idx1 p1) (replacePRG targetSeed idx0 idx1 p2)
  | Expression.Enc k m => Expression.Enc (replacePRG targetSeed idx0 idx1 k) (replacePRG targetSeed idx0 idx1 m)
  | Expression.Hidden k => Expression.Hidden (replacePRG targetSeed idx0 idx1 k)

  | Expression.G0 k =>
      if k == targetSeed then
        Expression.VarK idx0
      else
        Expression.G0 (replacePRG targetSeed idx0 idx1 k)

  | Expression.G1 k =>
      if k == targetSeed then
        Expression.VarK idx1
      else
        Expression.G1 (replacePRG targetSeed idx0 idx1 k)

-- REMOVED (see CHANGELOG 2026-09-16): `inductive symbolicEquivalence`.
--
-- It extended `symIndistinguishable` with an `idealize_PRG` constructor performing a
-- game hop at the level of the *symbolic* relation.  Two problems:
--   * it was dead code -- nothing consumed it, and `Soundness.lean` still quantifies
--     over `symIndistinguishable`;
--   * a symbolic equivalence with a cryptographic hop built into it is no longer decided
--     by "normalise and compare", which is the property that makes the symbolic method
--     worth having.
-- The PRG hop belongs inside the soundness proof (see `HidingOnePrgSeed.lean`), not in
-- the definition of symbolic equivalence.  `replacePRG` above is kept: it is a genuine
-- pseudorandom key renaming and is used by the soundness proof.

end PRG
