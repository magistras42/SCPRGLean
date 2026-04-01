import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Vector.Defs

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs

import SymbolicGarbledCircuitsInLean.Core.CardinalityLemmas

-- This file defines computational semantics (`exprToFamDistr`), a function that maps an expression (and an encryption scheme) to a distribution over bitstrings.

abbrev BitVector (n: ℕ) := List.Vector Bool n

open Classical
open PMF

-- We consider an encryption scheme
structure encryptionFunctions (κ : ℕ) where
  encryptLength : ℕ -> ℕ
  encrypt : {n : ℕ} -> (key : BitVector κ) -> (msg : BitVector n) -> PMF (BitVector (encryptLength n))
  decrypt : {n : ℕ} -> (key : BitVector κ) -> (msg : BitVector (encryptLength n)) -> BitVector n

def encryptionScheme : Type := (κ : ℕ) -> encryptionFunctions κ

def shapeLength (κ : ℕ) (scheme : encryptionFunctions κ) (s : Shape) : ℕ :=
  match s with
  | Shape.BitS => 1
  | Shape.KeyS => κ
  | Shape.EmptyS => 0
  | Shape.PairS s₁ s₂ => (shapeLength κ scheme s₁) + (shapeLength κ scheme s₂)
  | Shape.EncS s => scheme.encryptLength (shapeLength κ scheme s)

def allVarsSmallerThanBExpr (e : BitExpr) (n : ℕ ) : Prop :=
  match e with
  | BitExpr.VarB k => k < n
  | BitExpr.Bit _ => true
  | BitExpr.Not e' => allVarsSmallerThanBExpr e' n

def allVarsSmallerThan {s : Shape} (e : Expression s) (n : ℕ) : Prop :=
match e with
| Expression.BitE b => allVarsSmallerThanBExpr b n
| Expression.VarK k => k < n
| Expression.Pair e₁ e₂ => allVarsSmallerThan e₁ n ∧ allVarsSmallerThan e₂ n
| Expression.Enc e₁ e₂ => allVarsSmallerThan e₁ n ∧ allVarsSmallerThan e₂ n
| Expression.Perm e₁ e₂ e₃ => allVarsSmallerThan e₁ n ∧ allVarsSmallerThan e₂ n ∧ allVarsSmallerThan e₃ n
| Expression.Hidden (Expression.VarK k) => k < n
| Expression.Eps => True

def allVarsSmallerThanBExprMonotone {e : BitExpr} {n₁ : ℕ} {n₂ : ℕ} (h : n₁ ≤ n₂) (h' : allVarsSmallerThanBExpr e n₁) : allVarsSmallerThanBExpr e n₂ := by
  induction e
  case VarB k =>
    simp [allVarsSmallerThanBExpr] at h'
    exact Nat.lt_of_lt_of_le h' h
  case Bit b =>
    simp [allVarsSmallerThanBExpr]
  case Not e ihe =>
    simp [allVarsSmallerThanBExpr] at h'
    apply ihe
    assumption

def allVarsSmallerThanMonotone {s : Shape} (e : Expression s) (n₁ : ℕ ) (n₂ : ℕ) (h₁ : n₁ ≤ n₂) (h₂ : allVarsSmallerThan e n₁) : allVarsSmallerThan e n₂ := by
  induction e <;> try simp [allVarsSmallerThan]
  case BitE b =>
    simp [allVarsSmallerThan] at h₂
    apply allVarsSmallerThanBExprMonotone h₁ h₂
  case VarK k =>
    simp [allVarsSmallerThan] at h₂
    omega
  case Pair e₁ e₂ ih₁ ih₂ =>
    simp [allVarsSmallerThan] at h₂
    exact ⟨ih₁ h₂.1, ih₂ h₂.2⟩
  case Enc e₁ e₂ ih₁ ih₂ =>
    simp [allVarsSmallerThan] at h₂
    exact ⟨ih₁ h₂.1, ih₂ h₂.2⟩
  case Perm e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
    simp [allVarsSmallerThan] at h₂
    exact ⟨ih₁ h₂.1, ih₂ h₂.2.1, ih₃ h₂.2.2⟩
  case Hidden k ih =>
    cases k
    simp[allVarsSmallerThan]
    simp[allVarsSmallerThan] at h₂
    omega

def getMaxVarBExpr : BitExpr -> ℕ
  | BitExpr.VarB k => k
  | BitExpr.Bit _ => 0
  | BitExpr.Not e => getMaxVarBExpr e

def getMaxVar {s : Shape} : Expression s -> ℕ
  | Expression.BitE b => getMaxVarBExpr b
  | Expression.VarK k => k
  | Expression.Pair e₁ e₂ => max (getMaxVar e₁) (getMaxVar e₂)
  | Expression.Enc e₁ e₂ => max (getMaxVar e₁) (getMaxVar e₂)
  | Expression.Perm e₁ e₂ e₃ => max (max (getMaxVar e₁) (getMaxVar e₂)) (getMaxVar e₃)
  | Expression.Hidden (Expression.VarK k) => k
  | Expression.Eps => 0

lemma allVarsSmallerThanMaxBexpr (e : BitExpr) : allVarsSmallerThanBExpr e (getMaxVarBExpr e + 1) := by
  induction e
  case VarB k =>
    simp [getMaxVarBExpr]
    apply Nat.lt_succ_self
  case Bit b =>
    simp [getMaxVarBExpr, allVarsSmallerThanBExpr]
  case Not e' ih =>
    simp [getMaxVarBExpr, allVarsSmallerThanBExpr]
    assumption

lemma allVarsSmallerThanMax {s : Shape} (e : Expression s) : allVarsSmallerThan e (getMaxVar e + 1) := by
  induction e <;> try simp [getMaxVar, allVarsSmallerThan]
  case BitE b =>
    apply allVarsSmallerThanMaxBexpr
  case Pair e₁ e₂ ih₁ ih₂ =>
    constructor
    · apply allVarsSmallerThanMonotone e₁ (getMaxVar e₁ + 1)
      · omega
      · assumption
    · apply allVarsSmallerThanMonotone e₂ (getMaxVar e₂ + 1)
      · omega
      · assumption
  case Enc e₁ e₂ ih₁ ih₂ =>
    constructor
    · apply allVarsSmallerThanMonotone e₁ (getMaxVar e₁ + 1)
      · omega
      · assumption
    · apply allVarsSmallerThanMonotone e₂ (getMaxVar e₂ + 1)
      · omega
      · assumption
  case Perm e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
    constructor <;> try constructor
    · apply allVarsSmallerThanMonotone e₁ (getMaxVar e₁ + 1)
      · omega
      · assumption
    · apply allVarsSmallerThanMonotone e₂ (getMaxVar e₂ + 1)
      · omega
      · assumption
    · apply allVarsSmallerThanMonotone e₃ (getMaxVar e₃ + 1)
      · omega
      · assumption
  case Hidden k ih =>
    cases k
    simp[allVarsSmallerThan, getMaxVar]

lemma getMaxVarMonotone {s : Shape} (e1 e2 : Expression s) (H : e1 ⊆ e2) : getMaxVar e1 <= getMaxVar e2 :=
  by
  induction e2 <;> cases e1 <;> simp [ExpressionInclusion, getMaxVar] at *
  case BitE.BitE H =>
    rw [H]
  case VarK.VarK =>
    rw [H]
  case Pair.Pair s1 s2 e1 e2 H1 H2 f1 f2  =>
    have L : getMaxVar f1 ≤ getMaxVar e1 := by apply H1; apply H.1
    have R : getMaxVar f2 ≤ getMaxVar e2 := by apply H2; apply H.2
    omega
  case Perm.Perm s0 s1 s2 e1 H1 H2 e0 f1 f2 =>
    have L : getMaxVar f1 ≤ getMaxVar s1 := by apply H1; apply H.1
    have R : getMaxVar f2 ≤ getMaxVar s2 := by apply H2; apply H.2.1
    have Z : getMaxVar e0 ≤ getMaxVar s0 := by apply e1; apply H.2.2
    omega
  case Enc.Enc e1 e2 H1 H2 f1 f2 =>
    have R : getMaxVar f2 ≤ getMaxVar e2 := by apply H2; apply H.2
    rw [H.1]
    omega
  case Enc.Hidden e1 e2 e3 H2 f1 f2 =>
    -- have R : getMaxVar f2 ≤ getMaxVar e2 := by apply H2; apply H.2
    rw [H]
    cases e2; simp [getMaxVar]
  case Hidden.Hidden =>
    rw [H]

def evalBitExpr (bVars : ℕ -> Bool) (e : BitExpr) : Bool :=
  match e with
  | BitExpr.VarB v =>
    bVars v
  | BitExpr.Not e' =>
    not (evalBitExpr bVars e')
  | BitExpr.Bit b => b

def ones {k : ℕ} := List.Vector.replicate k true

noncomputable
def evalExpr (enc : encryptionFunctions κ) (kVars : ℕ -> BitVector κ) (bVars : ℕ -> Bool) (e : Expression s) : PMF (BitVector (shapeLength κ enc s)) :=
  match e with
  | Expression.Enc (Expression.VarK k) e => do
    let e' ← evalExpr enc kVars bVars e
    let key := kVars k
    enc.encrypt key e'
  | Expression.Pair e₁ e₂ => do
    let e₁' ← evalExpr enc kVars bVars e₁
    let e₂' ← evalExpr enc kVars bVars e₂
    PMF.pure $ List.Vector.append e₁' e₂'
  | Expression.BitE b => do
    let b' := evalBitExpr bVars b
    PMF.pure $ List.Vector.cons b' List.Vector.nil
  | Expression.VarK k => do
    PMF.pure (kVars k)
  | Expression.Perm (Expression.BitE b) e₁ e₂ => do
    let b' := evalBitExpr bVars b
    let e₁' ← evalExpr enc kVars bVars e₁
    let e₂' ← evalExpr enc kVars bVars e₂
    if b' then PMF.pure $ List.Vector.append e₂' e₁'
    else PMF.pure $ List.Vector.append e₁' e₂'
  | Expression.Eps =>
    PMF.pure List.Vector.nil
  | Expression.Hidden (Expression.VarK k) => do
    let key := kVars k
    enc.encrypt key ones

def extendFin {k : ℕ} (default : X) (x : Fin k -> X) :  (ℕ -> X) :=
  fun i =>
    if H : i<k then
      x ⟨i, H⟩
    else
      default

noncomputable
def evalExprVarsL {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (vars_length : ℕ) (e : Expression s)  : PMF (BitVector (shapeLength κ enc s)) := do
  -- let v := getMaxVar e + 1
  -- now we pick a random vector of v boolean values from the uniform distribution
  let bvars <- uniformOfFintype (Fin vars_length -> Bool)
  let kvars <- uniformOfFintype (Fin vars_length -> BitVector κ)
  evalExpr enc (extendFin ones kvars) (extendFin false bvars) e

def restrict {k l : ℕ} (H : l<=k) (f : Fin k -> S) : (Fin l -> S) :=
  fun i =>
    f ⟨i, by omega⟩

noncomputable
def exprToDistr {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (e : Expression s)  : PMF (BitVector (shapeLength κ enc s)) :=
  evalExprVarsL enc (getMaxVar e + 1) e

-- main definition of the module - computational semantic of expression
noncomputable
def exprToFamDistr (enc : encryptionScheme) (e : Expression s) : (κ : ℕ) → PMF (BitVector (shapeLength κ (enc κ) s)) :=
  fun κ => exprToDistr (enc κ) e

----- LEMMAS -----

def agreeOnPrefix (l : ℕ) (f1 f2 : ℕ -> S) := forall i, i < l -> f1 i = f2 i

lemma evalNoMatterBit (l : ℕ) (bVars1 bVars2 : ℕ -> Bool) (e : BitExpr) :
  agreeOnPrefix (l) bVars1 bVars2 ->
  l >= 1 + getMaxVarBExpr e ->
  evalBitExpr bVars1 e = evalBitExpr bVars2 e := by
  intro Hb Hl
  induction e <;> try simp [evalBitExpr]
  case VarB a =>
    simp [agreeOnPrefix] at Hb
    apply Hb

    simp [getMaxVarBExpr] at Hl
    omega
  case Not a Ha =>
    apply Ha
    assumption


lemma evalNoMatter {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (l : ℕ) (kVars1 kVars2: (ℕ -> BitVector κ)) (bVars1 bVars2 : ℕ -> Bool) (e : Expression s) :
  agreeOnPrefix l kVars1 kVars2 ->
  agreeOnPrefix l bVars1 bVars2 ->
  l >= getMaxVar e + 1 ->
  evalExpr enc kVars1 bVars1 e = evalExpr enc kVars2 bVars2 e := by
  intro Hk Hb Hl
  induction e <;> try (simp [evalExpr, evalBitExpr]; try simp [getMaxVar] at Hl)
  case BitE a =>
    rw [evalNoMatterBit l]
    assumption
    omega
  case VarK a =>
    rw [Hk]
    assumption
  case Pair s1s2 e1 e2 He1 He2 =>
    rw [He1, He2] <;> omega
  case Perm s e1 e2 Hs He1 He2 =>
    cases s
    simp [getMaxVar] at Hl
    simp [evalExpr]
    rw [He1] <;> try omega
    rw [He2] <;> try omega
    rw [evalNoMatterBit l] <;> try omega
  case Enc e1 e2 He1 He2 =>
    cases e1
    simp [getMaxVar] at Hl
    simp [evalExpr]
    rw [He2] <;> try omega
    rw [Hk] ; try omega
  case Hidden e He =>
    cases e
    simp [getMaxVar] at Hl
    simp [evalExpr]
    rw [Hk] ; try omega

lemma restrictAndExtend (l1 l2 : ℕ) (H : l1 <= l2) (f : Fin l2 -> S) (zero : S) :
  agreeOnPrefix l1 (extendFin zero f) (extendFin zero (restrict H f)) := by
  intro i Hi
  have H2 : i < l2 := by omega
  have Ha : extendFin zero f i = f ⟨i, H2⟩ := by
    simp [extendFin]
    exact dif_pos H2
  have Hb : extendFin zero (restrict H f) i = f ⟨i, H2⟩ := by
    simp [extendFin]
    exact dif_pos Hi
  rw [Ha, Hb]

lemma boring {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (l : ℕ) (l2 : ℕ) (kVars: (Fin l -> BitVector κ)) (bVars : Fin l -> Bool) (e : Expression s) :
  (H : l >= l2) ->
  (l2 >= getMaxVar e+1) ->
  evalExpr enc (extendFin ones kVars) (extendFin false bVars) e =
  evalExpr enc (extendFin ones (restrict H kVars)) (extendFin false (restrict H bVars)) e := by
  intro H Hl
  apply evalNoMatter _ (l2)
  apply restrictAndExtend
  apply restrictAndExtend
  assumption

noncomputable
def rnd1 (κ : ℕ) (vars_length : ℕ)  : PMF ((Fin vars_length -> Bool) × (Fin vars_length -> BitVector κ)) := do
  let bvars <- uniformOfFintype (Fin vars_length -> Bool)
  let kvars <- uniformOfFintype (Fin vars_length -> BitVector κ)
  return (bvars, kvars)

noncomputable
def rnd2 (κ : ℕ) (vars_length1 vars_length2 : ℕ) (H : vars_length2 <= vars_length1) : PMF ((Fin vars_length2 -> Bool) × (Fin vars_length2 -> BitVector κ)) := do
  let bvars <- uniformOfFintype (Fin vars_length1 -> Bool)
  let kvars <- uniformOfFintype (Fin vars_length1 -> BitVector κ)
  return (restrict H bvars, restrict H kvars)

lemma rndsEq {κ : ℕ} (vars_length1 vars_length2 : ℕ) (H : vars_length2 <= vars_length1) : rnd1 κ vars_length2 = rnd2 κ vars_length1 vars_length2 H := by
  simp [rnd1, rnd2]
  ext x
  -- cases x with | mk kv bv =>
  simp [Functor.map, PMF.bind, uniformOfFintype, uniformOfFinset, ofFinset, Bind.bind]
  simp [Subtype.mk, Functor.map, DFunLike.coe]
  rw [tsum_eq_single x.1]
  swap
  · intro a
    intro h
    rw [ENNReal.tsum_eq_zero.mpr] <;> try simp
    intro i hi
    apply h
    rw [hi]
  rw [tsum_eq_single x.2]
  swap
  · intro b hb
    simp
    intro hcontra
    apply hb
    rw [hcontra]
  simp
  conv =>
    rhs
    arg 1
    intro a
    arg 2
    arg 1
    intro b
    rw [← mul_one ((2 ^ κ) ^ vars_length1)⁻¹]
    rw [← mul_zero (((2 : ENNReal) ^ κ) ^ vars_length1)⁻¹]
    rw [←mul_ite]
    -- change
    --   ((2 ^ κ) ^ vars_length2)⁻¹ * ((fun x => if x = (a, b) then 1 else 0) x)
    rfl
  simp only [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  simp [tsum_fintype, ← Finset.card_subtype]
  -- have hfin : Fintype {p : (Fin vars_length1 → Bool) × (Fin vars_length1 → BitVector κ) // x.1 = restrict H p.1 /\ x.2 = restrict H p.2} := by
  --   infer_instance
  rw [@Fintype.card_congr _ {p : (Fin vars_length1 → Bool) × (Fin vars_length1 → BitVector κ) // (fun p1 => x.1 = restrict H p1) p.1 /\ (fun p2 => x.2 = restrict H p2) p.2}]
  swap
  · apply Equiv.subtypeEquivProp
    ext p
    constructor
    · intro hx
      simp [hx]
    · intro ⟨hx₁, hx₂⟩
      simp [<- hx₁, <- hx₂]
  rw [@Fintype.card_congr _ ({p // (fun p1 => x.1 = restrict H p1) p} × {p // (fun p2 => x.2 = restrict H p2) p})]
  swap
  · apply (@Equiv.subtypeProdEquivProd _ _ (fun p1 => x.1 = restrict H p1) (fun p2 => x.2 = restrict H p2))
  simp
  let S : Finset (Fin vars_length1) := { x : Fin vars_length1 | x < vars_length2}
  let x1' : Fin vars_length1 → Bool := fun i =>
    if H : i < vars_length2 then x.1 ⟨i.1, H⟩
    else false
  rw [@Fintype.card_congr _ { p : (Fin vars_length1 → Bool) // forall i : S, p i = x1' i }]
  swap
  · apply Equiv.subtypeEquivProp
    ext p
    constructor
    · intro hx ⟨i, hi⟩
      simp [hx, restrict, x1']
      simp [S] at hi
      intro
      assumption
    · intro h
      ext ⟨vi, hi⟩
      simp [restrict]
      let i' : S := ⟨⟨vi, by omega⟩ , by simp [S]; assumption⟩
      have hi' := h i'
      simp [i'] at hi'
      simp [hi', x1']
      rw [dite_cond_eq_true]
      simp
      assumption
  rw [cardinalityCount]
  simp [S]
  simp [← Finset.card_subtype]
  rw [@Fintype.card_congr _ (Fin vars_length2)]
  swap
  · exact {
      toFun := fun i => ⟨i, by omega⟩
      invFun := fun i => ⟨⟨i, by omega⟩, by simp⟩
      left_inv := by intro i; simp
      right_inv := by intro i; simp
    }
  simp
  let x2' : Fin vars_length1 → BitVector κ := fun i =>
    if H : i < vars_length2 then x.2 ⟨i.1, H⟩
    else ones
  rw [@Fintype.card_congr _ { p : (Fin vars_length1 → BitVector κ) // forall i : S, p i = x2' i }]
  swap
  · apply Equiv.subtypeEquivProp
    ext p
    constructor
    · intro hx ⟨i, hi⟩
      simp [hx, restrict, x2']
      simp [S] at hi
      rw [ite_cond_eq_true] ; (try (simp; assumption))
    · intro h
      ext ⟨vi, hi⟩
      simp [restrict]
      let i' : S := ⟨⟨vi, by omega⟩ , by simp [S]; assumption⟩
      have hi' := h i'
      simp [i'] at hi'
      simp [hi', x2']
      rw [dite_cond_eq_true]
      simp
      assumption
  rw [cardinalityCount x2' S]
  simp [S]
  simp [← Finset.card_subtype]
  rw [@Fintype.card_congr _ (Fin vars_length2)]
  swap
  · exact {
      toFun := fun i => ⟨i, by omega⟩
      invFun := fun i => ⟨⟨i, by omega⟩, by simp⟩
      left_inv := by intro i; simp
      right_inv := by intro i; simp
    }
  ring_nf
  simp [← ENNReal.rpow_natCast, ← ENNReal.rpow_neg, ←ENNReal.rpow_add]
  congr 1
  ring_nf
  repeat rw [Nat.cast_sub]
  simp [← neg_mul, mul_sub, add_sub]
  simp [neg_mul]
  simp [sub_eq_add_neg, add_comm]
  ring
  all_goals (try assumption)

noncomputable
def evalExprVarsL2 {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (vars_length : ℕ) (e : Expression s)  : PMF (BitVector (shapeLength κ enc s)) := do
  let rand <- rnd1 κ vars_length
  let (bvars, kvars) := rand
  evalExpr enc (extendFin ones kvars) (extendFin false bvars) e

lemma evalExprVarsL2Eq {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (vars_length : ℕ) (e : Expression s) : evalExprVarsL2 enc vars_length e = evalExprVarsL enc vars_length e := by
  simp [evalExprVarsL2, evalExprVarsL]
  simp [rnd1]


lemma evalExprVarsNoMatter {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (vars_length1 vars_length2: ℕ) (e : Expression s) :
  vars_length1 >= vars_length2 ->
  vars_length2 >= (getMaxVar e + 1) ->
  evalExprVarsL enc vars_length1 e = evalExprVarsL enc vars_length2 e := by
  intro Hv1 Hv2
  nth_rw 2 [<-evalExprVarsL2Eq]
  simp [evalExprVarsL]
  simp [evalExprVarsL2]
  rw [rndsEq vars_length1] <;> try assumption
  simp [rnd2]
  conv =>
    lhs
    congr
    · skip
    · intro x
      congr
      · skip
      · intro y
        rw [boring enc vars_length1 vars_length2 _ _ _ (by assumption) (by assumption)]
        skip

def subst {X n} (i : ℕ) (x : X) (f : Fin n -> X) : Fin n -> X :=
  fun j =>
    if i=j then
      x
    else f j

noncomputable
def resample {X: Type} [Fintype X] [Nonempty X] (n : ℕ) (i : ℕ) : PMF (Fin n → X) :=
  do
  let x <- uniformOfFintype (Fin n -> X)
  let y <- uniformOfFintype X
  return subst i y x

lemma subst_eq {X n} (i : ℕ) (hi : i < n) (f : Fin n -> X) :
  subst i (f ⟨i, hi⟩) f = f := by
    ext x
    simp [subst]
    intro hi
    simp [hi]

lemma subst_eq_le {X n} (i : ℕ) (hi : n ≤ i) (x : X) (f : Fin n -> X) :
  subst i x f = f := by
    ext j
    simp [subst]
    intro hj
    omega

lemma sym_eq (a : A) (b : A) : (a = b) = (b = a) := by
    apply (@iff_iff_eq (a = b) (b = a)).mp
    constructor <;> (intro; symm; assumption)


lemma resampleIsTrivial {X: Type} [Fintype X] [Nonempty X] : resample n i = uniformOfFintype (Fin n -> X) := by
  ext1 b
  simp [resample, Bind.bind, PMF.bind, DFunLike.coe, uniformOfFintype, uniformOfFinset, ofFinset, Functor.map, Pure.pure, PMF.pure]
  simp [ENNReal.tsum_mul_left]
  if H : i < n then
    conv =>
      lhs; arg 2; arg 1; intro v
      rw [tsum_eq_single (b ⟨i, H⟩)]
      rw [← @mul_one ENNReal _ (↑(Fintype.card X))⁻¹]
      rw [← mul_ite_zero]
      rfl
      tactic =>
        intro x' hx'
        rw [ite_cond_eq_false]
        simp
        intro hcontra
        apply hx'
        rw [hcontra]
        simp [subst]
    rw [ENNReal.tsum_mul_left]
    simp [tsum_fintype, ← Finset.card_subtype]
    let Si : Finset (Fin n) := {s : Fin n | s = ⟨i, H⟩}
    let S : Finset (Fin n) := Finset.univ \ Si

    conv =>
      lhs; arg 2; arg 2
      rw [@Fintype.card_congr _ {f : Fin n → X // ∀ (x : S), f x = b x}]
      rw [cardinalityCount]
      rfl
      tactic =>
        apply Equiv.subtypeEquivProp
        ext f
        constructor
        · intro hf x
          rw [hf]
          simp [subst]
          rw [ite_cond_eq_false]
          simp
          have ⟨vx, hx⟩ := x
          simp [S, Si] at hx
          simp
          intro hcontra
          apply hx
          symm
          ext
          simp
          assumption
        · simp [S, Si]
          intro ha
          ext j
          simp [subst]
          split
          next hij =>
            simp [hij]
          next hij =>
            rw [ha]
            intro hcontra
            apply hij
            symm
            rw [hcontra]
    simp[S, Si, Finset.card_sdiff, ←Finset.card_subtype]
    conv =>
      rhs; rw [← @mul_one ENNReal _ (↑(Fintype.card X) ^ n)⁻¹]
      rfl
    congr 1
    have : n - (n - 1) = 1 := by
      omega
    simp [this]
    rw [ENNReal.inv_mul_cancel]
    all_goals simp
  else
    conv =>
      lhs; arg 2; arg 1; intro v; arg 1; intro y
      rw [subst_eq_le]
      rfl
      tactic => omega
    simp [tsum_fintype]
    rw [ENNReal.mul_inv_cancel, mul_one]
    all_goals simp

def subst2 (i : ℕ) (val : X) (kVars : (ℕ -> X)) :=
  fun x =>
    if x = i then val else kVars x


def restrictInfToFin  (l : ℕ)  (f : ℕ -> S) : (Fin l -> S) :=
  fun i =>
    f i

noncomputable
def resampling2 {X: Type} [Fintype X] [Nonempty X] (n : ℕ) (key₀ : ℕ) (ones : X) : PMF (Fin n -> X) :=
  do
    let b <- uniformOfFintype (Fin n -> X)
    let y <- uniformOfFintype X
    return restrictInfToFin n (subst2 key₀ y (extendFin ones b))

lemma resampling2EqResample {X: Type} [Fintype X] [Nonempty X] (n : ℕ) (key₀ : ℕ) (ones : X) :
  resampling2 n key₀ ones = resample n key₀ := by
  ext1 b
  simp [resampling2, resample]
  congr
  ext x₁ x₂
  congr
  ext a₁ k
  simp [restrictInfToFin, extendFin, subst, subst2]
  congr 1
  simp [eq_comm]

lemma resampleIsTrivial2 {X: Type} [Fintype X] [Nonempty X] (ones : X):
  uniformOfFintype (Fin n -> X) =
  resampling2 n key₀ ones
   := by
    rw[resampling2EqResample, resampleIsTrivial]

lemma cutAndExtend [Fintype X] [Nonempty X] (ones : X) (Seq : ℕ -> X) :
  agreeOnPrefix n Seq (extendFin ones (@restrictInfToFin X n Seq)) :=
by
  intro i Hi
  simp [extendFin, Hi, restrictInfToFin]

lemma evalCutAndExtend (n : ℕ) (H : n > getMaxVar e):
  evalExpr enc (subst2 key₀ seed (extendFin ones b)) (extendFin false a) e =
  evalExpr enc (extendFin ones (@restrictInfToFin _ n (subst2 key₀ seed (extendFin ones b)))) (extendFin false a) e :=
by
  apply evalNoMatter _ n
  apply cutAndExtend
  simp [agreeOnPrefix]
  assumption

lemma veryBoring :
  (do
    let a ← PMF.uniformOfFintype (BitVector κ)
    let b ←  (PMF.uniformOfFintype (Fin l → Bool))
    let c ←  (PMF.uniformOfFintype (Fin l → BitVector κ))
    evalExpr enc (extendFin ones (restrictInfToFin l (subst2 key₀ a (extendFin ones c)))) (extendFin false b) e
  ) =
  (do
    let b ←  (PMF.uniformOfFintype (Fin l → Bool))
    let c <- resampling2 l key₀ ones
    evalExpr enc (extendFin ones c) (extendFin false b) e
  ) := by
  simp [resampling2]
  simp [Bind.bind]
  conv =>
    lhs
    rw [PMF.bind_comm]
    arg 2
    intro x
    rw [PMF.bind_comm]

lemma resamplingLemma2 {l : ℕ} (key₀ : ℕ) {enc : encryptionFunctions κ} : (l > getMaxVar e) ->
  (do
    let seed ← PMF.uniformOfFintype (BitVector κ)
    let a ←  (PMF.uniformOfFintype (Fin l → Bool))
    let b ←  (PMF.uniformOfFintype (Fin l → BitVector κ))
    evalExpr enc (subst2 key₀ seed (extendFin ones b)) (extendFin false a) e) =
   (exprToDistr enc e)
  := by
  intro Hi
  conv =>
    lhs
    arg 2; intro a
    arg 2; intro b
    arg 2; intro c
    rw [evalCutAndExtend l Hi]
  rw [veryBoring]
  rw [<-resampleIsTrivial2 ones]
  simp [exprToDistr]
  rw [<-evalExprVarsNoMatter _ l (getMaxVar e + 1)]
  · simp [evalExprVarsL]
  · exact Hi
  · apply Nat.le_refl


lemma lifting (x : PMF X) (f : X -> PMF Y) :
  let lhs : OptionT PMF Y := liftM (
    do
      let a : X <- x
      f a
  )
  let rhs : OptionT PMF Y :=
  (do
    let a : X <- liftM x
    liftM (f a)
  )
  lhs = rhs :=
  by
    simp [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk]
    conv =>
      rhs
      rw [@Bind.bind, Monad.toBind, OptionT.instMonad]
      simp [OptionT.bind, OptionT.mk]

lemma resamplingLemma : (l > getMaxVar e) ->
  (do
    let z : OptionT PMF _ := PMF.uniformOfFintype (BitVector κ)
    let seed ← z
    let a ← liftM (PMF.uniformOfFintype (Fin l → Bool))
    let b ← liftM (PMF.uniformOfFintype (Fin l → BitVector κ))
    liftM (evalExpr (enc κ) (subst2 key₀ seed (extendFin ones b)) (extendFin false a) e)) =
  liftM (exprToFamDistr enc e κ)
  :=
  by
    intro H
    rw [exprToFamDistr]
    rw [<-resamplingLemma2 key₀ H]
    simp [lifting]
