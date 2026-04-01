import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.Def

import SymbolicGarbledCircuitsInLean.Core.CardinalityLemmas

import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Probability.Distributions.Uniform

import Mathlib.Data.ENNReal.Inv



def applyKeyRenamingToKVars (f : KeyRenaming) (kVars : (ℕ -> BitVector κ)) : (ℕ -> BitVector κ) :=
  fun i => kVars (f i)

lemma applyKeyRenamingToKeyVarsCorrect
  (enc : encryptionFunctions κ) (keyVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  (expr : Expression s) (f : KeyRenaming) :
  evalExpr enc keyVars bVars (applyKeyRenamingP f expr) = evalExpr enc (applyKeyRenamingToKVars f keyVars) bVars expr := by
  induction expr <;> simp [applyKeyRenamingP, evalExpr, applyKeyRenamingToKVars]
  case Pair e1 e2 ih1 ih2 =>
    simp [ih1, ih2]
  case Perm eb e1 e2 ihb ih1 ih2 =>
    let (Expression.BitE b) := eb
    simp [evalExpr, ih1, ih2]
  case Enc k' e ihk ihe =>
    let (Expression.VarK k) := k'
    simp [evalExpr, ihk, ihe, applyKeyRenamingP, applyKeyRenamingToKVars]
  case Hidden k ihk =>
    let (Expression.VarK k) := k
    simp [evalExpr, ihk, applyKeyRenamingP, applyKeyRenamingToKVars]

def applyBitRenamingToBVars (f : BitRenaming) (bVars : ℕ -> Bool) : (ℕ -> Bool) :=
  fun i => match f i with
    | VarOrNegVar.Var k => bVars k
    | VarOrNegVar.NegVar k => not (bVars k)


lemma applyBitRenamingToBVarsCorrectB
  (bVars : ℕ -> Bool) (expr : BitExpr) (f : BitRenaming) :
  evalBitExpr (applyBitRenamingToBVars f bVars) expr = evalBitExpr bVars (applyBitRenamingB f expr) := by
  induction expr <;> simp [applyBitRenaming, evalBitExpr, applyBitRenamingToBVars]
  case Bit x =>
    simp [applyBitRenamingToBVars, applyBitRenamingB, evalBitExpr]
  case VarB x =>
    simp [applyBitRenamingToBVars, applyBitRenamingB, evalBitExpr]
    cases (f x) <;> simp [evalBitExpr, varOrNegVarToExpr]
  case Not x ihx =>
    simp [evalBitExpr, ihx, applyBitRenamingB]

lemma applyBitRenamingToBVarsCorrect
  (enc : encryptionFunctions κ) (keyVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  (expr : Expression s) (f : BitRenaming) :
  evalExpr enc keyVars (applyBitRenamingToBVars f bVars) expr = evalExpr enc keyVars bVars (applyBitRenaming f expr) := by
  induction expr <;> simp [applyBitRenaming, evalExpr, applyBitRenamingToBVars, applyBitRenamingB, applyBitRenamingB]
  case Pair e1 e2 ih1 ih2 =>
    simp [ih1, ih2]
  case Perm eb e1 e2 ihb ih1 ih2 =>
    let (Expression.BitE b) := eb
    simp [evalExpr, applyBitRenamingToBVars, ih1, ih2, ihb, evalBitExpr]
    rw [← applyBitRenamingToBVarsCorrectB]
  case Enc k e ihk ihe =>
    let (Expression.VarK k) := k
    simp [evalExpr, applyBitRenamingToBVars, ihk, ihe, applyBitRenaming]
  case Hidden k ihk =>
    let (Expression.VarK k) := k
    simp [evalExpr, applyBitRenamingToBVars, ihk, applyBitRenaming]
  case BitE b =>
     rw [← applyBitRenamingToBVarsCorrectB]

lemma uniformOfFintypeMapBijection
  [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (f : α → β) (hf : Function.Bijective f) :
    f <$> PMF.uniformOfFintype α = PMF.uniformOfFintype β := by
    ext x
    let x' := Function.invFun f x
    simp [Functor.map]
    rw [tsum_eq_single x']
    · rw[if_pos]
      · have hcard : Fintype.card α = Fintype.card β := by
          apply Fintype.card_congr
          apply Equiv.ofBijective f hf
        simp [hcard]
      · simp[x']
        have hfr := Function.rightInverse_invFun hf.2
        rw [Function.RightInverse, Function.LeftInverse] at hfr
        rw [hfr]
    · intro y h
      rw [if_neg]
      intro hcontra
      apply h
      simp [x']
      rw [hcontra]
      have hfr := Function.leftInverse_invFun hf.1
      rw [Function.LeftInverse] at hfr
      rw [hfr]

def restrictFromN (f : ℕ → α) (n : ℕ) : (Fin n → α) :=
  fun i => f (Fin.val i)

noncomputable
def extendRenameRestrictK (f : KeyRenaming) (κ n l : ℕ) : PMF (Fin n  -> BitVector κ) := do
  let a <- PMF.uniformOfFintype (Fin l -> BitVector κ)
  let a' := extendFin ones a
  let b := applyKeyRenamingToKVars f a'
  pure $ (restrictFromN b n)

noncomputable
def extendRenameRestrictB (f : BitRenaming) (n l : ℕ) : PMF (Fin n  -> Bool) := do
  let a <- PMF.uniformOfFintype (Fin l -> Bool)
  let a' := extendFin false a
  let b := applyBitRenamingToBVars f a'
  pure $ (restrictFromN b n)


instance : DecidableEq (BitVector κ) := by infer_instance
instance : DecidableEq (Fin l → BitVector κ) := by infer_instance

lemma countExtendRenameRestrictK (n l : ℕ) (f : KeyRenaming) (v : Fin n  -> BitVector κ) (hf : Function.Bijective f) (_ : n ≤ l) (h₂ : forall i, i < n -> f i < l) :
   Finset.card { x : Fin l -> BitVector κ | v = restrictFromN (applyKeyRenamingToKVars f (extendFin ones x)) n} =
    (2 ^ κ) ^ (l - n) := by
      simp [← Finset.card_subtype]
      let f' : Fin n → Fin l := fun i => ⟨f i.1, h₂ i.1 i.2⟩
      let used := Finset.image f' Finset.univ
      let v' : (used → BitVector κ) := fun i' =>
        let ⟨i, hi⟩ := i'
        v ⟨f.invFun i, by
          simp [used] at hi
          have ⟨i', hi'⟩ := hi
          simp [← hi', f']
          rw [Function.leftInverse_invFun hf.1]
          simp⟩
      let v'' : Fin l → BitVector κ := fun i =>
        if Hi : i ∈ used then
          v' ⟨i, Hi⟩
        else
          ones
      rw [@Fintype.card_congr _ {x : Fin l → BitVector κ // ∀ (i : used), x i = v'' i}]
      rw [cardinalityCount]
      · simp [used]
        congr
        rw [Finset.card_image_iff.mpr]
        simp [f']
        simp [Set.InjOn]
        intros i j h
        ext
        apply hf.1
        simp [f'] at h
        assumption
      · apply Equiv.subtypeEquivProp
        ext x
        constructor
        · intro h i
          simp [v'', v', h, restrictFromN, applyKeyRenamingToKVars, extendFin]
          split
          next =>
            congr
            have ⟨vi, hi⟩ := i
            simp
            have tmp := Function.rightInverse_invFun hf.2
            simp [Function.LeftInverse, Function.RightInverse] at tmp
            simp [tmp]
          next hc =>
            exfalso
            apply hc
            have tmp := Function.rightInverse_invFun hf.2
            simp [Function.LeftInverse, Function.RightInverse] at tmp
            simp [tmp]
        · simp [v'', v']
          intro h
          ext1 ⟨i, vi⟩
          simp [restrictFromN, applyKeyRenamingToKVars, extendFin]
          split
          next =>
            rw [h]
            congr
            have tmp := Function.leftInverse_invFun hf.1
            simp [Function.LeftInverse] at tmp
            simp [tmp]
            simp [used, f']
            exists ⟨i, vi⟩
          next used =>
            exfalso
            apply used
            apply h₂
            assumption

lemma countExtendRenameRestrictB (n l : ℕ) (f : BitRenaming) (v : Fin n  -> Bool) (hf : Function.Bijective (castVarOrNegVar ∘ f)) (_ : n ≤ l) (h₂ : forall i, i < n -> (castVarOrNegVar ∘ f) i < l) :
   Finset.card { x : Fin l → Bool | v = restrictFromN (applyBitRenamingToBVars f (extendFin false x)) n} =
    2 ^ (l - n) := by
      simp [← Finset.card_subtype]
      let f' : Fin n → Fin l := fun i => ⟨(castVarOrNegVar ∘ f) i.1, h₂ i.1 i.2⟩
      let used := Finset.image f' Finset.univ
      let v' : (used → Bool) := fun i' =>
        let ⟨i, hi⟩ := i'
        let pi := Function.invFun (castVarOrNegVar ∘ f) i
        let vi := v ⟨pi, by
          simp [pi]
          simp [used] at hi
          have ⟨⟨ i', hi₁'⟩, hi₂'⟩ := hi
          simp [f'] at hi₂'
          simp [←hi₂']
          have tmp := Function.leftInverse_invFun hf.1
          simp [Function.LeftInverse] at tmp
          simp [tmp]
          assumption⟩
        match f pi with
        | VarOrNegVar.Var k => vi
        | VarOrNegVar.NegVar k => not vi
      let v'' : Fin l → Bool := fun i =>
        if Hi : i ∈ used then
          v' ⟨i, Hi⟩
        else
          false
      rw [@Fintype.card_congr _ {x : Fin l → Bool // ∀ (i : used), x i = v'' i}]
      rw [cardinalityCount]
      · simp [used]
        congr
        rw [Finset.card_image_iff.mpr]
        simp
        simp [f', Set.InjOn]
        intros i j h
        ext
        apply hf.1
        apply h
      · apply Equiv.subtypeEquivProp
        · ext x
          constructor
          · intro hv i
            simp [v'', v', hv, restrictFromN, applyBitRenamingToBVars, extendFin]
            have tmp := Function.leftInverse_invFun hf.1
            simp [Function.LeftInverse, Function.RightInverse] at tmp
            have ⟨i', hi₂⟩ := i
            simp [used] at hi₂
            simp
            have ⟨i'', hil⟩ := i'
            simp
            have ⟨j, hj⟩ := hi₂
            simp [f'] at hj
            simp [← hj]
            simp [tmp]
            have ⟨j', hj'⟩ := j
            simp
            split
            next k heq =>
              simp[heq, castVarOrNegVar]
              rw [dite_cond_eq_true]
              simp
              change
                (castVarOrNegVar (VarOrNegVar.Var k)) < l
              simp [← heq]
              have tmp := h₂ j'
              simp at tmp
              apply tmp
              assumption
            next k heq =>
              simp [heq, castVarOrNegVar]
              rw [dite_cond_eq_true]
              simp
              change
                (castVarOrNegVar (VarOrNegVar.NegVar k)) < l
              simp [← heq]
              have tmp := h₂ j'
              simp at tmp
              apply tmp
              assumption
          · intro h
            simp [used] at h
            ext ⟨i, hi⟩
            simp [restrictFromN, applyBitRenamingToBVars, extendFin]

            simp [v'', f', v'] at h
            have h' := h ⟨i, hi⟩
            simp at h'
            have tmp := Function.leftInverse_invFun hf.1
            simp [Function.LeftInverse, Function.RightInverse] at tmp
            simp [tmp] at h'
            let fi := f i
            have hfi : fi = f i :=
              by simp [fi]
            match fi with
            | VarOrNegVar.Var k =>
              simp [<- hfi]
              simp [<- hfi, castVarOrNegVar] at h'
              rw [dite_cond_eq_true]
              simp [h']
              rw [dite_cond_eq_true]
              simp [used]
              exists ⟨i, hi⟩
              simp [f', hfi, castVarOrNegVar]
              simp [← hfi]
              simp
              change
                (castVarOrNegVar (VarOrNegVar.Var k)) < l
              rw [hfi]
              apply h₂
              assumption
            | VarOrNegVar.NegVar k =>
              simp [<- hfi]
              simp [<- hfi, castVarOrNegVar] at h'
              rw [dite_cond_eq_true]
              simp [h']
              rw [dite_cond_eq_true]
              simp
              simp [used]
              exists ⟨i, hi⟩
              simp [f', hfi, castVarOrNegVar]
              simp [← hfi]
              simp
              change
                (castVarOrNegVar (VarOrNegVar.NegVar k)) < l
              rw [hfi]
              apply h₂
              assumption

lemma extendRenameRestrictKUniform (f : KeyRenaming) (κ n l : ℕ)
  (h₁ : Function.Bijective f) (h₂ : forall i, i < n -> f i < l) (h₃ : l ≥ n) :
  extendRenameRestrictK f κ n l = PMF.uniformOfFintype (Fin n -> BitVector κ) := by
    ext v
    simp [extendRenameRestrictK, PMF.uniformOfFintype_apply, Functor.map]
    conv =>
      lhs
      arg 1
      intro a
      rw [← mul_one ((2 ^ κ) ^ l)⁻¹]
      rw [← mul_ite_zero]
      arg 2
      change
        (fun a => if v = restrictFromN (applyKeyRenamingToKVars f (extendFin ones a)) n then 1 else 0) a
      rfl
    generalize hc : ((2 ^ κ) ^ n : ENNReal)⁻¹ = c
    generalize hd : ((2 ^ κ) ^ l : ENNReal)⁻¹ = d
    have  : (∑' (a : Fin l → BitVector κ),
      d * if v = restrictFromN (applyKeyRenamingToKVars f (extendFin ones a)) n then 1 else 0) =
      d * (∑' (a : Fin l → BitVector κ),
      if v = restrictFromN (applyKeyRenamingToKVars f (extendFin ones a)) n then 1 else 0) := by
      exact ENNReal.tsum_mul_left
    rw [this]
    simp [tsum_fintype]
    rw [countExtendRenameRestrictK]
    simp [←hd, ← hc]
    generalize he : (2^κ : ENNReal) = e
    simp [← ENNReal.rpow_natCast, ENNReal.rpow_sub]
    rw [Nat.cast_sub]
    rw [ENNReal.rpow_sub]
    rw [← mul_div_assoc]
    rw [@ENNReal.inv_mul_cancel]
    simp
    all_goals try (simp[←he])
    all_goals assumption


lemma extendRenameRestrictBUniform (f : BitRenaming) (n l : ℕ)
  (h₁ : Function.Bijective (castVarOrNegVar ∘ f))
  (h₂ : forall i, i < n -> (castVarOrNegVar ∘ f) i  < l) (h₃ : l ≥ n) :
  extendRenameRestrictB f n l = PMF.uniformOfFintype (Fin n -> Bool) := by
    ext v
    simp [extendRenameRestrictB, PMF.uniformOfFintype_apply, Functor.map]
    conv =>
      lhs
      arg 1
      intro a
      rw [← mul_one (2^l : ENNReal)⁻¹]
      rw [← mul_ite_zero]
      arg 2
      change
        (fun a => if v = restrictFromN (applyBitRenamingToBVars f (extendFin false a)) n then 1 else 0) a
      rfl
    have : (∑' (a : Fin l → Bool),
      (2^l : ENNReal)⁻¹ * if v = restrictFromN (applyBitRenamingToBVars f (extendFin false a)) n then 1 else 0) =
      (2^l : ENNReal)⁻¹ * (∑' (a : Fin l → Bool),
      if v = restrictFromN (applyBitRenamingToBVars f (extendFin false a)) n then 1 else 0) := by
      exact ENNReal.tsum_mul_left
    rw [this]
    simp [tsum_fintype]
    rw [countExtendRenameRestrictB]
    simp [← ENNReal.rpow_natCast, ENNReal.rpow_sub]
    rw [Nat.cast_sub]
    rw [ENNReal.rpow_sub]
    rw [← mul_div_assoc]
    rw [@ENNReal.inv_mul_cancel]
    all_goals try simp
    all_goals try assumption


lemma extendRestrictAgree (n : ℕ) (v : A) (e : ℕ → A) : agreeOnPrefix n (extendFin v (restrictFromN e n)) e := by
  simp [agreeOnPrefix, extendFin, restrictFromN]
  intro i h1 h2
  omega

lemma renamePreservesComputationalSemantics
  (enc : encryptionFunctions κ) (expr : Expression s) (r : varRenaming) (hr : validVarRenaming r)
  :
  exprToDistr enc expr = exprToDistr enc (applyVarRenaming r expr) := by
    let b := r.1
    let b' := castVarOrNegVar ∘ b
    let f := r.2
    let hfb := hr.2
    let n := 1 + getMaxVar expr
    let m := 1 + Finset.max' ((Finset.range (n+1)).image (f)) (by
      apply Finset.image_nonempty.mpr
      apply Finset.nonempty_range_succ)
    let mb := 1 + Finset.max' ((Finset.range (n+1)).image (b')) (by
      apply Finset.image_nonempty.mpr
      apply Finset.nonempty_range_succ)
    let l := 1 + max (max n (max (mb + 1) (m + 1))) (getMaxVar (applyVarRenaming r expr) + 1)
    have hl1 : ∀ i < getMaxVar expr + 1, f i < l := by
      intro i hi
      trans m
      · simp [m]
        rw [add_comm]
        apply Nat.lt_add_one_of_le
        apply Finset.le_max'
        apply Finset.mem_image.mpr
        exists i
        constructor <;> try rfl
        simp [Finset.range, n]
        omega
      · simp [l]
        omega
    have hl2 : ∀ i < getMaxVar expr + 1, b' i < l := by
      intro i hi
      trans mb
      · simp [mb]
        rw [add_comm]
        apply Nat.lt_add_one_of_le
        apply Finset.le_max'
        simp [Finset.image]
        right
        exists i
        constructor <;> omega
      · simp [l]
        omega

    conv =>
      lhs
      rw [exprToDistr, evalExprVarsL]
      rw [← extendRenameRestrictBUniform b _ l hr.1 hl2]
      simp [extendRenameRestrictB]
      rfl
      tactic => omega

    conv =>
      lhs
      arg 2
      intro bvars
      rw [← extendRenameRestrictKUniform f κ _ l hfb hl1]
      simp [extendRenameRestrictK]
      arg 2
      intro kvars
      rw [evalNoMatter enc (getMaxVar expr + 1) _ (applyKeyRenamingToKVars f (extendFin ones kvars)) _ ((applyBitRenamingToBVars b (extendFin false bvars)))]
      rw [applyBitRenamingToBVarsCorrect]
      rw [← applyKeyRenamingToKeyVarsCorrect]
      rfl
      tactic => apply extendRestrictAgree
      tactic => apply extendRestrictAgree
      tactic => omega
      tactic => omega
    simp [exprToDistr]
    rw [← evalExprVarsNoMatter enc l] <;> try rfl
    simp [l]
    omega

lemma applyRenamePreservesCompSem2
  (enc : encryptionScheme) (expr : Expression s) (r : varRenaming) (hr : validVarRenaming r)
  :
  exprToFamDistr enc expr = exprToFamDistr enc (applyVarRenaming r expr) :=
  by
    ext κ c
    simp [exprToFamDistr]
    rw [renamePreservesComputationalSemantics]
    assumption
