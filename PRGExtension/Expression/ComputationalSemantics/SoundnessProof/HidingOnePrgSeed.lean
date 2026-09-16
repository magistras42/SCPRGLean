import PRGExtension.Expression.Defs
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.EncryptionIndCpa
import PRGExtension.Expression.ComputationalSemantics.PrgSecurity

namespace PRG

/--
  Key-level commutation.  Replacing `G0 t`/`G1 t` by the dummies `idx0`/`idx1` and then
  binding those to `(prg0 sd, prg1 sd)` gives the same value as evaluating the original
  key expression with `t` bound to `sd`.

  The hypothesis `k ≠ VarK t` is exactly LM18's requirement that the seed is never used
  directly: inside a key expression every `VarK` is either the root or the immediate
  argument of a `G`, and `replacePRG` rewrites the latter, so the root is the only place
  a bare `VarK t` could survive.
-/
lemma keyVal_replacePRG {κ : ℕ} (prg : prgFunctions κ) (kVars : ℕ -> BitVector κ)
    (t idx0 idx1 : ℕ) (sd : BitVector κ) (H_diff : idx0 ≠ idx1) :
    ∀ k : Expression Shape.KeyS,
      k ≠ Expression.VarK t →
      Expression.VarK idx0 ∉ keySubterms k →
      Expression.VarK idx1 ∉ keySubterms k →
      keyVal prg (subst3 idx0 idx1 (prg.prg0 sd) (prg.prg1 sd) kVars)
        (replacePRG (Expression.VarK t) idx0 idx1 k)
      = keyVal prg (subst2 t sd kVars) k
  | Expression.VarK n, hne, h0, h1 => by
      simp only [keySubterms, Finset.mem_singleton] at h0 h1
      have hn0 : n ≠ idx0 := fun h => h0 (by rw [h])
      have hn1 : n ≠ idx1 := fun h => h1 (by rw [h])
      have hnt : n ≠ t := fun h => hne (by rw [h])
      simp [replacePRG, keyVal, subst3, subst2, hn0, hn1, hnt]
  | Expression.G0 k, _, h0, h1 => by
      by_cases hk : k = Expression.VarK t
      · subst hk
        simp [replacePRG, keyVal, subst3, subst2]
      · have h0' : Expression.VarK idx0 ∉ keySubterms k := fun h => h0 (by simp [keySubterms, h])
        have h1' : Expression.VarK idx1 ∉ keySubterms k := fun h => h1 (by simp [keySubterms, h])
        simp only [replacePRG, beq_iff_eq, hk, if_false, keyVal]
        rw [keyVal_replacePRG prg kVars t idx0 idx1 sd H_diff k hk h0' h1']
  | Expression.G1 k, _, h0, h1 => by
      by_cases hk : k = Expression.VarK t
      · subst hk
        simp [replacePRG, keyVal, subst3, subst2, (Ne.symm H_diff)]
      · have h0' : Expression.VarK idx0 ∉ keySubterms k := fun h => h0 (by simp [keySubterms, h])
        have h1' : Expression.VarK idx1 ∉ keySubterms k := fun h => h1 (by simp [keySubterms, h])
        simp only [replacePRG, beq_iff_eq, hk, if_false, keyVal]
        rw [keyVal_replacePRG prg kVars t idx0 idx1 sd H_diff k hk h0' h1']

/--
  Expression-level commutation: evaluating `replacePRG t idx0 idx1 e` with the dummies
  bound to `(prg0 sd, prg1 sd)` is the same as evaluating `e` with `t` bound to `sd`.

  `H_seed : VarK t ∉ exprKeys e` is LM18's "the seed is never used directly" condition:
  `t` may occur only underneath a `G`, which is exactly what `replacePRG` rewrites.
-/
lemma evalExpr_replacePRG {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ)
    (kVars : ℕ -> BitVector κ) (bVars : ℕ -> Bool)
    (t idx0 idx1 : ℕ) (sd : BitVector κ) (H_diff : idx0 ≠ idx1) :
    ∀ {s : Shape} (e : Expression s),
      Expression.VarK t ∉ exprKeys e →
      Expression.VarK idx0 ∉ keySubterms e →
      Expression.VarK idx1 ∉ keySubterms e →
      evalExpr enc prg (subst3 idx0 idx1 (prg.prg0 sd) (prg.prg1 sd) kVars) bVars
        (replacePRG (Expression.VarK t) idx0 idx1 e)
      = evalExpr enc prg (subst2 t sd kVars) bVars e := by
  intro s e
  induction e with
  | BitE b => intro _ _ _; simp [replacePRG, evalExpr]
  | Eps => intro _ _ _; simp [replacePRG, evalExpr]
  | VarK n =>
      intro hs h0 h1
      have hk := keyVal_replacePRG prg kVars t idx0 idx1 sd H_diff (Expression.VarK n)
        (fun h => hs (by simp [exprKeys, h])) h0 h1
      rw [evalExpr_key, evalExpr_key, hk]
  | G0 k =>
      intro hs h0 h1
      have hk := keyVal_replacePRG prg kVars t idx0 idx1 sd H_diff (Expression.G0 k)
        (fun h => by simp at h) h0 h1
      rw [evalExpr_key, evalExpr_key, hk]
  | G1 k =>
      intro hs h0 h1
      have hk := keyVal_replacePRG prg kVars t idx0 idx1 sd H_diff (Expression.G1 k)
        (fun h => by simp at h) h0 h1
      rw [evalExpr_key, evalExpr_key, hk]
  | Pair e1 e2 ih1 ih2 =>
      intro hs h0 h1
      simp only [exprKeys, keySubterms, Finset.mem_union, not_or] at hs h0 h1
      simp only [replacePRG, evalExpr]
      rw [ih1 hs.1 h0.1 h1.1, ih2 hs.2 h0.2 h1.2]
  | Perm b e1 e2 _ihb ih1 ih2 =>
      intro hs h0 h1
      simp only [exprKeys, keySubterms, Finset.mem_union, not_or] at hs h0 h1
      cases b with | BitE x =>
      simp only [replacePRG, evalExpr]
      rw [ih1 hs.1 h0.1 h1.1, ih2 hs.2 h0.2 h1.2]
  | Enc k e _ihk ihe =>
      intro hs h0 h1
      simp only [exprKeys, keySubterms, Finset.mem_union, not_or] at hs h0 h1
      have hkey := keyVal_replacePRG prg kVars t idx0 idx1 sd H_diff k
        (fun h => hs.1 (by simp [exprKeys, h])) h0.1 h1.1
      simp only [replacePRG, evalExpr]
      rw [evalExpr_key, evalExpr_key, hkey, ihe hs.2 h0.2 h1.2]
  | Hidden k =>
      intro hs h0 h1
      simp only [exprKeys, keySubterms] at hs h0 h1
      have hkey := keyVal_replacePRG prg kVars t idx0 idx1 sd H_diff k
        (fun h => hs (by simp [exprKeys, h])) h0 h1
      simp only [replacePRG, evalExpr]
      rw [evalExpr_key, evalExpr_key, hkey]

/-- Number of variables the reduction samples: enough to cover the original expression,
    the rewritten one, and the two dummy indices. -/
def prgReductionVars {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS)
    (idx0 idx1 : ℕ) : ℕ :=
  max (getMaxVar expr) (max (getMaxVar (replacePRG targetSeed idx0 idx1 expr)) (max idx0 idx1)) + 1

lemma prgReductionVars_gt_expr {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS)
    (idx0 idx1 : ℕ) : prgReductionVars expr targetSeed idx0 idx1 > getMaxVar expr := by
  simp only [prgReductionVars]; omega

lemma prgReductionVars_gt_replaced {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS)
    (idx0 idx1 : ℕ) :
    prgReductionVars expr targetSeed idx0 idx1 > getMaxVar (replacePRG targetSeed idx0 idx1 expr) := by
  simp only [prgReductionVars]; omega

/--
  The Reduction.

  We sample the bit- and key-variables ourselves, ask the PRG oracle for its pair
  `(val0, val1)`, and then evaluate the *rewritten* expression
  `replacePRG targetSeed idx0 idx1 expr` in an environment where the two dummy variables
  `idx0`, `idx1` are bound to `val0`, `val1`.  The value of `targetSeed` itself is never
  needed -- that is exactly the side condition `VarK t ∉ exprKeys expr`.
-/
noncomputable
def reductionToPrgOracle (enc : encryptionScheme) (prg : prgScheme)
  {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ)
  (κ : ℕ) : OracleComp (withRandom (oracleSpecPrg κ)) (BitVector (shapeLength κ (enc κ) s)) := do
  let l := prgReductionVars expr targetSeed idx0 idx1
  let bVars ← sample (PMF.uniformOfFintype (Fin l -> Bool))
  let kVars ← sample (PMF.uniformOfFintype (Fin l -> BitVector κ))
  let r ← (withRandom (oracleSpecPrg κ)).query (Sum.inr ()) ()
  sample (evalExpr (enc κ) (prg κ)
    (subst3 idx0 idx1 r.1 r.2 (extendFin ones kVars)) (extendFin false bVars)
    (replacePRG targetSeed idx0 idx1 expr))

-- ===================================================================================
-- Simulating the reduction against each oracle.
-- ===================================================================================

lemma prgSimulateReal (enc : encryptionScheme) (prg : prgScheme) {s : Shape} (expr : Expression s)
    (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ) {κ : ℕ} (seed : BitVector κ) :
  OracleComp.simulateQ (addRandom ((seededPrgRealOracle prg).queryImpl κ seed))
      (reductionToPrgOracle enc prg expr targetSeed idx0 idx1 κ)
  = (do
      let bV ← liftM (PMF.uniformOfFintype (Fin (prgReductionVars expr targetSeed idx0 idx1) → Bool))
      let kV ← liftM (PMF.uniformOfFintype (Fin (prgReductionVars expr targetSeed idx0 idx1) → BitVector κ))
      liftM (evalExpr (enc κ) (prg κ)
        (subst3 idx0 idx1 ((prg κ).prg0 seed) ((prg κ).prg1 seed) (extendFin ones kV)) (extendFin false bV)
        (replacePRG targetSeed idx0 idx1 expr))) := by
  simp only [reductionToPrgOracle, addRandom, sample, seededPrgRealOracle, prgRealOracleImpl,
    OracleComp.simulateQ_bind, OracleComp.simulateQ_query, Function.comp_def]
  rw [prodImplL]
  dsimp only [prodImpl]
  simp only [randImpl]
  simp

lemma prgSimulateIdeal (enc : encryptionScheme) (prg : prgScheme) {s : Shape} (expr : Expression s)
    (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ) {κ : ℕ} (r : BitVector κ × BitVector κ) :
  OracleComp.simulateQ (addRandom (seededPrgIdealOracle.queryImpl κ r))
      (reductionToPrgOracle enc prg expr targetSeed idx0 idx1 κ)
  = (do
      let bV ← liftM (PMF.uniformOfFintype (Fin (prgReductionVars expr targetSeed idx0 idx1) → Bool))
      let kV ← liftM (PMF.uniformOfFintype (Fin (prgReductionVars expr targetSeed idx0 idx1) → BitVector κ))
      liftM (evalExpr (enc κ) (prg κ)
        (subst3 idx0 idx1 r.1 r.2 (extendFin ones kV)) (extendFin false bV)
        (replacePRG targetSeed idx0 idx1 expr))) := by
  simp only [reductionToPrgOracle, addRandom, sample, seededPrgIdealOracle, prgIdealOracleImpl,
    OracleComp.simulateQ_bind, OracleComp.simulateQ_query, Function.comp_def]
  rw [prodImplL]
  dsimp only [prodImpl]
  simp only [randImpl]
  simp

/--
  Real World Equivalence: with the REAL PRG oracle the reduction perfectly simulates `⟦expr⟧`.
  The seed the oracle holds plays the role of the key variable `t`; this is why `t` must
  not be used directly in `expr` (`H_seed`), only underneath a `G`.
-/
lemma reductionToPrgOracleRealEq (enc : encryptionScheme) (prg : prgScheme)
  {s : Shape} (expr : Expression s) (t idx0 idx1 : ℕ)
  (H_diff : idx0 ≠ idx1)
  (H_seed : Expression.VarK t ∉ exprKeys expr)
  (H0 : Expression.VarK idx0 ∉ keySubterms expr)
  (H1 : Expression.VarK idx1 ∉ keySubterms expr) :
  compToDistrGen (seededPrgRealOracle prg)
      (fun κ => reductionToPrgOracle enc prg expr (Expression.VarK t) idx0 idx1 κ) =
  famDistrLift (exprToFamDistr enc prg expr) := by
  delta famDistrLift
  delta compToDistrGen
  ext1 κ
  conv =>
    lhs
    arg 2
    intro seed
    rw [prgSimulateReal]
    arg 2
    intro bV
    arg 2
    intro kV
    rw [evalExpr_replacePRG (enc κ) (prg κ) (extendFin ones kV) (extendFin false bV)
          t idx0 idx1 seed H_diff expr H_seed H0 H1]
  exact resamplingLemma (key₀ := t) (prgReductionVars_gt_expr expr (Expression.VarK t) idx0 idx1)

/--
  Ideal World Equivalence: with the IDEAL oracle the two answers are fresh uniform
  strings, so the reduction perfectly simulates `⟦replacePRG t idx0 idx1 expr⟧`.
-/
lemma reductionToPrgOracleIdealEq (enc : encryptionScheme) (prg : prgScheme)
  {s : Shape} (expr : Expression s) (t idx0 idx1 : ℕ) :
  compToDistrGen seededPrgIdealOracle
      (fun κ => reductionToPrgOracle enc prg expr (Expression.VarK t) idx0 idx1 κ) =
  famDistrLift (exprToFamDistr enc prg (replacePRG (Expression.VarK t) idx0 idx1 expr)) := by
  delta famDistrLift
  delta compToDistrGen
  ext1 κ
  conv =>
    lhs
    arg 2
    intro seed
    rw [prgSimulateIdeal]
  simp only [seededPrgIdealOracle, bind_assoc, pure_bind]
  simp only [Bind.bind, Pure.pure, OptionT.bind, OptionT.mk, OptionT.pure, OptionT.run,
    PMF.pure_bind, Option.getM]
  exact resamplingLemmaPrg (κ := κ) (l := prgReductionVars expr (Expression.VarK t) idx0 idx1)
    (enc := enc) (prg := prg) (e := replacePRG (Expression.VarK t) idx0 idx1 expr)
    (i := idx0) (j := idx1)
    (prgReductionVars_gt_replaced expr (Expression.VarK t) idx0 idx1)

/--
  The PRG idealisation hop (LM18 Theorem 1, single-seed base case).

  If the PRG is secure then replacing `G0 (VarK t)` / `G1 (VarK t)` by two fresh
  independent key variables is computationally undetectable, provided `t` itself is never
  used directly (`H_seed`) and the two dummies are fresh and distinct.
-/
theorem symbolicToSemanticIndistinguishabilityPrgIdealization
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {I Spec Output} => IsPolyTime))
  (Hreduction : ∀ (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape)
    (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
  (enc : encryptionScheme)
  (prg : prgScheme)
  (HPrgSecure : prgSchemeSecure (fun {I Spec Output} => IsPolyTime) prg)
  {shape : Shape} (expr : Expression shape) (t idx0 idx1 : ℕ)
  (H_seed : Expression.VarK t ∉ exprKeys expr)
  (H_diff : idx0 ≠ idx1)
  (H_fresh0 : Expression.VarK idx0 ∉ keySubterms expr)
  (H_fresh1 : Expression.VarK idx1 ∉ keySubterms expr) :
  CompIndistinguishabilityDistr (fun {I Spec Output} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg expr))
    (famDistrLift (exprToFamDistr enc prg (replacePRG (Expression.VarK t) idx0 idx1 expr))) := by
  rw [← reductionToPrgOracleRealEq enc prg expr t idx0 idx1 H_diff H_seed H_fresh0 H_fresh1]
  rw [← reductionToPrgOracleIdealEq enc prg expr t idx0 idx1]
  apply IndistinguishabilityByReduction <;> try assumption
  apply Hreduction

-- ===================================================================================
-- LM18 Theorem 1, in the form the development needs: a finite sequence of idealisation
-- steps, one internal node of the PRG tree at a time.
-- ===================================================================================

/--
  A chain of PRG idealisation hops.  Each step carries its own side conditions, checked
  against the *current* expression rather than the original -- which is what makes the
  chain composable, and what makes the ordering of the PRG tree the caller's business.

  To idealise a whole tree, order its internal nodes so that a node is only rewritten
  once all of its ancestors have been: after an ancestor's hop the node's seed has become
  a fresh atomic variable, so the `H_seed` condition of the next hop is available.
-/
inductive PrgHopChain {s : Shape} : Expression s → Expression s → Prop
  | refl (e : Expression s) : PrgHopChain e e
  | step {e₁ e₃ : Expression s} (t idx0 idx1 : ℕ)
      (H_seed : Expression.VarK t ∉ exprKeys e₁)
      (H_diff : idx0 ≠ idx1)
      (H_fresh0 : Expression.VarK idx0 ∉ keySubterms e₁)
      (H_fresh1 : Expression.VarK idx1 ∉ keySubterms e₁)
      (rest : PrgHopChain (replacePRG (Expression.VarK t) idx0 idx1 e₁) e₃) :
      PrgHopChain e₁ e₃

/--
  Soundness of a chain of hops: every `PrgHopChain` relates computationally
  indistinguishable distributions.  This is LM18 Theorem 1 (⇒ direction) as used by the
  soundness proof: a symbolically independent family of PRG-derived keys is
  indistinguishable from a family of distinct atomic keys.
-/
theorem prgHopChainSound
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {I Spec Output} => IsPolyTime))
  (Hreduction : ∀ (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape)
    (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
  (enc : encryptionScheme) (prg : prgScheme)
  (HPrgSecure : prgSchemeSecure (fun {I Spec Output} => IsPolyTime) prg)
  {shape : Shape} {e₁ e₂ : Expression shape} (H : PrgHopChain e₁ e₂) :
  CompIndistinguishabilityDistr (fun {I Spec Output} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg e₁))
    (famDistrLift (exprToFamDistr enc prg e₂)) := by
  induction H with
  | refl e => apply indRfl
  | step t idx0 idx1 H_seed H_diff H0 H1 _rest ih =>
      apply indTrans
      · exact symbolicToSemanticIndistinguishabilityPrgIdealization IsPolyTime HPolyTime
          Hreduction enc prg HPrgSecure _ t idx0 idx1 H_seed H_diff H0 H1
      · exact ih

end PRG
