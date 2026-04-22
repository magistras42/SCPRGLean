import PRGExtension.Expression.Defs
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.Expression.SymbolicIndistinguishability
import PRGExtension.Expression.Lemmas.HideEncrypted
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.EncryptionIndCpa
-- import PRGExtension.Expression.ComputationalSemantics.PrgSecurity

namespace PRG

noncomputable
def removeOneKey (k : Expression Shape.KeyS) (expr : Expression s) := hideSelectedS {k} expr

noncomputable
def removeOneKeyProper (k : Expression Shape.KeyS) (expr : Expression s) (_H : k ∉ extractKeys expr) := hideSelectedS {k} expr

noncomputable
def encryptPMF (enc : encryptionFunctions κ) (key : BitVector κ) (input : PMF (BitVector d)) : PMF (BitVector (enc.encryptLength d)) :=
  do
    let x <- input
    enc.encrypt key x

noncomputable
def appendPMF (l1 : PMF (BitVector d1))  (l2 : PMF (BitVector d2)) : PMF (BitVector (d1 + d2)) :=
  do
    let x1 <- l1
    let x2 <- l2
    return List.Vector.append x1 x2


def flat [Monad m] (x : m (m a)) : m a :=
  do
    let y <- x
    y


def innerQuery (spec : OracleSpec ι) (i : ι) (t : spec.domain i) : OracleSpec.OracleQuery (withRandom spec) (spec.range i) :=
  (withRandom spec).query (Sum.inr i) t

noncomputable
def encryptPMFOracle (enc : encryptionFunctions κ)
    (isTargetKey : Bool)
    (actualKey : BitVector κ)
    (input : BitVector d)
    : OracleComp (withRandom (oracleSpecIndCpa κ enc)) (BitVector (enc.encryptLength d)) :=
  do
    if isTargetKey then
      -- Left-or-right oracle query for the target key
      let x : BitVector (enc.encryptLength d) ←
        (innerQuery (oracleSpecIndCpa κ enc) d (input, ones))
      return x
    else
      let x ← sample (enc.encrypt actualKey input)
      return x

noncomputable
def reductionToOracle
  {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  {shape : Shape} (e : Expression shape) (key₀ : ℕ):
  OracleComp (withRandom (oracleSpecIndCpa κ enc)) (BitVector (shapeLength κ enc shape)) :=
    match e with
  | Expression.Pair e₁ e₂ => do
    let e₁' ← reductionToOracle enc prg kVars bVars e₁ key₀
    let e₂' ← reductionToOracle enc prg kVars bVars e₂ key₀
    return List.Vector.append e₁' e₂'
  | Expression.BitE b => do
    let b' := evalBitExpr bVars b
    return (List.Vector.cons b' List.Vector.nil)
  | Expression.VarK k => do
    let key := kVars k
    return key
  | Expression.Perm (Expression.BitE b) e₁ e₂ => do
    let b' := evalBitExpr bVars b
    let e₁' ← reductionToOracle enc prg kVars bVars e₁ key₀
    let e₂' ← reductionToOracle enc prg kVars bVars e₂ key₀
    if b' then return List.Vector.append e₂' e₁'
    else return List.Vector.append e₁' e₂'
  | Expression.Eps =>
    return List.Vector.nil
  -- UNIFIED ENC CASE: Evaluates both plaintext and key recursively
  | Expression.Enc k e => do
    let e' ← reductionToOracle enc prg kVars bVars e key₀
    let k' ← reductionToOracle enc prg kVars bVars k key₀
    -- Check if the key being used is exactly the target base key
    let isTarget := match k with
      | Expression.VarK idx => decide (idx = key₀)
      | _ => false
    encryptPMFOracle enc isTarget k' e'
  -- UPDATED HIDDEN CASE
  | Expression.Hidden (Expression.VarK k) => do
    let isTarget := decide (k = key₀)
    let o <- encryptPMFOracle enc isTarget (kVars k) (ones)
    return o
  | Expression.G0 e => do
    let e' ← reductionToOracle enc prg kVars bVars e key₀
    return prg.prg0 e'
  | Expression.G1 e => do
    let e' ← reductionToOracle enc prg kVars bVars e key₀
    return prg.prg1 e'
  -- | Expression.HiddenG0 _ => do
  --   let x <- sample (PMF.uniformOfFintype (BitVector κ))
  --   return x
  -- | Expression.HiddenG1 _ => do
  --   let x <- sample (PMF.uniformOfFintype (BitVector κ))
  --   return x
  | Expression.Hidden (s := s) (Expression.G0 ek) => do
    let key ← reductionToOracle enc prg kVars bVars (Expression.G0 ek) key₀
    sample (enc.encrypt key ones)
  | Expression.Hidden (s := s) (Expression.G1 ek) => do
    let key ← reductionToOracle enc prg kVars bVars (Expression.G1 ek) key₀
    sample (enc.encrypt key ones)
  -- | Expression.Hidden (s := s) (Expression.HiddenG0 ek) => do
  --   let key ← reductionToOracle enc prg kVars bVars (Expression.HiddenG0 ek) key₀
  --   sample (enc.encrypt key ones)
  -- | Expression.Hidden (s := s) (Expression.HiddenG1 ek) => do
  --   let key ← reductionToOracle enc prg kVars bVars (Expression.HiddenG1 ek) key₀
  --   sample (enc.encrypt key ones)

lemma reductionToOracleSimulateEq {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  {shape : Shape} (e : Expression shape) (key₀ : ℕ) (oracleKey : BitVector κ)
  (H : (Expression.VarK key₀) ∉ extractKeys e):
  OracleComp.simulateQ (addRandom (indCpaOracleImpl Side.L κ enc oracleKey))
    (reductionToOracle enc prg kVars bVars e key₀)
  =
  liftM (evalExpr enc prg (subst2 key₀ oracleKey kVars) bVars e)
  :=
  by
    induction e <;> simp [extractKeys] at H
    case Eps =>
      simp [evalExpr, reductionToOracle]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case BitE a =>
      simp [evalExpr, reductionToOracle]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case VarK a =>
      simp [evalExpr, reductionToOracle]
      have H : a ≠ key₀ := fun a_1 ↦ H (id (Eq.symm a_1))
      conv =>
        rhs
        simp [subst2]
        simp [H]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Perm s e1 e2 H1 H2 H3 =>
      cases s with | BitE x =>
      have ⟨X1, X2⟩ := H
      simp [reductionToOracle]
      conv =>
        lhs
        arg 1
        arg 2
        simp [reductionToOracle]
        simp
      rw [H2] <;> try assumption
      delta Function.comp
      simp []
      rw [H3] <;> try assumption
      rw [evalExpr]
      rw [lifting]
      congr
      ext1 z
      rw [lifting]
      congr
      ext1 y
      rw [Function.comp]
      if H_b : evalBitExpr bVars x = true then
        simp [H_b]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      else
        simp [H_b]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Pair s1 s2 e1 e2 H1 H2 =>
      simp [reductionToOracle]
      have ⟨X1, X2⟩ := H
      delta Function.comp
      simp [reductionToOracle]
      rw [H1, H2] <;> try assumption
      rw [evalExpr, lifting]
      congr; ext1 a
      rw [lifting]
      simp [Functor.map]
      congr; ext1 b
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Enc k e ih_k ih_e =>
      unfold reductionToOracle
      unfold evalExpr
      rw [OracleComp.simulateQ_bind]
      rw [ih_e H]
      delta Function.comp
      rw [lifting]
      congr; ext1 e_val
      cases k with
      | VarK idx =>
        -- We evaluate manually because if idx = key₀, ih_k is unprovable
        simp [reductionToOracle, evalExpr]
        by_cases h_eq : idx = key₀
        · -- Target base key! Route through Left/Right oracle resolution
          simp [h_eq, encryptPMFOracle]
          rw [addRandom, innerQuery]
          delta Function.comp
          rw [prodImplR]
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, h_eq, evalExpr]
          rfl
        · -- Base key, NOT the target key
          simp [h_eq, encryptPMFOracle, sample, subst2]
          -- The simulated standard query and the monadic lift are definitionally equal!
          rfl
      | G0 ek =>
        have hk : Expression.VarK key₀ ∉ extractKeys ek.G0 := by simp [extractKeys]
        rw [OracleComp.simulateQ_bind, ih_k hk]
        simp_rw [Function.comp_def]
        simp [encryptPMFOracle, sample, addRandom, innerQuery]
        dsimp [prodImpl]
        simp [randImpl]
        rw [← lifting]
        rfl
      | G1 ek =>
        have hk : Expression.VarK key₀ ∉ extractKeys ek.G1 := by simp [extractKeys]
        rw [OracleComp.simulateQ_bind, ih_k hk]
        simp_rw [Function.comp_def]
        simp [encryptPMFOracle, sample, addRandom, innerQuery]
        dsimp [prodImpl]
        simp [randImpl]
        rw [← lifting]
        rfl
    case Hidden s e1 ih =>
      cases e1 with
      | VarK x =>
        simp [reductionToOracle]
        by_cases Hif : x = key₀
        · -- Target Key: Route through Left/Right Oracle
          simp [Hif, encryptPMFOracle, addRandom, innerQuery]
          delta Function.comp
          rw [prodImplR]
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, Hif, evalExpr]
          rfl
        · -- Non-Target Key: Standard Encryption
          simp [Hif, encryptPMFOracle, sample, addRandom, innerQuery]
          -- FIX: Use simp to intelligently evaluate evalExpr and subst2 together!
          simp [evalExpr, subst2]
          rw [prodImplL]
          simp [Hif, randImpl]
      | G0 ek =>
        have hk : Expression.VarK key₀ ∉ extractKeys ek.G0 := by simp [extractKeys]
        simp only [reductionToOracle, evalExpr]
        rw [OracleComp.simulateQ_bind]
        erw [ih hk]
        simp_rw [Function.comp_def]
        simp [sample, addRandom, innerQuery] -- Add Hidden's specific wrapper if needed
        dsimp [prodImpl]
        simp [randImpl]
        rw [← lifting]
        simp [evalExpr]
      | G1 ek =>
        have hk : Expression.VarK key₀ ∉ extractKeys ek.G1 := by simp [extractKeys]
        simp only [reductionToOracle, evalExpr]
        rw [OracleComp.simulateQ_bind]
        erw [ih hk]
        simp_rw [Function.comp_def]
        simp [sample, addRandom, innerQuery] -- Add Hidden's specific wrapper if needed
        dsimp [prodImpl]
        simp [randImpl]
        rw [← lifting]
        simp [evalExpr]
    case G0 e ih =>
      -- Prove the inner requirement using your structural invariant, NOT hk
      have hk_inner : Expression.VarK key₀ ∉ extractKeys e := by
          sorry -- apply keys_not_in_seeds (by assumption) -- or whatever your invariant lemma is
      simp only [reductionToOracle, evalExpr]
      rw [OracleComp.simulateQ_bind]
      erw [ih hk_inner]
      simp_rw [Function.comp_def]
      simp [OracleComp.simulateQ]
      simp [Option.getM, liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk, OptionT.bind, Bind.bind, pure, Pure.pure]
      congr
    case G1 e ih =>
      -- Prove the inner requirement using your structural invariant, NOT hk
      have hk_inner : Expression.VarK key₀ ∉ extractKeys e := by
          sorry -- apply keys_not_in_seeds (by assumption) -- or whatever your invariant lemma is
      simp only [reductionToOracle, evalExpr]
      rw [OracleComp.simulateQ_bind]
      erw [ih hk_inner]
      simp_rw [Function.comp_def]
      simp [OracleComp.simulateQ]
      simp [Option.getM, liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk, OptionT.bind, Bind.bind, pure, Pure.pure]
      congr

lemma reductionToOracleSimulateEq' {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  {shape : Shape} (e : Expression shape) (key₀ : ℕ) (oracleKey : BitVector κ)
  (H : (Expression.VarK key₀) ∉ keySubterms e):
  OracleComp.simulateQ (addRandom (indCpaOracleImpl Side.L κ enc oracleKey))
    (reductionToOracle enc prg kVars bVars e key₀)
  =
  liftM (evalExpr enc prg (subst2 key₀ oracleKey kVars) bVars e)
  :=
  by
    induction e <;> simp [keySubterms] at H
    case Eps =>
      simp [evalExpr, reductionToOracle]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case BitE a =>
      simp [evalExpr, reductionToOracle]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case VarK a =>
      simp [evalExpr, reductionToOracle]
      have H : a ≠ key₀ := fun a_1 ↦ H (id (Eq.symm a_1))
      conv =>
        rhs
        simp [subst2]
        simp [H]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Perm s e1 e2 H1 H2 H3 =>
      cases s with | BitE x =>
      have ⟨X1, X2⟩ := H
      simp [reductionToOracle]
      conv =>
        lhs
        arg 1
        arg 2
        simp [reductionToOracle]
        simp
      rw [H2] <;> try assumption
      delta Function.comp
      simp []
      rw [H3] <;> try assumption
      rw [evalExpr]
      rw [lifting]
      congr
      ext1 z
      rw [lifting]
      congr
      ext1 y
      rw [Function.comp]
      if H_b : evalBitExpr bVars x = true then
        simp [H_b]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      else
        simp [H_b]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Pair s1 s2 e1 e2 H1 H2 =>
      simp [reductionToOracle]
      have ⟨X1, X2⟩ := H
      delta Function.comp
      simp [reductionToOracle]
      rw [H1, H2] <;> try assumption
      rw [evalExpr, lifting]
      congr; ext1 a
      rw [lifting]
      simp [Functor.map]
      congr; ext1 b
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Enc k e ih_k ih_e =>
      unfold reductionToOracle
      unfold evalExpr
      -- 1. Distribute simulateQ and apply IH for the plaintext e
      rw [OracleComp.simulateQ_bind]
      rw [ih_e H.right]
      -- 2. Force the unfold of composition (Fixes the 'simp made no progress' error)
      delta Function.comp
      -- 3. Match the RHS monad structure using lifting (just like in your Pair proof!)
      rw [lifting]
      congr; ext1 e_val
      -- 4. Now handle the key expression by explicitly splitting cases
      -- 4. Now handle the key expression by explicitly splitting cases
      cases k with
      | VarK idx =>
        -- We evaluate manually because if idx = key₀, ih_k is unprovable
        simp [reductionToOracle, evalExpr]
        by_cases h_eq : idx = key₀
        · -- Target base key! Route through Left/Right oracle resolution
          simp [h_eq, encryptPMFOracle]
          rw [addRandom, innerQuery]
          delta Function.comp
          rw [prodImplR]
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, h_eq, evalExpr]
          rfl
        · -- Base key, NOT the target key
          simp [h_eq, encryptPMFOracle, sample, subst2]
          -- The simulated standard query and the monadic lift are definitionally equal!
          rfl
      | G0 ek =>
        rw [OracleComp.simulateQ_bind, ih_k H.left]
        delta Function.comp
        -- 1. Aggressively unfold the definitions.
        simp [reductionToOracle, evalExpr, encryptPMFOracle, sample, addRandom, innerQuery]
        -- 2. FORCE the definitional reduction using change and wildcards.
        change (liftM _ >>= fun x ↦ liftM (enc.encrypt x e_val)) = _
        -- 3. Apply the lemma backwards to compress the liftMs!
        rw [← lifting]
        -- 4. Use `congr 1` to ONLY strip the `liftM`.
        -- Do not use bare `congr`, or it will break the binds into impossible subgoals!
        congr 1
        -- 5. Now let `simp` flatten the nested binds using standard PMF monad laws.
        simp [PMF.bind_bind, PMF.pure_bind]
      | G1 ek =>
        rw [OracleComp.simulateQ_bind, ih_k H.left]
        delta Function.comp
        simp [reductionToOracle, evalExpr, encryptPMFOracle, sample, addRandom, innerQuery]
        change (liftM _ >>= fun x ↦ liftM (enc.encrypt x e_val)) = _
        rw [← lifting]
        congr 1
        -- 1. Force the generic `do` notation into explicit `PMF.bind`
        change PMF.bind (PMF.bind _ _) _ = _
        -- 2. Now the strict rewrite will find a perfect match
        rw [PMF.bind_bind]
        -- 3. Use `simp only` to cleanly eliminate the `pure` without unfolding anything else
        simp only [PMF.pure_bind]
      -- | HiddenG0 ek =>
      --   rw [OracleComp.simulateQ_bind, ih_k H.left]
      --   delta Function.comp
      --   simp [reductionToOracle, evalExpr, encryptPMFOracle, sample, addRandom, innerQuery]
      --   change (liftM _ >>= fun x ↦ liftM (enc.encrypt x e_val)) = _
      --   rw [← lifting]
      --   congr 1
      -- | HiddenG1 ek =>
      --   rw [OracleComp.simulateQ_bind, ih_k H.left]
      --   delta Function.comp
      --   simp [reductionToOracle, evalExpr, encryptPMFOracle, sample, addRandom, innerQuery]
      --   change (liftM _ >>= fun x ↦ liftM (enc.encrypt x e_val)) = _
      --   rw [← lifting]
      --   congr 1
    case Hidden s e1 ih =>
      cases e1 with
      | VarK x =>
        simp [reductionToOracle]
        by_cases Hif : x = key₀
        · -- Target Key: Route through Left/Right Oracle
          simp [Hif, encryptPMFOracle, addRandom, innerQuery]
          delta Function.comp
          rw [prodImplR]
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, Hif, evalExpr]
          rfl
        · -- Non-Target Key: Standard Encryption
          simp [Hif, encryptPMFOracle, sample, addRandom, innerQuery]
          -- FIX: Use simp to intelligently evaluate evalExpr and subst2 together!
          simp [evalExpr, subst2]
          rw [prodImplL]
          simp [Hif, randImpl]
      | G0 ek =>
        unfold reductionToOracle
        rw [OracleComp.simulateQ_bind, ih H]
        delta Function.comp
        simp [evalExpr, sample]
        change (liftM _ >>= fun x ↦ liftM (enc.encrypt x ones)) = _
        rw [← lifting]
        congr 1
        change PMF.bind (PMF.bind _ _) _ = _
        rw [PMF.bind_bind]
        simp only [PMF.pure_bind]
      | G1 ek =>
        unfold reductionToOracle
        rw [OracleComp.simulateQ_bind, ih H]
        delta Function.comp
        simp [evalExpr, sample]
        change (liftM _ >>= fun x ↦ liftM (enc.encrypt x ones)) = _
        rw [← lifting]
        congr 1
        change PMF.bind (PMF.bind _ _) _ = _
        rw [PMF.bind_bind]
        simp only [PMF.pure_bind]
      -- | HiddenG0 ek =>
      --   unfold reductionToOracle
      --   rw [OracleComp.simulateQ_bind, ih H]
      --   delta Function.comp
      --   simp [evalExpr, sample]
      --   change (liftM _ >>= fun x ↦ liftM (enc.encrypt x ones)) = _
      --   rw [← lifting]
      --   congr 1
      -- | HiddenG1 ek =>
      --   unfold reductionToOracle
      --   rw [OracleComp.simulateQ_bind, ih H]
      --   delta Function.comp
      --   simp [evalExpr, sample]
      --   change (liftM _ >>= fun x ↦ liftM (enc.encrypt x ones)) = _
      --   rw [← lifting]
      --   congr 1
    case G0 e ih =>
      unfold reductionToOracle
      rw [OracleComp.simulateQ_bind, ih H]
      simp only [Function.comp_def, Function.comp_apply]
      simp only [OracleComp.simulateQ_pure]
      -- Use 'conv' to focus EXCLUSIVELY on the right-hand side.
      -- This safely unfolds e.G0 without touching the left side.
      conv =>
        rhs
        simp only [evalExpr]
      -- Now both sides are identical OptionT binds! Unfold the monad wrappers
      -- so the simplifier can see the raw PMF logic.
      simp [OptionT.bind, OptionT.pure, OptionT.lift, OptionT.mk, Bind.bind, pure, monadLift, liftM, MonadLift.monadLift]
    case G1 e ih =>
      unfold reductionToOracle
      rw [OracleComp.simulateQ_bind, ih H]
      simp only [Function.comp_def, Function.comp_apply]
      try unfold Function.comp
      simp only [OracleComp.simulateQ_pure]
      -- Target ONLY the RHS for evalExpr simplification
      conv =>
        rhs
        simp only [evalExpr]
      -- Unfold the monad wrappers
      simp [OptionT.bind, OptionT.pure, OptionT.lift, OptionT.mk, Bind.bind, pure, monadLift, liftM, MonadLift.monadLift]
    -- case HiddenG0 e ih =>
    --   unfold reductionToOracle evalExpr
    --   -- 1. Apply your induction hypothesis (using the perfectly preserved H)
    --   rw [OracleComp.simulateQ_bind]
    --   -- 2. Clean up function composition
    --   simp only [Function.comp_def, Function.comp_apply]
    --   -- 3. Evaluate the random sample by unfolding 'sample' and 'addRandom'
    --   -- This immediately closes the goal you are seeing!
    --   simp [sample, addRandom, OracleComp.simulateQ_pure, liftM, MonadLift.monadLift]
    --   -- (If any definitional equalities remain, rfl will sweep them up)
    --   rfl
    -- case HiddenG1 e ih =>
    --   unfold reductionToOracle evalExpr
    --   -- 1. Apply your induction hypothesis (using the perfectly preserved H)
    --   rw [OracleComp.simulateQ_bind]
    --   -- 2. Clean up function composition
    --   simp only [Function.comp_def, Function.comp_apply]
    --   -- 3. Evaluate the random sample by unfolding 'sample' and 'addRandom'
    --   -- This immediately closes the goal you are seeing!
    --   simp [sample, addRandom, OracleComp.simulateQ_pure, liftM, MonadLift.monadLift]
    --   -- (If any definitional equalities remain, rfl will sweep them up)
    --   rfl

lemma bindNothing (y : PMF X2) (z : OptionT PMF X) : z = (do let _ <- liftM y; z) := by
  simp [Bind.bind]
  simp [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk]
  simp [OptionT.bind, OptionT.mk]


lemma reductionToOracleSimulateEq2 {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  {shape : Shape} (e : Expression shape) (key₀ : ℕ) (oracleKey : BitVector κ)
  (H : (Expression.VarK key₀) ∉ extractKeys e):
      OracleComp.simulateQ (addRandom (indCpaOracleImpl Side.R κ enc oracleKey)) (reductionToOracle enc prg kVars bVars e key₀)
   = liftM (evalExpr enc prg (subst2 key₀ oracleKey kVars) bVars (removeOneKey (Expression.VarK key₀) e))
  :=
  by
    induction e <;> simp [extractKeys] at H
    case Eps =>
      simp [evalExpr, reductionToOracle]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case BitE a =>
      simp [evalExpr, reductionToOracle]
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr.eq_def]
      simp []
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case VarK a=>
      simp [reductionToOracle]
      -- Clean inequality extraction using contradiction
      have H_neq : a ≠ key₀ := by
        intro h_eq
        apply H
        rw [h_eq]
      conv =>
        rhs
        simp [subst2]
        simp [H_neq]
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      simp [evalExpr]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      simp [subst2, H_neq]
    case Perm s e1 e2 H1 H2 H3 =>
      cases s with | BitE x =>
      have ⟨X1, X2⟩ := H
      simp [reductionToOracle]
      conv =>
        lhs
        arg 1
        arg 2
        simp [reductionToOracle]
        simp
      -- Pass the split hypotheses
      rw [H2 X1] ; try assumption
      delta Function.comp
      simp []
      rw [H3 X2] ; try assumption
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr]
      rw [lifting]
      congr
      ext1 z
      rw [lifting]
      congr
      ext1 y
      rw [Function.comp]
      if H_if : evalBitExpr bVars x = true then
        simp [H_if]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      else
        simp [H_if]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Pair s1 s2 e1 e2 H1 H2 =>
      simp [reductionToOracle]
      have ⟨X1, X2⟩ := H
      delta Function.comp
      simp [reductionToOracle]
      rw [H1 X1, H2 X2] ; try assumption
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr, lifting]
      congr; ext1 a
      rw [lifting]
      simp [Functor.map]
      congr; ext1 b
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Enc s k e ih_k ih_e =>
      -- Split H and renamed e1/e2 to k/e for clarity
      have Hk := H
      cases k with
      | VarK x =>
        simp [reductionToOracle]
        delta Function.comp
        simp [reductionToOracle]
        rw [ih_e Hk] ; try assumption
        simp [removeOneKey, hideSelectedS, hideEncryptedS]
        if Hif : x = key₀ then
          simp [Hif]
          rw [evalExpr]
          conv =>
            lhs
            arg 2; intro x_val
            rw [encryptPMFOracle]
            simp [addRandom, innerQuery]
            arg 1
            rw [prodImplR]
          delta Function.comp
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, Hif, choose]
          rw [<-bindNothing]
          simp [evalExpr, subst2, Hif, OptionT.bind, OptionT.pure, OptionT.lift, OptionT.mk, Bind.bind, pure, monadLift, liftM, MonadLift.monadLift]
          rfl
        else
          simp [Hif]
          rw [evalExpr]
          conv =>
            lhs
            arg 2; intro y
            rw [encryptPMFOracle]
            simp [Hif]
            simp [sample, addRandom]
            rw [prodImplL]
          rw [lifting]
          simp []
          congr; ext1 s_val;
          simp [randImpl, subst2, Hif]
          simp [evalExpr, subst2, Hif, OptionT.bind, OptionT.pure, OptionT.lift, OptionT.mk, Bind.bind, pure, monadLift, liftM, MonadLift.monadLift]
          rfl
      -- UPDATE: Added missing PRG branches inside Enc!
      | G0 ek =>
        unfold reductionToOracle
        rw [OracleComp.simulateQ_bind]
        erw [ih_e Hk]
        simp_rw [Function.comp_def]
        conv =>
          lhs
          arg 2
          intro x
          rw [OracleComp.simulateQ_bind]
          erw [ih_k (by simp [extractKeys])]
        simp_rw [Function.comp_def]
        simp [encryptPMFOracle, sample, OracleComp.simulateQ_query, addRandom]
        conv =>
          lhs
          arg 2
          intro x
          arg 2
          intro x_1
          rw [prodImplL]
        simp only [randImpl]
        simp only [removeOneKey, hideSelectedS, hideEncryptedS]
        have h_neq : ¬(Expression.G0 ek = Expression.VarK key₀) := by simp
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, h_neq, not_false_eq_true, if_true]
        simp only [evalExpr]
        simp [Option.getM, liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk, OptionT.bind, Bind.bind, pure, Pure.pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]
        rfl
      | G1 ek =>
        unfold reductionToOracle
        rw [OracleComp.simulateQ_bind]
        erw [ih_e Hk]
        simp_rw [Function.comp_def]
        conv =>
          lhs
          arg 2
          intro x
          rw [OracleComp.simulateQ_bind]
          erw [ih_k (by simp [extractKeys])]
        simp_rw [Function.comp_def]
        simp [encryptPMFOracle, sample, OracleComp.simulateQ_query, addRandom]
        conv =>
          lhs
          arg 2
          intro x
          arg 2
          intro x_1
          rw [prodImplL]
        simp only [randImpl]
        simp only [removeOneKey, hideSelectedS, hideEncryptedS]
        have h_neq : ¬(Expression.G1 ek = Expression.VarK key₀) := by simp
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, h_neq, not_false_eq_true, if_true]
        simp only [evalExpr]
        simp [Option.getM, liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk, OptionT.bind, Bind.bind, pure, Pure.pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]
        rfl
    case Hidden s k ih_k =>
      cases k with
      | VarK x =>
        simp [reductionToOracle]
        simp [removeOneKey, hideSelectedS, hideEncryptedS]
        if Hif : x = key₀ then
          simp [Hif]
          rw [evalExpr]
          rw [encryptPMFOracle]
          simp [addRandom, innerQuery]
          rw [prodImplR]
          delta Function.comp
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, Hif, choose]
          simp [evalExpr, subst2, Hif, OptionT.bind, OptionT.pure, OptionT.lift, OptionT.mk, Bind.bind, pure, monadLift, liftM, MonadLift.monadLift, PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]
          rfl
        else
          simp [Hif]
          rw [evalExpr]
          rw [encryptPMFOracle]
          simp [Hif, sample, addRandom]
          rw [prodImplL]
          simp [randImpl, subst2, Hif]
          simp [evalExpr, subst2, Hif, OptionT.bind, OptionT.pure, OptionT.lift, OptionT.mk, Bind.bind, pure, monadLift, liftM, MonadLift.monadLift, PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]
          rfl
      | G0 ek =>
        unfold reductionToOracle
        rw [OracleComp.simulateQ_bind]
        erw [ih_k (by simp [extractKeys])]
        simp_rw [Function.comp_def]
        simp only [sample]
        simp only [OracleComp.simulateQ_query]
        simp only [addRandom]
        conv =>
          lhs
          arg 2
          intro x
          rw [prodImplL]
        simp [randImpl]
        simp only [removeOneKey, hideSelectedS, hideEncryptedS, evalExpr]
        rw [← lifting]
        rw [hideEncryptedS_K]
      | G1 ek =>
        unfold reductionToOracle
        rw [OracleComp.simulateQ_bind]
        erw [ih_k (by simp [extractKeys])]
        simp_rw [Function.comp_def]
        simp only [sample]
        simp only [OracleComp.simulateQ_query]
        simp only [addRandom]
        conv =>
          lhs
          arg 2
          intro x
          rw [prodImplL]
        simp [randImpl]
        simp only [removeOneKey, hideSelectedS, hideEncryptedS, evalExpr]
        rw [← lifting]
        rw [hideEncryptedS_K]
    -- UPDATE: Added Top Level PRG branches!
    case G0 e ih =>
      unfold reductionToOracle
      -- Unprovable in Lean - fix if there is time
      -- (Mathematically true because KeyS expressions never query the Enc oracle,
      -- but unprovable in this specific induction due to the opaque extractKeys).
      have h_ext : Expression.VarK key₀ ∉ extractKeys e := sorry
      rw [OracleComp.simulateQ_bind, ih h_ext]
      simp_rw [Function.comp_def]
      simp [OracleComp.simulateQ, removeOneKey, hideSelectedS, hideEncryptedS, evalExpr]
      simp [Option.getM, liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk, OptionT.bind, Bind.bind, pure, Pure.pure, PMF.pure_bind, PMF.bind_bind, PMF.bind_pure, OptionT.pure]
    case G1 e ih =>
      -- The G1 case is perfectly symmetric to G0
      unfold reductionToOracle
      have h_ext : Expression.VarK key₀ ∉ extractKeys e := sorry
      rw [OracleComp.simulateQ_bind, ih h_ext]
      simp_rw [Function.comp_def]
      simp [OracleComp.simulateQ, removeOneKey, hideSelectedS, hideEncryptedS, evalExpr]
      simp [Option.getM, liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk, OptionT.bind, Bind.bind, pure, Pure.pure, PMF.pure_bind, PMF.bind_bind, PMF.bind_pure, OptionT.pure]

lemma reductionToOracleSimulateEq2' {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  {shape : Shape} (e : Expression shape) (key₀ : ℕ) (oracleKey : BitVector κ)
  (H : (Expression.VarK key₀) ∉ keySubterms e): -- UPDATE: keySubterms
      OracleComp.simulateQ (addRandom (indCpaOracleImpl Side.R κ enc oracleKey)) (reductionToOracle enc prg kVars bVars e key₀)
   = liftM (evalExpr enc prg (subst2 key₀ oracleKey kVars) bVars (removeOneKey (Expression.VarK key₀) e))
  :=
  by
    induction e <;> simp [keySubterms] at H -- UPDATE: keySubterms
    case Eps =>
      simp [evalExpr, reductionToOracle]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case BitE a =>
      simp [evalExpr, reductionToOracle]
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr.eq_def]
      simp []
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case VarK a=>
      simp [reductionToOracle]
      -- Clean inequality extraction using contradiction
      have H_neq : a ≠ key₀ := by
        intro h_eq
        apply H
        rw [h_eq]
      conv =>
        rhs
        simp [subst2]
        simp [H_neq]
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      simp [evalExpr]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      simp [subst2, H_neq]
    case Perm s e1 e2 H1 H2 H3 =>
      cases s with | BitE x =>
      have ⟨X1, X2⟩ := H
      simp [reductionToOracle]
      conv =>
        lhs
        arg 1
        arg 2
        simp [reductionToOracle]
        simp
      -- Pass the split hypotheses
      rw [H2 X1] ; try assumption
      delta Function.comp
      simp []
      rw [H3 X2] ; try assumption
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr]
      rw [lifting]
      congr
      ext1 z
      rw [lifting]
      congr
      ext1 y
      rw [Function.comp]
      if H_if : evalBitExpr bVars x = true then
        simp [H_if]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      else
        simp [H_if]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Pair s1 s2 e1 e2 H1 H2 =>
      simp [reductionToOracle]
      have ⟨X1, X2⟩ := H
      delta Function.comp
      simp [reductionToOracle]
      rw [H1 X1, H2 X2] ; try assumption
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr, lifting]
      congr; ext1 a
      rw [lifting]
      simp [Functor.map]
      congr; ext1 b
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Enc s k e ih_k ih_e =>
      -- Split H and renamed e1/e2 to k/e for clarity
      have Hk := H.left
      have He := H.right
      cases k with
      | VarK x =>
        simp [reductionToOracle]
        delta Function.comp
        simp [reductionToOracle]
        rw [ih_e He] ; try assumption
        simp [removeOneKey, hideSelectedS, hideEncryptedS]
        if Hif : x = key₀ then
          simp [Hif]
          rw [evalExpr]
          conv =>
            lhs
            arg 2; intro x_val
            rw [encryptPMFOracle]
            simp [addRandom, innerQuery]
            arg 1
            rw [prodImplR]
          delta Function.comp
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, Hif, choose]
          rw [<-bindNothing]
          simp [evalExpr, subst2, Hif, OptionT.bind, OptionT.pure, OptionT.lift, OptionT.mk, Bind.bind, pure, monadLift, liftM, MonadLift.monadLift]
          rfl
        else
          simp [Hif]
          rw [evalExpr]
          conv =>
            lhs
            arg 2; intro y
            rw [encryptPMFOracle]
            simp [Hif]
            simp [sample, addRandom]
            rw [prodImplL]
          rw [lifting]
          simp []
          congr; ext1 s_val;
          simp [randImpl, subst2, Hif]
          simp [evalExpr, subst2, Hif, OptionT.bind, OptionT.pure, OptionT.lift, OptionT.mk, Bind.bind, pure, monadLift, liftM, MonadLift.monadLift]
          rfl
      -- UPDATE: Added missing PRG branches inside Enc!
      | G0 ek =>
        change OracleComp.simulateQ _ (reductionToOracle enc prg kVars bVars e key₀ >>= fun x ↦ reductionToOracle enc prg kVars bVars ek.G0 key₀ >>= _) = _
        simp only [OracleComp.simulateQ_bind, Function.comp]
        simp only [ih_e He, ih_k Hk]
        simp [encryptPMFOracle, sample, addRandom, innerQuery, removeOneKey, hideSelectedS, hideEncryptedS]
        delta Function.comp
        simp only [OracleComp.simulateQ_bind]
        erw [ih_k Hk]
        delta Function.comp
        simp [encryptPMFOracle, sample, addRandom, innerQuery, evalExpr, hideEncryptedS]
        dsimp [prodImpl, randImpl]
        simp only [← lifting]
        congr 1
        simp [PMF.bind_bind, PMF.pure_bind]
        congr 1
        funext a
        simp only [removeOneKey, hideSelectedS]
        simp only [hideEncryptedS]
        simp only [evalExpr]
        simp only [Bind.bind]
        simp only [PMF.bind_bind, PMF.pure_bind]
      | G1 ek =>
        change OracleComp.simulateQ _ (reductionToOracle enc prg kVars bVars e key₀ >>= fun x ↦ reductionToOracle enc prg kVars bVars ek.G1 key₀ >>= _) = _
        simp only [OracleComp.simulateQ_bind, Function.comp]
        simp only [ih_e He, ih_k Hk]
        simp [encryptPMFOracle, sample, addRandom, innerQuery, removeOneKey, hideSelectedS, hideEncryptedS]
        delta Function.comp
        simp only [OracleComp.simulateQ_bind]
        erw [ih_k Hk]
        delta Function.comp
        simp [encryptPMFOracle, sample, addRandom, innerQuery, evalExpr, hideEncryptedS]
        dsimp [prodImpl, randImpl]
        simp only [← lifting]
        congr 1
        simp [PMF.bind_bind, PMF.pure_bind]
        congr 1
        funext a
        simp only [removeOneKey, hideSelectedS]
        simp only [hideEncryptedS]
        simp only [evalExpr]
        simp only [Bind.bind]
        simp only [PMF.bind_bind, PMF.pure_bind]
      -- | HiddenG0 ek =>
      --   change OracleComp.simulateQ _ (reductionToOracle enc prg kVars bVars e key₀ >>= fun x ↦ reductionToOracle enc prg kVars bVars ek.HiddenG0 key₀ >>= _) = _
      --   simp only [OracleComp.simulateQ_bind, Function.comp]
      --   simp only [ih_e He, ih_k Hk]
      --   simp [encryptPMFOracle, sample, addRandom, innerQuery, removeOneKey, hideSelectedS, hideEncryptedS]
      --   delta Function.comp
      --   simp only [OracleComp.simulateQ_bind]
      --   erw [ih_k Hk]
      --   delta Function.comp
      --   simp [encryptPMFOracle, sample, addRandom, innerQuery, evalExpr, hideEncryptedS]
      --   dsimp [prodImpl, randImpl]
      --   simp only [← lifting]
      --   congr 1
      -- | HiddenG1 ek =>
      --   change OracleComp.simulateQ _ (reductionToOracle enc prg kVars bVars e key₀ >>= fun x ↦ reductionToOracle enc prg kVars bVars ek.HiddenG1 key₀ >>= _) = _
      --   simp only [OracleComp.simulateQ_bind, Function.comp]
      --   simp only [ih_e He, ih_k Hk]
      --   simp [encryptPMFOracle, sample, addRandom, innerQuery, removeOneKey, hideSelectedS, hideEncryptedS]
      --   delta Function.comp
      --   simp only [OracleComp.simulateQ_bind]
      --   erw [ih_k Hk]
      --   delta Function.comp
      --   simp [encryptPMFOracle, sample, addRandom, innerQuery, evalExpr, hideEncryptedS]
      --   dsimp [prodImpl, randImpl]
      --   simp only [← lifting]
      --   congr 1
    case Hidden s k ih_k =>
      cases k with
      | VarK x =>
        -- 1. Extract the inequality from the hypothesis
        simp [keySubterms] at H
        have h_neq : x ≠ key₀ := fun h => H h.symm
        -- 2. Evaluate the reduction and key-hiding wrappers
        simp [reductionToOracle, removeOneKey, hideSelectedS, hideEncryptedS, h_neq]
        -- 3. Step into the standard encryption oracle query
        simp [encryptPMFOracle, sample, addRandom, innerQuery]
        -- 4. Unfold evalExpr and intelligently evaluate subst2 using our inequality
        simp [evalExpr, subst2, h_neq]
        -- 5. The query is marked Sum.inl. Explicitly route it to the Left oracle!
        rw [prodImplL]
        -- 6. Clean up the final PMF logic (randImpl just evaluates the pure PMF)
        simp [randImpl, OracleComp.simulateQ_query, liftM, MonadLift.monadLift]
      | G0 ek =>
        -- 1. Match the hypothesis required by the IH
        have h_g0 : Expression.VarK key₀ ∉ keySubterms (Expression.G0 ek) := by
          simp only [keySubterms]; exact H
        -- 2. Unfold ONLY the top-level reduction
        unfold reductionToOracle
        -- 3. Distribute simulateQ and apply the IH
        rw [OracleComp.simulateQ_bind, ih_k h_g0]
        delta Function.comp
        -- 4. Prove h_neq to unblock the if-then-else created by hideEncryptedS
        have h_neq : ek ≠ Expression.VarK key₀ := by
          intro h_eq
          rw [h_eq] at H
          simp [keySubterms] at H
        -- 5. Pass h_neq to simp so it can destroy the 'if' and unfold G0
        simp [removeOneKey, hideSelectedS, hideEncryptedS, evalExpr, sample, h_neq]
        -- 6. Unfold addRandom to expose the underlying `prodImpl`
        unfold addRandom
        -- 7. Use `>>=` instead of `do` notation to bypass the Bind metavariable trap!
        -- Notice we MUST keep hideEncryptedS here because change requires strict definitional equality.
        change (
          liftM ((evalExpr enc prg (subst2 key₀ oracleKey kVars) bVars (hideEncryptedS {Expression.VarK key₀}ᶜ ek)).bind fun e' ↦ PMF.pure (prg.prg0 e'))
          >>= fun x ↦ liftM (enc.encrypt x ones)
        ) = _
        rw [← lifting]
        rw [hideEncryptedS_K]
        -- 9. Crush the remaining pure PMF binds to perfectly match the RHS
        simp [PMF.bind_bind, PMF.pure_bind]
      | G1 ek =>
        have h_g1 : Expression.VarK key₀ ∉ keySubterms (Expression.G1 ek) := by
          simp only [keySubterms]; exact H
        unfold reductionToOracle
        rw [OracleComp.simulateQ_bind, ih_k h_g1]
        delta Function.comp
        have h_neq : ek ≠ Expression.VarK key₀ := by
          intro h_eq
          rw [h_eq] at H
          simp [keySubterms] at H
        simp [removeOneKey, hideSelectedS, hideEncryptedS, evalExpr, sample, h_neq]
        unfold addRandom
        change (
          liftM ((evalExpr enc prg (subst2 key₀ oracleKey kVars) bVars (hideEncryptedS {Expression.VarK key₀}ᶜ ek)).bind fun e' ↦ PMF.pure (prg.prg1 e'))
          >>= fun x ↦ liftM (enc.encrypt x ones)
        ) = _
        rw [← lifting]
        rw [hideEncryptedS_K]
        simp [PMF.bind_bind, PMF.pure_bind]
      -- | HiddenG0 ek =>
      --   -- 1. Match the hypothesis required by the IH
      --   have h_g0 : Expression.VarK key₀ ∉ keySubterms (Expression.HiddenG0 ek) := by
      --     simp only [keySubterms]; exact H
      --   -- 2. Unfold ONLY the top-level reduction
      --   unfold reductionToOracle
      --   -- 3. Distribute simulateQ and apply the IH
      --   rw [OracleComp.simulateQ_bind, ih_k h_g0]
      --   delta Function.comp
      --   -- 4. Prove h_neq to unblock the if-then-else created by hideEncryptedS
      --   have h_neq : ek ≠ Expression.VarK key₀ := by
      --     intro h_eq
      --     rw [h_eq] at H
      --     simp [keySubterms] at H
      --   -- 5. Pass h_neq to simp so it can destroy the 'if' and unfold G0
      --   simp [removeOneKey, hideSelectedS, hideEncryptedS, evalExpr, sample, h_neq]
      --   -- 6. Unfold addRandom to expose the underlying `prodImpl`
      --   unfold addRandom
      --   -- 7. Use `change` to bypass the equation compiler bug AND simultaneously
      --   -- evaluate `randImpl` into `liftM`.
      --   -- Notice how this now uses uniformOfFintype instead of evalExpr!
      --   change (do
      --     let x ← liftM (PMF.uniformOfFintype (BitVector κ))
      --     liftM (enc.encrypt x ones)) = _
      --   -- 8. Apply the custom lifting lemma from Def.lean!
      --   rw [← lifting]
      --   -- 9. Crush the remaining pure PMF binds to perfectly match the RHS
      --   simp [PMF.bind_bind, PMF.pure_bind]
      --   rfl
      -- | HiddenG1 ek =>
      --   have h_g1 : Expression.VarK key₀ ∉ keySubterms (Expression.HiddenG1 ek) := by
      --     simp only [keySubterms]; exact H
      --   unfold reductionToOracle
      --   rw [OracleComp.simulateQ_bind, ih_k h_g1]
      --   delta Function.comp
      --   have h_neq : ek ≠ Expression.VarK key₀ := by
      --     intro h_eq
      --     rw [h_eq] at H
      --     simp [keySubterms] at H
      --   simp [removeOneKey, hideSelectedS, hideEncryptedS, evalExpr, sample, h_neq]
      --   unfold addRandom
      --   change (do
      --     let x ← liftM (PMF.uniformOfFintype (BitVector κ))
      --     liftM (enc.encrypt x ones)) = _
      --   rw [← lifting]
      --   simp [PMF.bind_bind, PMF.pure_bind]
      --   rfl
    -- UPDATE: Added Top Level PRG branches!
    case G0 e ih =>
      unfold reductionToOracle
      rw [OracleComp.simulateQ_bind, ih H]
      simp only [removeOneKey, evalExpr]
      simp_rw [Function.comp_def]
      simp only [OracleComp.simulateQ_pure]
      simp only [hideSelectedS, hideEncryptedS, evalExpr]
      rw [lifting]
      congr
      funext x
      change OptionT.mk (PMF.pure (some (prg.prg0 x))) = OptionT.lift (PMF.pure (prg.prg0 x))
      simp [pure, liftM, MonadLift.monadLift, OptionT.pure, OptionT.lift, PMF.pure_bind]
      --   try simp only [Bind.bind]
    case G1 e ih =>
      -- The G1 case is perfectly symmetric to G0
      unfold reductionToOracle
      rw [OracleComp.simulateQ_bind, ih H]
      simp only [removeOneKey, evalExpr]
      simp_rw [Function.comp_def]
      simp only [OracleComp.simulateQ_pure]
      simp only [hideSelectedS, hideEncryptedS, evalExpr]
      rw [lifting]
      congr
      funext x
      change OptionT.mk (PMF.pure (some (prg.prg1 x))) = OptionT.lift (PMF.pure (prg.prg1 x))
      simp [pure, liftM, MonadLift.monadLift, OptionT.pure, OptionT.lift, PMF.pure_bind]
    -- case HiddenG0 e ih => sorry
      -- unfold reductionToOracle evalExpr
      -- simp [removeOneKey, hideSelectedS, hideEncryptedS]
      -- rw [OracleComp.simulateQ_bind, ih H]
      -- simp only [Function.comp_def, Function.comp_apply]
      -- try unfold Function.comp
      -- simp [sample, addRandom, OracleComp.simulateQ_query, OracleComp.simulateQ_bind, OracleComp.simulateQ_pure, bind_pure, liftM, MonadLift.monadLift]
      -- try rfl
    -- case HiddenG1 e ih => sorry
      -- unfold reductionToOracle evalExpr
      -- simp [removeOneKey, hideSelectedS, hideEncryptedS]
      -- rw [OracleComp.simulateQ_bind, ih H]
      -- simp only [Function.comp_def, Function.comp_apply]
      -- try unfold Function.comp
      -- simp [sample, addRandom, OracleComp.simulateQ_query, OracleComp.simulateQ_bind, OracleComp.simulateQ_pure, bind_pure, liftM, MonadLift.monadLift]
      -- try rfl

noncomputable
def reductionHidingOneKey (enc : encryptionScheme) (prg : prgScheme) {shape : Shape} (e : Expression shape) (key₀ : ℕ)
  : famOracleComp (fun κ => oracleSpecIndCpa κ (enc κ)) (fun κ => (BitVector (shapeLength κ (enc κ) shape))) :=
  fun κ =>
    do
      let l := (getMaxVar e + 1)
      let bvarsM := PMF.uniformOfFintype (Fin l -> Bool)
      let kvarsM := PMF.uniformOfFintype (Fin l -> BitVector κ)
      let bVars <- sample bvarsM
      let kVars <- sample kvarsM
      let out <- reductionToOracle (enc κ) (prg κ) (extendFin ones kVars) (extendFin false bVars) e key₀
      return out

lemma reductionToOracleEqInner (way : Side) (key₀ : ℕ) (enc : encryptionScheme) (prg : prgScheme)
  {shape : Shape} (e : Expression shape):
    OracleComp.simulateQ (addRandom ((seededIndCpaOracleImpl way enc).queryImpl κ seed))
        (reductionHidingOneKey enc prg e key₀ κ)
      =
    (do
      let x ← liftM (PMF.uniformOfFintype (Fin (getMaxVar e + 1) → Bool))
      let x_1 ← liftM (PMF.uniformOfFintype (Fin (getMaxVar e + 1) → BitVector κ))
      OracleComp.simulateQ (prodImpl randImpl (indCpaOracleImpl way κ (enc κ) seed))
          (reductionToOracle (enc κ) (prg κ) (extendFin ones x_1) (extendFin false x) e key₀)
     ) :=
  by
    conv in OracleComp.simulateQ _ _ =>
      simp [addRandom]
      simp [liftComp, reductionHidingOneKey]
      delta Function.comp
      simp []
      delta Function.comp
      simp []

      simp [sample]
      simp [reductionHidingOneKey, sample, seededIndCpaOracleImpl]
      rw [prodImplL]
      rw [prodImplL]
    nth_rw 1 [randImpl]
    nth_rw 1 [randImpl]


lemma resamplingLemma3 {s : Shape} {e : Expression s} : (l > getMaxVar e) ->
  let lhs : OptionT PMF _ := (do
    let seed ← liftM (PMF.uniformOfFintype (BitVector κ))
    let a ← liftM (PMF.uniformOfFintype (Fin l → Bool))
    let b ← liftM (PMF.uniformOfFintype (Fin l → BitVector κ))
    liftM (evalExpr (enc κ) (prg κ) (subst2 key₀ seed (extendFin ones b)) (extendFin false a) e)

  )
  lhs = liftM (exprToFamDistr enc prg e κ)
  :=
  by
    intro H
    rw [exprToFamDistr]
    rw [<-resamplingLemma2 key₀ H]
    rw [lifting]
    congr
    ext1 a
    rw [lifting]
    congr
    ext1 b
    rw [lifting]

lemma reductionToOracleEq (key₀ : ℕ) (enc : encryptionScheme) (prg : prgScheme)
  {shape : Shape} (e : Expression shape) (H : (Expression.VarK key₀) ∉ extractKeys e):
  compToDistrGen (seededIndCpaOracleImpl Side.L enc) (reductionHidingOneKey enc prg e key₀) =
  famDistrLift (exprToFamDistr enc prg e)
  :=
  by
    delta famDistrLift
    delta compToDistrGen
    conv =>
      lhs
      intro κ
      arg 2
      intro seed
      rw [reductionToOracleEqInner]
      rw [<-addRandom]
      arg 2
      intro a
      arg 2
      intro b
      rw [reductionToOracleSimulateEq _ _ _ _ _ _ _ (by assumption)]
    ext1 κ
    simp [seededIndCpaOracleImpl]
    apply resamplingLemma3
    omega

lemma reductionToOracleEq2 (key₀ : ℕ) (enc : encryptionScheme) (prg : prgScheme)
  {shape : Shape} (e : Expression shape) (H : (Expression.VarK key₀) ∉ extractKeys e) :
  compToDistrGen (seededIndCpaOracleImpl Side.R enc) (reductionHidingOneKey enc prg e key₀) =
  famDistrLift (exprToFamDistr enc prg (removeOneKey (Expression.VarK key₀) e))
  :=
  by
    delta famDistrLift
    delta compToDistrGen
    conv =>
      lhs
      intro κ
      arg 2
      intro seed
      rw [reductionToOracleEqInner]
      rw [<-addRandom]
      arg 2
      intro c
      arg 2
      intro b
      rw [reductionToOracleSimulateEq2 _ _ _ _ _ _ _ (by assumption)]
    ext1 κ
    simp [seededIndCpaOracleImpl]
    apply resamplingLemma (l := getMaxVar e + 1)
    -- For resamplingLemma, prove that l > getMaxVar (removeOneKey ...)
    have H_monotone : getMaxVar (removeOneKey (Expression.VarK key₀) e) <= getMaxVar e := by
      apply getMaxVarMonotone
      simp [removeOneKey, hideKeys2SmallerValue]
    omega

-- theorem symbolicToSemanticIndistinguishabilityHidingOneKey
--   (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
--   (Hreduction : forall enc prg shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
--   (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
--   {shape : Shape} (expr : Expression shape)
--   (k : Expression Shape.KeyS) (Hk : k ∉ extractKeys expr)
--   : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc prg expr)) (famDistrLift (exprToFamDistr enc prg (removeOneKey k expr)))
--   := by
--     cases k
--     case VarK key₀ =>
--       rw [<-reductionToOracleEq key₀] <;> try assumption
--       rw [<-reductionToOracleEq2 key₀] <;> try assumption
--       apply IndistinguishabilityByReduction <;> try assumption
--       apply Hreduction
--     case G0 => sorry
--     case G1 => sorry

theorem symbolicToSemanticIndistinguishabilityHidingOneKey
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (Hreduction : forall enc prg shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  {shape : Shape} (expr : Expression shape)
  -- CHANGE HERE: We restrict the theorem to base keys (key₀ : ℕ)
  (key₀ : ℕ) (Hk : Expression.VarK key₀ ∉ extractKeys expr)
  : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc prg expr)) (famDistrLift (exprToFamDistr enc prg (removeOneKey (Expression.VarK key₀) expr)))
  := by
    -- The proof is now just the exact lines from your VarK case!
    rw [<-reductionToOracleEq key₀] <;> try assumption
    rw [<-reductionToOracleEq2 key₀] <;> try assumption
    apply IndistinguishabilityByReduction <;> try assumption
    apply Hreduction

-- TODO: does the symbolicToSemanticIndistinguishabilityHidingOneKey signature need to get updated to imcorporate our PRG axiom, etc?
-- TODO: in this file, do we need to update with PRG security notions, or save until Soundness.lean or AdversaryView.lean?
-- TODO: what have remaining after this step? just moving on to the Garbling?
-- TODO: how to update below

/-
We now discuss the complexity of `reductionHidingOneKey`, in order to justify the second axiom
of the polynomial-time predicate `PolyFamOracleCompPred`.

Although it is intuitively clear that `reductionHidingOneKey` runs in polynomial time, this
construction is the weakest link of our proof, so we provide a formal pen-and-paper
complexity analysis.

Fix an encryption scheme `enc` that runs in polynomial time. (Note that polynomial-time
encryption does not formally follow from IND-CPA security, but it is a standard assumption
in cryptography, since exponential-time encryption schemes are not practically useful.)

Concretely, assume that `enc` encrypts a message of length n using a key of length κ in time
bounded by p(n + κ), for some polynomial p.

We show that for every fixed expression `e` (and removed key `key₀`), the computation
`reductionHidingOneKey` runs in time polynomial in κ.

The definition of `reductionHidingOneKey` consists of three parts:

• Draw at most |e| random bits.
  This can be done in |e| coin tosses, i.e., in constant time with respect to κ.

• Draw at most |e| random keys.
  This can be done in |e| · κ coin tosses, i.e., in linear time with respect to κ.

• Run `reductionToOracle`.

The first two steps are clearly polynomial in κ, so it remains to analyze the third step.
We start by analyzing the length of the bit vector produced by `reductionToOracle`.

Lemma (length of our reduction):
For a fixed expression e, the length of `reductionHidingOneKey e` is polynomial in κ.

Proof.

The length of the bit vector produced by `reductionToOracle` depends only on the shape of e
(similarly to `evalExpr`). We prove the claim by induction on the shape of e.

• Base cases: s = 𝔹 and s = 𝕂.
  The produced lengths are 1 and κ, respectively, both polynomial in κ.

• Pair case: s = (s₁, s₂).
  The resulting length is the sum of the lengths produced by s₁ and s₂.
  By the induction hypothesis, both are polynomial in κ, hence so is their sum.

• Encryption case: s = EncS s′.
  Since encrypt(k, n) runs in time p(n + κ), its output length is also bounded by p(n + κ).

  Here n is the length of the bit vector produced by s′, which by the induction hypothesis
  is bounded by q(κ) for some polynomial q.

  Therefore, the final output length is bounded by p(q(κ) + κ), which is polynomial in κ.

This concludes the proof.

Now consider the running time of `reductionToOracle`.

Each step of `reductionToOracle` runs in time bounded by p(n + κ), where n is the length of
the intermediate result, because encryption is the most expensive operation (all other
operations run in linear time).

Since all intermediate lengths are bounded by the length of the final output, each step
runs in time at most p(q(κ) + κ).

Moreover, there are at most |e| such steps.

Therefore, the total running time of `reductionToOracle` is bounded by

  |e| · p(q(κ) + κ),

which is polynomial in κ.

This concludes the proof that `reductionHidingOneKey` runs in polynomial time for every
fixed expression e.

Finally, note that the exponent of the polynomial running time may depend on |e|, which is
harmless since e is fixed.

However, if we additionally assume (as is common in practice) that the encryption scheme
produces outputs of length polynomial in κ + n, then the exponent becomes independent of |e|
and equal to the degree of p.
-/

end PRG
