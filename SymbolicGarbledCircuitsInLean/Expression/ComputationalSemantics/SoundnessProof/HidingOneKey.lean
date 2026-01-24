import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability
import SymbolicGarbledCircuitsInLean.Expression.Lemmas.HideEncrypted
-- import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Def
import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Lemmas
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.Def
import SymbolicGarbledCircuitsInLean.Expression.ComputationalSemantics.EncryptionIndCpa


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
def encryptPMFOracle (enc : encryptionFunctions κ) (key₀ : ℕ) (kVars : (ℕ -> BitVector κ)) (key :ℕ) (input : (BitVector d))
: OracleComp (withRandom (oracleSpecIndCpa κ enc)) (BitVector (enc.encryptLength d)) :=
  do
    if key = key₀ then
      -- let input_unpacked <- sample input
      let x : (BitVector (enc.encryptLength d)) <-
        (innerQuery (oracleSpecIndCpa κ enc) d (input, ones))
      return x
    else
      let x <- sample (enc.encrypt (kVars key) input)
      return x
--

noncomputable
def reductionToOracle
  {κ : ℕ} (enc : encryptionFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  {shape : Shape} (e : Expression shape) (key₀ : ℕ):
  OracleComp (withRandom (oracleSpecIndCpa κ enc)) (BitVector (shapeLength κ enc shape)) :=
    match e with
  | Expression.Enc (Expression.VarK k) e => do
    let e' ← reductionToOracle enc kVars bVars e key₀
    let o <- encryptPMFOracle enc key₀ kVars k e'
    return o
  | Expression.Pair e₁ e₂ => do
    let e₁' ← reductionToOracle enc kVars bVars e₁ key₀
    let e₂' ← reductionToOracle enc kVars bVars e₂ key₀
    return List.Vector.append e₁' e₂'
  | Expression.BitE b => do
    let b' := evalBitExpr bVars b
    return (List.Vector.cons b' List.Vector.nil)
  | Expression.VarK k => do
    let key := kVars k
    return key
  | Expression.Perm (Expression.BitE b) e₁ e₂ => do
    let b' := evalBitExpr bVars b
    let e₁' ← reductionToOracle enc kVars bVars e₁ key₀
    let e₂' ← reductionToOracle enc kVars bVars e₂ key₀
    if b' then return List.Vector.append e₂' e₁'
    else return List.Vector.append e₁' e₂'
  | Expression.Eps =>
    return List.Vector.nil
  | Expression.Hidden (Expression.VarK k) => do
    -- let ones := List.Vector.replicate _ true
    let o <- encryptPMFOracle enc key₀ kVars k (ones)
    return o



lemma reductionToOracleSimulateEq {κ : ℕ} (enc : encryptionFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  {shape : Shape} (e : Expression shape) (key₀ : ℕ) (oracleKey : BitVector κ)
  (H : (Expression.VarK key₀) ∉ extractKeys e):

  OracleComp.simulateQ (addRandom (indCpaOracleImpl Side.L κ enc oracleKey))
    (reductionToOracle enc kVars bVars e key₀)
  =
  liftM (evalExpr enc (subst2 key₀ oracleKey kVars) bVars e)
  :=
  by
    induction e <;> simp [extractKeys, extractKeys] at H
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
      if H : evalBitExpr bVars x = true then
        simp [H]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      else
        simp [H]
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
    case Enc s e1 e2 H1 H2 =>
      cases e1 with | VarK x =>
        simp [reductionToOracle]
        delta Function.comp
        simp [reductionToOracle]
        rw [H2] <;> try assumption
        rw [evalExpr, lifting]
        congr; ext1 a
        rw [encryptPMFOracle]
        if Hif : x = key₀ then
          simp [Hif]
          rw [addRandom, innerQuery]
          delta Function.comp
          rw [prodImplR]
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, Hif]
          rfl
        else
          simp [Hif]
          rw [addRandom]
          simp [sample]
          rw [prodImplL]
          simp [randImpl, Option.getM]
          rw [subst2,]
          simp [Hif]
    case Hidden s e1 H1 =>
      cases e1 with | VarK x =>
        simp [reductionToOracle]
        rw [encryptPMFOracle]
        if Hif : x = key₀ then
          simp [Hif]
          rw [addRandom, innerQuery]
          delta Function.comp
          rw [prodImplR]
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, Hif, evalExpr]
          rfl
        else
          simp [Hif]
          rw [addRandom]
          simp [sample]
          rw [prodImplL]
          simp [randImpl, Option.getM]
          rw [evalExpr, subst2]
          simp [Hif]


lemma bindNothing (y : PMF X2) (z : OptionT PMF X) : z = (do let _ <- liftM y; z) := by
  simp [Bind.bind]
  simp [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk]
  simp [OptionT.bind, OptionT.mk]

lemma reductionToOracleSimulateEq2 {κ : ℕ} (enc : encryptionFunctions κ) (kVars : (ℕ -> BitVector κ)) (bVars : ℕ -> Bool)
  {shape : Shape} (e : Expression shape) (key₀ : ℕ) (oracleKey : BitVector κ)
  (H : (Expression.VarK key₀) ∉ extractKeys e):
      OracleComp.simulateQ (addRandom (indCpaOracleImpl Side.R κ enc oracleKey)) (reductionToOracle enc kVars bVars e key₀)
   = liftM (evalExpr enc (subst2 key₀ oracleKey kVars) bVars (removeOneKey (Expression.VarK key₀) e))
  :=
  by
    induction e <;> simp [extractKeys, extractKeys] at H
    case Eps =>
      simp [evalExpr, reductionToOracle]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case BitE a =>
      simp [evalExpr, reductionToOracle]
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr.eq_def]
      simp []
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case VarK a =>
      simp [reductionToOracle]
      have H : a ≠ key₀ := fun a_1 ↦ H (id (Eq.symm a_1))
      conv =>
        rhs
        simp [subst2]
        simp [H]
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      simp [evalExpr]
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      simp [subst2, H]
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
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr]
      rw [lifting]
      congr
      ext1 z
      rw [lifting]
      congr
      ext1 y
      rw [Function.comp]
      if H : evalBitExpr bVars x = true then
        simp [H]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
      else
        simp [H]
        simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Pair s1 s2 e1 e2 H1 H2 =>
      simp [reductionToOracle]
      have ⟨X1, X2⟩ := H
      delta Function.comp
      simp [reductionToOracle]
      rw [H1, H2] <;> try assumption
      simp [removeOneKey, hideSelectedS, hideEncryptedS]
      rw [evalExpr, lifting]
      congr; ext1 a
      rw [lifting]
      simp [Functor.map]
      congr; ext1 b
      simp [pure, OptionT.pure, liftM, monadLift, MonadLift.monadLift, OptionT.lift]
    case Enc s e1 e2 H1 H2 =>
      cases e1 with | VarK x =>
        simp [reductionToOracle]
        delta Function.comp
        simp [reductionToOracle]
        rw [H2] <;> try assumption
        simp [removeOneKey, hideSelectedS, hideEncryptedS]
        if Hif : x = key₀ then
          simp [Hif]
          rw [evalExpr]
          conv =>
            lhs
            arg 2; intro x
            rw [encryptPMFOracle]
            simp [addRandom, innerQuery]
            arg 1
            rw [prodImplR]
          delta Function.comp
          nth_rw 1 [indCpaOracleImpl]
          simp [subst2, Hif, choose]
          rw [<-bindNothing]
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
          congr; ext1 s;
          simp [randImpl, subst2, Hif]
    case Hidden s e1 H1 =>
      cases e1 with | VarK x =>
        simp [reductionToOracle]
        simp [removeOneKey, hideSelectedS, hideEncryptedS]
        if Hif : x = key₀ then
          simp [encryptPMFOracle]
          simp [Hif]
          conv =>
            lhs
            congr
            · simp [addRandom, innerQuery]
              rw [prodImplR]
              simp [indCpaOracleImpl]
            · simp [addRandom, innerQuery]
              delta Function.comp
              intro k
              simp []
          simp [evalExpr, subst2]
          rw [choose]
        else
          simp [encryptPMFOracle]
          simp [Hif]
          rw [evalExpr]
          simp [addRandom, sample]
          rw [prodImplL]
          simp [randImpl, subst2, Hif]

noncomputable
def reductionHidingOneKey (enc : encryptionScheme) {shape : Shape} (e : Expression shape) (key₀ : ℕ)
  : famOracleComp (fun κ => oracleSpecIndCpa κ (enc κ)) (fun κ => (BitVector (shapeLength κ (enc κ) shape))) :=
  fun κ =>
    do
      let l := (getMaxVar e + 1)
      let bvarsM := PMF.uniformOfFintype (Fin l -> Bool)
      let kvarsM := PMF.uniformOfFintype (Fin l -> BitVector κ)
      let bVars <- sample bvarsM
      let kVars <- sample kvarsM
      let out <- reductionToOracle (enc κ) (extendFin ones kVars) (extendFin false bVars) e key₀
      return out

lemma reductionToOracleEqInner (way : Side) (key₀ : ℕ) (enc : encryptionScheme)
  {shape : Shape} (e : Expression shape):
    OracleComp.simulateQ (addRandom ((seededIndCpaOracleImpl way enc).queryImpl κ seed))
        (reductionHidingOneKey enc e key₀ κ)
      =
    (do
      let x ← liftM (PMF.uniformOfFintype (Fin (getMaxVar e + 1) → Bool))
      let x_1 ← liftM (PMF.uniformOfFintype (Fin (getMaxVar e + 1) → BitVector κ))
      OracleComp.simulateQ (prodImpl randImpl (indCpaOracleImpl way κ (enc κ) seed))
          (reductionToOracle (enc κ) (extendFin ones x_1) (extendFin false x) e key₀)
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
    liftM (evalExpr (enc κ) (subst2 key₀ seed (extendFin ones b)) (extendFin false a) e)

  )
  lhs = liftM (exprToFamDistr enc e κ)
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



lemma reductionToOracleEq (key₀ : ℕ) (enc : encryptionScheme)
  {shape : Shape} (e : Expression shape) (H : (Expression.VarK key₀) ∉ extractKeys e):
  compToDistrGen (seededIndCpaOracleImpl Side.L enc) (reductionHidingOneKey enc e key₀) =
  famDistrLift (exprToFamDistr enc e)
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
      rw [reductionToOracleSimulateEq _ _ _ _ _ _ (by assumption)]
    ext1 κ
    simp [seededIndCpaOracleImpl]
    apply resamplingLemma3
    omega
lemma reductionToOracleEq2 (key₀ : ℕ) (enc : encryptionScheme)
  {shape : Shape} (e : Expression shape) (H : (Expression.VarK key₀) ∉ extractKeys e) :
  compToDistrGen (seededIndCpaOracleImpl Side.R enc) (reductionHidingOneKey enc e key₀) =
  famDistrLift (exprToFamDistr enc (removeOneKey (Expression.VarK key₀) e))
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
      rw [reductionToOracleSimulateEq2 _ _ _ _ _ _ (by assumption)]
    ext1 κ
    simp [seededIndCpaOracleImpl]
    have X := @resamplingLemma (getMaxVar e + 1) shape (removeOneKey (Expression.VarK key₀) e) enc κ key₀
    have H : getMaxVar (removeOneKey (Expression.VarK key₀) e) <= getMaxVar e := by
      apply getMaxVarMonotone
      simp [removeOneKey, hideKeys2SmallerValue]
    apply resamplingLemma3
    omega

theorem symbolicToSemanticIndistinguishabilityHidingOneKey
  (IsPolyTime : PolyFamOracleCompPred) (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (Hreduction : forall enc shape (expr : Expression shape) key₀, IsPolyTime (reductionHidingOneKey enc expr key₀))
  (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  {shape : Shape} (expr : Expression shape)
  (k : Expression Shape.KeyS) (Hk : k ∉ extractKeys expr)
  : CompIndistinguishabilityDistr IsPolyTime (famDistrLift (exprToFamDistr enc expr)) (famDistrLift (exprToFamDistr enc (removeOneKey k expr)))
  := by
    let (Expression.VarK key₀) := k
    rw [<-reductionToOracleEq key₀] <;> try assumption
    rw [<-reductionToOracleEq2 key₀] <;> try assumption
    apply IndistinguishabilityByReduction <;> try assumption
    apply Hreduction

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
