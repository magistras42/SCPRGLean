import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.OracleSpec
import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.OracleComp
import SymbolicGarbledCircuitsInLean.VCVio2.VCVio.OracleComp.SimSemantics.SimulateQ

-- In this file, we want to define a notion of computational indistinguishability,
-- for families of of distributions parameterized by the security parameter (κ : ℕ).

-- In more detail, it defines computational indistinguishability between two oracles. It also defines indistinguishability between two families of distributions. These definitions rely on an abstract notion of complexity which captures all allowed adversarial behavior(called PolynomialTime, as commonly assumed in cryptography). For more details, see our paper.

def oracleSpecForRand : OracleSpec Type :=
  fun type =>
    (PMF type, type)

noncomputable
def randImpl : QueryImpl oracleSpecForRand (OptionT PMF) := {
  impl
  | OracleSpec.OracleQuery.query t x =>
    let a : PMF t := x
    let b : OptionT PMF t := liftM a
    b
}



def withRandom (spec : OracleSpec X) : OracleSpec (Type ⊕ X) := oracleSpecForRand ++ₒ spec
def withRandomI (spec : ℕ -> OracleSpec X) : ℕ -> OracleSpec (Type ⊕ X) := fun κ => oracleSpecForRand ++ₒ spec κ


def sample {X : Type} (z :  PMF X) : OracleComp (withRandom spec) X :=
  ((withRandom spec).query (Sum.inl X) z)

def famDistr (Domain : ℕ -> Type) := (κ : ℕ) -> OptionT PMF (Domain κ)
def famDistrStrict (Domain : ℕ -> Type) := (κ : ℕ) -> PMF (Domain κ)

noncomputable
def famDistrLift {Domain : ℕ -> Type} (x : famDistrStrict Domain) : famDistr Domain :=
  fun κ =>
    liftM (x κ)

-- The computations of the family of distributions are also parameterized by the security parameter κ.

def famComp (Input : ℕ -> Type) (Output : ℕ -> Type) := (κ : ℕ) -> (Input κ) -> (PMF (Output κ))

-- We also want to talk about indistinguishability of oracles, which in our case are seeded oracles, i.e.
-- that are initialized with a random value, but don't have any other state. We build this type,
-- on the VCVio Oracle framework.

structure famSeededOracle {I : Type}  (Spec : ℕ -> OracleSpec I) where
  Seed : (κ : ℕ) -> Type
  seedDistr : famDistr Seed
  queryImpl : (κ : ℕ) -> Seed κ -> QueryImpl (Spec κ) (OptionT PMF)

def prodImpl {spec1 : OracleSpec X1} {spec2 : OracleSpec X2} (impl1 : QueryImpl spec1 M) (impl2 : QueryImpl spec2 M) : QueryImpl (spec1 ++ₒ spec2) M := {
  impl
  | OracleSpec.OracleQuery.query (Sum.inl a) x => impl1.impl (OracleSpec.OracleQuery.query a x)
  | OracleSpec.OracleQuery.query (Sum.inr b) x => impl2.impl (OracleSpec.OracleQuery.query b x)
}

lemma prodImplL {spec1 : OracleSpec X1} {spec2 : OracleSpec X2} (impl1 : QueryImpl spec1 M) (impl2 : QueryImpl spec2 M) (a : X1) (x : spec1.domain a)
: (prodImpl impl1 impl2).impl (OracleSpec.OracleQuery.query (Sum.inl a) x) =
  impl1.impl (OracleSpec.OracleQuery.query a x) :=
  by
    delta prodImpl
    simp []


lemma prodImplR {spec1 : OracleSpec X1} {spec2 : OracleSpec X2} (impl1 : QueryImpl spec1 M) (impl2 : QueryImpl spec2 M) (a : X2) (x : spec2.domain a)
: (prodImpl impl1 impl2).impl (OracleSpec.OracleQuery.query (Sum.inr a) x) =
  impl2.impl (OracleSpec.OracleQuery.query a x) :=
  by
    delta prodImpl
    simp []

noncomputable
def addRandom (impl : QueryImpl spec (OptionT PMF)) : QueryImpl (withRandom spec) (OptionT PMF) :=
  prodImpl randImpl impl


-- The computations on oracles are already defined in the VCVio as `OracleComp`. We extend this definition
-- by the security parameter κ.

def famOracleComp {I : Type} (Spec : ℕ -> OracleSpec I) (Output : ℕ -> Type) := (κ : ℕ) -> OracleComp (withRandomI Spec κ) (Output κ)

-- In order to define computational indistinguishability, we need to talk about polynomial time, and negligible probabilities.
-- We define negligible functions directly:

def negl (f : ℕ -> NNReal) : Prop :=
  ∀ k, ∃ (B : ℝ), ∀ i, (f i) * (i^k) <= B

-- We use a slightly non-standard definition of negligible function (to avoid additional quantifiers),
-- so we briefly explain its equivalence with the standard one.
--
-- Standard (cryptographic) definition:
--   ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n * n^k ≤ 1
--
-- Let us now show two implications:
--
-- (Standard ⇒ our bounded form)
-- Assume: ∀ k, ∃ N, ∀ n ≥ N, f n * n^k ≤ 1.
-- Fix k and obtain N from the assumption. Define B as maximum of f n * n^k for n ∈ {0, ..., N}, but at least 1.
-- Then for `n ≥ N` we have `f n * n^k ≤ 1 ≤ B`, and for `n < N` we have
-- `f n * n^k ≤ max_{0 ≤ m < N} f m * m^k ≤ B`.
--
-- (Our bounded form ⇒ standard)
-- Assume our definition:
--   ∀ k : ℕ, ∃ B : ℝ, ∀ n : ℕ, f n * n^k ≤ B.
-- Fix k. Apply the assumption to `k+1` to obtain `B` such that
--   ∀ n, f n * n^(k+1) ≤ B.
-- It follows that:
--   ∀ n, f n * n^k ≤ B / n.
-- Let N be larger than B.
-- Then for any `n ≥ N` we have `n ≥ B`. It follows that
--   f n * n^k ≤ B / n ≤ 1.

-- On the other hand we do not want to define polynomial time directly, but rather abstractly as a predicate
-- on a family of oracle computations. Later we will axiomatize, some properties that we need in our proof.

def PolyFamOracleCompPred : Type _ :=
  {I : Type} -> {Spec : ℕ -> OracleSpec I} -> {Output : ℕ -> Type} -> famOracleComp Spec Output -> Prop

-- Next, we can use any predicate `PolyFamOracleCompPred` to define a polynomial family of non-oracle computations.
-- This is because every `famComp` can be seen as a `famOracleComp` with a single oracle call to get the input.

def simpleCompSpec (Input : Type) : OracleSpec Unit := fun _ => (Unit, Input)
def getInputArg (Input : ℕ → Type) (κ : ℕ):  OracleSpec.OracleQuery (withRandomI (fun κ ↦ simpleCompSpec (Input κ)) κ) (Input κ) :=
  OracleSpec.query (Sum.inr ()) ()

noncomputable
def simpleCompAsGenComp (simpleComp : famComp Input Output)
  : famOracleComp (fun κ => simpleCompSpec (Input κ)) Output :=
  fun κ => do
      let (x : Input κ) <- getInputArg Input κ
      let ret <- sample (simpleComp κ x)
      return ret

-- Now, using `simpleCompAsGenComp`, we define `polyTimeFamComp`.
def polyTimeFamComp (polyTime : PolyFamOracleCompPred) (o : famComp Input Output) : Prop :=
  polyTime (simpleCompAsGenComp o)

-- Now, we are ready to define computational indistinguishability for families of distributions.
-- We start by showing how to apply `famComp` to a `famDistr` to get another `famDistr`.

noncomputable
def compToDistrSimple {Input : ℕ -> Type} (input : famDistr Input) (o : famComp Input Output) (κ : ℕ) : OptionT PMF (Output κ) :=
  do
    let z <- input κ
    o κ z

-- Next, we define a function the get the probability of a given element in the distribution.
-- The type NNReal denotes the set [0, +inf] (this is is because how Lean defines PMF), but we can show that +inf cannot happen.

def getPMF (r : PMF X) (x : X) : NNReal := (r x).toNNReal -- toNNReal map +inf to zero. Lemma below show that this is never happens here.

lemma pmf_non_inf (r : PMF X) (x : X) : getPMF r x = r x :=
  by
  simp [getPMF]
  have : r x ≠ ⊤ := by
    apply PMF.apply_ne_top
  exact ENNReal.coe_toNNReal this

-- Next, we define the distance between two NNReal values.

def distance (x y : NNReal) : NNReal := ⟨dist x y, dist_nonneg⟩

noncomputable
def advantage (x y : ℕ → PMF (Option Bool)) : ℕ → NNReal :=
  fun κ =>
    distance (getPMF (x κ) (some True)) (getPMF (y κ) (some True))


-- Now, we can define indistinguishability of two families of distributions. It states that for every
-- poly-time `distinguisher` (a family of computations that returns boolean). The distance between
-- `distinguisher distr1` and `distinguisher distr2` is negligible.

noncomputable
def CompIndistinguishabilityDistr
  (IsPolyTime : PolyFamOracleCompPred)
  (distr1 distr2 : famDistr Domain) : Prop :=
  forall distingisher : famComp Domain (fun _ => Bool),
    (polyTimeFamComp IsPolyTime distingisher) ->
    negl (advantage (compToDistrSimple distr1 distingisher) (compToDistrSimple distr2 distingisher))


noncomputable
def CompIndistinguishabilityStrict
  (IsPolyTime : PolyFamOracleCompPred)
  {Domain : ℕ -> Type}
  (distr1 distr2 : famDistrStrict Domain) :=
  CompIndistinguishabilityDistr IsPolyTime (famDistrLift distr1) (famDistrLift distr2)

-- Finally, we want to define computational indistinguishability of two families of seeded oracles.
-- We start by showing how to apply `famOracleComp` to `famSeededOracle` to get a family of distribution.
-- Since OracleComputations can always fail in VCVio, we use `OptionT PMF` to represent the output of the computation.

noncomputable
def liftComp (c : OracleComp Spec (PMF X)) :  OracleComp Spec (OptionT PMF X) :=
  do
    let x <- c
    return (liftM x)


noncomputable
def compToDistrGen {I : Type} {Spec : ℕ -> OracleSpec I}
  {Output : ℕ -> Type}
  (oracle : famSeededOracle Spec)
  (o : famOracleComp Spec Output) (κ : ℕ)
  : (OptionT PMF (Output κ)) :=
  do
    let seed <- oracle.seedDistr κ
    -- in fact, "optionT" inside is never a none, due to use of liftComp
    OracleComp.simulateQ (addRandom (oracle.queryImpl κ seed)) (o κ)


-- Now, we can define computational indistinguishability of two families of seeded oracles, by saying
-- that there is no poly-time distinguisher that can distinguish between them with non-negligible probability.


noncomputable
def CompIndistinguishabilitySeededOracle
  (IsPolyTime : PolyFamOracleCompPred)
  (o1 o2 : famSeededOracle Spec)
  : Prop :=
    -- All distinguishers ...
    ∀ distinguisher : famOracleComp Spec (fun _ => Bool),
    -- ... that run in polynomial time ...
    (IsPolyTime distinguisher) ->
    -- ... only achieve negligible advantage.
    negl (advantage (compToDistrGen o1 distinguisher) (compToDistrGen o2 distinguisher))

-- def OptionFam (T : ℕ -> Type) : ℕ -> Type := fun κ => Option (T κ)

-- def liftOptionFam {T: ℕ -> Type} (fam : (κ : ℕ) -> T κ) (κ : ℕ): OptionFam T κ := some (fam κ)

-- def liftOptionFamComp {T: ℕ -> Type} (fam : (κ : ℕ) -> T κ) (κ : ℕ): OptionFam T κ := some (fam κ)

noncomputable
def composeOracleCompWithSimpleComp
  (oracleComp : famOracleComp Spec Domain)
  (simpleComp : famComp (Domain) Output)
  : famOracleComp Spec Output := fun κ => do
    let val : (Domain κ) <- oracleComp κ
    let ret <- sample (simpleComp κ val)
    return ret

lemma compositionSemantics {I : Type} {Spec : ℕ -> OracleSpec I}
  {Domain : ℕ -> Type}
  (queryImpl : famSeededOracle Spec)
  (oracleComp : famOracleComp Spec Domain)
  (simpleComp : famComp (Domain) Output)
  : forall κ,
  (compToDistrSimple (compToDistrGen queryImpl oracleComp) simpleComp κ)
  =
  compToDistrGen queryImpl (composeOracleCompWithSimpleComp oracleComp simpleComp) κ
:=
by
  intro κ
  simp [compToDistrSimple, composeOracleCompWithSimpleComp, compToDistrGen, liftComp]
  conv =>
    rhs
    arg 2
    intro seed
    arg 2
    intro val
    simp [addRandom, sample]
    rw [prodImplL]
    simp [randImpl]

def PolyTimeClosedUnderComposition (isPolyTime : PolyFamOracleCompPred) : Prop :=
  forall I (Spec : (κ : ℕ) -> OracleSpec I) Domain Output,
  forall (oracleComp : famOracleComp Spec Domain) (simpleComp : famComp Domain Output),
  isPolyTime oracleComp ->
  polyTimeFamComp isPolyTime simpleComp ->
  isPolyTime (composeOracleCompWithSimpleComp oracleComp simpleComp)
