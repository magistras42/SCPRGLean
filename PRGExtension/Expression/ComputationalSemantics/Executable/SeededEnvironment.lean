import PRGExtension.Expression.ComputationalSemantics.Executable.ExecutableDistribution
import PRGExtension.ComputationalIndistinguishability.Def
import PRGExtension.ComputationalIndistinguishability.Lemmas
import PRGExtension.Expression.ComputationalSemantics.Games

/-!
# Expanding a seed into an environment: the variable-stretch construction

`execToDistr` draws the environment from `uniformOfFintype` — every wire key an independent
uniform `BitVector κ`.  A deployment cannot afford that (`scratch/checks/GarbleMain.lean`'s default mode
does it honestly, and needs `32 · keys` bytes from the OS per circuit); what it does instead is
draw one short seed and expand it.  Expanded keys are **not** uniform — the support has size at
most `2 ^ κ` — so `execToDistr_eq`, and hence `garblingSecureExec`, do not apply to a seeded
deployment.  Closing that is a PRF hybrid.

This file starts it, by the route that keeps the development self-contained: build variable
stretch **from the length-doubling PRG the framework already assumes**, rather than assuming a
second primitive.

* `expandKeys` — the sequential (Blum–Micali) construction: emit `prg0 s`, keep `prg1 s` as the
  next state.  `n` blocks of `κ` bits from a `κ`-bit seed, and computable.
* `idealExpand` — the same shape with each step's output drawn uniformly instead of computed.
* **`idealExpand_eq_uniform`** — the ideal expansion *is* the uniform distribution.  This is the
  endpoint the hybrid argument telescopes to, and it is proved here.
* `hybridExpand` — the hybrid family: the first `i` blocks ideal, the rest generated.  Its two
  endpoints are proved (`hybridExpand_zero`, `hybridExpand_full`).

**What remains** is the step: consecutive hybrids are computationally indistinguishable, by one
application of `prgSchemeSecure`, and `n` of those compose.  That needs the game machinery in
`ComputationalSemantics/Games.lean` and the advantage arithmetic, and is stated here as
`VariableStretchSecure` rather than proved.  `FUTURE-WORK.md` scopes the remainder.

Note the shape of the final result: it is an *indistinguishability*, not an equality.  The
support of a seeded environment is exponentially smaller than the uniform one, so no equational
refinement of the kind `execToDistr_eq` provides is available here — which is exactly why the
gap exists.
-/

namespace PRG

open PMF

variable {κ : ℕ}

/-! ## The construction -/

/-- **Sequential expansion.**  At each step emit `prg0 s` and carry `prg1 s` forward, giving `n`
blocks of `κ` bits from a `κ`-bit seed.  This is the standard length-doubling-to-variable-stretch
construction, and it is computable — a deployment would call this. -/
def expandKeys (prg : prgFunctions κ) (s : BitVector κ) : (n : ℕ) → Fin n → BitVector κ
  | 0 => Fin.elim0
  | n + 1 => Fin.cons (prg.prg0 s) (expandKeys prg (prg.prg1 s) n)

/-- The ideal counterpart: each step's output block is drawn uniformly, and the state it would
have carried is discarded — in the ideal world the next step does not depend on it. -/
noncomputable def idealExpand (κ : ℕ) : (n : ℕ) → PMF (Fin n → BitVector κ)
  | 0 => PMF.pure Fin.elim0
  | n + 1 => (uniformOfFintype (BitVector κ)).bind fun a =>
      (idealExpand κ n).map fun r => Fin.cons a r

/-! ## The endpoint: ideal expansion is uniform

The whole hybrid argument is a walk from `expandKeys` to a uniform environment.  This is the far
end of that walk, and unlike the steps it is an *equality*, provable now.
-/

/-- **The ideal expansion is exactly the uniform distribution.**  Proved by induction with
`uniformFinArrow_cons` (`Core/UniformProduct.lean`): drawing one block and then an independent
block of `n` is drawing a uniform block of `n + 1`. -/
theorem idealExpand_eq_uniform (κ : ℕ) :
    ∀ n : ℕ, idealExpand κ n = uniformOfFintype (Fin n → BitVector κ)
  | 0 => by
      refine PMF.ext fun f => ?_
      have hf : f = Fin.elim0 := funext fun i => i.elim0
      subst hf
      simp [idealExpand]
  | n + 1 => by
      rw [idealExpand, uniformFinArrow_cons]
      exact congrArg _ (funext fun a => congrArg _ (idealExpand_eq_uniform κ n))

/-! ## The hybrid family

`hybridExpand prg i n s` draws the first `i` blocks the ideal way and generates the remaining
`n - i` from the state.  `i = 0` is the real construction, `i = n` is uniform, and the argument
that has to be supplied is that consecutive hybrids are indistinguishable.
-/

/-- The first `i` blocks ideal, the rest generated from the carried state. -/
noncomputable def hybridExpand (prg : prgFunctions κ) :
    (i n : ℕ) → BitVector κ → PMF (Fin n → BitVector κ)
  | _, 0, _ => PMF.pure Fin.elim0
  | 0, n + 1, s => PMF.pure (expandKeys prg s (n + 1))
  | i + 1, n + 1, _ => (uniformOfFintype (BitVector κ)).bind fun a =>
      (uniformOfFintype (BitVector κ)).bind fun s' =>
        (hybridExpand prg i n s').map fun r => Fin.cons a r

/-- Endpoint one: no ideal steps is the real construction. -/
theorem hybridExpand_zero (prg : prgFunctions κ) (n : ℕ) (s : BitVector κ) :
    hybridExpand prg 0 n s = PMF.pure (expandKeys prg s n) := by
  cases n with
  | zero => simp [hybridExpand, expandKeys]
  | succ m => rw [hybridExpand]

/-- Endpoint two: **all steps ideal is exactly uniform.**  The discarded state draws vanish, and
what is left is `idealExpand`. -/
theorem hybridExpand_full (prg : prgFunctions κ) :
    ∀ (n : ℕ) (s : BitVector κ),
      hybridExpand prg n n s = uniformOfFintype (Fin n → BitVector κ)
  | 0, s => by
      refine PMF.ext fun f => ?_
      have hf : f = Fin.elim0 := funext fun i => i.elim0
      subst hf
      simp [hybridExpand]
  | n + 1, s => by
      rw [hybridExpand, uniformFinArrow_cons]
      refine congrArg _ (funext fun a => ?_)
      -- name the cons map, so `Fin.cons`'s motive is pinned rather than inferred twice
      set f : (Fin n → BitVector κ) → (Fin (n + 1) → BitVector κ) := fun r => Fin.cons a r
      calc (uniformOfFintype (BitVector κ)).bind (fun s' => (hybridExpand prg n n s').map f)
          = (uniformOfFintype (BitVector κ)).bind
              (fun _ => (uniformOfFintype (Fin n → BitVector κ)).map f) := by
            refine congrArg _ (funext fun s' => ?_)
            rw [hybridExpand_full prg n s']
        _ = _ := PMF.bind_const _ _

/-! ## The seeded hybrids

`hybridExpand` takes the state as a parameter, which is what makes the recursion work; but the
statement the reduction needs has the *initial seed drawn uniformly* — with a fixed, known seed
the real expansion is a point mass on a value the distinguisher can recompute, and no
indistinguishability claim could hold.
-/

/-- Hybrid `i`, with the initial seed drawn uniformly.  `i = 0` is what a seeded deployment
computes; `i = n` is uniform. -/
noncomputable def hybridSeeded (prg : prgFunctions κ) (i n : ℕ) : PMF (Fin n → BitVector κ) :=
  (uniformOfFintype (BitVector κ)).bind fun s => hybridExpand prg i n s

/-- **The real end**: no ideal steps is exactly "draw a seed, expand it" — the deployment. -/
theorem hybridSeeded_zero (prg : prgFunctions κ) (n : ℕ) :
    hybridSeeded prg 0 n
      = (uniformOfFintype (BitVector κ)).bind fun s => PMF.pure (expandKeys prg s n) := by
  refine congrArg _ (funext fun s => ?_)
  exact hybridExpand_zero prg n s

/-- **The ideal end**: all steps ideal is uniform, whatever the seed was. -/
theorem hybridSeeded_full (prg : prgFunctions κ) (n : ℕ) :
    hybridSeeded prg n n = uniformOfFintype (Fin n → BitVector κ) := by
  rw [hybridSeeded]
  have h : ∀ s : BitVector κ,
      hybridExpand prg n n s = uniformOfFintype (Fin n → BitVector κ) :=
    fun s => hybridExpand_full prg n s
  simp only [h]
  exact PMF.bind_const _ _

/-- **The recursion the reduction mirrors.**  One more ideal step at the head is: draw the block,
draw the state — and the drawn state is exactly the uniform *initial seed* of the shorter
hybrid.  That is why a single oracle query at the head suffices. -/
theorem hybridSeeded_succ (prg : prgFunctions κ) (i m : ℕ) :
    hybridSeeded prg (i + 1) (m + 1)
      = (uniformOfFintype (BitVector κ)).bind fun a =>
          (hybridSeeded prg i m).map fun r => Fin.cons a r := by
  rw [hybridSeeded]
  have h : ∀ s : BitVector κ, hybridExpand prg (i + 1) (m + 1) s
      = (uniformOfFintype (BitVector κ)).bind fun a =>
          (hybridSeeded prg i m).map fun r => Fin.cons a r := by
    intro s
    rw [hybridExpand, hybridSeeded]
    refine congrArg _ (funext fun a => ?_)
    rw [PMF.map_bind]
  simp only [h]
  exact PMF.bind_const _ _

/-! ## The reduction

One oracle query, placed at position `i`.  The `i` blocks before it the reduction draws itself;
everything after it is the deterministic expansion from the query's second component.  Against
the **real** oracle the query answers `(prg0 seed, prg1 seed)` for a uniform seed, so the result
is hybrid `i`; against the **ideal** oracle it answers a uniform pair, so the result is hybrid
`i + 1`.  That is the whole argument, and `IndistinguishabilityByReduction` turns it into the
step.
-/

/-- The reduction for the step from hybrid `i` to hybrid `i + 1`. -/
noncomputable def expandRed (prg : prgScheme) (κ : ℕ) : (i n : ℕ) →
    OracleComp (withRandom (oracleSpecPrg κ)) (Fin n → BitVector κ)
  | _, 0 => pure Fin.elim0
  | 0, m + 1 => do
      let r ← (withRandom (oracleSpecPrg κ)).query (Sum.inr ()) ()
      pure (Fin.cons r.1 (expandKeys (prg κ) r.2 m))
  | i + 1, m + 1 => do
      let a ← sample (PMF.uniformOfFintype (BitVector κ))
      let rest ← expandRed prg κ i m
      pure (Fin.cons a rest)

/-- What the reduction computes against the **real** oracle, which holds a fixed `seed` and
answers every query with `(prg0 seed, prg1 seed)`. -/
noncomputable def realSim (prg : prgScheme) (κ : ℕ) (seed : BitVector κ) :
    (i n : ℕ) → PMF (Fin n → BitVector κ)
  | _, 0 => PMF.pure Fin.elim0
  | 0, m + 1 => PMF.pure (expandKeys (prg κ) seed (m + 1))
  | i + 1, m + 1 => (uniformOfFintype (BitVector κ)).bind fun a =>
      (realSim prg κ seed i m).map fun r => Fin.cons a r

/-- What it computes against the **ideal** oracle, which answers every query with a fixed
uniformly drawn pair `r`. -/
noncomputable def idealSim (prg : prgScheme) (κ : ℕ) (r : BitVector κ × BitVector κ) :
    (i n : ℕ) → PMF (Fin n → BitVector κ)
  | _, 0 => PMF.pure Fin.elim0
  | 0, m + 1 => PMF.pure (Fin.cons r.1 (expandKeys (prg κ) r.2 m))
  | i + 1, m + 1 => (uniformOfFintype (BitVector κ)).bind fun a =>
      (idealSim prg κ r i m).map fun r' => Fin.cons a r'

/-! ### Averaging over the oracle's seed gives the hybrids

The reduction's own draws and the oracle's seed are independent, so they commute
(`PMF.bind_comm`) — which is what lets the oracle's seed slide into the position of the
sub-hybrid's *initial* seed.
-/

/-- Real oracle, seed averaged: hybrid `i`. -/
theorem realSim_seeded (prg : prgScheme) (κ : ℕ) :
    ∀ i n, ((uniformOfFintype (BitVector κ)).bind fun seed => realSim prg κ seed i n)
      = hybridSeeded (prg κ) i n
  | _, 0 => by
      rw [hybridSeeded]
      simp [realSim, hybridExpand]
  | 0, m + 1 => by
      rw [hybridSeeded_zero]
      rfl
  | i + 1, m + 1 => by
      rw [hybridSeeded_succ, ← realSim_seeded prg κ i m]
      simp only [realSim]
      rw [PMF.bind_comm]
      refine congrArg _ (funext fun a => ?_)
      rw [PMF.map_bind]

/-- The ideal oracle's seed distribution is the uniform distribution on pairs.  Written as two
draws in `Games.lean` to mirror the reduction's own sampling; `uniformOfFintype_prod` is
exactly the fact that the two agree. -/
theorem idealSeedDistr_eq (κ : ℕ) :
    (do
      let r0 ← PMF.uniformOfFintype (BitVector κ)
      let r1 ← PMF.uniformOfFintype (BitVector κ)
      PMF.pure (r0, r1))
      = uniformOfFintype (BitVector κ × BitVector κ) := by
  show ((uniformOfFintype (BitVector κ)).bind fun r0 =>
        (uniformOfFintype (BitVector κ)).bind fun r1 => PMF.pure (r0, r1))
      = uniformOfFintype (BitVector κ × BitVector κ)
  rw [uniformOfFintype_prod]
  rfl

/-- Ideal oracle, answer averaged: hybrid `i + 1`. -/
theorem idealSim_seeded (prg : prgScheme) (κ : ℕ) :
    ∀ i n, ((uniformOfFintype (BitVector κ × BitVector κ)).bind fun r => idealSim prg κ r i n)
      = hybridSeeded (prg κ) (i + 1) n
  | _, 0 => by
      rw [hybridSeeded]
      simp [idealSim, hybridExpand]
  | 0, m + 1 => by
      rw [hybridSeeded_succ, hybridSeeded_zero, ← idealSeedDistr_eq]
      simp only [idealSim, Bind.bind, Pure.pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind,
        PMF.pure_map]
  | i + 1, m + 1 => by
      rw [hybridSeeded_succ, ← idealSim_seeded prg κ i m]
      simp only [idealSim]
      rw [PMF.bind_comm]
      refine congrArg _ (funext fun a => ?_)
      rw [PMF.map_bind]

/-! ### Simulating the reduction against each oracle -/

/-- Lifting a point mass into `OptionT PMF` is the point mass.  Needed at every leaf of the
simulation, since the reduction ends in `pure`. -/
theorem liftM_pure_pmf {α : Type} (x : α) : (liftM (PMF.pure x) : OptionT PMF α) = Pure.pure x := by
  simp [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk]
  rfl

/-- `liftM` is a monad morphism on the fragment the reduction uses: a sampled draw followed by a
lifted continuation is the lift of the combined draw. -/
theorem liftM_bind_pmf {α β : Type} (p : PMF α) (q : α → PMF β) :
    ((liftM p : OptionT PMF α) >>= fun a => (liftM (q a) : OptionT PMF β))
      = liftM (p.bind q) := by
  simp only [liftM, monadLift, MonadLift.monadLift, OptionT.lift,
    Bind.bind, Pure.pure, OptionT.bind, OptionT.mk, OptionT.pure, OptionT.run,
    PMF.pure_bind, Option.getM, PMF.bind_bind]

/-- Against the real oracle the reduction computes `realSim`. -/
theorem expandSimulateReal (prg : prgScheme) (κ : ℕ) (seed : BitVector κ) :
    ∀ i n, OracleComp.simulateQ (addRandom ((seededPrgRealOracle prg).queryImpl κ seed))
             (expandRed prg κ i n)
      = liftM (realSim prg κ seed i n)
  | _, 0 => by simp [expandRed, realSim, OracleComp.simulateQ_pure, liftM_pure_pmf]
  | 0, m + 1 => by
      simp only [expandRed, realSim, addRandom, seededPrgRealOracle, prgRealOracleImpl,
        OracleComp.simulateQ_bind, OracleComp.simulateQ_query, Function.comp_def]
      rw [prodImplR]
      simp [expandKeys, OracleComp.simulateQ_pure, liftM_pure_pmf]
  | i + 1, m + 1 => by
      have IH := expandSimulateReal prg κ seed i m
      simp only [addRandom] at IH
      simp only [expandRed, realSim, addRandom, sample,
        OracleComp.simulateQ_bind, OracleComp.simulateQ_query, Function.comp_def]
      rw [prodImplL]
      simp only [IH]
      simp only [randImpl, OracleComp.simulateQ_pure, ← liftM_pure_pmf, liftM_bind_pmf]
      rfl

/-- Against the ideal oracle the reduction computes `idealSim`. -/
theorem expandSimulateIdeal (prg : prgScheme) (κ : ℕ) (r : BitVector κ × BitVector κ) :
    ∀ i n, OracleComp.simulateQ (addRandom (seededPrgIdealOracle.queryImpl κ r))
             (expandRed prg κ i n)
      = liftM (idealSim prg κ r i n)
  | _, 0 => by simp [expandRed, idealSim, OracleComp.simulateQ_pure, liftM_pure_pmf]
  | 0, m + 1 => by
      simp only [expandRed, idealSim, addRandom, seededPrgIdealOracle, prgIdealOracleImpl,
        OracleComp.simulateQ_bind, OracleComp.simulateQ_query, Function.comp_def]
      rw [prodImplR]
      simp [OracleComp.simulateQ_pure, liftM_pure_pmf]
  | i + 1, m + 1 => by
      have IH := expandSimulateIdeal prg κ r i m
      simp only [addRandom] at IH
      simp only [expandRed, idealSim, addRandom, sample,
        OracleComp.simulateQ_bind, OracleComp.simulateQ_query, Function.comp_def]
      rw [prodImplL]
      simp only [IH]
      simp only [randImpl, OracleComp.simulateQ_pure, ← liftM_pure_pmf, liftM_bind_pmf]
      rfl

/-! ### The reduction realises the two hybrids -/

/-- Against the real oracle: hybrid `i`. -/
theorem expandRedRealEq (prg : prgScheme) (i n : ℕ) :
    compToDistrGen (seededPrgRealOracle prg) (fun κ => expandRed prg κ i n)
      = famDistrLift (fun κ => hybridSeeded (prg κ) i n) := by
  delta famDistrLift
  delta compToDistrGen
  ext1 κ
  conv =>
    lhs
    arg 2
    intro seed
    rw [expandSimulateReal]
  dsimp only
  rw [← realSim_seeded prg κ i n]
  exact liftM_bind_pmf _ _

/-- Against the ideal oracle: hybrid `i + 1`. -/
theorem expandRedIdealEq (prg : prgScheme) (i n : ℕ) :
    compToDistrGen seededPrgIdealOracle (fun κ => expandRed prg κ i n)
      = famDistrLift (fun κ => hybridSeeded (prg κ) (i + 1) n) := by
  delta famDistrLift
  delta compToDistrGen
  ext1 κ
  conv =>
    lhs
    arg 2
    intro r
    rw [expandSimulateIdeal]
  dsimp only
  rw [← idealSim_seeded prg κ i n, ← idealSeedDistr_eq κ]
  rw [← liftM_bind_pmf]
  simp only [seededPrgIdealOracle, bind_assoc, pure_bind]
  simp only [liftM, monadLift, MonadLift.monadLift, OptionT.lift,
    Bind.bind, Pure.pure, OptionT.bind, OptionT.mk, OptionT.pure, OptionT.run,
    PMF.pure_bind, Option.getM, PMF.bind_bind]

/-! ## The step, and the whole walk

`IndistinguishabilityByReduction` converts the two realisation lemmas into one hybrid step, and
`indTrans` walks the `n` steps from the real expansion to the uniform environment.
-/

/-- The reduction runs in polynomial time.  Assumed, in exactly the form and for exactly the
reason `PrgReductionPolyTime` is (`SoundnessProof/HidingOnePrgSeed.lean`): the reduction draws
`i` blocks, makes one query, and runs `expandKeys`, so this is derivable from LM18 Definition 1's
efficiency requirement in any cost model that has one. -/
def ExpandReductionPolyTime (IsPolyTime : PolyFamOracleCompPred) (prg : prgScheme) : Prop :=
  ∀ i n : ℕ, IsPolyTime (fun κ => expandRed prg κ i n)

/-- **The hybrid step.**  Consecutive hybrids are indistinguishable, by one application of PRG
security: the reduction realises hybrid `i` against the real oracle and hybrid `i + 1` against
the ideal one. -/
theorem hybridStep (IsPolyTime : PolyFamOracleCompPred)
    (HisPoly : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
    (prg : prgScheme)
    (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
    (Hred : ExpandReductionPolyTime (fun {_ _ _} => IsPolyTime) prg) (i n : ℕ) :
    CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (fun κ => hybridSeeded (prg κ) i n))
      (famDistrLift (fun κ => hybridSeeded (prg κ) (i + 1) n)) := by
  rw [← expandRedRealEq prg i n, ← expandRedIdealEq prg i n]
  exact IndistinguishabilityByReduction (fun {_ _ _} => IsPolyTime) HisPoly _ _ HPrgSecure _
    (Hred i n)

/-- **Variable stretch from length doubling.**  The sequential expansion of a uniform seed is
computationally indistinguishable from a uniform environment — `n` hybrid steps, composed.

This is what a seeded deployment needs: `scratch/checks/GarbleMain.lean --seeded` draws one seed and
expands it, and this says the environment it obtains is as good as the uniform one the theorems
quantify over. -/
theorem expandKeys_indist_uniform (IsPolyTime : PolyFamOracleCompPred)
    (HisPoly : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
    (prg : prgScheme)
    (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
    (Hred : ExpandReductionPolyTime (fun {_ _ _} => IsPolyTime) prg) (n : ℕ) :
    CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (fun κ => (uniformOfFintype (BitVector κ)).bind fun s =>
        PMF.pure (expandKeys (prg κ) s n)))
      (famDistrLift (fun κ => uniformOfFintype (Fin n → BitVector κ))) := by
  have walk : ∀ j, CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (fun κ => hybridSeeded (prg κ) 0 n))
      (famDistrLift (fun κ => hybridSeeded (prg κ) j n)) := by
    intro j
    induction j with
    | zero => exact indRfl _
    | succ k ih =>
        exact indTrans _ ih (hybridStep IsPolyTime HisPoly prg HPrgSecure Hred k n)
  have hend := walk n
  simp only [hybridSeeded_full, hybridSeeded_zero] at hend
  exact hend

/-! ## Post-processing, without a new assumption

The composition with garbling needs the expanded key block to be *used* — fed to the evaluator —
and indistinguishability preserved under that use.  Rather than assume a closure property
("indistinguishability survives poly-time post-processing"), the post-processing goes *inside the
reduction*: `expandRedWith` runs `expandRed` and then samples `post`.  The poly-time hypothesis
is then about the concrete reduction that includes `post`, which is the same kind of hypothesis
the development already carries, rather than a new axiom about the adversary class.
-/

/-- The reduction, with a continuation applied to the key block it produces. -/
noncomputable def expandRedWith (prg : prgScheme) (κ : ℕ) {Out : Type}
    (post : (Fin n → BitVector κ) → PMF Out) (i : ℕ) :
    OracleComp (withRandom (oracleSpecPrg κ)) Out := do
  let block ← expandRed prg κ i n
  sample (post block)

/-- Simulating the post-processed reduction against the real oracle. -/
theorem expandWithSimulateReal (prg : prgScheme) (κ : ℕ) {Out : Type} (n i : ℕ)
    (post : (Fin n → BitVector κ) → PMF Out) (seed : BitVector κ) :
    OracleComp.simulateQ (addRandom ((seededPrgRealOracle prg).queryImpl κ seed))
        (expandRedWith prg κ post i)
      = liftM ((realSim prg κ seed i n).bind post) := by
  simp only [expandRedWith, OracleComp.simulateQ_bind, expandSimulateReal, sample,
    OracleComp.simulateQ_query, Function.comp_def]
  simp only [addRandom]
  conv =>
    lhs
    arg 2
    intro x
    rw [prodImplL]
  simp only [randImpl]
  rw [liftM_bind_pmf]

/-- Simulating the post-processed reduction against the ideal oracle. -/
theorem expandWithSimulateIdeal (prg : prgScheme) (κ : ℕ) {Out : Type} (n i : ℕ)
    (post : (Fin n → BitVector κ) → PMF Out) (r : BitVector κ × BitVector κ) :
    OracleComp.simulateQ (addRandom (seededPrgIdealOracle.queryImpl κ r))
        (expandRedWith prg κ post i)
      = liftM ((idealSim prg κ r i n).bind post) := by
  simp only [expandRedWith, OracleComp.simulateQ_bind, expandSimulateIdeal, sample,
    OracleComp.simulateQ_query, Function.comp_def]
  simp only [addRandom]
  conv =>
    lhs
    arg 2
    intro x
    rw [prodImplL]
  simp only [randImpl]
  rw [liftM_bind_pmf]

/-- Against the real oracle: hybrid `i`, post-processed. -/
theorem expandRedWithRealEq (prg : prgScheme) {Out : ℕ → Type} (n i : ℕ)
    (post : (κ : ℕ) → (Fin n → BitVector κ) → PMF (Out κ)) :
    compToDistrGen (seededPrgRealOracle prg) (fun κ => expandRedWith prg κ (post κ) i)
      = famDistrLift (fun κ => (hybridSeeded (prg κ) i n).bind (post κ)) := by
  delta famDistrLift
  delta compToDistrGen
  ext1 κ
  conv =>
    lhs
    arg 2
    intro seed
    rw [expandWithSimulateReal]
  dsimp only
  rw [← realSim_seeded prg κ i n, PMF.bind_bind]
  exact liftM_bind_pmf _ _

/-- Against the ideal oracle: hybrid `i + 1`, post-processed. -/
theorem expandRedWithIdealEq (prg : prgScheme) {Out : ℕ → Type} (n i : ℕ)
    (post : (κ : ℕ) → (Fin n → BitVector κ) → PMF (Out κ)) :
    compToDistrGen seededPrgIdealOracle (fun κ => expandRedWith prg κ (post κ) i)
      = famDistrLift (fun κ => (hybridSeeded (prg κ) (i + 1) n).bind (post κ)) := by
  delta famDistrLift
  delta compToDistrGen
  ext1 κ
  conv =>
    lhs
    arg 2
    intro r
    rw [expandWithSimulateIdeal]
  dsimp only
  rw [← idealSim_seeded prg κ i n, PMF.bind_bind, ← idealSeedDistr_eq κ]
  rw [← liftM_bind_pmf]
  simp only [seededPrgIdealOracle, bind_assoc, pure_bind]
  simp only [liftM, monadLift, MonadLift.monadLift, OptionT.lift,
    Bind.bind, Pure.pure, OptionT.bind, OptionT.mk, OptionT.pure, OptionT.run,
    PMF.pure_bind, Option.getM, PMF.bind_bind]

/-- The post-processed reduction runs in polynomial time.  Same standing as
`ExpandReductionPolyTime`: a cost-model obligation about a concrete computation, not a new
assumption about the adversary class. -/
def ExpandReductionWithPolyTime (IsPolyTime : PolyFamOracleCompPred) (prg : prgScheme)
    {Out : ℕ → Type} (n : ℕ) (post : (κ : ℕ) → (Fin n → BitVector κ) → PMF (Out κ)) : Prop :=
  ∀ i : ℕ, IsPolyTime (fun κ => expandRedWith prg κ (post κ) i)

/-- The hybrid step, post-processed. -/
theorem hybridStepWith (IsPolyTime : PolyFamOracleCompPred)
    (HisPoly : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
    (prg : prgScheme) (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
    {Out : ℕ → Type} (n : ℕ) (post : (κ : ℕ) → (Fin n → BitVector κ) → PMF (Out κ))
    (Hred : ExpandReductionWithPolyTime (fun {_ _ _} => IsPolyTime) prg n post) (i : ℕ) :
    CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (fun κ => (hybridSeeded (prg κ) i n).bind (post κ)))
      (famDistrLift (fun κ => (hybridSeeded (prg κ) (i + 1) n).bind (post κ))) := by
  rw [← expandRedWithRealEq prg n i post, ← expandRedWithIdealEq prg n i post]
  exact IndistinguishabilityByReduction (fun {_ _ _} => IsPolyTime) HisPoly _ _ HPrgSecure _
    (Hred i)

/-- **Variable stretch, usable.**  Expanding a uniform seed and then *using* the result is
indistinguishable from drawing the environment uniformly and using it.  This is the form the
garbling composition consumes. -/
theorem expandKeys_indist_uniform_post (IsPolyTime : PolyFamOracleCompPred)
    (HisPoly : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
    (prg : prgScheme) (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
    {Out : ℕ → Type} (n : ℕ) (post : (κ : ℕ) → (Fin n → BitVector κ) → PMF (Out κ))
    (Hred : ExpandReductionWithPolyTime (fun {_ _ _} => IsPolyTime) prg n post) :
    CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (fun κ => ((uniformOfFintype (BitVector κ)).bind fun s =>
        PMF.pure (expandKeys (prg κ) s n)).bind (post κ)))
      (famDistrLift (fun κ => (uniformOfFintype (Fin n → BitVector κ)).bind (post κ))) := by
  have walk : ∀ j, CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (fun κ => (hybridSeeded (prg κ) 0 n).bind (post κ)))
      (famDistrLift (fun κ => (hybridSeeded (prg κ) j n).bind (post κ))) := by
    intro j
    induction j with
    | zero => exact indRfl _
    | succ k ih =>
        exact indTrans _ ih (hybridStepWith IsPolyTime HisPoly prg HPrgSecure n post Hred k)
  have hend := walk n
  simp only [hybridSeeded_full, hybridSeeded_zero] at hend
  exact hend

/-! ## What is assumed, and what is not

Nothing about variable stretch is assumed any more: `expandKeys_indist_uniform` is proved from
`prgSchemeSecure` — the framework's existing length-doubling assumption — and nothing else.

The one hypothesis carried along is `ExpandReductionPolyTime`, that the reduction itself runs in
polynomial time.  That is the same hypothesis, in the same form and for the same reason, that
every other reduction in this development carries (`PrgReductionPolyTime`,
`EncReductionPolyTime`); it is discharged by a cost model, not by cryptography, and
`ComputationalSemantics/PolyTime.lean` is where its siblings are discharged.

What still separates this from a seeded *garbling* theorem: `expandKeys_indist_uniform` says the
expanded environment is indistinguishable from the uniform one, and `garblingSecureExec` says
garbling is secure when the environment *is* uniform.  Composing them needs the environment to
be substituted into `execToDistr`, which is a step of the same kind as the reduction above —
`FUTURE-WORK.md` carries it as the remaining item.
-/

end PRG
