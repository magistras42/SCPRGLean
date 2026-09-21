import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOnePrgSeed

/-!
# Efficiency of the reductions

The framework's `IsPolyTime` is an abstract predicate on families of oracle computations,
with one structural property assumed (`PolyTimeClosedUnderComposition`).  There is no cost
semantics for `OracleComp`, here or in the oracle-computation library, so "this reduction
runs in polynomial time" cannot be *proved* from first principles.  What can be done is to
make the assumption as small and as auditable as possible, and that is what this file does.

Two things were wrong with the inherited treatment.

**The hypotheses were over-strong.**  They read
`∀ enc prg …, IsPolyTime (reductionHidingOneKey enc prg …)` — quantified over *all* schemes.
In any concrete cost model that is false: pick an inefficient encryption scheme and its
reduction is inefficient too.  So every downstream theorem would have become vacuous the
moment `IsPolyTime` was instantiated — the same defect as the `Seed := Unit` bug in
`PrgSecurity.lean`.  `EncReductionPolyTime` and `PrgReductionPolyTime` fix this by fixing
`enc` and `prg`.

**The PRG was never required to be efficient at all.**  LM18 Definition 1 demands
polynomial-time computability; `prgFunctions` is an arbitrary pair of functions.
`EfficientPrg` and `EfficientEnc` state the missing requirement.

`reductionToPrgOracle_polyTime` then *derives* `PrgReductionPolyTime` from two much smaller
claims, using the framework's own composition closure.  The IND-CPA reduction is not handled
the same way here: `reductionToOracle` recurses over the expression making oracle queries, so
the analogous decomposition needs closure under sequencing *two oracle computations*, which
this model does not provide.

That closure — and with it `EncReductionPolyTime` and `EvalEfficiencyFromPrimitives`, both
of which are hypotheses *in this file* — is supplied by `PolyTimeModel` in
`ComputationalSemantics/CostModel.lean`, where both become theorems.  The informal cost
argument they formalise is at the end of `HidingOneKey.lean`.
-/

open PRG
namespace PRG

/-- The environment-sampling-plus-one-query prefix of the PRG reduction. -/
noncomputable def prgEnvSampler {s : Shape} (expr : Expression s)
    (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ) :
    (κ : ℕ) → OracleComp (withRandom (oracleSpecPrg κ))
      ((Fin (prgReductionVars expr targetSeed idx0 idx1) → Bool)
        × (Fin (prgReductionVars expr targetSeed idx0 idx1) → BitVector κ)
        × (BitVector κ × BitVector κ)) := fun κ => do
  let l := prgReductionVars expr targetSeed idx0 idx1
  let bVars ← sample (PMF.uniformOfFintype (Fin l -> Bool))
  let kVars ← sample (PMF.uniformOfFintype (Fin l -> BitVector κ))
  let r ← (withRandom (oracleSpecPrg κ)).query (Sum.inr ()) ()
  return (bVars, kVars, r)

/-- The pure (oracle-free) tail: evaluate the idealised expression in the sampled
    environment.  This is where the *scheme's own* efficiency is all that is needed. -/
noncomputable def prgEvalStep (enc : encryptionScheme) (prg : prgScheme) {s : Shape}
    (expr : Expression s) (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ) :
    famComp (fun κ => (Fin (prgReductionVars expr targetSeed idx0 idx1) → Bool)
                    × (Fin (prgReductionVars expr targetSeed idx0 idx1) → BitVector κ)
                    × (BitVector κ × BitVector κ))
            (fun κ => BitVector (shapeLength κ (enc κ) s)) := fun κ env =>
  evalExpr (enc κ) (prg κ)
    (subst3 idx0 idx1 env.2.2.1 env.2.2.2 (extendFin ones env.2.1))
    (extendFin false env.1)
    (replacePRG targetSeed idx0 idx1 expr)

/-- The PRG reduction *is* "sample an environment, query once, then evaluate". -/
lemma reductionToPrgOracle_decompose (enc : encryptionScheme) (prg : prgScheme)
    {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ) :
    (fun κ => reductionToPrgOracle enc prg expr targetSeed idx0 idx1 κ)
      = composeOracleCompWithSimpleComp (prgEnvSampler expr targetSeed idx0 idx1)
          (prgEvalStep enc prg expr targetSeed idx0 idx1) := by
  funext κ
  simp only [reductionToPrgOracle, composeOracleCompWithSimpleComp, prgEnvSampler,
    prgEvalStep, bind_pure_comp, bind_assoc, Functor.map_map]
  rfl

/--
  **LM18 Definition 1's efficiency requirement for the PRG**, which the inherited model
  omitted entirely: `prgFunctions` was an arbitrary pair of functions with no tie to
  `IsPolyTime`.
-/
def EfficientPrg (IsPolyTime : PolyFamOracleCompPred) (prg : prgScheme) : Prop :=
  polyTimeFamComp IsPolyTime
    (Input := fun κ => BitVector κ) (Output := fun κ => BitVector κ)
    (fun κ seed => PMF.pure ((prg κ).prg0 seed))
  ∧ polyTimeFamComp IsPolyTime
    (Input := fun κ => BitVector κ) (Output := fun κ => BitVector κ)
    (fun κ seed => PMF.pure ((prg κ).prg1 seed))

/-- The corresponding requirement for the encryption scheme. -/
def EfficientEnc (IsPolyTime : PolyFamOracleCompPred) (enc : encryptionScheme) : Prop :=
  ∀ n : ℕ, polyTimeFamComp IsPolyTime
    (Input := fun κ => BitVector κ × BitVector n)
    (Output := fun κ => BitVector ((enc κ).encryptLength n))
    (fun κ km => (enc κ).encrypt km.1 km.2)

/--
**LM18 Definition 1 for the encryption scheme, in the form a cost analysis can consume.**

`EfficientEnc` above fixes the message length `n` independently of `κ`.  That is too weak for
any induction over an expression: at an `Enc` node the message is the value of the
sub-expression, whose length `shapeLength κ (enc κ) s` *grows with* `κ`.  So the requirement
has to range over length *families* — and only over polynomially bounded ones, since a scheme
whose ciphertexts blow up could not be efficient anyway.

This is where `LengthPoly` (`ComputationalSemantics/Def.lean`) earns its keep:
`shapeLength_poly` is what supplies the `PolyLength` side condition at each `Enc` node.
-/
def EfficientEncPoly (IsPolyTime : PolyFamOracleCompPred) (enc : encryptionScheme) : Prop :=
  ∀ (d : ℕ → ℕ), PolyLength d →
    polyTimeFamComp IsPolyTime
      (Input := fun κ => BitVector κ × BitVector (d κ))
      (Output := fun κ => BitVector ((enc κ).encryptLength (d κ)))
      (fun κ km => (enc κ).encrypt km.1 km.2)

/-- The κ-indexed requirement is a strengthening of `EfficientEnc`: take the constant family. -/
theorem EfficientEncPoly.toEfficientEnc {IsPolyTime : PolyFamOracleCompPred}
    {enc : encryptionScheme} (h : EfficientEncPoly IsPolyTime enc) :
    EfficientEnc IsPolyTime enc :=
  fun n => h (fun _ => n) (PolyLength.const n)

/--
  **What the PRG reduction actually needs**: evaluating a *fixed* expression in a supplied
  environment is a polynomial-time family.  This is LM18 Definition 1 for both primitives
  together with `|e|` being a constant, packaged in the only vocabulary the abstract cost
  predicate provides.  Deriving it from `EfficientPrg` and `EfficientEnc` alone would need a
  cost semantics for `evalExpr`'s recursion, which the model does not have — see
  `report.md` §6.
-/
def EfficientEvalPrg (IsPolyTime : PolyFamOracleCompPred)
    (enc : encryptionScheme) (prg : prgScheme) : Prop :=
  ∀ {s : Shape} (e : Expression s) (l idx0 idx1 : ℕ),
    polyTimeFamComp IsPolyTime
      (Input := fun κ => (Fin l → Bool) × (Fin l → BitVector κ) × (BitVector κ × BitVector κ))
      (Output := fun κ => BitVector (shapeLength κ (enc κ) s))
      (fun κ env => evalExpr (enc κ) (prg κ)
        (subst3 idx0 idx1 env.2.2.1 env.2.2.2 (extendFin ones env.2.1))
        (extendFin false env.1) e)

/--
  **`PrgReductionPolyTime` is derivable, not an assumption.**

  The PRG reduction is exactly "sample an environment, query the oracle once, then evaluate"
  (`reductionToPrgOracle_decompose`), so the framework's own composition closure reduces its
  efficiency to two much smaller claims: that the fixed-size sampling prefix is efficient,
  and that the *scheme itself* evaluates efficiently — the latter being LM18 Definition 1.
-/
theorem reductionToPrgOracle_polyTime
    (IsPolyTime : PolyFamOracleCompPred)
    (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
    (enc : encryptionScheme) (prg : prgScheme)
    (Hsampler : ∀ {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS)
      (idx0 idx1 : ℕ), IsPolyTime (prgEnvSampler expr targetSeed idx0 idx1))
    (Heval : EfficientEvalPrg IsPolyTime enc prg) :
    PrgReductionPolyTime IsPolyTime enc prg := by
  intro s expr targetSeed idx0 idx1
  rw [reductionToPrgOracle_decompose]
  exact HPolyTime _ _ _ _ _ _ (Hsampler expr targetSeed idx0 idx1)
    (Heval (replacePRG targetSeed idx0 idx1 expr) _ idx0 idx1)


/--
  **`EfficientEvalPrg` from efficiency of the primitives.**

  `evalExpr` walks a fixed expression doing one `encrypt`, `prg0` or `prg1` call per node, so
  this ought to *follow* from LM18 Definition 1 rather than be assumed.  It does:
  `PRG.evalEfficiencyFromPrimitives_holds` in `ComputationalSemantics/CostModel.lean` proves
  it, relative to the auditable `PolyTimeModel` interface.

  Note the two hypotheses that are *not* the inherited ones.

  * `LengthPoly enc` is mandatory, not a convenience.  Without it `encryptLength n = 2 ^ n`
    is a legal scheme, the value of a nested `Enc` is exponentially long in the expression
    depth, and the conclusion is false in any cost model.  The inherited statement omitted it
    and was therefore not provable as written.
  * `EfficientEncPoly` rather than `EfficientEnc`, because the message length at an `Enc` node
    grows with `κ`.  It is the strictly stronger of the two (`EfficientEncPoly.toEfficientEnc`).
-/
def EvalEfficiencyFromPrimitives (IsPolyTime : PolyFamOracleCompPred) : Prop :=
  ∀ (enc : encryptionScheme) (prg : prgScheme),
    LengthPoly enc → EfficientEncPoly IsPolyTime enc → EfficientPrg IsPolyTime prg →
    EfficientEvalPrg IsPolyTime enc prg

/-- `PrgReductionPolyTime` from LM18 Definition 1. -/
theorem reductionToPrgOracle_polyTime_of_primitives
    (IsPolyTime : PolyFamOracleCompPred)
    (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
    (enc : encryptionScheme) (prg : prgScheme)
    (Hsampler : ∀ {s : Shape} (expr : Expression s) (targetSeed : Expression Shape.KeyS)
      (idx0 idx1 : ℕ), IsPolyTime (prgEnvSampler expr targetSeed idx0 idx1))
    (Hcost : EvalEfficiencyFromPrimitives IsPolyTime) (Hlen : LengthPoly enc)
    (Henc : EfficientEncPoly IsPolyTime enc) (Hprg : EfficientPrg IsPolyTime prg) :
    PrgReductionPolyTime IsPolyTime enc prg :=
  reductionToPrgOracle_polyTime IsPolyTime HPolyTime enc prg Hsampler
    (Hcost enc prg Hlen Henc Hprg)

end PRG
