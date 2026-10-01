import PRGExtension.Garbling.Security.Security
import PRGExtension.Expression.ComputationalSemantics.Efficiency.CostModel
import PRGExtension.Expression.ComputationalSemantics.Efficiency.GeneratedPolyTime

/-!
# Computational security from the primitives alone

`garblingSecureFromEfficiency` (in `Security.lean`) still carries three efficiency
hypotheses about the *reductions*: `EncReductionPolyTime`, `EfficientEvalPrg`, and
efficiency of `prgEnvSampler`.  All three are now theorems — `CostModel.lean` derives them
from the `PolyTimeModel` interface — so this file states the version of the security theorem
in which the only efficiency inputs are about the primitives themselves.

What it assumes, and nothing else:

* `PolyTimeClosedUnderComposition` — the development's original closure hypothesis;
* `PolyTimeModel` — fifteen one-line closure clauses for the cost predicate;
* `BitOpsEfficient` — seven bit-vector operations (`append`, `keyVar`, …), stated against
  the model's own value predicate `IsPolyTimeVal`;
* `LengthPoly enc` — ciphertexts grow polynomially (LM18 Definition 1, length half);
* `EfficientEncVal`, `EfficientPrgVal` — LM18 Definition 1 for the two primitives;
* IND-CPA security of `enc` and security of `prg`.

`GeneratedPolyTime.lean` now supplies a concrete `IsPolyTime` for which the first three *are*
theorems, so `garblingSecureGenerated` below is the version with the interface discharged.
Read its caveats before citing it: the generated class is currently too narrow to make the
statement mean much (`CHECKPOINT.md` §3.1, F8).
-/

open PRG
namespace PRG

/--
**The garbling scheme is computationally secure, with every efficiency claim about the
*reductions* discharged.**

Compare `garblingSecureFromEfficiency`, which takes `EncReductionPolyTime`,
`EfficientEvalPrg` and the sampler's efficiency as hypotheses.  Here they are supplied by
`encReduction_polyTime`, `evalEfficiencyFromPrimitives_holds` and `prgEnvSampler_polyTime`
respectively, so what is left to assume about efficiency is LM18 Definition 1 for `enc` and
`prg`, plus the cost-model interface.
-/
theorem garblingSecureFromCostModel
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
  (M : PolyTimeModel (fun {_ _ _} => IsPolyTime))
  (Bops : BitOpsEfficient M.IsPolyTimeVal)
  (enc : encryptionScheme) (prg : prgScheme)
  (Hlen : LengthPoly enc)
  (Henc : EfficientEncVal M.IsPolyTimeVal enc)
  (Hprg : EfficientPrgVal M.IsPolyTimeVal prg)
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
  {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
  CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
    (famDistrLift (exprToFamDistr enc prg (Garble c x)))
    (famDistrLift (exprToFamDistr enc prg (Simulate c (evalCircuit c x)))) :=
  garblingSecureFromEfficiency IsPolyTime HPolyTime enc prg
    (encReduction_polyTime M Bops enc prg Henc Hprg Hlen)
    (fun expr targetSeed idx0 idx1 => prgEnvSampler_polyTime M expr targetSeed idx0 idx1)
    (efficientEvalPrg_holds M Bops enc prg Hlen Henc Hprg)
    HEncIndCpa HPrgSecure c x

/--
**The garbling scheme is secure against the generated adversary class** — the same theorem at
a *concrete* `IsPolyTime`, with the whole interface discharged rather than assumed.

Compare `garblingSecureFromCostModel`, which takes `PolyTimeModel`, `BitOpsEfficient` and
LM18 Definition 1 as hypotheses: here they are supplied by `genPolyTimeModel`,
`genBitOpsEfficient`, `genEfficientEncVal` and `genEfficientPrgVal`, each a theorem.  What is
left to assume is `LengthPoly`, the two security assumptions, and
`PolyTimeClosedUnderComposition` — see the caveat below.

**Two things must travel with this statement.**

1. **The class is currently far too narrow for this to say much** (`CHECKPOINT.md` §3.1, F8).
   No `PolyVal` generator takes a `BitVector` to a `Bool` — the only `Bool`-producing
   generator, `bitExpr`, reads a *sampled bit environment* — so no distinguisher in
   `GenPolyTime enc prg` can produce an output depending on the challenge at all.  The theorem
   is sound; its content is close to nil until the class is widened.  Widening needs bit
   indexing and boolean gates (easy) and a bounded-iteration generator (not easy: derivations
   are finite, so members are *constant*-size compositions, while a real adversary takes κ-many
   steps).  Do not cite this theorem as "secure against polynomial-time adversaries".
2. `PolyTimeClosedUnderComposition` remains a hypothesis here, where the interface's own
   clauses did not.  Not an oversight: it is stated with `polyTimeFamComp`, so it inherits
   exactly the non-invertibility that finding F6 is about — discharging it would need to read
   a value function back out of the input-querying encoding.  `CHECKPOINT.md` §3.1, F7.
-/
theorem garblingSecureGenerated
  (enc : encryptionScheme) (prg : prgScheme) (Hlen : LengthPoly enc)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => GenPolyTime enc prg))
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => GenPolyTime enc prg) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => GenPolyTime enc prg) prg)
  {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
  CompIndistinguishabilityDistr (fun {_ _ _} => GenPolyTime enc prg)
    (famDistrLift (exprToFamDistr enc prg (Garble c x)))
    (famDistrLift (exprToFamDistr enc prg (Simulate c (evalCircuit c x)))) :=
  garblingSecureFromCostModel (fun {_ _ _} => GenPolyTime enc prg) HPolyTime
    (genPolyTimeModel enc prg) (genBitOpsEfficient enc prg) enc prg Hlen
    (genEfficientEncVal enc prg) (genEfficientPrgVal enc prg) HEncIndCpa HPrgSecure c x

/-! ## Closing the gap: security against an *arbitrary* adversary class

`garblingSecureGenerated` above states security against `GenPolyTime enc prg`, and however
wide that class is made, "is every poly-time adversary in it?" has no answer without a
formalised machine model (`GeneratedPolyTime.lean`, "Completeness for PTIME").

That question can be sidestepped entirely, because the generated class is used for **two
different jobs** that do not have to be done by the same class:

* it must contain the *reductions* — proved, `gen_encReduction_polyTime` and friends;
* it bounds the *adversaries* — where narrowness hurts.

Splitting them gives security against an arbitrary class `A`.  The reductions stay certified
by the concrete class; `A` need only be closed under composition and large enough to contain
those reductions.  This is how a cryptographic proof is normally structured: one never
characterises PPT, one shows the reduction is efficient and relies on the adversary class
absorbing it. -/

/-- `R`'s members are all members of `A`. -/
def ClassContained (R A : PolyFamOracleCompPred) : Prop :=
  ∀ {I : Type} {Spec : ℕ → OracleSpec I} {Output : ℕ → Type} (oa : famOracleComp Spec Output),
    R oa → A oa

/--
**The garbling scheme is secure against any adversary class that absorbs the reductions.**

`A` is arbitrary — read it as "all probabilistic polynomial-time adversaries".  What is
assumed about it is only structural:

* `HPolyTime` — closure under composition, the development's original hypothesis;
* `Hcontain` — `A` contains the generated class.  This is exactly the content "the reductions
  are efficient", now factored into a form that can be checked one generator at a time (33 of
  them) whenever `A` is made concrete.

Neither mentions the garbling scheme, and neither is a security assumption.  The security
hypotheses — IND-CPA and PRG security — are stated at `A`, so **the narrowness of
`GenPolyTime` no longer weakens the conclusion**: it certifies the reductions and nothing
else.

What remains genuinely open is unchanged and unavoidable: IND-CPA and PRG security cannot be
proved (either would give one-way functions, hence `P ≠ NP`), and `LengthPoly` is a modelling
requirement on the scheme.
-/
theorem garblingSecureRelative
  (A : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => A))
  (enc : encryptionScheme) (prg : prgScheme) (Hlen : LengthPoly enc)
  (Hcontain : ClassContained (fun {_ _ _} => GenPolyTime enc prg) (fun {_ _ _} => A))
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => A) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => A) prg)
  {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
  CompIndistinguishabilityDistr (fun {_ _ _} => A)
    (famDistrLift (exprToFamDistr enc prg (Garble c x)))
    (famDistrLift (exprToFamDistr enc prg (Simulate c (evalCircuit c x)))) :=
  garblingSecure A HPolyTime enc prg
    (fun shape expr key₀ =>
      Hcontain _ (gen_encReduction_polyTime enc prg Hlen shape expr key₀))
    (reductionToPrgOracle_polyTime A HPolyTime enc prg
      (fun expr targetSeed idx0 idx1 =>
        Hcontain _ (gen_prgEnvSampler_polyTime enc prg expr targetSeed idx0 idx1))
      (fun e l idx0 idx1 => Hcontain _ (gen_efficientEvalPrg enc prg Hlen e l idx0 idx1)))
    HEncIndCpa HPrgSecure c x

end PRG
