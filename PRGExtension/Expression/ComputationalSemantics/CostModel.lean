import PRGExtension.Expression.ComputationalSemantics.PolyTime
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey

/-!
# An auditable poly-time interface, and the two efficiency obligations discharged against it

**Read this first.**  This file does *not* build a cost semantics, and nothing here proves
that any particular computation runs in polynomial time.  What it does is replace two large,
opaque assumptions about two large terms with one small interface whose clauses a reader can
check by eye, one at a time, against the definitions they talk about.

The two assumptions are

* `EncReductionPolyTime` — `IsPolyTime (reductionHidingOneKey enc prg expr key₀)`, and
* `EvalEfficiencyFromPrimitives` — `EfficientEnc → EfficientPrg → EfficientEvalPrg`,

each quantified over *every* expression.  Both become theorems below, relative to
`PolyTimeModel` (fifteen structural closure clauses about the cost predicate) and
`BitOpsEfficient` (seven clauses naming the concrete bit-vector operations the semantics
performs).  The interface is still *assumed*; the gain is that the assumption is now about
`bind`, `query` and `append` rather than about a 200-line recursive reduction.

## Why this shape

`PolyFamOracleCompPred` is a predicate on whole *families of closed computations*.  The only
closure property the development assumed is `PolyTimeClosedUnderComposition`, i.e.
oracle-computation-then-pure-computation.  That suffices for `reductionToPrgOracle`, which is
literally `sample; sample; query; evaluate` — see `reductionToPrgOracle_polyTime`.  It does
not suffice for `reductionToOracle`, which recurses over the expression *while querying*, so
its decomposition needs sequencing of two oracle computations.

Sequencing needs a continuation, and a continuation is a *function*, so the interface needs a
second predicate `IsPolyTimeFn` on function families.  Two failed attempts are worth
recording, since both look reasonable:

* Quantifying `bind`'s continuation pointwise over arbitrary semantic value families
  (`∀ v, IsPolyTime (fun κ => f κ (v κ))`) typechecks but is vacuous in the direction needed:
  at a `Pair` node it demands efficiency of `fun κ => append (v κ) (w κ)` for an arbitrary,
  possibly uncomputable `v`.
* An unconstrained `pure` clause (`∀ v, IsPolyTime (fun κ => pure (v κ))`) makes every pure
  computation free, which is false of any cost model and lets arbitrary work hide in `v`.

So every clause below that produces a value requires that value to come from a poly-time
*function*, spelled `polyTimeFamComp IsPolyTime` — the development's existing vocabulary,
and already the form of `EfficientEnc` and `EfficientPrg`.

## Where this bottoms out

At the primitives, which is the correct place: `enc.encrypt`, `prg0`, `prg1`,
`List.Vector.append` and `evalBitExpr` are arbitrary Lean functions, so their cost must stay
a parameter.  That is LM18 Definition 1.  See `report.md` §6 for the assumption boundary.
-/

open PRG
namespace PRG

/-! ## Function families -/

/-- A family of *functions* from an input family into oracle computations: the continuation
shape that sequencing needs and that `famOracleComp` cannot express. -/
def famOracleFn {I : Type} (Spec : ℕ → OracleSpec I) (Domain Output : ℕ → Type) :=
  (κ : ℕ) → Domain κ → OracleComp (withRandomI Spec κ) (Output κ)

/-- The function-family analogue of `PolyFamOracleCompPred`. -/
def PolyFamOracleFnPred : Type _ :=
  {I : Type} → {Spec : ℕ → OracleSpec I} → {Domain Output : ℕ → Type} →
    famOracleFn Spec Domain Output → Prop

/--
The predicate type for *value* functions.

**Why this is primitive rather than `polyTimeFamComp IsPolyTime`** (which is what it used to
be).  `polyTimeFamComp` encodes "this value function is poly-time" as "the oracle computation
that *queries for its input* and then runs it is poly-time".  That encoding is not
invertible: a clause that *takes* a value-level hypothesis receives it in the encoded form,
and getting back out needs an inversion of the oracle-level predicate on a term whose
constructors are Lean functions.  Reusing `polyTimeFamComp` costs nothing while the interface
is *assumed* — nothing is ever proved about it — and blocks every attempt to build a model.
See `CHECKPOINT.md` §3.1, finding F6.
-/
def PolyFamCompPred : Type _ :=
  {D O : ℕ → Type} → famComp D O → Prop

/-- Abbreviation for "this value function is poly-time".  Deterministic functions appear as
`fun κ d => PMF.pure (f κ d)`. -/
abbrev PolyTimeVal (V : PolyFamCompPred) {D O : ℕ → Type}
    (f : famComp D O) : Prop := V f

/-! ## The interface -/

/--
**The poly-time interface.**  Fifteen closure clauses over a *pair* of predicates: the
development's `IsPolyTime` on closed families, and a new `IsPolyTimeFn` on function families.

Read them as a cost model would have to satisfy them:

*Value level* (`polyTimeFamComp IsPolyTime`, i.e. oracle-free computations)
1. `valId`, 2. `valFst`, 3. `valSnd`, 4. `valUnit` — the identity, the projections and the
unit constant are free;
5. `valPair` — running two poly-time functions on the same input and pairing is poly-time;
6. `precompVal` — precomposing with a poly-time function is poly-time;
7. `bindVal` — sequencing, with the input carried into the continuation.

*Oracle level*
8. `pureFn` — returning the result of a poly-time function, with no oracle call;
9. `liftVal` — an oracle-free *randomised* step is a poly-time function family;
10. `bindFn` — sequencing, with the input carried into the continuation;
11. `precompFn` — precomposing with a poly-time function;
12. `queryFn` — *one* oracle query, on a poly-time-computed argument, at an index fixed by κ;
13. `closeFn` — a poly-time function family on the trivial input is a poly-time family.

*Sampling*
14. `uniformBits`, 15. `uniformKeys` — drawing `l` uniform bits, or `l` uniform κ-bit keys,
is poly-time.

Note that `pureFn` is the *constrained* form of the `ret` clause warned about above: the
returned value must come from a poly-time function, so no work can hide inside it.

**The `PolySized` side conditions are load-bearing, not decoration.**  Seven clauses here
(`valId`, `valFst`, `valSnd`, `valUnit`, `queryFn`, `uniformBits`, `uniformKeys`) and two of
`BitOpsEfficient` (`constVec`, `nilVec`) are generic in a type family that nothing else in
their statement constrains.  Without the condition they are *false* of any cost model that
charges for moving data: a family of poly-size circuits has I/O width bounded by its size, so
`valId` at `D κ := BitVector (2 ^ κ)` would demand a poly-size circuit with `2 ^ κ` output
wires.  The remaining clauses need nothing, because every family they touch either comes from
a hypothesis that is already a poly-time claim or carries `PolyLength`.

`PolySized` carries its width as *data*.  That is the `calf`-style "carry the bound"
formulation: each primitive's cost will be a function of exactly that width, so a concrete
cost model's obligations become arithmetic in `width` rather than a re-derivation of these
statements.
Clause 12 is deliberately weak: the oracle index may depend on κ but not on the input, which
is how both reductions use it.  Nothing here says a computation *is* poly-time; each clause
says only that poly-time is preserved by one syntactic construction.
-/
structure PolyTimeModel (IsPolyTime : PolyFamOracleCompPred) where
  IsPolyTimeFn : PolyFamOracleFnPred
  IsPolyTimeVal : PolyFamCompPred
  -- value level
  valId : ∀ {D : ℕ → Type}, PolySized D →
    PolyTimeVal IsPolyTimeVal (D := D) (O := D) (fun _ d => PMF.pure d)
  valFst : ∀ {D E : ℕ → Type}, PolySized D → PolySized E →
    PolyTimeVal IsPolyTimeVal (D := fun κ => D κ × E κ) (O := D) (fun _ p => PMF.pure p.1)
  valSnd : ∀ {D E : ℕ → Type}, PolySized D → PolySized E →
    PolyTimeVal IsPolyTimeVal (D := fun κ => D κ × E κ) (O := E) (fun _ p => PMF.pure p.2)
  valUnit : ∀ {D : ℕ → Type}, PolySized D →
    PolyTimeVal IsPolyTimeVal (D := D) (O := fun _ => Unit) (fun _ _ => PMF.pure ())
  valPair : ∀ {D A B : ℕ → Type} (f : (κ : ℕ) → D κ → A κ) (g : (κ : ℕ) → D κ → B κ),
    PolyTimeVal IsPolyTimeVal (fun κ d => PMF.pure (f κ d)) →
    PolyTimeVal IsPolyTimeVal (fun κ d => PMF.pure (g κ d)) →
    PolyTimeVal IsPolyTimeVal (O := fun κ => A κ × B κ) (fun κ d => PMF.pure (f κ d, g κ d))
  precompVal : ∀ {D D' O : ℕ → Type} (φ : (κ : ℕ) → D' κ → D κ) (f : famComp D O),
    PolyTimeVal IsPolyTimeVal (fun κ d => PMF.pure (φ κ d)) → PolyTimeVal IsPolyTimeVal f →
    PolyTimeVal IsPolyTimeVal (fun κ d => f κ (φ κ d))
  bindVal : ∀ {D A B : ℕ → Type} (g : famComp D A) (k : famComp (fun κ => D κ × A κ) B),
    PolyTimeVal IsPolyTimeVal g → PolyTimeVal IsPolyTimeVal k →
    PolyTimeVal IsPolyTimeVal (fun κ d => g κ d >>= fun a => k κ (d, a))
  -- oracle level
  pureFn : ∀ {I : Type} {Spec : ℕ → OracleSpec I} {D O : ℕ → Type} (f : (κ : ℕ) → D κ → O κ),
    PolyTimeVal IsPolyTimeVal (fun κ d => PMF.pure (f κ d)) →
    IsPolyTimeFn (I := I) (Spec := Spec) (fun κ d => pure (f κ d))
  liftVal : ∀ {I : Type} {Spec : ℕ → OracleSpec I} {D O : ℕ → Type} (f : famComp D O),
    PolyTimeVal IsPolyTimeVal f →
    IsPolyTimeFn (I := I) (Spec := Spec) (fun κ d => sample (f κ d))
  bindFn : ∀ {I : Type} {Spec : ℕ → OracleSpec I} {D A B : ℕ → Type}
    (g : famOracleFn Spec D A) (k : famOracleFn Spec (fun κ => D κ × A κ) B),
    IsPolyTimeFn g → IsPolyTimeFn k →
    IsPolyTimeFn (fun κ d => g κ d >>= fun a => k κ (d, a))
  precompFn : ∀ {I : Type} {Spec : ℕ → OracleSpec I} {D D' B : ℕ → Type}
    (φ : (κ : ℕ) → D' κ → D κ) (g : famOracleFn Spec D B),
    PolyTimeVal IsPolyTimeVal (fun κ d => PMF.pure (φ κ d)) → IsPolyTimeFn g →
    IsPolyTimeFn (fun κ d => g κ (φ κ d))
  queryFn : ∀ {I : Type} {Spec : ℕ → OracleSpec I} {D : ℕ → Type} (i : (κ : ℕ) → I)
    (t : (κ : ℕ) → D κ → (Spec κ).domain (i κ)),
    PolySized (fun κ => (Spec κ).range (i κ)) →
    PolyTimeVal IsPolyTimeVal (fun κ d => PMF.pure (t κ d)) →
    IsPolyTimeFn (Output := fun κ => (Spec κ).range (i κ))
      (fun κ d => (OracleComp.lift ((withRandomI Spec κ).query (Sum.inr (i κ)) (t κ d))
        : OracleComp (withRandomI Spec κ) ((Spec κ).range (i κ))))
  closeFn : ∀ {I : Type} {Spec : ℕ → OracleSpec I} {B : ℕ → Type}
    (g : famOracleFn Spec (fun _ => Unit) B),
    IsPolyTimeFn g → IsPolyTime (fun κ => g κ ())
  /-- The link to the framework's own vocabulary, in the only direction that is available.
      `EfficientEvalPrg` and the IND-CPA/PRG security definitions are phrased with
      `polyTimeFamComp`, so results have to be delivered in that form even though the
      interface works in `IsPolyTimeVal`. -/
  valToFamComp : ∀ {D O : ℕ → Type} (f : famComp D O), PolySized D → PolySized O →
    PolyTimeVal IsPolyTimeVal f → polyTimeFamComp IsPolyTime f
  -- sampling
  uniformBits : ∀ {D : ℕ → Type}, PolySized D → ∀ (l : ℕ),
    PolyTimeVal IsPolyTimeVal (D := D) (O := fun _ => Fin l → Bool)
      (fun _ _ => PMF.uniformOfFintype (Fin l → Bool))
  uniformKeys : ∀ {D : ℕ → Type}, PolySized D → ∀ (l : ℕ),
    PolyTimeVal IsPolyTimeVal (D := D) (O := fun κ => Fin l → BitVector κ)
      (fun κ _ => PMF.uniformOfFintype (Fin l → BitVector κ))

/-! ## LM18 Definition 1, at the value level

`EfficientEncPoly` and `EfficientPrg` (in `PolyTime.lean`) are phrased with
`polyTimeFamComp`.  For the same reason as `PolyFamCompPred` itself (F6), the interface needs
them against the model's own value predicate; `PolyTimeModel.valToFamComp` recovers the
`polyTimeFamComp` form where the framework demands it. -/

/-- LM18 Definition 1 for the encryption scheme, against a value predicate. -/
def EfficientEncVal (V : PolyFamCompPred) (enc : encryptionScheme) : Prop :=
  ∀ (d : ℕ → ℕ), PolyLength d →
    PolyTimeVal V (D := fun κ => BitVector κ × BitVector (d κ))
      (O := fun κ => BitVector ((enc κ).encryptLength (d κ)))
      (fun κ km => (enc κ).encrypt km.1 km.2)

/-- LM18 Definition 1 for the PRG, against a value predicate. -/
def EfficientPrgVal (V : PolyFamCompPred) (prg : prgScheme) : Prop :=
  PolyTimeVal V (D := fun κ => BitVector κ) (O := fun κ => BitVector κ)
      (fun κ seed => PMF.pure ((prg κ).prg0 seed))
  ∧ PolyTimeVal V (D := fun κ => BitVector κ) (O := fun κ => BitVector κ)
      (fun κ seed => PMF.pure ((prg κ).prg1 seed))

/-! ## Derived combinators

Everything below is *proved* from the clauses above; the induction in the next section uses
these rather than the raw fields. -/

namespace PolyTimeModel

/-- Composition of poly-time value functions.  (`precompVal`, read the other way round.) -/
lemma compVal {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    {D A B : ℕ → Type} (f : (κ : ℕ) → D κ → A κ) (g : (κ : ℕ) → A κ → B κ)
    (hf : PolyTimeVal M.IsPolyTimeVal (fun κ d => PMF.pure (f κ d)))
    (hg : PolyTimeVal M.IsPolyTimeVal (fun κ a => PMF.pure (g κ a))) :
    PolyTimeVal M.IsPolyTimeVal (fun κ d => PMF.pure (g κ (f κ d))) :=
  M.precompVal f (fun κ a => PMF.pure (g κ a)) hf hg

/-- `p.1.1`, and by iteration every projection out of a nest of pairs. -/
lemma valFstFst {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    {D E F : ℕ → Type} (hD : PolySized D) (hE : PolySized E) (hF : PolySized F) :
    PolyTimeVal M.IsPolyTimeVal (D := fun κ => (D κ × E κ) × F κ) (O := D)
      (fun _ p => PMF.pure p.1.1) :=
  M.compVal (fun _ (p : (D _ × E _) × F _) => p.1) (fun _ (q : D _ × E _) => q.1)
    (M.valFst (hD.prod hE) hF) (M.valFst hD hE)

lemma valSndFst {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    {D E F : ℕ → Type} (hD : PolySized D) (hE : PolySized E) (hF : PolySized F) :
    PolyTimeVal M.IsPolyTimeVal (D := fun κ => (D κ × E κ) × F κ) (O := E)
      (fun _ p => PMF.pure p.1.2) :=
  M.compVal (fun _ (p : (D _ × E _) × F _) => p.1) (fun _ (q : D _ × E _) => q.2)
    (M.valFst (hD.prod hE) hF) (M.valSnd hD hE)

/-- Discarding the second component of the input is free. -/
lemma weakenFn {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    {I : Type} {Spec : ℕ → OracleSpec I} {D E B : ℕ → Type}
    (hD : PolySized D) (hE : PolySized E)
    (g : famOracleFn Spec D B) (hg : M.IsPolyTimeFn g) :
    M.IsPolyTimeFn (Domain := fun κ => D κ × E κ)
      (fun κ (p : D κ × E κ) => g κ p.1) :=
  M.precompFn (fun _ (p : D _ × E _) => p.1) g (M.valFst hD hE) hg

/-- Postcomposing an oracle computation with a poly-time value function. -/
lemma mapFn {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    {I : Type} {Spec : ℕ → OracleSpec I} {D A B : ℕ → Type}
    (g : famOracleFn Spec D A) (f : (κ : ℕ) → (D κ × A κ) → B κ)
    (hg : M.IsPolyTimeFn g)
    (hf : PolyTimeVal M.IsPolyTimeVal (fun κ p => PMF.pure (f κ p))) :
    M.IsPolyTimeFn (fun κ d => g κ d >>= fun a => pure (f κ (d, a))) :=
  M.bindFn g (fun κ p => pure (f κ p)) hg (M.pureFn f hf)

end PolyTimeModel

/-! ## What the primitives must satisfy

Two groups.  `EfficientEncPoly` and `EfficientPrg` are LM18 Definition 1 for the two
cryptographic primitives; `BitOpsEfficient` names the handful of *non*-cryptographic
bit-vector operations the semantics performs between them. -/

/--
**The non-cryptographic work.**  Seven clauses, one per operation that `reductionToOracle` and
`evalExpr` perform on bit vectors.  Each is checkable against its definition in two lines,
and each carries the `PolyLength` side condition that makes it honest — concatenating two
bit vectors is linear in their length, which is only cheap when the length is.
-/
structure BitOpsEfficient (V : PolyFamCompPred) where
  /-- Concatenation (`Pair`). -/
  append : ∀ (d₁ d₂ : ℕ → ℕ), PolyLength d₁ → PolyLength d₂ →
    PolyTimeVal V (D := fun κ => BitVector (d₁ κ) × BitVector (d₂ κ))
      (O := fun κ => BitVector (d₁ κ + d₂ κ))
      (fun _ p => PMF.pure (List.Vector.append p.1 p.2))
  /-- Conditional swap-and-concatenate (`Perm`). -/
  condAppend : ∀ (d : ℕ → ℕ), PolyLength d →
    PolyTimeVal V (D := fun κ => Bool × BitVector (d κ) × BitVector (d κ))
      (O := fun κ => BitVector (d κ + d κ))
      (fun _ p => PMF.pure (if p.1 then List.Vector.append p.2.2 p.2.1
                                   else List.Vector.append p.2.1 p.2.2))
  /-- Evaluating a fixed bit expression against the sampled bit environment (`BitE`, `Perm`). -/
  bitExpr : ∀ (l : ℕ) (b : BitExpr),
    PolyTimeVal V (D := fun _ => Fin l → Bool) (O := fun _ => Bool)
      (fun _ bv => PMF.pure (evalBitExpr (extendFin false bv) b))
  /-- Packaging a bit as a one-element vector (`BitE`). -/
  bitToVec : PolyTimeVal V (D := fun _ => Bool) (O := fun _ => BitVector 1)
      (fun _ b => PMF.pure (List.Vector.cons b List.Vector.nil))
  /-- Reading a key variable out of the sampled key environment (`VarK`). -/
  keyVar : ∀ (l n : ℕ),
    PolyTimeVal V (D := fun κ => Fin l → BitVector κ) (O := fun κ => BitVector κ)
      (fun _ kv => PMF.pure (extendFin ones kv n))
  /-- The two fixed constants: the all-ones plaintext (`Hidden`) and the empty vector
      (`Eps`). -/
  constVec : ∀ {D : ℕ → Type}, PolySized D → ∀ (d : ℕ → ℕ), PolyLength d →
    PolyTimeVal V (D := D) (O := fun κ => BitVector (d κ))
      (fun _ _ => PMF.pure ones)
  nilVec : ∀ {D : ℕ → Type}, PolySized D →
    PolyTimeVal V (D := D) (O := fun _ => BitVector 0)
      (fun _ _ => PMF.pure List.Vector.nil)

/-! ## (O1): the IND-CPA reduction is poly-time

`reductionToOracle` recurses over the expression *while querying the oracle*, which is why
`PolyTimeClosedUnderComposition` alone could never discharge it.  With `bindFn` it is a
routine induction: nine cases, each one `bind` of the recursive call with a post-step that is
either `pure` of a `BitOpsEfficient` operation, one `query`, or one `enc.encrypt` sample.
-/

/-- The environment `reductionHidingOneKey` samples: `l` bits and `l` keys. -/
abbrev RedEnv (l : ℕ) : ℕ → Type := fun κ => (Fin l → Bool) × (Fin l → BitVector κ)

/-! ### Size witnesses

The `PolySized` evidence the clauses need, for the handful of families that actually occur.
Each carries an explicit width, so a concrete cost model's obligations are arithmetic in
those widths. -/

/-- A single key: `κ` bits. -/
def sizedKey : PolySized (fun κ => BitVector κ) := PolySized.bitVector _ PolyLength.id

/-- The value of a fixed shape.  This is where `LengthPoly` enters the size discipline —
without it `shapeLength` is not polynomially bounded and the family is not poly-sized. -/
def sizedShape (enc : encryptionScheme) (Hlen : LengthPoly enc) (s : Shape) :
    PolySized (fun κ => BitVector (shapeLength κ (enc κ) s)) :=
  PolySized.bitVector _ (shapeLength_poly enc Hlen s)

/-- The IND-CPA reduction's sampled environment. -/
def sizedRedEnv (l : ℕ) : PolySized (RedEnv l) :=
  (PolySized.bitEnv l).prod (PolySized.keyEnv l)

/-- `reductionToOracle` read as a function of the sampled environment — the form the
induction needs, since the recursive calls all run in the *same* environment. -/
noncomputable def redFn (enc : encryptionScheme) (prg : prgScheme) (l key₀ : ℕ) {s : Shape}
    (e : Expression s) :
    famOracleFn (fun κ => oracleSpecIndCpa κ (enc κ)) (RedEnv l)
      (fun κ => BitVector (shapeLength κ (enc κ) s)) :=
  fun κ env =>
    reductionToOracle (enc κ) (prg κ) (extendFin ones env.2) (extendFin false env.1) e key₀

section Reduction


/-- Abbreviation for the length family of a shape. -/
private abbrev dl (enc : encryptionScheme) (s : Shape) : ℕ → ℕ :=
  fun κ => shapeLength κ (enc κ) s

/-- **The single encryption step**, shared by the `Enc` and `Hidden` cases.

This is where the target key is either queried (the IND-CPA oracle, because the reduction
does not know `key₀`) or encrypted locally.  Both branches are one operation; `LengthPoly`
enters through the `PolyLength` side condition on the message length. -/
lemma encryptStep_polyTime {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    (Bops : BitOpsEfficient M.IsPolyTimeVal) (enc : encryptionScheme)
    (Henc : EfficientEncVal M.IsPolyTimeVal enc) (Hlen : LengthPoly enc)
    {D : ℕ → Type} (hD : PolySized D) (isTarget : Bool) (s : Shape)
    (kf : (κ : ℕ) → D κ → BitVector κ) (mf : (κ : ℕ) → D κ → BitVector (dl enc s κ))
    (hk : PolyTimeVal M.IsPolyTimeVal (fun κ d => PMF.pure (kf κ d)))
    (hm : PolyTimeVal M.IsPolyTimeVal (fun κ d => PMF.pure (mf κ d))) :
    M.IsPolyTimeFn (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) (Domain := D)
      (Output := fun κ => BitVector ((enc κ).encryptLength (dl enc s κ)))
      (fun κ d => encryptPMFOracle (enc κ) isTarget (kf κ d) (mf κ d)) := by
  cases isTarget with
  | true =>
      -- one left-or-right oracle query on `(message, ones)`
      have h : PolyTimeVal M.IsPolyTimeVal
          (fun κ d => PMF.pure
            ((mf κ d, (ones : BitVector (dl enc s κ)))
              : (oracleSpecIndCpa κ (enc κ)).domain (dl enc s κ))) :=
        M.valPair mf (fun κ _ => (ones : BitVector (dl enc s κ))) hm
          (Bops.constVec hD (dl enc s) (shapeLength_poly enc Hlen s))
      have := M.queryFn (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) (D := D)
        (fun κ => dl enc s κ) (fun κ d => (mf κ d, ones))
        (sizedShape enc Hlen (Shape.EncS s)) h
      convert this using 2 with κ d
  | false =>
      -- one local encryption under a key the reduction knows
      have h : PolyTimeVal M.IsPolyTimeVal
          (fun κ (d : D κ) => (enc κ).encrypt (kf κ d) (mf κ d)) :=
        M.precompVal (fun κ d => (kf κ d, mf κ d))
          (fun κ km => (enc κ).encrypt km.1 km.2) (M.valPair kf mf hk hm)
          (Henc (dl enc s) (shapeLength_poly enc Hlen s))
      have := M.liftVal (Spec := fun κ => oracleSpecIndCpa κ (enc κ))
        (fun κ (d : D κ) => (enc κ).encrypt (kf κ d) (mf κ d)) h
      convert this using 2 with κ d

/-- **An `Enc` node.**  `do e' ← _; k' ← _; encryptPMFOracle enc isTarget k' e'`: two
recursive calls, then the single encryption step.  Factored out because `reductionToOracle`
decides `isTarget` by matching on the key expression, so the three key constructors have to
be handled separately at the call site; the body is the same for all three. -/
lemma encNode_polyTime {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    (Bops : BitOpsEfficient M.IsPolyTimeVal) (enc : encryptionScheme) (prg : prgScheme)
    (Henc : EfficientEncVal M.IsPolyTimeVal enc) (Hlen : LengthPoly enc) (l key₀ : ℕ) {s : Shape}
    (k : Expression Shape.KeyS) (e : Expression s) (tgt : Bool)
    (ihk : M.IsPolyTimeFn (redFn enc prg l key₀ k))
    (ihe : M.IsPolyTimeFn (redFn enc prg l key₀ e))
    (hnode : redFn enc prg l key₀ (Expression.Enc k e)
      = fun κ env => redFn enc prg l key₀ e κ env >>= fun e' =>
          (fun κ' (p : RedEnv l κ' × BitVector (dl enc s κ')) =>
            redFn enc prg l key₀ k κ' p.1 >>= fun k' =>
              encryptPMFOracle (enc κ') tgt k' p.2) κ (env, e')) :
    M.IsPolyTimeFn (redFn enc prg l key₀ (Expression.Enc k e)) := by
  rw [hnode]
  exact M.bindFn (redFn enc prg l key₀ e)
    (fun κ (p : RedEnv l κ × BitVector (dl enc s κ)) =>
      redFn enc prg l key₀ k κ p.1 >>= fun k' => encryptPMFOracle (enc κ) tgt k' p.2) ihe
    (M.bindFn
      (fun κ (p : RedEnv l κ × BitVector (dl enc s κ)) => redFn enc prg l key₀ k κ p.1)
      (fun κ (q : (RedEnv l κ × BitVector (dl enc s κ)) × BitVector κ) =>
        encryptPMFOracle (enc κ) tgt q.2 q.1.2)
      (M.weakenFn (sizedRedEnv l) (sizedShape enc Hlen s) (redFn enc prg l key₀ k) ihk)
      (encryptStep_polyTime M Bops enc Henc Hlen
        (D := fun κ => (RedEnv l κ × BitVector (dl enc s κ)) × BitVector κ)
        (((sizedRedEnv l).prod (sizedShape enc Hlen s)).prod sizedKey) tgt s
        (fun _ (q : (RedEnv l _ × BitVector (dl enc s _)) × BitVector _) => q.2)
        (fun _ (q : (RedEnv l _ × BitVector (dl enc s _)) × BitVector _) => q.1.2)
        (M.valSnd ((sizedRedEnv l).prod (sizedShape enc Hlen s)) sizedKey)
        (M.valSndFst (sizedRedEnv l) (sizedShape enc Hlen s) sizedKey)))

set_option maxHeartbeats 2000000 in
/--
**(O1) is a theorem**, relative to the interface: for a fixed expression, the IND-CPA
reduction's body is a poly-time function of the sampled environment.

The arms mirror `reductionToOracle`'s arms one for one.  Read them side by side: each is
`bindFn` of the recursive calls followed by a single post-step, and the post-step is exactly
the operation named in the corresponding `BitOpsEfficient` clause — or, at `Enc`/`Hidden`,
the single `encryptStep_polyTime` above.
-/
theorem redFn_polyTime {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    (Bops : BitOpsEfficient M.IsPolyTimeVal) (enc : encryptionScheme) (prg : prgScheme)
    (Henc : EfficientEncVal M.IsPolyTimeVal enc)
    (Hprg : EfficientPrgVal M.IsPolyTimeVal prg) (Hlen : LengthPoly enc) (l key₀ : ℕ) :
    ∀ {s : Shape} (e : Expression s), M.IsPolyTimeFn (redFn enc prg l key₀ e)
  | _, Expression.Eps => by
      -- `return nil`
      have h := M.pureFn (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) (D := RedEnv l)
        (fun _ _ => (List.Vector.nil : BitVector 0)) (Bops.nilVec (sizedRedEnv l))
      exact h
  | _, Expression.BitE b => by
      -- `return (cons (evalBitExpr bVars b) nil)`
      have hb : PolyTimeVal M.IsPolyTimeVal
          (fun κ (env : RedEnv l κ) => PMF.pure (evalBitExpr (extendFin false env.1) b)) :=
        M.compVal (D := RedEnv l) (fun _ (env : RedEnv l _) => env.1)
          (fun _ (bv : Fin l → Bool) => evalBitExpr (extendFin false bv) b)
          (M.valFst (PolySized.bitEnv l) (PolySized.keyEnv l)) (Bops.bitExpr l b)
      have hf : PolyTimeVal M.IsPolyTimeVal
          (fun κ (env : RedEnv l κ) => PMF.pure
            (List.Vector.cons (evalBitExpr (extendFin false env.1) b) List.Vector.nil)) :=
        M.compVal (D := RedEnv l) (fun _ (env : RedEnv l _) =>
          evalBitExpr (extendFin false env.1) b)
          (fun _ (b' : Bool) => List.Vector.cons b' List.Vector.nil) hb Bops.bitToVec
      have h := M.pureFn (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) _ hf
      exact h
  | _, Expression.VarK n => by
      -- `return (kVars n)`
      have hf : PolyTimeVal M.IsPolyTimeVal
          (fun κ (env : RedEnv l κ) => PMF.pure (extendFin ones env.2 n)) :=
        M.compVal (D := RedEnv l) (fun _ (env : RedEnv l _) => env.2)
          (fun _ (kv : Fin l → BitVector _) => extendFin ones kv n)
          (M.valSnd (PolySized.bitEnv l) (PolySized.keyEnv l)) (Bops.keyVar l n)
      have h := M.pureFn (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) _ hf
      exact h
  | _, Expression.Pair (s₁ := s₁) (s₂ := s₂) e₁ e₂ => by
      -- `do v₁ ← _; v₂ ← _; return (append v₁ v₂)`
      have ih₁ := redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ e₁
      have ih₂ := redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ e₂
      have hf : PolyTimeVal M.IsPolyTimeVal
          (fun κ (q : (RedEnv l κ × BitVector (dl enc s₁ κ)) × BitVector (dl enc s₂ κ)) =>
            PMF.pure (List.Vector.append q.1.2 q.2)) :=
        M.compVal
          (fun _ (q : (RedEnv l _ × BitVector (dl enc s₁ _)) × BitVector (dl enc s₂ _)) =>
            (q.1.2, q.2))
          (fun _ (pr : BitVector (dl enc s₁ _) × BitVector (dl enc s₂ _)) =>
            List.Vector.append pr.1 pr.2)
          (M.valPair
            (fun _ (q : (RedEnv l _ × BitVector (dl enc s₁ _)) × BitVector (dl enc s₂ _)) => q.1.2)
            (fun _ (q : (RedEnv l _ × BitVector (dl enc s₁ _)) × BitVector (dl enc s₂ _)) => q.2)
            (M.valSndFst (sizedRedEnv l) (sizedShape enc Hlen s₁) (sizedShape enc Hlen s₂))
            (M.valSnd ((sizedRedEnv l).prod (sizedShape enc Hlen s₁)) (sizedShape enc Hlen s₂)))
          (Bops.append (dl enc s₁) (dl enc s₂)
            (shapeLength_poly enc Hlen s₁) (shapeLength_poly enc Hlen s₂))
      have h := M.bindFn (redFn enc prg l key₀ e₁)
        (fun κ (p : RedEnv l κ × BitVector (dl enc s₁ κ)) =>
          redFn enc prg l key₀ e₂ κ p.1 >>= fun v₂ => pure (List.Vector.append p.2 v₂)) ih₁
        (M.mapFn
          (fun κ (p : RedEnv l κ × BitVector (dl enc s₁ κ)) => redFn enc prg l key₀ e₂ κ p.1)
          (fun _ (q : (RedEnv l _ × BitVector (dl enc s₁ _)) × BitVector (dl enc s₂ _)) =>
            List.Vector.append q.1.2 q.2)
          (M.weakenFn (sizedRedEnv l) (sizedShape enc Hlen s₁) (redFn enc prg l key₀ e₂) ih₂) hf)
      exact h
  | _, Expression.G0 k => by
      -- `do a ← _; return (prg0 a)`
      have ih := redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ k
      have hf : PolyTimeVal M.IsPolyTimeVal
          (fun κ (p : RedEnv l κ × BitVector κ) => PMF.pure ((prg κ).prg0 p.2)) :=
        M.compVal (fun _ (p : RedEnv l _ × BitVector _) => p.2)
          (fun κ (a : BitVector κ) => (prg κ).prg0 a)
          (M.valSnd (sizedRedEnv l) sizedKey) Hprg.1
      have h := M.mapFn (redFn enc prg l key₀ k)
        (fun κ (p : RedEnv l κ × BitVector κ) => (prg κ).prg0 p.2) ih hf
      exact h
  | _, Expression.G1 k => by
      have ih := redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ k
      have hf : PolyTimeVal M.IsPolyTimeVal
          (fun κ (p : RedEnv l κ × BitVector κ) => PMF.pure ((prg κ).prg1 p.2)) :=
        M.compVal (fun _ (p : RedEnv l _ × BitVector _) => p.2)
          (fun κ (a : BitVector κ) => (prg κ).prg1 a)
          (M.valSnd (sizedRedEnv l) sizedKey) Hprg.2
      have h := M.mapFn (redFn enc prg l key₀ k)
        (fun κ (p : RedEnv l κ × BitVector κ) => (prg κ).prg1 p.2) ih hf
      exact h
  | _, Expression.Perm (s := s) (Expression.BitE b) e₁ e₂ => by
      -- `do v₁ ← _; v₂ ← _; if b' then return (append v₂ v₁) else return (append v₁ v₂)`
      have ih₁ := redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ e₁
      have ih₂ := redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ e₂
      have hbit : PolyTimeVal M.IsPolyTimeVal
          (fun κ (q : (RedEnv l κ × BitVector (dl enc s κ)) × BitVector (dl enc s κ)) =>
            PMF.pure (evalBitExpr (extendFin false q.1.1.1) b)) :=
        M.compVal
          (fun _ (q : (RedEnv l _ × BitVector (dl enc s _)) × BitVector (dl enc s _)) => q.1.1.1)
          (fun _ (bv : Fin l → Bool) => evalBitExpr (extendFin false bv) b)
          (M.compVal
            (fun _ (q : (RedEnv l _ × BitVector (dl enc s _)) × BitVector (dl enc s _)) => q.1.1)
            (fun _ (r : RedEnv l _) => r.1)
            (M.valFstFst (sizedRedEnv l) (sizedShape enc Hlen s) (sizedShape enc Hlen s)) (M.valFst (PolySized.bitEnv l) (PolySized.keyEnv l)))
          (Bops.bitExpr l b)
      have hf : PolyTimeVal M.IsPolyTimeVal
          (fun κ (q : (RedEnv l κ × BitVector (dl enc s κ)) × BitVector (dl enc s κ)) =>
            PMF.pure (if evalBitExpr (extendFin false q.1.1.1) b
              then List.Vector.append q.2 q.1.2 else List.Vector.append q.1.2 q.2)) :=
        M.compVal
          (fun _ (q : (RedEnv l _ × BitVector (dl enc s _)) × BitVector (dl enc s _)) =>
            (evalBitExpr (extendFin false q.1.1.1) b, q.1.2, q.2))
          (fun _ (p : Bool × BitVector (dl enc s _) × BitVector (dl enc s _)) =>
            if p.1 then List.Vector.append p.2.2 p.2.1 else List.Vector.append p.2.1 p.2.2)
          (M.valPair _ _ hbit
            (M.valPair
              (fun _ (q : (RedEnv l _ × BitVector (dl enc s _)) × BitVector (dl enc s _)) => q.1.2)
              (fun _ (q : (RedEnv l _ × BitVector (dl enc s _)) × BitVector (dl enc s _)) => q.2)
              (M.valSndFst (sizedRedEnv l) (sizedShape enc Hlen s) (sizedShape enc Hlen s))
              (M.valSnd ((sizedRedEnv l).prod (sizedShape enc Hlen s)) (sizedShape enc Hlen s))))
          (Bops.condAppend (dl enc s) (shapeLength_poly enc Hlen s))
      have h : M.IsPolyTimeFn (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) (Domain := RedEnv l)
          (Output := fun κ => BitVector (shapeLength κ (enc κ) (Shape.PairS s s)))
          (fun κ env => redFn enc prg l key₀ e₁ κ env >>= fun a =>
            (fun κ' (p : RedEnv l κ' × BitVector (dl enc s κ')) =>
              redFn enc prg l key₀ e₂ κ' p.1 >>= fun v₂ =>
                pure (if evalBitExpr (extendFin false p.1.1) b
                      then List.Vector.append v₂ p.2 else List.Vector.append p.2 v₂))
              κ (env, a)) :=
        M.bindFn (redFn enc prg l key₀ e₁)
        (fun κ (p : RedEnv l κ × BitVector (dl enc s κ)) =>
          redFn enc prg l key₀ e₂ κ p.1 >>= fun v₂ =>
            pure (if evalBitExpr (extendFin false p.1.1) b
                  then List.Vector.append v₂ p.2 else List.Vector.append p.2 v₂)) ih₁
        (M.mapFn
          (fun κ (p : RedEnv l κ × BitVector (dl enc s κ)) => redFn enc prg l key₀ e₂ κ p.1)
          (fun _ (q : (RedEnv l _ × BitVector (dl enc s _)) × BitVector (dl enc s _)) =>
            if evalBitExpr (extendFin false q.1.1.1) b
            then List.Vector.append q.2 q.1.2 else List.Vector.append q.1.2 q.2)
          (M.weakenFn (sizedRedEnv l) (sizedShape enc Hlen s) (redFn enc prg l key₀ e₂) ih₂) hf)
      convert h using 2 with κ env
      all_goals (funext env
                 simp [redFn, reductionToOracle, bind_pure_comp,
                   ← apply_ite (f := fun x => (pure x : OracleComp _ _))])
  | _, Expression.Enc (s := s) (Expression.VarK n) e => by
      exact encNode_polyTime M Bops enc prg Henc Hlen l key₀ (Expression.VarK n) e
        (decide (n = key₀)) (redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ _)
        (redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ e) (by
          funext κ env; simp [redFn, reductionToOracle])
  | _, Expression.Enc (s := s) (Expression.G0 kk) e => by
      exact encNode_polyTime M Bops enc prg Henc Hlen l key₀ (Expression.G0 kk) e false
        (redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ _)
        (redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ e) (by
          funext κ env; simp [redFn, reductionToOracle])
  | _, Expression.Enc (s := s) (Expression.G1 kk) e => by
      exact encNode_polyTime M Bops enc prg Henc Hlen l key₀ (Expression.G1 kk) e false
        (redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ _)
        (redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ e) (by
          funext κ env; simp [redFn, reductionToOracle])
  | _, Expression.Hidden (s := s) (Expression.VarK n) => by
      -- `do o ← encryptPMFOracle enc isTarget (kVars n) ones; return o`
      have h : M.IsPolyTimeFn (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) (Domain := RedEnv l)
          (Output := fun κ => BitVector (shapeLength κ (enc κ) (Shape.EncS s)))
          (fun κ (env : RedEnv l κ) => encryptPMFOracle (enc κ) (decide (n = key₀))
            (extendFin ones env.2 n) (ones : BitVector (dl enc s κ))) :=
        encryptStep_polyTime M Bops enc Henc Hlen (D := RedEnv l) (sizedRedEnv l)
          (decide (n = key₀)) s (fun _ (env : RedEnv l _) => extendFin ones env.2 n)
          (fun _ (_ : RedEnv l _) => (ones : BitVector (dl enc s _)))
          (M.compVal (D := RedEnv l) (fun _ (env : RedEnv l _) => env.2)
            (fun _ (kv : Fin l → BitVector _) => extendFin ones kv n)
            (M.valSnd (PolySized.bitEnv l) (PolySized.keyEnv l)) (Bops.keyVar l n))
          (Bops.constVec (sizedRedEnv l) (dl enc s) (shapeLength_poly enc Hlen s))
      convert h using 2 with κ env
      all_goals (funext env; simp [redFn, reductionToOracle])
  | _, Expression.Hidden (s := s) (Expression.G0 k) => by
      -- `do key ← _; sample (enc.encrypt key ones)`
      have ih := redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ (Expression.G0 k)
      have henc : PolyTimeVal M.IsPolyTimeVal
          (fun κ (p : RedEnv l κ × BitVector κ) =>
            (enc κ).encrypt p.2 (ones : BitVector (dl enc s κ))) :=
        M.precompVal
          (fun κ (p : RedEnv l κ × BitVector κ) => (p.2, (ones : BitVector (dl enc s κ))))
          (fun κ (km : BitVector κ × BitVector (dl enc s κ)) => (enc κ).encrypt km.1 km.2)
          (M.valPair (fun _ (p : RedEnv l _ × BitVector _) => p.2)
            (fun _ (_ : RedEnv l _ × BitVector _) => (ones : BitVector (dl enc s _)))
            (M.valSnd (sizedRedEnv l) sizedKey)
            (Bops.constVec ((sizedRedEnv l).prod sizedKey) (dl enc s)
              (shapeLength_poly enc Hlen s)))
          (Henc (dl enc s) (shapeLength_poly enc Hlen s))
      have h := M.bindFn (redFn enc prg l key₀ (Expression.G0 k))
        (fun κ (p : RedEnv l κ × BitVector κ) =>
          sample ((enc κ).encrypt p.2 (ones : BitVector (dl enc s κ)))) ih
        (M.liftVal (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) _ henc)
      exact h
  | _, Expression.Hidden (s := s) (Expression.G1 k) => by
      have ih := redFn_polyTime M Bops enc prg Henc Hprg Hlen l key₀ (Expression.G1 k)
      have henc : PolyTimeVal M.IsPolyTimeVal
          (fun κ (p : RedEnv l κ × BitVector κ) =>
            (enc κ).encrypt p.2 (ones : BitVector (dl enc s κ))) :=
        M.precompVal
          (fun κ (p : RedEnv l κ × BitVector κ) => (p.2, (ones : BitVector (dl enc s κ))))
          (fun κ (km : BitVector κ × BitVector (dl enc s κ)) => (enc κ).encrypt km.1 km.2)
          (M.valPair (fun _ (p : RedEnv l _ × BitVector _) => p.2)
            (fun _ (_ : RedEnv l _ × BitVector _) => (ones : BitVector (dl enc s _)))
            (M.valSnd (sizedRedEnv l) sizedKey)
            (Bops.constVec ((sizedRedEnv l).prod sizedKey) (dl enc s)
              (shapeLength_poly enc Hlen s)))
          (Henc (dl enc s) (shapeLength_poly enc Hlen s))
      have h := M.bindFn (redFn enc prg l key₀ (Expression.G1 k))
        (fun κ (p : RedEnv l κ × BitVector κ) =>
          sample ((enc κ).encrypt p.2 (ones : BitVector (dl enc s κ)))) ih
        (M.liftVal (Spec := fun κ => oracleSpecIndCpa κ (enc κ)) _ henc)
      exact h
/-! ### The sampling prefix, and (O1) at top level -/

/-- `reductionHidingOneKey` is "draw `l` bits, draw `l` keys, then run the body in that
environment".  Both draws are `uniformBits`/`uniformKeys`; `closeFn` turns the result back
into a family. -/
lemma sampleEnv_polyTime {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    {I : Type} {Spec : ℕ → OracleSpec I} {B : ℕ → Type} (l : ℕ)
    (g : famOracleFn Spec (RedEnv l) B) (hg : M.IsPolyTimeFn g) :
    IsPolyTime (fun κ => do
      let bVars ← sample (PMF.uniformOfFintype (Fin l → Bool))
      let kVars ← sample (PMF.uniformOfFintype (Fin l → BitVector κ))
      g κ (bVars, kVars)) := by
  refine M.closeFn _ (M.bindFn (Spec := Spec) (D := fun _ => Unit)
    (fun κ _ => sample (PMF.uniformOfFintype (Fin l → Bool)))
    (fun κ (p : Unit × (Fin l → Bool)) => do
      let kVars ← sample (PMF.uniformOfFintype (Fin l → BitVector κ))
      g κ (p.2, kVars))
    (M.liftVal _ (M.uniformBits PolySized.unit l)) ?_)
  exact M.bindFn (Spec := Spec)
    (fun κ (_ : Unit × (Fin l → Bool)) => sample (PMF.uniformOfFintype (Fin l → BitVector κ)))
    (fun κ (q : (Unit × (Fin l → Bool)) × (Fin l → BitVector κ)) => g κ (q.1.2, q.2))
    (M.liftVal _ (M.uniformKeys (PolySized.unit.prod (PolySized.bitEnv l)) l))
    (M.precompFn (fun κ (q : (Unit × (Fin l → Bool)) × (Fin l → BitVector κ)) => (q.1.2, q.2)) g
      (M.valPair _ _ (M.valSndFst PolySized.unit (PolySized.bitEnv l) (PolySized.keyEnv l))
        (M.valSnd (PolySized.unit.prod (PolySized.bitEnv l)) (PolySized.keyEnv l))) hg)

/--
**(O1) discharged.**  `EncReductionPolyTime` — the assumption that the whole IND-CPA
reduction is poly-time, for every expression and every removed key — is a theorem relative to
the interface.

What remains assumed is `PolyTimeModel` (fifteen one-line closure clauses), `BitOpsEfficient`
(seven bit-vector operations), LM18 Definition 1 for the two primitives, and `LengthPoly`.
-/
theorem encReduction_polyTime {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    (Bops : BitOpsEfficient M.IsPolyTimeVal) (enc : encryptionScheme) (prg : prgScheme)
    (Henc : EfficientEncVal M.IsPolyTimeVal enc) (Hprg : EfficientPrgVal M.IsPolyTimeVal prg)
    (Hlen : LengthPoly enc) :
    EncReductionPolyTime IsPolyTime enc prg := by
  intro shape expr key₀
  have h := sampleEnv_polyTime M (getMaxVar expr + 1) (redFn enc prg (getMaxVar expr + 1) key₀ expr)
    (redFn_polyTime M Bops enc prg Henc Hprg Hlen (getMaxVar expr + 1) key₀ expr)
  convert h using 2 with κ
  all_goals simp [reductionHidingOneKey, redFn]

end Reduction

/-! ## (O2): the computational semantics itself is poly-time

Same shape of argument one level down.  `evalExpr` has no oracle, so this lives entirely at
the value level: `bindVal` and `precompVal` in place of `bindFn` and `precompFn`, with the
*same* `BitOpsEfficient` clauses at the leaves. -/

section Eval

set_option maxHeartbeats 2000000 in
/--
**Evaluating a fixed expression is poly-time in the environment.**

`kf` and `bf` supply the key and bit environments as poly-time functions of the input.  They
are quantified per *variable* rather than as whole functions `ℕ → BitVector κ`, which is what
makes the hypotheses statable: "reading one key variable is cheap", not "this infinite
function is cheap".
-/
theorem evalExpr_polyTime {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    (Bops : BitOpsEfficient M.IsPolyTimeVal) (enc : encryptionScheme) (prg : prgScheme)
    (Henc : EfficientEncVal M.IsPolyTimeVal enc) (Hprg : EfficientPrgVal M.IsPolyTimeVal prg)
    (Hlen : LengthPoly enc) {D : ℕ → Type} (hD : PolySized D)
    (kf : (κ : ℕ) → D κ → (ℕ → BitVector κ)) (bf : (κ : ℕ) → D κ → (ℕ → Bool))
    (hk : ∀ n : ℕ, PolyTimeVal M.IsPolyTimeVal (fun κ d => PMF.pure (kf κ d n)))
    (hb : ∀ b : BitExpr, PolyTimeVal M.IsPolyTimeVal (fun κ d => PMF.pure (evalBitExpr (bf κ d) b))) :
    ∀ {s : Shape} (e : Expression s),
      PolyTimeVal M.IsPolyTimeVal (D := D)
        (O := fun κ => BitVector (shapeLength κ (enc κ) s))
        (fun κ d => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) e)
  | _, Expression.Eps => by
      have h := Bops.nilVec (D := D) hD
      exact h
  | _, Expression.BitE b => by
      have h : PolyTimeVal M.IsPolyTimeVal (D := D) (O := fun _ => BitVector 1)
          (fun κ d => PMF.pure
            (List.Vector.cons (evalBitExpr (bf κ d) b) List.Vector.nil)) :=
        M.compVal (fun κ (d : D κ) => evalBitExpr (bf κ d) b)
          (fun _ (b' : Bool) => List.Vector.cons b' List.Vector.nil) (hb b) Bops.bitToVec
      exact h
  | _, Expression.VarK n => by
      have h := hk n
      exact h
  | _, Expression.Pair (s₁ := s₁) (s₂ := s₂) e₁ e₂ => by
      have ih₁ := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb e₁
      have ih₂ := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb e₂
      have hf : PolyTimeVal M.IsPolyTimeVal
          (D := fun κ => (D κ × BitVector (dl enc s₁ κ)) × BitVector (dl enc s₂ κ))
          (O := fun κ => BitVector (dl enc s₁ κ + dl enc s₂ κ))
          (fun _ q => PMF.pure (List.Vector.append q.1.2 q.2)) :=
        M.compVal
          (fun _ (q : (D _ × BitVector (dl enc s₁ _)) × BitVector (dl enc s₂ _)) => (q.1.2, q.2))
          (fun _ (pr : BitVector (dl enc s₁ _) × BitVector (dl enc s₂ _)) =>
            List.Vector.append pr.1 pr.2)
          (M.valPair _ _ (M.valSndFst hD (sizedShape enc Hlen s₁) (sizedShape enc Hlen s₂))
            (M.valSnd (hD.prod (sizedShape enc Hlen s₁)) (sizedShape enc Hlen s₂)))
          (Bops.append (dl enc s₁) (dl enc s₂)
            (shapeLength_poly enc Hlen s₁) (shapeLength_poly enc Hlen s₂))
      have h := M.bindVal (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) e₁)
        (fun κ (p : D κ × BitVector (dl enc s₁ κ)) =>
          evalExpr (enc κ) (prg κ) (kf κ p.1) (bf κ p.1) e₂ >>= fun v₂ =>
            PMF.pure (List.Vector.append p.2 v₂)) ih₁
        (M.bindVal
          (fun κ (p : D κ × BitVector (dl enc s₁ κ)) =>
            evalExpr (enc κ) (prg κ) (kf κ p.1) (bf κ p.1) e₂)
          (fun _ (q : (D _ × BitVector (dl enc s₁ _)) × BitVector (dl enc s₂ _)) =>
            PMF.pure (List.Vector.append q.1.2 q.2))
          (M.precompVal (fun _ (p : D _ × BitVector (dl enc s₁ _)) => p.1)
            (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) e₂)
            (M.valFst hD (sizedShape enc Hlen s₁)) ih₂)
          hf)
      exact h
  | _, Expression.G0 k => by
      have ih := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb k
      have h := M.bindVal (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) k)
        (fun κ (p : D κ × BitVector κ) => PMF.pure ((prg κ).prg0 p.2)) ih
        (M.precompVal (fun _ (p : D _ × BitVector _) => p.2)
          (fun κ (seed : BitVector κ) => PMF.pure ((prg κ).prg0 seed))
          (M.valSnd hD sizedKey) Hprg.1)
      exact h
  | _, Expression.G1 k => by
      have ih := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb k
      have h := M.bindVal (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) k)
        (fun κ (p : D κ × BitVector κ) => PMF.pure ((prg κ).prg1 p.2)) ih
        (M.precompVal (fun _ (p : D _ × BitVector _) => p.2)
          (fun κ (seed : BitVector κ) => PMF.pure ((prg κ).prg1 seed))
          (M.valSnd hD sizedKey) Hprg.2)
      exact h
  | _, Expression.Perm (s := s) (Expression.BitE b) e₁ e₂ => by
      have ih₁ := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb e₁
      have ih₂ := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb e₂
      have hf : PolyTimeVal M.IsPolyTimeVal
          (D := fun κ => (D κ × BitVector (dl enc s κ)) × BitVector (dl enc s κ))
          (O := fun κ => BitVector (dl enc s κ + dl enc s κ))
          (fun _ q => PMF.pure (if evalBitExpr (bf _ q.1.1) b
            then List.Vector.append q.2 q.1.2 else List.Vector.append q.1.2 q.2)) :=
        M.compVal
          (fun κ (q : (D κ × BitVector (dl enc s κ)) × BitVector (dl enc s κ)) =>
            (evalBitExpr (bf κ q.1.1) b, q.1.2, q.2))
          (fun _ (p : Bool × BitVector (dl enc s _) × BitVector (dl enc s _)) =>
            if p.1 then List.Vector.append p.2.2 p.2.1 else List.Vector.append p.2.1 p.2.2)
          (M.valPair _ _
            (M.compVal (fun _ (q : (D _ × BitVector (dl enc s _)) × BitVector (dl enc s _)) => q.1.1)
              (fun κ (d : D κ) => evalBitExpr (bf κ d) b)
              (M.valFstFst hD (sizedShape enc Hlen s) (sizedShape enc Hlen s)) (hb b))
            (M.valPair _ _ (M.valSndFst hD (sizedShape enc Hlen s) (sizedShape enc Hlen s))
              (M.valSnd (hD.prod (sizedShape enc Hlen s)) (sizedShape enc Hlen s))))
          (Bops.condAppend (dl enc s) (shapeLength_poly enc Hlen s))
      have h : PolyTimeVal M.IsPolyTimeVal (D := D)
          (O := fun κ => BitVector (shapeLength κ (enc κ) (Shape.PairS s s)))
          (fun κ d => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) e₁ >>= fun v₁ =>
            (fun κ' (p : D κ' × BitVector (dl enc s κ')) =>
              evalExpr (enc κ') (prg κ') (kf κ' p.1) (bf κ' p.1) e₂ >>= fun v₂ =>
                PMF.pure (if evalBitExpr (bf κ' p.1) b
                  then List.Vector.append v₂ p.2 else List.Vector.append p.2 v₂)) κ (d, v₁)) :=
        M.bindVal (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) e₁)
          (fun κ (p : D κ × BitVector (dl enc s κ)) =>
            evalExpr (enc κ) (prg κ) (kf κ p.1) (bf κ p.1) e₂ >>= fun v₂ =>
              PMF.pure (if evalBitExpr (bf κ p.1) b
                then List.Vector.append v₂ p.2 else List.Vector.append p.2 v₂)) ih₁
          (M.bindVal
            (fun κ (p : D κ × BitVector (dl enc s κ)) =>
              evalExpr (enc κ) (prg κ) (kf κ p.1) (bf κ p.1) e₂)
            (fun _ (q : (D _ × BitVector (dl enc s _)) × BitVector (dl enc s _)) =>
              PMF.pure (if evalBitExpr (bf _ q.1.1) b
                then List.Vector.append q.2 q.1.2 else List.Vector.append q.1.2 q.2))
            (M.precompVal (fun _ (p : D _ × BitVector (dl enc s _)) => p.1)
              (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) e₂)
              (M.valFst hD (sizedShape enc Hlen s)) ih₂)
            hf)
      convert h using 2 with κ d
      all_goals (funext d
                 simp [evalExpr, ← apply_ite (f := fun x => (PMF.pure x : PMF _))])
  | _, Expression.Enc (s := s) k e => by
      have ihk := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb k
      have ihe := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb e
      have hf : PolyTimeVal M.IsPolyTimeVal
          (D := fun κ => (D κ × BitVector (dl enc s κ)) × BitVector κ)
          (O := fun κ => BitVector ((enc κ).encryptLength (dl enc s κ)))
          (fun κ q => (enc κ).encrypt q.2 q.1.2) :=
        M.precompVal
          (fun _ (q : (D _ × BitVector (dl enc s _)) × BitVector _) => (q.2, q.1.2))
          (fun κ (km : BitVector κ × BitVector (dl enc s κ)) => (enc κ).encrypt km.1 km.2)
          (M.valPair _ _ (M.valSnd (hD.prod (sizedShape enc Hlen s)) sizedKey)
            (M.valSndFst hD (sizedShape enc Hlen s) sizedKey))
          (Henc (dl enc s) (shapeLength_poly enc Hlen s))
      have h := M.bindVal (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) e)
        (fun κ (p : D κ × BitVector (dl enc s κ)) =>
          evalExpr (enc κ) (prg κ) (kf κ p.1) (bf κ p.1) k >>= fun key =>
            (enc κ).encrypt key p.2) ihe
        (M.bindVal
          (fun κ (p : D κ × BitVector (dl enc s κ)) =>
            evalExpr (enc κ) (prg κ) (kf κ p.1) (bf κ p.1) k)
          (fun κ (q : (D κ × BitVector (dl enc s κ)) × BitVector κ) =>
            (enc κ).encrypt q.2 q.1.2)
          (M.precompVal (fun _ (p : D _ × BitVector (dl enc s _)) => p.1)
            (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) k)
            (M.valFst hD (sizedShape enc Hlen s)) ihk)
          hf)
      exact h
  | _, Expression.Hidden (s := s) k => by
      have ihk := evalExpr_polyTime M Bops enc prg Henc Hprg Hlen hD kf bf hk hb k
      have hf : PolyTimeVal M.IsPolyTimeVal (D := fun κ => D κ × BitVector κ)
          (O := fun κ => BitVector ((enc κ).encryptLength (dl enc s κ)))
          (fun κ p => (enc κ).encrypt p.2 (ones : BitVector (dl enc s κ))) :=
        M.precompVal
          (fun κ (p : D κ × BitVector κ) => (p.2, (ones : BitVector (dl enc s κ))))
          (fun κ (km : BitVector κ × BitVector (dl enc s κ)) => (enc κ).encrypt km.1 km.2)
          (M.valPair _ _ (M.valSnd hD sizedKey)
            (Bops.constVec (hD.prod sizedKey) (dl enc s) (shapeLength_poly enc Hlen s)))
          (Henc (dl enc s) (shapeLength_poly enc Hlen s))
      have h := M.bindVal (fun κ (d : D κ) => evalExpr (enc κ) (prg κ) (kf κ d) (bf κ d) k)
        (fun κ (p : D κ × BitVector κ) =>
          (enc κ).encrypt p.2 (ones : BitVector (dl enc s κ))) ihk hf
      exact h

/-- The environment `reductionToPrgOracle` samples: `l` bits, `l` keys, and the oracle's
answer, which occupies the two challenge seed positions `idx0`/`idx1`. -/
abbrev PrgEnv (l : ℕ) : ℕ → Type :=
  fun κ => (Fin l → Bool) × (Fin l → BitVector κ) × (BitVector κ × BitVector κ)

/-- Its size witness. -/
def sizedPrgEnv (l : ℕ) : PolySized (PrgEnv l) :=
  (PolySized.bitEnv l).prod ((PolySized.keyEnv l).prod (sizedKey.prod sizedKey))

/-- Reading one key variable out of that environment.  `subst3` overrides two named
positions, and for a *fixed* index that is decided statically — so this is one of three
projections and needs no assumption beyond `keyVar`. -/
lemma prgEnvKey_polyTime {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime)
    (Bops : BitOpsEfficient M.IsPolyTimeVal) (l idx0 idx1 n : ℕ) :
    PolyTimeVal M.IsPolyTimeVal (D := PrgEnv l) (O := fun κ => BitVector κ)
      (fun _ env => PMF.pure
        (subst3 idx0 idx1 env.2.2.1 env.2.2.2 (extendFin ones env.2.1) n)) := by
  have hpair : PolyTimeVal M.IsPolyTimeVal (D := PrgEnv l)
      (O := fun κ => BitVector κ × BitVector κ) (fun _ (env : PrgEnv l _) => PMF.pure env.2.2) :=
    M.compVal (fun _ (env : PrgEnv l _) => env.2)
      (fun _ (r : (Fin l → BitVector _) × (BitVector _ × BitVector _)) => r.2)
      (M.valSnd (PolySized.bitEnv l) ((PolySized.keyEnv l).prod (sizedKey.prod sizedKey)))
      (M.valSnd (PolySized.keyEnv l) (sizedKey.prod sizedKey))
  have hkeys : PolyTimeVal M.IsPolyTimeVal (D := PrgEnv l)
      (O := fun κ => Fin l → BitVector κ) (fun _ (env : PrgEnv l _) => PMF.pure env.2.1) :=
    M.compVal (fun _ (env : PrgEnv l _) => env.2)
      (fun _ (r : (Fin l → BitVector _) × (BitVector _ × BitVector _)) => r.1)
      (M.valSnd (PolySized.bitEnv l) ((PolySized.keyEnv l).prod (sizedKey.prod sizedKey)))
      (M.valFst (PolySized.keyEnv l) (sizedKey.prod sizedKey))
  by_cases h0 : n = idx0
  · have h : PolyTimeVal M.IsPolyTimeVal (D := PrgEnv l) (O := fun κ => BitVector κ)
        (fun _ (env : PrgEnv l _) => PMF.pure env.2.2.1) :=
      M.compVal (fun _ (env : PrgEnv l _) => env.2.2)
        (fun _ (v : BitVector _ × BitVector _) => v.1) hpair (M.valFst sizedKey sizedKey)
    convert h using 3 with κ env
    simp [subst3, h0]
  · by_cases h1 : n = idx1
    · have h : PolyTimeVal M.IsPolyTimeVal (D := PrgEnv l) (O := fun κ => BitVector κ)
          (fun _ (env : PrgEnv l _) => PMF.pure env.2.2.2) :=
        M.compVal (fun _ (env : PrgEnv l _) => env.2.2)
          (fun _ (v : BitVector _ × BitVector _) => v.2) hpair (M.valSnd sizedKey sizedKey)
      convert h using 3 with κ env
      subst h1
      simp [subst3, h0]
    · have h : PolyTimeVal M.IsPolyTimeVal (D := PrgEnv l) (O := fun κ => BitVector κ)
          (fun _ (env : PrgEnv l _) => PMF.pure (extendFin ones env.2.1 n)) :=
        M.compVal (fun _ (env : PrgEnv l _) => env.2.1)
          (fun _ (kv : Fin l → BitVector _) => extendFin ones kv n) hkeys (Bops.keyVar l n)
      convert h using 3 with κ env
      simp [subst3, h0, h1]

/--
**(O2) discharged.**  `EvalEfficiencyFromPrimitives` is a theorem: the computational
semantics of a fixed expression runs in polynomial time whenever the two primitives do and
the scheme's ciphertexts grow polynomially (`LengthPoly`).

Beyond `evalExpr_polyTime` the only work is supplying its two environment hypotheses for the
environment the PRG reduction uses — `prgEnvKey_polyTime` for the keys, and one `compVal`
for the bits.
-/
theorem efficientEvalPrg_holds {IsPolyTime : PolyFamOracleCompPred}
    (M : PolyTimeModel IsPolyTime) (Bops : BitOpsEfficient M.IsPolyTimeVal)
    (enc : encryptionScheme) (prg : prgScheme) (Hlen : LengthPoly enc)
    (Henc : EfficientEncVal M.IsPolyTimeVal enc)
    (Hprg : EfficientPrgVal M.IsPolyTimeVal prg) :
    EfficientEvalPrg IsPolyTime enc prg := by
  intro s e l idx0 idx1
  refine M.valToFamComp _ (sizedPrgEnv l) (sizedShape enc Hlen s) ?_
  exact evalExpr_polyTime M Bops enc prg Henc Hprg Hlen (D := PrgEnv l) (sizedPrgEnv l)
    (fun κ env => subst3 idx0 idx1 env.2.2.1 env.2.2.2 (extendFin ones env.2.1))
    (fun _ env => extendFin false env.1)
    (fun n => prgEnvKey_polyTime M Bops l idx0 idx1 n)
    (fun b => M.compVal (fun _ (env : PrgEnv l _) => env.1)
      (fun _ (bv : Fin l → Bool) => evalBitExpr (extendFin false bv) b)
      (M.valFst (PolySized.bitEnv l) ((PolySized.keyEnv l).prod (sizedKey.prod sizedKey)))
      (Bops.bitExpr l b)) e

/--
The framework encodes "value function is poly-time" as "the computation that queries for its
input is poly-time", and that encoding is not invertible (F6).  A model that *does* support
the backward direction says so with this; `EvalEfficiencyFromPrimitives`, whose hypotheses are
stated in the encoded form, needs it.
-/
def ValFromFamComp {IsPolyTime : PolyFamOracleCompPred} (M : PolyTimeModel IsPolyTime) : Prop :=
  ∀ {D O : ℕ → Type} (f : famComp D O),
    polyTimeFamComp IsPolyTime f → PolyTimeVal M.IsPolyTimeVal f

/-- **(O2) in the framework's own vocabulary**, for a model that can read a value function
back out of the input-querying encoding.  `efficientEvalPrg_holds` is the version that does
not need that, and is what `garblingSecureFromCostModel` uses. -/
theorem evalEfficiencyFromPrimitives_holds {IsPolyTime : PolyFamOracleCompPred}
    (M : PolyTimeModel IsPolyTime) (Bops : BitOpsEfficient M.IsPolyTimeVal)
    (hinv : ValFromFamComp M) : EvalEfficiencyFromPrimitives IsPolyTime := by
  intro enc prg Hlen Henc Hprg
  exact efficientEvalPrg_holds M Bops enc prg Hlen
    (fun d hd => hinv _ (Henc d hd)) ⟨hinv _ Hprg.1, hinv _ Hprg.2⟩

/--
**The PRG reduction's sampling prefix is poly-time.**

`prgEnvSampler` is `sample; sample; query once; return`, so this is `sampleEnv_polyTime` plus
a single `queryFn`.  Discharging it removes the last efficiency hypothesis of
`garblingSecureFromEfficiency` that was not already covered.
-/
theorem prgEnvSampler_polyTime {IsPolyTime : PolyFamOracleCompPred}
    (M : PolyTimeModel IsPolyTime) {s : Shape} (expr : Expression s)
    (targetSeed : Expression Shape.KeyS) (idx0 idx1 : ℕ) :
    IsPolyTime (prgEnvSampler expr targetSeed idx0 idx1) := by
  have hq := M.queryFn (Spec := fun κ => oracleSpecPrg κ)
    (D := RedEnv (prgReductionVars expr targetSeed idx0 idx1))
    (fun _ => ()) (fun _ _ => ()) (sizedKey.prod sizedKey)
    (M.valUnit (sizedRedEnv (prgReductionVars expr targetSeed idx0 idx1)))
  have hg := M.mapFn
    (fun κ (env : RedEnv (prgReductionVars expr targetSeed idx0 idx1) κ) =>
      (OracleComp.lift ((withRandomI (fun κ => oracleSpecPrg κ) κ).query (Sum.inr ()) ())
        : OracleComp (withRandomI (fun κ => oracleSpecPrg κ) κ) (BitVector κ × BitVector κ)))
    (fun _ (q : RedEnv (prgReductionVars expr targetSeed idx0 idx1) _
        × (BitVector _ × BitVector _)) => (q.1.1, q.1.2, q.2))
    hq
    (M.valPair _ _
      (M.valFstFst (PolySized.bitEnv (prgReductionVars expr targetSeed idx0 idx1))
        (PolySized.keyEnv (prgReductionVars expr targetSeed idx0 idx1))
        (sizedKey.prod sizedKey))
      (M.valPair _ _
        (M.valSndFst (PolySized.bitEnv (prgReductionVars expr targetSeed idx0 idx1))
          (PolySized.keyEnv (prgReductionVars expr targetSeed idx0 idx1))
          (sizedKey.prod sizedKey))
        (M.valSnd (sizedRedEnv (prgReductionVars expr targetSeed idx0 idx1))
          (sizedKey.prod sizedKey))))
  have h := sampleEnv_polyTime M (prgReductionVars expr targetSeed idx0 idx1) _ hg
  exact h

end Eval

/-! ## A consistency check on the interface -/

/--
**The interface is consistent.**  The trivial predicate satisfies every clause of
`PolyTimeModel` and `BitOpsEfficient`, so the hypotheses of `encReduction_polyTime`,
`evalEfficiencyFromPrimitives_holds` and `garblingSecureFromCostModel` are not contradictory
— those theorems are not vacuous for that reason.

It shows nothing more than that, and in particular it is *not* the non-vacuity witness the
development wants — it discharges the `PolySized` conditions without ever looking at them,
which is exactly what a predicate that charges nothing would do.  Note which hypothesis rules
it out, because it is not the obvious one:
IND-CPA security is *satisfiable* under `fun _ => True`, by a scheme whose ciphertext ignores
the message — `encryptionFunctions` has no correctness field, so such a scheme is legal and
its two IND-CPA oracles are literally equal (`scratch/DegenerateEnc.lean` proves it).  What
fails is **PRG security**: the real oracle answers with `(prg0 s, prg1 s)` for a κ-bit seed
while the ideal answers with a uniform 2κ-bit pair, so an unbounded distinguisher deciding
membership in the image wins with advantage at least `1 - 2 ^ (-κ)`, and no `prg` escapes
that.  Exhibiting a concrete `IsPolyTime` satisfying these clauses for which `prgSchemeSecure`
is consistent remains open; see `report.md` §6 and `CHECKPOINT.md` §3.0.
-/
def trivialPolyTimeModel : PolyTimeModel (fun {_ _ _} _ => True) where
  IsPolyTimeFn _ := True
  IsPolyTimeVal _ := True
  valToFamComp := by intros; trivial
  valId := by intros; trivial
  valFst := by intros; trivial
  valSnd := by intros; trivial
  valUnit := by intros; trivial
  valPair := by intros; trivial
  precompVal := by intros; trivial
  bindVal := by intros; trivial
  pureFn := by intros; trivial
  liftVal := by intros; trivial
  bindFn := by intros; trivial
  precompFn := by intros; trivial
  queryFn := by intros; trivial
  closeFn := by intros; trivial
  uniformBits := by intros; trivial
  uniformKeys := by intros; trivial

/-- Companion to `trivialPolyTimeModel`; same caveat. -/
def trivialBitOpsEfficient : BitOpsEfficient (fun {_ _} _ => True) where
  append := by intros; trivial
  condAppend := by intros; trivial
  bitExpr := by intros; trivial
  bitToVec := trivial
  keyVar := by intros; trivial
  constVec := by intros; trivial
  nilVec := by intros; trivial

end PRG
