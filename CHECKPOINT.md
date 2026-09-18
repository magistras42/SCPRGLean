# CHECKPOINT — handoff for completing the cost semantics

**Branch** `prg-fixes` · **HEAD** `f9b619e` · `lake build` clean, `sorry`-free, no `axiom`
declarations in `PRGExtension/`.

Read `report.md` first for what the development *is*. This file is only about the one piece
of work left that would strengthen the guarantee: giving `IsPolyTime` real content, so that
the two remaining efficiency hypotheses become theorems.

---

## 1. Do not break these

Before and after any change, these must all still hold. This is the regression suite.

```
lake build                                              # clean
grep -rn "sorry\|^axiom " --include=*.lean PRGExtension  # nothing outside comments
```

```lean
import SymbolicGarbledCircuitsInLean
#print axioms PRG.garblingSecureFromEfficiency   -- [propext, Classical.choice, Quot.sound]
#print axioms PRG.garblingSecure                 -- same
#print axioms symbolicToSemanticSoundness        -- same
#print axioms PRG.fixpointStepSound              -- same
#print axioms PRG.theorem5                       -- same
#print axioms PRG.lemma7                         -- same
#print axioms PRG.lemma8                         -- same
#print axioms PRG.prgRenameRel_substKeys_general -- same
#print axioms PRG.adversaryView_eq_gStar         -- same
#print axioms PRG.theorem4_holds                 -- [propext, Quot.sound]
#print axioms PRG.garbleCorrect                  -- [propext, Quot.sound]
```

If `sorryAx` ever appears in that list, stop and find out why — §5 explains the most likely
cause (VCVio2 has live `sorry`s in modules the build currently does *not* import).

---

## 2. The two obligations, exactly

Both in `PRGExtension/Expression/ComputationalSemantics/`.

**(O1)** `EncReductionPolyTime` — `SoundnessProof/HidingOneKey.lean`

```lean
def EncReductionPolyTime (IsPolyTime : PolyFamOracleCompPred)
    (enc : encryptionScheme) (prg : prgScheme) : Prop :=
  ∀ (shape : Shape) (expr : Expression shape) (key₀ : ℕ),
    IsPolyTime (reductionHidingOneKey enc prg expr key₀)
```

**(O2)** `EvalEfficiencyFromPrimitives` — `PolyTime.lean`

```lean
def EvalEfficiencyFromPrimitives (IsPolyTime : PolyFamOracleCompPred) : Prop :=
  ∀ (enc : encryptionScheme) (prg : prgScheme),
    EfficientEnc IsPolyTime enc → EfficientPrg IsPolyTime prg →
    EfficientEvalPrg IsPolyTime enc prg
```

Discharging both makes `garblingSecureFromEfficiency` rest only on IND-CPA security,
PRG security, and `PolyTimeClosedUnderComposition`.

---

## 3. Why they are stuck right now

`PolyFamOracleCompPred` (`ComputationalIndistinguishability/Def.lean:118`) is

```lean
def PolyFamOracleCompPred : Type _ :=
  {I : Type} → {Spec : ℕ → OracleSpec I} → {Output : ℕ → Type} →
  famOracleComp Spec Output → Prop
```

— an **opaque predicate on whole families of computations**. It has no notion of a poly-time
*function*, no size measure, no per-step cost. The only structural property assumed is

```lean
def PolyTimeClosedUnderComposition (isPolyTime) : Prop :=
  ∀ I Spec Domain Output (oracleComp : famOracleComp Spec Domain)
    (simpleComp : famComp Domain Output),
    isPolyTime oracleComp → polyTimeFamComp isPolyTime simpleComp →
    isPolyTime (composeOracleCompWithSimpleComp oracleComp simpleComp)
```

i.e. **oracle-computation-then-pure-computation**, and nothing else.

That is exactly enough for the PRG reduction, which has the shape
`sample; sample; query; evaluate` — one oracle prefix followed by one pure tail. See
`reductionToPrgOracle_decompose` and `reductionToPrgOracle_polyTime` in `PolyTime.lean`:
**`PrgReductionPolyTime` is already derived, not assumed.** Copy that pattern where you can.

It is *not* enough for (O1). `reductionToOracle` (`HidingOneKey.lean:56`) recurses over the
expression **while making oracle queries** — at an `Enc` node it calls `encryptPMFOracle`,
which is either an IND-CPA query or a local `enc.encrypt` sample. So the decomposition needs
closure under sequencing **two oracle computations**, which the interface does not provide.

Nor is it enough for (O2): `evalExpr`'s recursion has no cost attached at all.

---

## 4. Dead ends already tried — do not repeat

* **Stating `bind` closure pointwise over value families.** The natural-looking

  ```lean
  bind : IsPolyTime c → (∀ v : (κ : ℕ) → Domain κ, IsPolyTime (fun κ => f κ (v κ))) → …
  ```

  typechecks but is **useless**: quantifying over arbitrary *semantic* value families loses
  the computational content. At a `Pair` node you then need
  `polyTimeVal (fun κ => append (v κ) (w κ))` for an arbitrary, possibly non-computable `v`,
  which is not derivable. A continuation must be required to be a poly-time **function**,
  which needs a second predicate — i.e. you are designing a cost model whether you like it
  or not.

* **Unconstrained `ret`.** `ret : ∀ v, IsPolyTime (fun κ => pure (v κ))` for arbitrary `v`
  makes every pure computation free, which is false of any real cost model and would let
  arbitrary work be smuggled into `v`.

* **`Equiv.extendSubtype`** for anything over `ℕ` — it needs `[Fintype α]`. (Unrelated to
  cost, but the same class of mistake; `exists_perm_extending` in
  `Expression/Lemmas/PseudorandomRenaming.lean` is the `ℕ` replacement.)

---

## 5. What exists to build on

### In this repo

| Thing | Where | Use |
|---|---|---|
| `PolyTimeClosedUnderComposition` | `ComputationalIndistinguishability/Def.lean:268` | the one closure property assumed today |
| `polyTimeFamComp`, `simpleCompAsGenComp` | same file, 129–138 | lifts a `famComp` to a `famOracleComp` |
| `composeOracleCompWithSimpleComp` | same file, 237 | oracle-then-pure |
| `reductionToPrgOracle_decompose` | `PolyTime.lean` | the template: exhibit a reduction as `compose` |
| `reductionToPrgOracle_polyTime` | `PolyTime.lean` | `PrgReductionPolyTime` derived from it |
| `prgEnvSampler`, `prgEvalStep` | `PolyTime.lean` | the two halves of that decomposition |
| Prose cost analysis | end of `HidingOneKey.lean` | **the informal proof you are formalising** — output-length induction on shapes, then `|e| · p(q(κ)+κ)`, plus the 2026-09-17 addendum covering `G0`/`G1` and `reductionToPrgOracle` |

### In the vendored VCVio2 — read the caveats

`VCVio2/VCVio/OracleComp/QueryBound.lean` already has:

* `IsQueryBound oa qb` — `qb` bounds the queries `oa` makes, via `countingOracle`;
* proved `isQueryBound_pure`, `isQueryBound_failure`, `isQueryBound_mono`,
  `isQueryBound_query_iff_pos`;
* `structure PolyQueries` (line 303) — polynomial query bounds for a family, which is very
  close to the shape you want.

**Three caveats, all load-bearing:**

1. **`isQueryBound_bind` and `isQueryBound_bind'` are commented out**, and the second has a
   `sorry` inside the comment. The compositionality lemma the whole induction needs **does
   not exist** and must be proved. Budget for this; it is the crux, not a detail.
2. `QueryBound.lean` is **not currently imported** — the build pulls in only
   `VCVio2.ToMathlib.Control.MonadTransformer`, `VCVio2.VCVio.OracleComp.OracleComp`,
   `VCVio2.VCVio.OracleComp.DistSemantics.EvalDist` (see `SymbolicGarbledCircuitsInLean.lean`
   lines 22–24). Importing it brings in one **live** `sorry`
   (`isQueryBound_iff_probEvent`, line 49). Using the proved lemmas is fine; using that one
   is not. Re-run the §1 axiom checks immediately after adding the import.
3. **Query count is not running time.** `PolyQueries` bounds oracle calls only. Running time
   additionally needs the cost of local computation — which is where the primitives come in
   (§6). Do not mistake one for the other.

`OracleComp spec = OptionT (FreeMonad (OracleQuery spec))` (`OracleComp.lean:112`), so every
computation is `pure x`, `query i t >>= k`, or `failure`, and `OracleComp.inductionOn` is the
induction principle.

---

## 6. A gap nobody has flagged yet — fix this before anything else

`encryptionFunctions` (`ComputationalSemantics/Def.lean:28`) is

```lean
structure encryptionFunctions (κ : ℕ) where
  encryptLength : ℕ → ℕ          -- ← completely unconstrained
  encrypt : {n : ℕ} → BitVector κ → BitVector n → PMF (BitVector (encryptLength n))
  decrypt : …
```

`encryptLength` has **no growth bound**. A scheme with `encryptLength n = 2^n` is a legal
inhabitant, and then the ciphertext of a nested `Enc` is exponential in the expression depth
— so no polynomial bound on `reductionToOracle`'s output length exists, and the prose cost
analysis is simply false for such a scheme. The analysis silently assumes
`encrypt(k,n)` runs in time `p(n + κ)`; nothing in the types says so.

**First deliverable, independent of everything else:** add the missing requirement, e.g.

```lean
/-- LM18 Def. 1: ciphertexts grow polynomially. -/
def LengthPoly (enc : encryptionScheme) : Prop :=
  ∃ p : Polynomial ℕ, ∀ κ n, (enc κ).encryptLength n ≤ p.eval (n + κ)
```

and thread it wherever the length induction is used. This is small, is a real modelling gap
of the same class as the `Seed := Unit` bug fixed in `[2026-09-16]`, and every later step
depends on it. `prgFunctions` needs no analogue — `prg0`/`prg1` are `BitVector κ → BitVector κ`,
so lengths are fixed by the type.

---

## 7. Two designs

### Design A — reduce the assumption to an auditable interface (~300–400 lines)

Do **not** claim this is a cost model; it is not. It replaces one opaque assumption about a
large term with a handful of small ones, each checkable by eye.

1. Add a second predicate for poly-time *function* families:
   `IsPolyTimeFn : ((κ : ℕ) → Domain κ → OracleComp (withRandomI Spec κ) (Output κ)) → Prop`.
2. Bundle the closure properties as a `structure PolyTimeModel` over the *pair* of
   predicates: `pure` of a poly-time value function, `bind` of a poly-time computation with a
   poly-time continuation, a single `query`, `sample` of a uniform on `Fin l → BitVector κ`,
   and the existing composition closure as a consequence.
3. **Prove (O1)** by induction on the expression, exactly mirroring `reductionToOracle`'s
   nine cases (`Pair`, `BitE`, `VarK`, `Perm`, `Eps`, `Enc`, `Hidden`, `G0`, `G1`). Each is
   `bind` of a recursive call with a `pure` post-step, except `Enc`/`Hidden`, which are one
   `encryptPMFOracle` — itself either one `query` or one `enc.encrypt` sample.
4. Add the env-sampling closure and finish `reductionHidingOneKey` from
   `reductionToOracle`.
5. **Prove (O2)** the same way over `evalExpr`'s cases, using `EfficientEnc`/`EfficientPrg`
   at the leaves and `LengthPoly` (§6) for the length bound.

Net effect: (O1) and (O2) become theorems relative to `PolyTimeModel`, and
`PolyTimeModel` is ~6 clauses a reader can audit. **Be explicit in the docstring that the
interface is still assumed** — do not let the file read as if efficiency has been proved.

### Design B — a concrete cost semantics (the real thing, much larger)

The honest goal. Note up front: **a cost semantics for `OracleComp` is not a cost semantics
for Lean.** You can count query nodes and structural steps, but `enc.encrypt`, `prg0`,
`prg1`, `List.Vector.append` and `evalBitExpr` are arbitrary Lean functions — their cost must
remain a *parameter*. So even Design B terminates at "efficiency of the primitives", i.e. at
LM18 Def. 1. That is the correct endpoint, not a failure.

1. Define `cost : OracleComp spec α → ℕ` (or a `WriterT ℕ` instrumented semantics) over the
   free-monad structure: `pure` ↦ 0, `query >>= k` ↦ 1 + cost of the continuation, `failure`
   ↦ 0. Reuse `countingOracle`/`IsQueryBound` rather than rebuilding, but expect to prove the
   `bind` lemma yourself (§5 caveat 1).
2. Add a size measure and prove `shapeLength` grows polynomially given `LengthPoly` (§6).
   This is the "output length" half of the prose argument, and it is the half that actually
   needs §6.
3. Instantiate `IsPolyTime` concretely: `∃ p : Polynomial ℕ, ∀ κ, cost (oa κ) ≤ p.eval κ`,
   with the primitive costs as parameters.
4. **Prove `PolyTimeClosedUnderComposition` as a theorem** for that instance. This is the
   single most valuable step in the whole file: it retroactively justifies every existing use
   of that hypothesis, and it is a good early check that the definition is workable.
5. Then (O1) and (O2) as in Design A, but with the closure clauses now theorems.
6. Finally — and this is the payoff — exhibit **one concrete `IsPolyTime` for which all of
   `PolyTimeClosedUnderComposition`, (O1) and (O2) hold simultaneously**. That is the
   non-vacuity witness the development currently lacks: today's hypotheses are satisfiable in
   isolation (`IsPolyTime := fun _ => True`) but nothing shows they are *jointly* satisfiable
   alongside IND-CPA security, which requires `IsPolyTime` to be small enough that secure
   schemes exist.

### Recommended order

§6 first (small, independent, and a genuine gap). Then Design A, which is shippable on its
own and leaves the development strictly better. Then Design B steps 1–4, treating step 4 as
the go/no-go checkpoint. Do not start B without A: A tells you exactly which closure clauses
B has to prove.

---

## 8. Repo-specific landmines

Learned the hard way; each of these cost real time.

* **`⊆` is shadowed.** `SymbolicIndistinguishability.lean` declares
  `notation p1 "⊆" p2 => ExpressionInclusion p1 p2`, which captures `Finset` subset in that
  file and everything importing it. Symptoms: `ExpressionInclusion` type mismatches on a
  goal you wrote as a set inclusion. Fix: write `∀ k ∈ A, k ∈ B`, or feed
  `Finset.union_subset` / `Finset.Subset.trans` directly.
* **Tuple syntax is shadowed** in `Garbling/`. `Circuits.lean` declares
  `notation "(" o1 "," o2 ")" => WireBundle.PairB o1 o2` and `notation "o" => SimpleB`.
* **The equation compiler on `Expression` is often not defeq.** `Expression` is an indexed
  family, so `rfl` frequently fails where you expect it (`baseVar`, `keySubterms`,
  `strictYields`). Use `simp [f]`, or add `@[simp]` equation lemmas once and reuse them.
* **`induction k` fails on `Expression Shape.KeyS`.** Use structural recursion with explicit
  match arms (`| Expression.VarK n => …`), as in `keySubterms_self`, `atomic_eq_varK`.
* **`bundleBool o` does not syntactically reduce to `Bool`**, so `if v then _ else _` fails
  to find `Decidable`. Use `cond v a b`.
* **`set x := e with h` bites.** Terms you build afterwards still mention `e`, so
  `Finset.Subset.trans` and friends fail to unify against the `x` in the goal. Prefer writing
  the term out, or `rw [h]` first.
* **`split_ifs at h` sometimes closes the goal itself**, giving "no goals to be solved" on the
  next bullet. Prefer `by_cases` + `rw [if_pos …]` / `rw [if_neg …]`.
* **`omega` fails on defeq-but-not-syntactically-equal atoms** that print identically. Build
  the contradiction by hand with `lt_of_lt_of_le` + `absurd`.
* **`set_option maxHeartbeats 2000000`** is already set in
  `Garbling/SymbolicHiding/GarbleProof.lean` for the Lemma 6 induction. Expect to need it.
* **Write files atomically.** `open(p,'w').write(expr)` truncated a source file to 0 bytes
  once when `expr` raised. Write to a temp file and `os.replace`.

---

## 9. Where things are

```
PRGExtension/
  ComputationalIndistinguishability/Def.lean      PolyFamOracleCompPred, the closure property
  Expression/ComputationalSemantics/
    Def.lean                                      encryptionFunctions (§6!), prgFunctions, evalExpr
    PolyTime.lean                                 EfficientPrg/Enc/EvalPrg, the PRG derivation
    Soundness.lean                                symbolicToSemanticSoundnessFromEfficiency
    SoundnessProof/HidingOneKey.lean              reductionToOracle, EncReductionPolyTime, prose analysis
    SoundnessProof/HidingOnePrgSeed.lean          reductionToPrgOracle, PrgReductionPolyTime
  Garbling/Security.lean                          garblingSecureFromEfficiency
VCVio2/VCVio/OracleComp/QueryBound.lean           IsQueryBound, PolyQueries (not imported; see §5)
```

Companions: `report.md` (what the development is, §6 = the assumption boundary),
`PRGExtension-Analysis.md` (original defect analysis with STATUS markers),
`CHANGELOG.md` (dated record — read `[2026-09-17a]` and `[2026-09-17d]` for the efficiency
work so far).

Sanity-check scripts, not part of the library, run with `lake env lean scratch/<f>.lean`:
`TwoGateFixpoint`, `ExtractKeysSelfCounterexample`, `GarbleSideCondition`, `DupTrailing`,
`GarbleCorrectness`.
