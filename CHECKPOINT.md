# CHECKPOINT — handoff for completing the cost semantics

**Branch** `prg-fixes` · `lake build` clean and warning-free, `sorry`-free, no `axiom`
declarations in `PRGExtension/`.

Read `report.md` first for what the development *is*, and `summary.md` for how the proofs
chain together, the deviations from the pen-and-paper proofs, and the adversary model.

**Status (2026-09-18c).** The two obligations this file was written to hand off — `(O1)`
`EncReductionPolyTime` and `(O2)` `EvalEfficiencyFromPrimitives` — **are now theorems**, and
so is the PRG sampler's efficiency.  §6 of the previous checkpoint (the unconstrained
`encryptLength`) is fixed.  What remains is Design B: making the *interface* they are proved
against into theorems too, and the non-vacuity witness.  See `CHANGELOG.md [2026-09-18c]`.

**The interface has since been audited against poly-size circuits (2026-09-18d).  Read §3.0
before starting Design B** — one finding is a blocker that reorders its steps, and one
restates what the non-vacuity witness has to be.

**Design B step 1 was attempted on 2026-09-21 and is impossible as written.  Read §3.1** —
it has the proof of why, and the replacement, which is **now implemented**: `IsPolyTime` is a
concrete predicate (`GenPolyTime`), and `PolyTimeModel` / `BitOpsEfficient` / LM18
Definition 1 / (O1) / (O2) are theorems about it rather than assumptions.

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
-- added 2026-09-18c
#print axioms PRG.garblingSecureFromCostModel    -- [propext, Classical.choice, Quot.sound]
#print axioms PRG.encReduction_polyTime          -- same
#print axioms PRG.evalEfficiencyFromPrimitives_holds -- same
#print axioms PRG.prgEnvSampler_polyTime         -- same
#print axioms PRG.shapeLength_poly               -- same
-- added 2026-09-21
#print axioms PRG.genPolyTimeModel               -- same
#print axioms PRG.gen_encReduction_polyTime      -- same
#print axioms PRG.gen_efficientEvalPrg           -- same
#print axioms PRG.garblingSecureGenerated        -- same
```

If `sorryAx` ever appears in that list, stop and find out why — §5 explains the most likely
cause (VCVio2 has live `sorry`s in modules the build currently does *not* import).

---

## 2. What was done, and what it does and does not buy

`ComputationalSemantics/CostModel.lean` introduces a second predicate, `IsPolyTimeFn`, on
*function* families (`famOracleFn`), because sequencing two oracle computations needs a
continuation and a continuation is a function.  `PolyTimeModel` bundles fifteen closure
clauses over the pair; `BitOpsEfficient` names seven concrete bit-vector operations.  Against
those:

| Was assumed | Now | Where |
|---|---|---|
| `EncReductionPolyTime` | theorem | `encReduction_polyTime` |
| `EvalEfficiencyFromPrimitives` | theorem | `evalEfficiencyFromPrimitives_holds` |
| efficiency of `prgEnvSampler` | theorem | `prgEnvSampler_polyTime` |
| `PrgReductionPolyTime` | theorem (since 2026-09-17) | `reductionToPrgOracle_polyTime` |

`garblingSecureFromCostModel` (`Garbling/Security/SecurityFromPrimitives.lean`) is the entry point
with all of it composed.

**This is not a cost semantics.**  It trades two opaque assumptions about two large recursive
terms for twenty-two small ones, each checkable by eye against one definition.  Nothing shows
a concrete `IsPolyTime` satisfies them.

**Two dead ends are recorded in `CostModel.lean`'s header — do not retry them.** Quantifying
`bind`'s continuation pointwise over arbitrary semantic value families typechecks but is
useless at a `Pair` node; an unconstrained `pure` clause makes every pure computation free.
`pureFn` is the constrained form and is the one that works.

Also do not retry **`Equiv.extendSubtype`** for anything over `ℕ` — it needs `[Fintype α]`.
`exists_perm_extending` in `Expression/Lemmas/PseudorandomRenaming.lean` is the replacement.

### Calculi considered and rejected (2026-09-18e)

Three published calculi were evaluated as candidates to adopt wholesale.  **None is a fit**,
and it is worth knowing why before someone proposes them again.

| Paper | Verdict |
|---|---|
| Liao, Hammer & Miller, *ILC* (PLDI '19) | No, and not close |
| Atkey, *Polynomial Time and Dependent Types* (POPL '24) | Right problem, wrong instrument |
| Niu, Sterling, Grodin & Harper, *calf* (POPL '22) | Closest; read it, don't adopt it |

**ILC.**  Its `PPT` judgment is metatheoretic, not typed — §6.1 says outright that "the ILC
typing rules do not guarantee termination, let alone polynomial time normalization, so we
must tackle this in metatheory".  Adopting it swaps one externally-imposed assumption for
another and discharges nothing.  Its notion is also defined only for *closed whole systems*
("an entire system of ITMs"); per-entity PPT, which is what the clause list is entirely
about, is explicitly deferred to future work.  Its real contribution — affine write tokens
enforcing confluence — solves scheduling nondeterminism in concurrent channel-passing
protocols.  `OracleComp` is sequential.  Relevant only if this project ever moves to UC.

**Atkey.**  Attractive because his systems are sound *and complete* for PTIME, which is the
two-sided property non-vacuity needs, and because his `Dist` monad (§4.3.2) has the same
free-monad-over-choice-nodes shape as `OracleComp`.  Rejected because: it is a type theory,
not a predicate on existing terms, and Lean is not QTT, so bridging means deep-embedding QTT
plus the calculus plus Dal Lago–Hofmann realisability; the primitives (`enc.encrypt`,
`prg0`, `List.Vector.append`) would have to become well-typed *syntax* rather than opaque
Lean functions, which replaces this development's interface to LM18 Definition 1; the system
is uniform and F2 commits us to non-uniform; and his `ND`/`Dist` effects are guess/coin
effects the program owns, not an external oracle whose implementation the game supplies.
Decisively, his case against cost-as-effect — that it "delivers only conspicuous consumption"
— does not bite here, because §3.1 has already conceded that primitive costs are parameters.
The approach he argues against is the one to use.

*Taken from Atkey:* the `Dist` remark that "the use of a function type here ensures that each
branch of the tree is constructable in polynomial time, not the whole tree".  That settles how
`cost (query i t >>= k)` must be defined — see the constraint box in §3.1.

**calf.**  The closest, and the one to read before writing `cost`.  Its conclusion names
exactly the difficulty that forced `IsPolyTimeFn` into existence: deep-embedding/operational
cost "is not compositional because one may speak about operational semantics only on closed
terms and must quantify over closing instances for open terms".  `IsPolyTimeFn` is the ad-hoc
shadow of calf's CBPV `F ⊣ U` adjunction, which makes the cost of a function itself a
function.  Its `isBounded` rules (Return / Step / Bind / Relax) are the shape ours converge
to.  Rejected because: it has **no probabilistic or oracle effects at all** (zero occurrences
of *probabilistic*, *random*, *nondeterministic*, *oracle*, *distribution* in 31 pages — every
case study is deterministic), and composing a cost writer effect with a probability monad is
unaddressed and genuinely subtle; it is **axiomatic** (§1.8.3 keeps `F(A)` deliberately
abstract, and the Agda implementation postulates the signature), which fails §1's no-`axiom`
check outright, so adopting it means building its model (§6, Artin gluing); and its phase
distinction solves a problem we avoid by construction — §1.8.3 notes that the transparent
version is unproblematic "because of the stratification of the source language (of programs)
and target language (of recurrences)", which is exactly our situation, `OracleComp` being the
source and Lean the target.  calf *instruments* programs with `step`; instrumenting
`OracleComp` would break every behavioural equality (`reductionToOracleSimulateEq`,
`adversaryView_eq_gStar`) down to the extensional phase.  We measure instead.

*Taken from calf:* state the primitive layer as **costs carried as data, not opaque
predicates**.  `PolySized` already does this for widths (its `width` field is data for exactly
this reason); the remaining step is that each `BitOpsEfficient` clause's eventual obligation
should be arithmetic in those widths.

**The pattern.**  Each paper's central machinery addresses a difficulty this framework
sidesteps: ILC's, concurrency (we are sequential); Atkey's, controlling iteration (the clause
list has no fixpoint); calf's, analysing cost inside the theory whose programs you analyse
(ours are a free monad we measure from outside).  Three different reasons, same conclusion —
the cost model needed here is small because the setting is constrained.

---

## 3. The remaining work

### 3.0 Audit of the interface against poly-size circuits (done 2026-09-18d)

Before building a concrete `cost`, the 22 clauses (`PolyTimeModel` 15 + `BitOpsEfficient` 7)
were checked against the textbook notion Design B will have to instantiate: **families of
poly-size oracle circuits**.  Four findings; F1 is a blocker and changes the step order.

Reassuring half first: **no clause admits recursion, iteration or unbounded repetition** —
everything is straight-line composition — so the interface cannot build a brute-forcing
distinguisher.  And `BitOpsEfficient` is uniformly clean, because every one of its clauses
already carries its own `PolyLength` side condition.  14 of the 22 need nothing.

**F1 — three clauses are false for arbitrary type families. (Blocker — FIXED 2026-09-18e.)**

A poly-size circuit family has I/O width bounded by its size, so every domain and output
family must be poly-sized.  Nothing in the statements of

```
valId  : D → D        valFst : D × E → D        valSnd : D × E → E
```

constrains `D` or `E`.  Take `D κ := BitVector (2 ^ κ)`: `valId` demands a poly-size circuit
with `2 ^ κ` output wires.  A further five clauses — `valUnit`, `uniformBits`, `uniformKeys`,
`constVec`, `nilVec` — are generic in a domain they only *discard*, so their truth depends on
whether the model charges for unread input; attach the condition to all eight rather than
litigate that.  (The other clauses are safe because every family they touch either comes from
an assumed-poly-time function or carries `PolyLength`.)

This is **not** a soundness problem.  The theorems in `CostModel.lean` are correctly proved
relative to the interface, and `trivialPolyTimeModel` shows the interface is consistent.  It
is a *satisfiability* problem: no cost-charging model can discharge the interface as written,
and discharging it is exactly what Design B is for.

**Fixed 2026-09-18e.**  `PolySized` (`ComputationalSemantics/Def.lean`) is the poly-size
measure, carrying its `width` as *data* rather than hiding it behind an existential, with
constructors `bitVector`, `bool`, `unit`, `bitEnv`, `keyEnv`, `prod`.  It is now a side
condition on nine clauses — the eight above plus `queryFn`, whose *output* family
`(Spec κ).range (i κ)` is not constrained by its `t`-is-poly-time hypothesis either; that one
turned up while implementing and was not in the original finding.  Size witnesses
`sizedKey`, `sizedShape`, `sizedRedEnv`, `sizedPrgEnv` sit next to `RedEnv` in
`CostModel.lean`; `sizedShape` is where `LengthPoly` enters the size discipline, since without
it `shapeLength` is not polynomially bounded and the family is not poly-sized at all.

This was the old Design B step 2 ("add a size measure"), pulled ahead of step 1 as the audit
indicated.

**F2 — `queryFn`'s oracle index commits the model to non-uniformity.**

`i : (κ : ℕ) → I` carries no computability condition.  That is fine for poly-size circuit
families, where the index is wired in per `κ`, and false in a uniform Turing-machine model.
Both reductions only ever use an index that is a fixed function of `κ`
(`shapeLength κ (enc κ) s`, or `()`), so nothing is lost — but `cost` must be non-uniform to
match, and that should be a deliberate choice rather than a discovery.

**F3 — the randomness oracle's query payload is an entire `PMF`.**

`oracleSpecForRand : OracleSpec Type := fun type => (PMF type, type)`, so `sample` hands the
oracle a whole distribution, not a finite bit-string.  Any `cost` that charges per query must
decide what constructing that argument costs.  `liftVal`'s hypothesis
(`polyTimeFamComp IsPolyTime f`) is what carries the weight today.  Cleanest route: have
`cost` charge `sample (f κ d)` as `cost f` plus the output width, and never look inside the
`PMF`.

**F4 — the non-vacuity target as previously stated has a trivial, useless answer.**

`encryptionFunctions` relates `encrypt` and `decrypt` by nothing — there is no correctness
field — so `encrypt k m = pure ⟨true⟩` is a legal scheme whose IND-CPA left and right oracles
are *literally the same function*.  `constEnc_indCpa` (`scratch/archive/DegenerateEnc.lean`) proves it
is IND-CPA secure against **every** adversary class, `fun _ => True` included.  So "exhibit
`IsPolyTime` jointly satisfiable with IND-CPA security" is answered by the trivial model, and
answered uselessly.

The constraint that actually binds is **`prgSchemeSecure`**, and it cannot be dodged the same
way.  The real oracle answers with `(prg0 s, prg1 s)` for a κ-bit seed; the ideal answers with
a uniform 2κ-bit pair.  The real answer therefore ranges over at most `2 ^ κ` of `2 ^ (2 * κ)`
points, so the unbounded distinguisher "query once, decide membership in the image of
`s ↦ (prg0 s, prg1 s)`" wins with advantage at least `1 - 2 ^ (-κ)`.  No `prg` is secure under
`fun _ => True`, and no degenerate `prg` escapes it: unlike encryption, there is no
entropy-preserving cheat.  *(Counting argument, not formalised — the advantage bound is a
real measure-theoretic exercise in this framework.  The IND-CPA half above is a Lean
theorem.)*

Two consequences:

* Step 6 below is restated in terms of PRG security.
* Independent hardening, required by no theorem: give `encryptionFunctions` a correctness
  field (`decrypt k (encrypt k m) = m`), closing the degenerate loophole on the IND-CPA side
  too.  Cheap, and it makes `EncReductionPolyTime`'s content less accidental.

### 3.1 Design B — attempted 2026-09-21; step 1 is impossible as written

**Read this before writing any code.**  Step 1 used to say: define
`cost : OracleComp spec α → ℕ` by recursion over the free monad, charging for local
computation.  That cannot be done, and the reason is structural rather than a matter of
effort.  Both obstructions are formally demonstrated in `scratch/findings/CostAttempt.lean`.

**Obstruction A (fixable).**  The supremum over a query's response type need not exist in `ℕ`.
`oracleSpecForRand : fun type => (PMF type, type)` makes the response type of a randomness
query an *arbitrary* `Type`, so `⨆ u, cost (k u)` ranges over an infinite family — and
Mathlib's `⨆` silently returns `0` there (`(⨆ n : ℕ, n) = 0`).  A `ℕ`-valued `cost` is
therefore quietly wrong, not merely partial.  Fixable by using `ℕ∞` or, better, a bound
*relation* in calf's `isBounded` style.

**Obstruction B (fatal).**  *Local running time is not a property of an `OracleComp` term.*
The free monad records oracle queries and nothing else: every local computation lives inside
a Lean function — a query payload, a continuation, or the value under `pure` — where no
structural recursion can see it.  Two consequences, both proved:

* `cost_blind`: **any** `cost : OracleComp spec α → ℕ`, structural or not, is invariant under
  replacing a continuation by an extensionally equal one.  In Lean a brute-force search and a
  lookup table with the same graph are the *same function*.
* `cost₁ (pure x) = 0` for every `x`, however expensive `x` was to compute.

So a structurally-defined cost on `OracleComp` **is** a query count, however it is dressed up
— which is exactly the vacuity trap the box below warns about.  The box was right; step 1 was
not a way to satisfy it.

> **The constraint that motivated step 1, retained because it is still the design goal.**
> A cost model must charge for local computation, not only for oracle queries.  A query-only
> instance satisfies `PolyTimeClosedUnderComposition`, all fifteen `PolyTimeModel` clauses and
> all seven `BitOpsEfficient` clauses — `polyTimeFamComp` degenerates to "makes one query" —
> while making `encryptionSchemeIndCpa` unsatisfiable for any non-degenerate scheme, since a
> distinguisher may brute-force the key with one query and exponential local work.  Neither
> step 4 nor step 5 of the old plan caught this.
>
> Atkey's rule, still correct for the query-counting *component*: cost each branch, not the
> tree — `cost (query i t >>= k) = cost t + 1 + ⨆ a, cost (k a)`.  The tree has `|range i|`
> branches; costing it would make `bindFn` false immediately.

#### The replacement: generate the class rather than measure the terms

Since cost cannot be read off a term, supply it with the term.  Define `IsPolyTime` as the
**smallest class containing the primitives and closed under the combinators** — an inductive
family whose *derivations are the implementations*.  This is realizability with derivation
trees as programs, and it needs no machine model.

Prototyped in `scratch/archive/GenClass.lean`, which is further along than a sketch:

* `PolyVal enc prg : famComp D O → Prop` — generated value functions: `id`, `fst`, `snd`,
  `unit`, `pair`, `precomp`, `bind`, `uniformBits`, `uniformKeys`, the seven bit primitives,
  and `encrypt`/`prg0`/`prg1` as generators (LM18 Definition 1 becomes a *generator* rather
  than a hypothesis).
* `PolyFn enc prg` — generated oracle computations: `ofPure`, `ofSample`, `bind`, `precomp`,
  `query`.
* `GenPolyTime enc prg : PolyFamOracleCompPred` — close over the trivial input.
* `polyVal_to_famComp` — **the bridge, proved**: `PolyVal f` implies
  `polyTimeFamComp (GenPolyTime enc prg) f`.

Both inductives elaborate (the indices range over `I : Type` and `ℕ → Type`, which was the
viability risk) and the bridge closes.  What this buys: `PolyTimeModel` and
`BitOpsEfficient` stop being assumptions and become theorems about a concrete class; the
class contains no iteration constructor, so brute force is not in it and security is
plausible; and non-vacuity becomes "this class is not empty", which is immediate.

What it costs, and this must be stated wherever the result is: the class is generated by
*these* primitives, so IND-CPA against it is a weaker hypothesis than IND-CPA against all
PPT adversaries — the usual algebraic/generic-adversary trade.  Weaker, but sound and
non-vacuous, which is a strict improvement on an assumed interface.

#### Findings from the prototype

**F5 — `PolySized` is needed on *outputs*, not just domains.  Handled.**
`polyVal_to_famComp` requires `PolySized Output` as well as `PolySized Input`.  No clause-level
change was needed in the end: once F6 moved the value clauses off the encoding, the only place
that crosses it is `PolyTimeModel.valToFamComp`, which carries both conditions.

**F6 — `PolyTimeModel`'s value-level clauses must not be phrased via `polyTimeFamComp`.
FIXED 2026-09-21.**  This was the blocker for the whole pivot, and a defect in the
*interface*, found only by trying to instantiate it.

`PolyTimeVal IsPolyTime f` is defined as `polyTimeFamComp IsPolyTime f`, i.e. `IsPolyTime`
applied to the computation that *queries for its input* and then runs `f`.  A clause with no
`PolyTimeVal` hypotheses (`valFst`) discharges immediately through the bridge.  A clause that
*takes* `PolyTimeVal` hypotheses (`valPair`, `precompVal`, `bindVal`, `pureFn`, `liftVal`,
`precompFn`, `queryFn`) cannot: its hypotheses arrive in the input-querying encoding and
getting back to `PolyVal` needs the **converse** of the bridge — an inversion of `PolyFn` on
a term whose constructors are Lean functions.  Both cases are demonstrated at the end of
`scratch/archive/GenClass.lean`.

Fixed by giving `PolyTimeModel` two more fields: `IsPolyTimeVal : PolyFamCompPred`, against
which every value clause is now stated, and `valToFamComp`, the one-directional link to the
framework's `polyTimeFamComp` (carrying F5's two `PolySized` conditions).  `EfficientEncVal`
and `EfficientPrgVal` are the value-level restatements of LM18 Definition 1.

Reusing `polyTimeFamComp` was economical when the interface was assumed — nothing ever had to
be proved *about* it.  It stops being economical the moment you try to build a model.

**F7 — `PolyTimeClosedUnderComposition` inherits the same non-invertibility.**  It is stated
with `polyTimeFamComp`, so discharging it for `GenPolyTime` would need to read a value
function back out of the input-querying encoding.  It therefore remains a *hypothesis* of
`garblingSecureGenerated`, where the interface's own clauses do not.  Fixing it means
restating it at the value level in `ComputationalIndistinguishability/Def.lean`, which is
more invasive than F6 was; also note that `evalEfficiencyFromPrimitives_holds` now takes a
`ValFromFamComp` hypothesis for the same reason, while `efficientEvalPrg_holds` — the version
the capstone actually uses — does not.

#### Done 2026-09-21

0. ~~F6~~ **done** — `PolyTimeModel` carries `IsPolyTimeVal` and `valToFamComp`; F5 folded in.
1. ~~Land `PolyVal` / `PolyFn` / `GenPolyTime`~~ **done** —
   `ComputationalSemantics/GeneratedPolyTime.lean`.
2. ~~Prove `PolyTimeModel` and `BitOpsEfficient` for the generated class~~ **done** —
   `genPolyTimeModel`, `genBitOpsEfficient`; every clause is the matching constructor.  LM18
   Definition 1 likewise (`genEfficientEncVal`, `genEfficientPrgVal`): a *generator*, not a
   hypothesis.  (O1), (O2) and the PRG sampler follow at the concrete predicate
   (`gen_encReduction_polyTime`, `gen_efficientEvalPrg`, `gen_prgEnvSampler_polyTime`), and
   `garblingSecureGenerated` is the capstone.

**F8 — the generated class was far too narrow to be a meaningful adversary class.
FIXED 2026-09-21d.**  Found by inspecting the generator list; it superseded the softer
"weaker but sound and non-vacuous" framing in `[2026-09-21b]`.

Read off the nineteen `PolyVal` constructors: the only one whose *output* is `Bool` is
`bitExpr`, and its *domain* is `fun _ => Fin l → Bool` — a sampled bit environment.  The only
generator producing a `Fin l → Bool` is `uniformBits`, which ignores its input.  There is no
generator taking a `BitVector` to a `Bool`: no indexing, no comparison, no boolean algebra on
ciphertext bits.

Consequently **no distinguisher in the class can produce a Boolean that depends on a bit
vector**, so none can depend on the IND-CPA challenge or on the garbled expression at all.
`encryptionSchemeIndCpa (GenPolyTime enc prg) enc` is therefore satisfied by essentially any
scheme, and the conclusion of `garblingSecureGenerated` is correspondingly weak.  The theorem
is *sound* — it says exactly what it says — but its content is close to nil.

This is a syntactic check over nineteen constructors, not a formalised theorem.  Formalising
it means an induction over `PolyVal` with a "no information flows from `BitVector` to `Bool`"
invariant; worth doing, because it converts an inspection into a guarantee.

Two causes, both now addressed (19 generators → 33).

1. **Missing generators.**  The set was chosen to make the *reductions* expressible, then
   reused as the *adversary* class — a category error.  Added: `index`/`update` (random access,
   position taken as **input**), `bitsToFin`, `notB`/`andB`/`select`/`eqBits`/`xorBits`,
   `finSucc`, `constBits`/`constFin`/`constBool`.
2. **Derivations are finite, so the class was constant-size.**  Added `iterate` (a declared
   polynomial number of passes over a fixed `PolySized` state) and `iterateIdx` (the same, with
   the step able to see the loop counter — needed for inner loops over bit positions).

**A correction to the earlier framing.**  I wrote that bounded iteration "is exactly the
problem LFPL and Atkey solve", implying their machinery had to be adopted.  More precisely:
LFPL exists to **infer** a polynomial bound from a typing discipline.  Generating the class
lets us **declare** it, so the payment discipline is unnecessary — the one trap it guards
against, data growth under iteration, is closed for free by requiring the iteration state to
be a fixed `PolySized` family, which pins the width in the type.  §2's rejection of Atkey
stands; the LFPL entry there should be read as "relevant reference, not machinery to adopt".

**Formal completeness for PTIME is not available**, and the obstruction is structural: it
presupposes a formalised machine model to be complete *with respect to*, which is exactly the
cost generating the class was meant to avoid.  Soundness-by-construction and completeness pull
opposite ways.  `GeneratedPolyTime.lean`'s header carries the informal RAM-simulation argument,
clearly marked as not formalised, plus the list of what *is* proved.

Two membership witnesses now exist in place of the (deliberately unformalised) negative
statement: `polyVal_readBit` and `polyFn_indCpaBitAdversary`, the latter being a distinguisher
that queries the left-or-right oracle and reports a bit of the ciphertext — the exact shape F8
said was unreachable.  These stay true as the class grows, which the negative statement would
not have.

#### What is left

3. **`PolyTimeClosedUnderComposition` (F7)** — still a hypothesis.  In
   `garblingSecureRelative` this is no longer awkward: it is a hypothesis about the *abstract*
   class `A`, where one would not expect to prove it anyway.  It only looked like a defect
   while the same class had to play both roles.  Restating it at the value level remains the
   route if a concrete `A` is ever wanted.
4. ~~**Widen the class.**~~  **Done 2026-09-21d** (19 generators → 33), and then made largely
   moot by `garblingSecureRelative` (2026-09-21e), which states security against an
   **arbitrary** adversary class `A`.  The generated class is used only to *certify the
   reductions*; `A` need only be closed under composition and contain them
   (`ClassContained`).  Its narrowness therefore no longer weakens the conclusion.  Cite
   `garblingSecureRelative`, not `garblingSecureGenerated`.
5. **A quantitative bound, if one is wanted.**  Index the derivations by a cost, using
   `PolySized.width` as the quantity costs are functions of.  This needs the derivations to be
   **`Type`-valued rather than `Prop`-valued** — `PolySized` carries its width as data, and a
   `Prop` derivation cannot yield it by large elimination.  `GenPolyTime` would become
   `Nonempty (PolyFn …)`, which also reads correctly as "there exists an implementation".
   Not needed for soundness; needed only to connect the class to a standard complexity class.

### 3.2 Smaller, independent

* ~~**F9 — computational correctness.**~~  **DONE 2026-09-21h.**
  `Garbling/Correctness/ComputationalCorrectness.lean` proves `garbleCorrectComp`:
  `∀ v ∈ (evalExpr … (Garble c x)).support, EvaluateComp enc prg c v = evalCircuit c x`.
  That is the base paper's correctness definition, `Evaluate(Garble(C,x)) = C(x)`, on real bit
  vectors.  The development now has computational **security** *and* computational
  **correctness**.

  Ingredients, in case they are useful elsewhere: `decrypt_encrypt` on `encryptionFunctions`;
  `evalExpr_decrypt`; `vecTake`/`vecDrop` with `get_append_left`/`get_append_right`;
  `perm_select` (point-and-permute); `xorVarB_eq_xor_val` (the symbolic name-and-parity
  comparison equals XOR of the actual values); `gEvComp_sim` (the simulation lemma, by
  induction on the circuit).

  F4 closed with it: the degenerate scheme is no longer constructible, so IND-CPA is not
  trivially satisfiable.

* **Sharing the substrate between the two schemes.**  `lake build` now builds both roots
  (`PRGExtension` and `SymbolicGarbledCircuitsInLean`, 2026-09-21j), so neither rots — but they
  are still two copies.  They differ by far less than their size suggests: the circuit language
  is identical, the algebras differ by `G0`/`G1`, and the schemes differ only in how `DupC`
  derives its output labels.

  Merging them means putting the two developments in **disjoint namespaces** — they currently
  declare the same names at root level, which is why they cannot appear in one import graph —
  and then factoring the shared substrate (expressions, symbolic indistinguishability,
  computational semantics, the soundness bridge) into modules both import.  Roughly 27 files to
  re-namespace.

  Note the catch before attempting it: the encryption-only proofs are written against the
  *smaller* algebra.  Re-basing them on the extension's `Expression` means every induction over
  `Expression` gains two constructors (`G0`, `G1`) that must be discharged as impossible or
  vacuous.  That is the real cost, not the renaming.

* ~~**An executable garbling implementation, and a refinement proof.**~~  **Half 1 DONE
  2026-09-28.**  `Expression/ComputationalSemantics/Executable/Executable.lean` (`ExecScheme`,
  `evalExprExec`, `evalExprExec_mem_support`, and the lift over the sampled environment) and
  `Garbling/Correctness/ExecutableCorrectness.lean` (`GarbleExec`, **`garbleExecCorrect`**,
  `garbleExec_projective`) give a computable garbling scheme whose output is proved to lie in
  the support of `exprToDistr` and to satisfy `Evaluate(Garble(C,x)) = C(x)`.
  `scratch/checks/ExecDemo.lean` instantiates it with a toy scheme and runs ten circuit evaluations.

  The support-level refinement was the right target: `garbleCorrectComp` is stated over the
  support, so it transports to the implementation directly.  `Garble_projective` transported
  too (`garbleExec_projective`), coin threading and all.

  **`#eval` done 2026-09-28b.**  The first version ran only by kernel reduction, because
  `vecTake`/`vecDrop` consume `shapeLength κ enc …` as data and no concrete
  `encryptionFunctions` is computable.  Fixed by generalising `shapeLength` to `shapeLengthOn`
  (over the ciphertext-length function alone, so the original is *delta*-equal and nothing
  downstream changed), generalising the evaluators the same way, and adding **`ExecEnc`** — an
  implementation with the specification *derived* from it, so `EvaluateComp ex.spec` is
  `EvaluateExec ex` definitionally and `garbleCorrectComp` applies with no bridge lemma.
  `Crypto/ChaCha20.lean` instantiates both primitives; `scratch/checks/ExecDemo.lean` garbles and
  evaluates four circuits under them by `#eval`.

  **Security transported 2026-09-28c.**  The distributional refinement (Half 2) is proved:
  `Core/UniformProduct.lean` supplies the uniform-on-a-product lemma that was not in Mathlib,
  `ComputationalSemantics/ExecutableDistribution.lean` the coin-count measure and the
  change-of-variables induction (**`execDistr_eq`**, `execToDistr_eq`, `toFamDistr_eq`), and
  `Garbling/Security/ExecutableSecurity.lean` the payoff **`garblingSecureExec`** — `garblingSecureRelative`
  for the distributions the implementation actually produces.  650 lines against an estimate of
  600–900.  `randLen` had to become a constant: a supply of type `(n : ℕ) → BitVector (randLen n)`
  is an infinite dependent product, so no distribution over it is expressible.

  **Still assumed, and not a gap this work could close:** `encryptionSchemeIndCpa` and
  `prgSchemeSecure` for the denoted scheme family.  `ExecEncScheme` is an implementation at every
  security parameter, so the fixed-key-size ChaCha20 cannot instantiate it.

* ~~**The "no holes" invariant on `Garble` / `Simulate`.**~~  **DONE 2026-09-28.**
  `Expression/HoleFree.lean` and `Garbling/HoleFree.lean`: `HoleFree`, `holeFree_key` (every
  `Expression 𝕂` is hole-free by the shape index), `holeFree_enc_exists`, and
  **`garble_holeFree`** / **`simulate_holeFree`**.  What LM18 gets from `𝙶𝚋 : … → 𝐄𝐱𝐩`, this
  development now gets from two theorems; the alternative — splitting `Expression` into two
  grammars — is argued against in `FUTURE-WORK.md` (B1–B3).

* `BitOpsEfficient.condAppend` could be derived from `append` plus a conditional, if the
  model gained an `if` clause.  Cosmetic; seven clauses is already short.
* `EfficientEnc` (constant message length) is now only used via
  `EfficientEncPoly.toEfficientEnc`.  It could be retired, at the cost of churning the
  `PolyTime.lean` docstrings.

## 4. What exists to build on

### In this repo

| Thing | Where | Use |
|---|---|---|
| `PolyTimeModel`, `BitOpsEfficient` | `ComputationalSemantics/CostModel.lean` | the clause list Design B must discharge |
| `trivialPolyTimeModel` | same file | consistency check; read its docstring before citing it |
| `PolyLength`, `LengthPoly`, `shapeLength_poly` | `ComputationalSemantics/Def.lean` | the output-length half of the prose argument |
| `PolySized` + constructors | same file | the poly-size measure on type families (F1); `width` is data |
| `sizedKey`, `sizedShape`, `sizedRedEnv`, `sizedPrgEnv` | `CostModel.lean` | the size witnesses the clauses need |
| `PolyVal`, `PolyFn`, `GenPolyTime`, `genPolyTimeModel` | `ComputationalSemantics/GeneratedPolyTime.lean` | the concrete `IsPolyTime` and the discharged interface |
| `garblingSecureRelative`, `ClassContained` | `Garbling/Security/SecurityFromPrimitives.lean` | security against an arbitrary adversary class — **the statement to cite** |
| `cost_blind` | `scratch/findings/CostAttempt.lean` | why a structural `cost` cannot work |
| `polyEvalMono` | same file | monotonicity of `Polynomial.eval` over `ℕ` |
| `PolyTimeClosedUnderComposition` | `ComputationalIndistinguishability/Def.lean:268` | the original closure property — Design B step 4 |
| `polyTimeFamComp`, `simpleCompAsGenComp` | same file, 129–138 | lifts a `famComp` to a `famOracleComp` |
| `composeOracleCompWithSimpleComp` | same file, 237 | oracle-then-pure |
| `reductionToPrgOracle_decompose` | `PolyTime.lean` | the PRG reduction as `compose` |
| Prose cost analysis | end of `HidingOneKey.lean` | the informal proof, now annotated with the one step that was false |

### In the vendored VCVio2 — read the caveats

`VCVio2/VCVio/OracleComp/QueryBound.lean` already has:

* `IsQueryBound oa qb` — `qb` bounds the queries `oa` makes, via `countingOracle`;
* proved `isQueryBound_pure`, `isQueryBound_failure`, `isQueryBound_mono`,
  `isQueryBound_query_iff_pos`;
* `structure PolyQueries` (line 303) — polynomial query bounds for a family.

**Three caveats, all load-bearing:**

1. **`isQueryBound_bind` and `isQueryBound_bind'` are commented out**, and the second has a
   `sorry` inside the comment.  The compositionality lemma **does not exist** and must be
   proved *if* you go this route.  Note after 2026-09-21: query bounding is now known to be
   only a *component* of a cost model and not the interesting one (§3.1, obstruction B), so
   this is no longer on the critical path.  If you do want it, state it as an inductive bound
   relation (`pure`/`failure` ↦ 0, `query >>= k` ↦ `1 + n` when every branch is `≤ n`, plus a
   `Relax` rule) rather than via `countingOracle`; `bind` is then an easy induction instead of
   the hard lemma VCVio2 left undone.
2. `QueryBound.lean` is **not currently imported** — the build pulls in only
   `VCVio2.ToMathlib.Control.MonadTransformer`, `VCVio2.VCVio.OracleComp.OracleComp`,
   `VCVio2.VCVio.OracleComp.DistSemantics.EvalDist`.  Importing it brings in one **live**
   `sorry` (`isQueryBound_iff_probEvent`, line 49).  Using the proved lemmas is fine; using
   that one is not.  Re-run the §1 axiom checks immediately after adding the import.
3. **Query count is not running time.**  `PolyQueries` bounds oracle calls only.  Running
   time additionally needs the cost of local computation — which is where the primitives come
   in.  Do not mistake one for the other.

`OracleComp spec = OptionT (FreeMonad (OracleQuery spec))` (`OracleComp.lean:112`), so every
computation is `pure x`, `query i t >>= k`, or `failure`, and `OracleComp.inductionOn` is the
induction principle.

---

## 5. Repo-specific landmines

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
  match arms (`| Expression.VarK n => …`), as in `keySubterms_self`, `atomic_eq_varK`, and as
  `redFn_polyTime` / `evalExpr_polyTime` do.
* **An inline `match` inside a tactic block captures the local context** into its motive, so
  two syntactically identical matches elaborated in different contexts will not unify.  This
  bit the `Enc` case of `redFn_polyTime`: the fix was to split the arm on the key's three
  constructors and pass the resulting `Bool` to `encNode_polyTime` as a parameter.
* **`convert h using 2` is the workhorse for these goals, but it will invent a spurious
  type-family equality** when the two sides' output families are defeq-but-not-syntactic
  (e.g. `shapeLength κ (enc κ) (PairS s s)` vs `d κ + d κ`).  Pin the family with an explicit
  `(Output := …)` ascription on `h` first; see the `Perm` and `Hidden (VarK n)` arms.
* **Section `variable`s are not auto-included** in a lemma whose *statement* does not mention
  them, and the error is a bare `unknown identifier 'Bops.append'`.  Bind such parameters
  explicitly in the signature.
* **`set_option … in` goes above the docstring**, not between it and the declaration;
  otherwise you get `unexpected token 'set_option'; expected 'lemma'`.
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
  `Garbling/SymbolicHiding/GarbleProof.lean` (Lemma 6) and on `redFn_polyTime` /
  `evalExpr_polyTime`. Expect to need it.
* **Write files atomically.** `open(p,'w').write(expr)` truncated a source file to 0 bytes
  once when `expr` raised. Write to a temp file and `os.replace`.

---

## 6. Where things are

```
PRGExtension/
  ComputationalIndistinguishability/Def.lean      PolyFamOracleCompPred, the closure property
  Expression/ComputationalSemantics/
    Def.lean                                      encryptionFunctions, PolyLength/LengthPoly,
                                                  PolySized, shapeLength_poly, evalExpr
    Efficiency/GeneratedPolyTime.lean             PolyVal/PolyFn/GenPolyTime; the interface
                                                  discharged at a concrete predicate
    Efficiency/PolyTime.lean                      EfficientPrg/Enc/EncPoly/EvalPrg, PRG derivation
    Efficiency/CostModel.lean                     PolyTimeModel, BitOpsEfficient, (O1) and (O2)
    Soundness.lean                                symbolicToSemanticSoundnessFromEfficiency
    SoundnessProof/HidingOneKey.lean              reductionToOracle, EncReductionPolyTime, prose
    SoundnessProof/HidingOnePrgSeed.lean          reductionToPrgOracle, PrgReductionPolyTime
  Garbling/Security/
    Security.lean                                 garblingSecure, garblingSecureFromEfficiency
    SecurityFromPrimitives.lean                   garblingSecureFromCostModel
VCVio2/VCVio/OracleComp/QueryBound.lean           IsQueryBound, PolyQueries (not imported; §4)
```

Companions: `report.md` (what the development is, §6 = the assumption boundary),
`PRGExtension-Analysis.md` (original defect analysis with STATUS markers),
`CHANGELOG.md` (dated record — `[2026-09-17a]`, `[2026-09-17d]` and `[2026-09-18c]` are the
efficiency work).

Sanity-check scripts, not part of the library, grouped by role and run with
`lake env lean scratch/<group>/<f>.lean`: `checks/` is what a reader should run, `findings/`
holds machine-checked refutations, `archive/` superseded records, `probes/` one-off
exploration.  `probes/TwoGateFixpoint`, `findings/ExtractKeysSelfCounterexample`,
`probes/GarbleSideCondition`, `probes/DupTrailing`, `checks/GarbleCorrectness`,
`checks/AxiomCheck` (the §1 suite), `archive/DegenerateEnc` (§3.0 finding F4),
`findings/CostAttempt` (§3.1, why step 1 is impossible), `findings/symgc/` (LM18's Haskell
artifact built and measured against Definition 3 — `bash scratch/findings/symgc/build.sh`), `archive/GenClass` (§3.1, the F6
demonstration — two deliberate `sorry`s marking exactly what the old encoding blocked),
`checks/ExecDemo` (§3.2, the executable scheme garbling and evaluating under ChaCha20 — run it
with `lake env lean -s 65536`), `checks/ChaCha20Kat` (RFC 8439 vectors against OpenSSL),
`archive/PrngFeasibility` (the feasibility probe that scoped the project, superseded by the
library modules).

Two scratch files used **not** to build, both for reasons predating this work; both were
repaired on 2026-09-29 and every scratch file now elaborates.
`findings/ExtractKeysSelfCounterexample` had degraded when `Finset.toList` became
`noncomputable` in Mathlib; it was rewritten as kernel-checked theorems, so the refutation is
now verified rather than `#eval`-printed.  `probes/Instance` imported the *encryption-only*
root, whose `encryptionFunctions` has no `decrypt_encrypt` field; it was repointed at
`PRGExtension`, where `decrypt_encrypt` and `LengthPoly` live.
