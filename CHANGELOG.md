# Changelog

All notable changes to the proofs and code in this repository.
Section numbers in brackets refer to [`PRGExtension-Analysis.md`](PRGExtension-Analysis.md).

## [2026-09-16g] LM18 Lemma 6 proved

Still `sorry`-free.

### Added — `PRGExtension/Garbling/Lemma6.lean`

**`lemma6` (LM18 Lemma 6) is proved.**  Conditions (1) and (2) by induction against
`lemma5core`'s three outputs; condition (3) was already available from `Lemma5.lean`.

Condition (1) — `𝖦⁺(k) ∩ Keys(C̃) = ∅` for every encryption key `k` — is exactly the
`seedFree` side condition of `symbolicToSemanticIndistinguishabilityHidingOneKey`: the
IND-CPA reduction never learns an encryption key, so it must never be asked to compute
`prg0` of it.  The garbling scheme now provably satisfies it.

Supporting lemmas:

* `freshKey_not_in` and **`fresh_chain_contra`** — a fresh variable and an "old" key cannot
  both sit in the chain of one key.  This is the workhorse of the `Compose` cases in both
  directions, and it is where `keySubterms_linear` earns its keep;
* `exprKeys_keyVarsBelow`, `encKeys_subset_exprKeys`;
* `nand_exprKeys`, `nand_encKeys`, `nand_labelKeys` — one-off computations of the `NAnd`
  table's key sets, hoisted out of the induction so the large `simp`s run once (inline they
  blew the heartbeat limit).

### Status of the garbling layer

| obligation | status |
|---|---|
| `lemma4` | **proved** |
| `Lemma5` | **proved** |
| `Lemma6` | **proved** |
| `Theorem4` | **proved** |
| `Lemma7`, `Lemma8` | open — see below |
| `Theorem5` | open |
| `FixpointStepSound` | open |

Lemmas 4–6 and Theorem 4 are pure key bookkeeping.  Lemmas 7 and 8 are a different kind of
statement — they are where the symbolic invariants meet the greatest fixpoint — and they
need machinery that does not exist yet:

1. a membership characterisation for `prgClosure` (saturation, and "everything in the
   closure is in the base or derived from it"), hence that `adversaryKeys e` is closed
   under PRG derivation **and reflects it**.  The `Dup` case needs both directions: from
   `k_z ∈ S` conclude `G0 k_z ∈ S`, and from `k_{1-z} ∉ S` conclude `G0 k_{1-z} ∉ S`;
2. Lemma 4 lifted from `gb`'s output to the whole `Garble c x` expression (the `∉`
   direction above goes through "a non-atomic key is never a *part*", then Lemma 6(1) rules
   out the ancestor clause);
3. lemmas connecting a `SubCircuit`'s garbling to the global one, so that facts about
   `adversaryKeys (Garble c x)` can be applied at a sub-circuit.  `SubCircuit` is defined
   but has no lemmas yet.

---

## [2026-09-16f] LM18 Lemma 5 proved (with Lemma 6's condition (3))

Still `sorry`-free.

### Added — `PRGExtension/Garbling/Lemma5.lean`

**`lemma5` (LM18 Lemma 5) is proved**, together with **`lemma6_cond3`** (LM18 Lemma 6's
condition (3)).

The two come out of **one** induction, `lemma5core`, which proves three things at once:

1. `Gb` maps strongly independent input labels to strongly independent output labels;
2. every output key has no strict PRG-descendant in `Keys((C̃,u))`, and is yielded by some
   key appearing as a *part* of `(C̃,u)`;
3. every key the garbled circuit *uses* is yielded by some key appearing as a part of
   `(C̃,u)`.

They cannot be separated: Lemma 5's `First` case needs (3) for the sub-circuit, and (3)'s
`Compose` case needs Lemma 5's condition (2).  My earlier note that "the four lemmas have
to be done together" was right in spirit but too pessimistic — 5 and 6(3) suffice as a
package, and 6(1)/(2) can then be run against them.

Supporting lemmas, all proved:

* `keySubterms_linear` — a key's chain is linearly ordered, which is what licenses LM18's
  repeated "either `k'' ⪯ k` or `k ≺ k''`" steps;
* `keySubterms_subset_of_mem`, `yields_mem_keySubterms`, `labelKeys_below`;
* `exprKeys_gbEntry`, `extractKeys_gbEntry`, `exprKeys_labelToExpr`,
  `extractKeys_labelToExpr`;
* `sy_G0_self`/`sy_G1_self`, `sy_of_G0_left`/`sy_of_G1_left`, `sy_G0_k`/`sy_G1_k`, `sy_GG4`,
  `sy_varK_of_below`, `sy_to_varK`;
* `lemma5_rearrange` for the `ε`-garbling cases (`Swap`/`Assoc`/`UnAssoc`).

### Changed — `StronglyIndependent` corrected

It now reads `IndependentKeys (labelKeys u) ∧ DistinctLabels u`, following LM18: the
independence clause is about `Keys(w)` **as a whole**.  My earlier version only required
per-label independence plus disjointness of the two halves, which is strictly weaker —
`k` and `G0 k` can sit in disjoint halves and still be dependent, and the `Swap` case needs
the global version.

### Status of the garbling layer

| obligation | status |
|---|---|
| `lemma4` | **proved** |
| `Lemma5` | **proved** (`lemma5`) |
| `Lemma6` condition (3) | **proved** (`lemma6_cond3`) |
| `Lemma6` conditions (1), (2) | open — induction sketched, runs against `lemma5core` |
| `Lemma7`, `Lemma8` | open — need the label invariant against the real fixpoint `adversaryKeys (Garble c x)` |
| `Theorem4` | **proved** (`theorem4_holds`) |
| `Theorem5` | open |
| `FixpointStepSound` | open |

---

## [2026-09-16e] Theorem 4 proved; counter-freshness; Lemma 5/6 statements corrected

Still `sorry`-free.  `garbleCorrect` needs only `propext, Quot.sound`.

### Added — LM18 Theorem 4 (correctness), **proved**

`PRGExtension/Garbling/Correctness.lean`: `parseEncodedBundleCorrect`,
`parseMaskedBundleCorrect`, `gEvCorrect`, `decodeCorrect`, **`garbleCorrect`**, and
`theorem4_holds : Theorem4`.  Ported from the encryption-only framework; the new case is
`Dup`, where `Gb` derives `(G0 k⁰, G0 k¹)` / `(G1 k⁰, G1 k¹)` and `GEv` re-derives
`G0 k` / `G1 k` from the single encoded key — they agree on either input bit.

Two changes were needed to make it go through:

* **`WireLabel.bit` is now a variable index (`ℕ`), not a general `BitExpr`.**  `decodeCorrect`
  is *false* for an arbitrary bit expression: `Decode` compares the encoded bit with the
  mask via `xorVarB`, which returns `none` unless both are variables or negated variables.
  LM18 has this as a standing fact — label bits are atomic symbols `B_h`, the first clause
  of the paper's Condition 1 — so encoding it in the type is faithful, and it lets
  `LabelInvariant` drop that clause.
* `gEnc`/`gMask`/`sEnc`/`sMask` return label *bundles* (what `gEv` consumes), with explicit
  `encodedLabelToExpr` / `maskedLabelToExpr` converters used by `Garble`/`Simulate`.

### Added — `PRGExtension/Garbling/Freshness.lean`

LM18 writes `h ← new` and thereafter treats `B_h, K_h⁰, K_h¹` as fresh.  That bookkeeping
is now explicit and proved: `keyVarsBelow`, `LabelsBelow`, `labelsBelow_mono`,
`makeLabels_below`, **`gb_ctr_mono`** (`Gb` never rewinds the counter) and
**`gb_labels_below`** (`Gb` keeps every output label strictly below the counter it returns).

### Changed — Lemma 5 and Lemma 6 statements corrected

Both now take `LabelsBelow ctr u`.  **Without it they are false**: `u` could already mention
the key variables `2·ctr`, `2·ctr+1` that the `NAnd` case is about to create, or a
`G`-descendant of them, breaking condition (1).  `gb_labels_below` shows the hypothesis
propagates through `Gb`, and `makeLabels_below` establishes it at the top, so it is
available at every inductive step.

(This is the second statement of mine that needed strengthening before it could be
discharged; Lemmas 7 and 8 were corrected the same way on 2026-09-16c.)

### Still open

| obligation | status |
|---|---|
| `Theorem4` | **proved** (`theorem4_holds`) |
| `lemma4` | **proved** |
| `Lemma5`, `Lemma6` | statements corrected; not proved |
| `Lemma7`, `Lemma8` | statements corrected earlier; not proved |
| `Theorem5` | not proved |
| `FixpointStepSound` | not proved |

`Lemma5`'s `First` case needs the disjointness `labelKeys v₁ ∩ labelKeys u₂ = ∅`, which is
exactly what conditions (1)/(2) of the lemma supply — so the strong-independence half is
not separable from the rest, and the four lemmas have to be done together (as in LM18,
where 5 and 6 are proved by parallel inductions and 7/8 depend on 6).

`FixpointStepSound` needs the commutation theory for `replacePRG` against `hideEncrypted`,
`extractKeys`, `exprKeys`, `keySubterms` and `keyRecovery`, plus termination of the
atomicisation iteration.  None of that is started.

---

## [2026-09-16d] Atomicisation lemma; `GEval`; the obligation relocated

Still `sorry`-free; all new results check with only `propext, Classical.choice, Quot.sound`.

### Clarification — LM18 is not at fault

Nothing found in this work contradicts LM18. The `keyRecovery`, reduction-lemma,
`prgSchemeSecure` and `extractKeys_hideEncrypted_self` defects were all in the Lean
extension. The `hidingSideCondition` failure is an *incompleteness of the formalization*:
LM18 Lemma 3 has two cases — `Roots(Keys(e)) ⊆ 𝐊`, proved from IND-CPA, and the general
case, reduced to it by a pseudorandom key renaming — and only the first was implemented.
`scratch/GarbleSideCondition.lean` now confirms the general case is genuinely reached:
at an intermediate fixpoint stage of `Garble andC (true,true)` the keys being hidden are
`{K₅, G0 K₅, G1 K₅}` and `Roots(Keys(view))` is non-atomic, because `K₅` has itself been
hidden away.

### Added — the atomicisation lemma (LM18 Lemma 3, property 1), proved

`SymbolicIndistinguishability.lean`:

* `keySize_le_of_mem_keySubterms`, `G0_not_mem_keySubterms`, `G1_not_mem_keySubterms`,
  `keySubterms_card` — a key chain has exactly `keySize k` distinct members;
* `keySubterms_subset_of_mem_exprKeys`;
* `prgClosure_eq_iterate`, `prgStep_iterate_extensive`, `prgStep_iterate_monotone`,
  `prgStep_iterate_mono_exp`, `mem_iterate_of_strictYields`,
  `mem_prgClosure_of_strictYields` — the bounded `prgClosure` really does reach a whole
  chain (`keySize k ≤ |U|` because the chain sits inside the universe);
* `rOf` — LM18's `r(e)` at a pattern;
* **`hiddenKeys_atomic_of_atomicRoots`** — if `Roots(Keys(e)) ⊆ 𝐊` then every key of
  `Keys(e)` that is *not* recovered is atomic, hence a legitimate IND-CPA target;
* `AtomicRoots`, `atomicRoots_of_atomicKeys`.

### Added — `PRGExtension/Garbling/Evaluation.lean`

`extractPair`, `condSwap`, `xorVarB`, `extractPerm`, `decrypt`, `gEv`, `decode`, `GEval`,
`parseGarbleOutput`, `GEvalExpr`, `testGarbleEval`, and `Theorem4` (LM18 correctness).
`GEv(Dup, ε, (b,k)) = ((b, G0 k), (b, G1 k))` is the PRG case.

`scratch/GarbleCorrectness.lean` checks `Theorem4` by `#eval` on *every* input of `notC`,
`NAnd`, `andC` and `orC` — all pass. Three of those contain `Dup`, so the PRG path in both
`Gb` and `GEv` is exercised; this is evidence that the two definitions are mutually
consistent and faithful to LM18 §4.

### Changed — the remaining obligation relocated

**Removed** `AtomicisationBridge` and `symbolicToSemanticIndistinguishabilityOfBridge`.
The bridge demanded the side condition at *every* fixpoint stage for one globally renamed
expression, which nothing with PRG structure can satisfy — a vacuous hypothesis, the same
defect as the `prgSchemeSecure` bug. Atomicisation must happen per step, not once.

**Added** to `AdversaryView.lean`:

* `FixpointStepSound` — soundness of one step of the greatest-fixpoint iteration;
* `symbolicToSemanticIndistinguishabilityAdversaryViewOfStep`;

and to `Soundness.lean`:

* **`symbolicToSemanticIndistinguishabilityOfStep`** — full soundness, **no side
  conditions**, from `FixpointStepSound` alone.

`FixpointStepSound` is now the single outstanding obligation of the expression layer. Its
docstring records the construction that should discharge it: pick a non-atomic root `k` of
`Keys(v)`; because `k` is a root nothing in `Keys(v)` yields it, so its atomic bottom
`VarK t` satisfies `VarK t ∉ exprKeys v` — exactly the hypothesis `PrgRenameRel.idealize`
needs; the hop shortens every chain through `VarK t`, so iterating reaches atomic roots,
where `hiddenKeys_atomic_of_atomicRoots` applies. What is missing is the termination and
commutation bookkeeping.

---

## [2026-09-16c] LM18 Lemma 2 proved; garbling module and Lemmas 4–8

Still `sorry`-free; all new results check with only `propext, Classical.choice, Quot.sound`.

### Added — LM18 Lemma 2 (proved)

`Soundness.lean`: `PrgRenameRel`, the class of pseudorandom key renamings presented by its
generators (atomic-variable bijections, and re-rooting one PRG node via `replacePRG`,
closed under `symm`/`trans`), and

* **`prgRename`** — expressions related by a pseudorandom key renaming have
  computationally indistinguishable semantics. The atomic generator contributes an *exact*
  equality (`applyRenamePreservesCompSem2`); only the re-rooting generator consumes PRG
  security.

Not formalised: the purely symbolic factorisation result [Mic09, Lemma 2] that every
abstractly `𝖦`-preserving map arises from these generators. The computational content of
Lemma 2 is proved.

### Added — the side condition is discharged on the PRG-free fragment

`AtomicKeys`, `atomicKeys_of_subset`, `seedFree_of_atomicKeys`,
`allParts_subset_keySubterms`, `atomicKeys_hideEncrypted`,
`hidingSideCondition_of_atomicKeys`, and

* **`symbolicToSemanticIndistinguishabilityAtomic`** — soundness with **no** side
  conditions whenever every key subterm is atomic, i.e. the extended framework specialises
  back to the original encryption-only one.

Also `encKeys` (the keys used *as encryption keys*) and
`exprKeys_eq_extractKeys_union_encKeys`, which is LM18's split of `Keys(e)` into parts and
encrypting keys; Lemma 6 is stated over `encKeys`.

### Added — `PRGExtension/Garbling/`

* `Circuits.lean` — LM18 §3 circuits, plus `WireLabel`. **This is the structural change
  the port needed**: a label now carries key *expressions*, where the encryption-only
  framework had `labelType := bundleType ℕ` with keys fixed to `VarK (2n)`/`VarK (2n+1)`.
* `GarblingDef.lean` — `makeLabels`, `gbEntry`, `gb`, `sim`, `gEnc`, `gMask`, `sEnc`,
  `sMask`, `labelToExpr`, `Garble`, `Simulate` (LM18 §4–§5). `Gb(Dup, (b,(k⁰,k¹)))` now
  derives `(b,(G0 k⁰, G0 k¹))` and `(b,(G1 k⁰, G1 k¹))` instead of duplicating the label.
* `Independence.lean` — `labelKeys`, `StronglyIndependent`, `LabelInvariant`,
  `garbledWithLabels`, `SubCircuit`, and:
  * **`lemma4` (proved)** — every key appearing as a *part* of a garbled circuit is atomic.
    PRG-derived keys occur only as encryption keys.
  * `Lemma5`, `Lemma6`, `Lemma7`, `Lemma8`, `Theorem5` — written down as named, type-checked
    propositions rather than `theorem … := by sorry`, so the library stays `sorry`-free and
    the obligations are explicit. Lemmas 7 and 8 are stated faithfully: `S` is the fixpoint
    of the *ambient* garbling and the lemma ranges over `SubCircuit`s, because the `Dup`
    case argues via Lemma 6 about the whole circuit.

### Discovered — `hidingSideCondition` is false for PRG garbled circuits

`scratch/GarbleSideCondition.lean` computes `Garble andC (true,true)` (a `NAnd` feeding a
`Dup` feeding a second `NAnd`). At the fixpoint the hidden key set is `{G0 K₄, G1 K₄}` —
**not atomic**. So the side condition threaded through on 2026-09-16 is not satisfiable by
the intended application; this is LM18's `Roots(Keys(e)) ⊆ 𝐊` failing, now confirmed on a
real garbled circuit rather than a hand-built witness.

### Added — the remaining gap, reduced to one symbolic obligation

`Soundness.lean`:

* `AtomicisationBridge` — for every `e` there is an `e'` with `PrgRenameRel e e'`, whose
  hidden keys are atomic at every stage, and with `PrgRenameRel (adversaryView e') (adversaryView e)`.
  This is the general case of LM18 Lemma 3, and it is **purely symbolic**.
* **`symbolicToSemanticIndistinguishabilityOfBridge` (proved)** — given the bridge,
  soundness holds with **no side conditions**. Every cryptographic step is discharged:
  the renaming hops by `prgRename` (PRG security), the adversary-view hop by IND-CPA, the
  rest by exact equalities.

So the outstanding work on the expression layer is now exactly one statement with no
cryptography in it.

---

## [2026-09-16b] PRG reduction implemented; library is `sorry`-free

`lake build` succeeds with **no `sorry` in `PRGExtension/`**.
`#print axioms symbolicToSemanticIndistinguishability` reports only
`propext, Classical.choice, Quot.sound` — no `sorryAx`, no custom axioms.

### Fixed — the `Ras` step of the fixpoint argument [§4.5]

`symbolicToSemanticIndistinguishabilityAdversaryView` proved
`hide z expr ≈ hide (keyRecovery expr z) expr` via
`H_ext_eq : extractKeys (hide K expr) = extractKeys (hide z expr)`, which is false, closed
by the equally false `extractKeys_hideEncrypted_self`.

Since `Hz : keyRecovery expr z ⊆ z`, moving from `z` to `K` hides exactly `z \ K`, and
`extractKeys (hide z expr) ⊆ K`, so the step is **one** application of
`symbolicToSemanticIndistinguishabilityHidingInner` with removal set
`(z \ K) ∩ allParts (hide z expr)`. Added `hideSelectedRestrict` (restricting the removed
set to `allParts` changes nothing) to justify the intersection, which keeps the removal set
inside the expression so the side conditions apply.

Removed `extractKeys_hideEncrypted_self` and `iterationOrFresh`.

### Added — `reductionToPrgOracle` has a body, and the hop is proved [§4.7-1]

`Def.lean`:
* `keyVal` / `evalExpr_key` — evaluating a key expression is a Dirac `PMF` [§4.7-5].
* `subst3`, `subst3_eq_subst2`.
* Two-index resampling, mirroring the existing one-index chain: `resample3`,
  `resampling3`, `restrict_subst3`, `resampling3EqResample3`, `resample3IsTrivial`,
  `resampleIsTrivial3`, `evalCutAndExtend3`, `veryBoring3`, `resamplingLemma3Prg`,
  `resamplingLemmaPrg`.

`HidingOnePrgSeed.lean`:
* `keyVal_replacePRG`, `evalExpr_replacePRG` — evaluating `replacePRG t i j e` with the
  dummies bound to `(prg0 sd, prg1 sd)` equals evaluating `e` with `t` bound to `sd`.
* `prgReductionVars` (+ the two bounds), `reductionToPrgOracle` with a real body.
* `prgSimulateReal`, `prgSimulateIdeal`, then `reductionToPrgOracleRealEq` and
  `reductionToPrgOracleIdealEq`.
* `symbolicToSemanticIndistinguishabilityPrgIdealization` proved from
  `IndistinguishabilityByReduction`.

**Two hypothesis changes**, both forced by the reduction:
* the side condition is now the syntactic `VarK t ∉ exprKeys expr` (§4.3 item 1), not the
  unusable semantic `targetSeed ∉ adversaryKeys expr`;
* the seed must be **atomic** — the real-world simulation identifies the oracle's uniform
  seed with a key *variable*, which only works when the seed is one. A non-atomic seed
  `G0(K)` has a pseudorandom, not uniform, value.

`PrgSecurity.lean`: the ideal oracle's `seedDistr` is written as two independent draws
rather than `uniformOfFintype` on the product, so it matches the reduction's own sampling
shape (same distribution, no extra lemma needed).

### Added — LM18 Theorem 1 as a composable chain [§5.3]

`PrgHopChain` (inductive) and `prgHopChainSound`. Each hop carries its own side conditions
checked against the *current* expression, so hops compose; `prgHopChainSound` discharges a
whole chain by `indTrans` over the single-seed theorem. Ordering the PRG tree — rewrite a
node only after all its ancestors, so its seed has already become a fresh atomic variable —
is left to the caller, which is where the concrete circuit structure lives.

### Added — LM18 §2.1 independence vocabulary [§5.3, §5.4]

`SymbolicIndistinguishability.lean`: `keySize`, `strictYields_size`,
`strictYields_irrefl`, `strictYields_trans`, `yields` (`⪯`), `IndependentKeys`,
`descendantKeys` (`𝖦⁺(S) ∩ S`), `rootsOf` (`Roots`), `mem_descendantKeys`,
`rootsOf_subset`, `mem_rootsOf`, `rootsOf_independent`, `independentKeys_iff_rootsOf`
(LM18: `S` independent iff `S = Roots(S)`), and `ancestorKeys_eq_empty_iff` — the bridge
showing the ancestor clause of `keyRecovery` fires on exactly the non-independent key sets.

LM18 Lemmas 5–8, which the garbled-circuit proof is stated in terms of, can now be
written down against this library.

---

## [2026-09-16] Correctness fixes to the PRG extension

`lake build` succeeds. `sorry` count: **9 declarations → 4**, and the two *false*
lemmas that the IND-CPA half of the proof rested on are gone.

| | before | after |
|---|---:|---:|
| declarations using `sorry` | 9 | 4 |
| files containing `sorry` | 4 | 2 |
| `AdversaryView.lean` | 12 occurrences | 0 |
| `HidingOneKey.lean` | 4 occurrences | 0 |

---

### Fixed — `prgSchemeSecure` was unsatisfiable [§4.4]

**File:** `PRGExtension/Expression/ComputationalSemantics/PrgSecurity.lean`

`famSeededOracle` samples `Seed` once and then runs a *stateless* `queryImpl` on every
query. `prgIdealOracleImpl` sampled fresh `(r0, r1)` inside `impl`, so the ideal oracle
answered two queries with independent values while the real oracle answered both with the
same `(prg0 seed, prg1 seed)`. A distinguisher that queries twice and compares won with
probability `1 − 2^(−2κ)`, so `prgSchemeSecure IsPolyTime prg` was **false for every
`prg`** and every theorem assuming it was vacuously true.

* `prgIdealOracleImpl` now takes the answer pair as a parameter and returns it with `pure`.
* `seededPrgIdealOracle.Seed` changed from `Unit` to `BitVector κ × BitVector κ`, drawn
  uniformly once — mirroring `seededPrgRealOracle`, which draws one seed once.

### Fixed — `keyRecovery` implemented only half of LM18 Definition 3 [§4.1]

**File:** `PRGExtension/Expression/SymbolicIndistinguishability.lean`

LM18 Def. 3 is
`r(e) = 𝖦*({k ∈ Keys(e) | (k ⋐ e) ∨ (∃k' ∈ Keys(e). k ≺ k')})`.
Only the first disjunct (`extractKeys`) was implemented. The missing *ancestor clause*
is what forbids treating a key as an unknown uniform value while a PRG-descendant of it
is visible; without it the top-level soundness theorem was **false** (counterexample in
§4.1: `⟨G0(K₀), Enc K₀ (Bit true)⟩` vs `⟨G0(K₀), Enc K₀ (Bit false)⟩`).

Added:

* `exprKeys` — LM18 `Keys(e)`: every key *as used*, without decomposing PRG applications
  (`exprKeys (G0 k) = {G0 k}`). Deliberately distinct from `extractKeys` (drops encryption
  keys) and `keySubterms` (recurses into seeds); the three now have clearly separate roles.
* `strictYields k k'` — LM18 `k ≺ k'`.
* `isAtomicKey`, `ancestorKeys`, `mem_ancestorKeys`, `ancestorKeys_subset`,
  `ancestorKeysMonotone`.
* `exprKeysMonotone`, `exprKeys_subset_keySubterms`.
* `import Mathlib.Data.Finset.Union` (for `Finset.biUnion`).

Changed:

* `keyRecovery` now closes `extractKeys view ∪ ancestorKeys (exprKeys view)`.
* `keyRecoveryMonotone` — extended with `exprKeysMonotone` + `ancestorKeysMonotone`.
* `keyRecoveryContained` — rewritten; both halves of the union are bounded by
  `keySubterms p`. (`⊆` is shadowed by `ExpressionInclusion` in this file, so the union
  step feeds `Finset.union_subset` directly rather than using the notation.)
* `AdversaryView.lean`: `H_extract_sub_recovery` passes through
  `Finset.subset_union_left` before `subset_prgClosure`.

Verified on a concrete two-gate garbled circuit
(`scratch/TwoGateFixpoint.lean`): the fixpoint, the recovered key set and the hidden
payloads are **unchanged** by the new clause, i.e. it does not over-recover.

### Fixed — `reductionToOracleSimulateEq{,2}` were false as stated [§4.2]

**File:** `.../SoundnessProof/HidingOneKey.lean`

With `e = G0 (VarK key₀)` the hypothesis `VarK key₀ ∉ extractKeys e` holds
(`extractKeys e = {G0 (VarK key₀)}`), yet the reduction computes `prg0 (kVars key₀)`
while `evalExpr` computes `prg0 oracleKey`. The two `sorry`s in each lemma were therefore
unclosable, and `symbolicToSemanticIndistinguishabilityHidingOneKey` — which depends on
them — was unsound.

Added to `SymbolicIndistinguishability.lean`:

* `strictYields_keySubterms`, `seedFree_G_inner` — if `k` is neither `e` nor a strict
  PRG-ancestor of `e`, it does not occur in `e`'s seed chain.
* `seedFree key₀ e` — LM18 Lemma 3, property 3: `𝖦⁺(VarK key₀) ∩ Keys(e) = ∅`.
* `seedFree_mono` and the constructor projections `seedFree_pair_left/right`,
  `seedFree_perm_left/right`, `seedFree_enc_key/msg`, `seedFree_hidden`,
  `seedFree_G0_chain`, `seedFree_G1_chain`.

Changed in `HidingOneKey.lean`:

* The `'` variants (`reductionToOracleSimulateEq'`, `reductionToOracleSimulateEq2'`),
  previously dead code, are now **declared first and used**: on a `G` node the seed chain
  provably avoids `key₀`, which is exactly their hypothesis.
* Both general lemmas take a new hypothesis `Hseed : seedFree key₀ e`, threaded through
  the induction via the projections above. **All four `sorry`s removed.**
* `reductionToOracleEq`, `reductionToOracleEq2` and
  `symbolicToSemanticIndistinguishabilityHidingOneKey` carry `Hseed` through.
* A stray `noncomputable` displaced by the reordering was reattached to
  `def reductionHidingOneKey`.

### Changed — the `G0`/`G1` game hops replaced by an explicit side condition [§4.3]

**File:** `.../SoundnessProof/AdversaryView.lean`

Under LM18's key-recovery function, a non-atomic key is never a member of the set being
hidden (Lemma 3, property 1), so the two PRG branches of
`symbolicToSemanticIndistinguishabilityHidingInner` are vacuous. ~90 lines and **12
`sorry`s** of `replacePRG` game hops — including two hard-coded "fresh" indices
`9998`/`9999` and two unproved `H_commute` lemmas — were replaced by a two-line
contradiction.

The premise of that argument, `Roots(Keys(e)) ⊆ 𝐊`, is **not** preserved by the fixpoint
iteration, so it is carried explicitly rather than assumed silently:

* New predicate `hidingSideCondition e`, bundling LM18 Lemma 3 properties 1 and 3.
* `symbolicToSemanticIndistinguishabilityHidingInnerMotive` gains `_Hatomic` and `_Hseed`.
* `symbolicToSemanticIndistinguishabilityHiding` gains `Hatomic : hidingSideCondition expr`.
* `symbolicToSemanticIndistinguishabilityAdversaryView` gains
  `Hatomic : ∀ S, hidingSideCondition (hideEncrypted S expr)`.
* `symbolicToSemanticIndistinguishability` (in `Soundness.lean`) gains `Hatomic1`,
  `Hatomic2` for the two expressions.

`scratch/TwoGateFixpoint.lean` exhibits a two-gate garbled circuit whose fixpoint has the
non-atomic roots `G0(K_h^0)`, `G1(K_h^0)`, i.e. the side condition genuinely fails there —
so it is an assumption to be discharged (LM18 Lemma 2 / Theorem 1), not a triviality.

### Removed — dead code at the wrong layer [§4.3]

* `inductive symbolicEquivalence` (`SymbolicIndistinguishability.lean`). Nothing consumed
  it; `Soundness.lean` quantifies over `symIndistinguishable`. Putting a cryptographic
  game hop into the *symbolic* relation also destroys decidability-by-normalisation.
  `replacePRG` is **kept** — it is a genuine pseudorandom key renaming.
* `axiom idealize_PRG_soundness` (`PrgSecurity.lean`). Three independent reasons:
  1. **Duplicative** — its hypotheses and conclusion are literally those of
     `symbolicToSemanticIndistinguishabilityPrgIdealization`, whose own docstring says
     "Replaces `idealize_PRG_soundness` axiom". It asserted as an axiom the theorem the
     development is meant to prove, so nothing is lost by dropping it.
  2. **Dead** — the only occurrence outside its own declaration was in a comment.
  3. **False under the definitions then in force** — with the pre-fix `keyRecovery`,
     `e = ⟨G0(K₀), Enc K₀ (Bit true)⟩` gave `adversaryKeys e = {G0(K₀)}`, so the side
     condition `targetSeed ∉ adversaryKeys e` held for `targetSeed = K₀`, yet the asserted
     conclusion fails for the PRF-based IND-CPA scheme of §4.1. Unlike `sorry`, an `axiom`
     produces no build warning, so a false one is invisible. (After the §4.1 fix the
     ancestor clause puts `K₀` into `adversaryKeys e`, and this witness no longer satisfies
     the hypothesis — checked by computation.)
* `symbolicToSemanticIndistinguishabilityAdversaryView'` (`AdversaryView.lean`), an
  earlier copy of the theorem below it whose last step was `sorry`.
* An unused `have Z := …` in the base case of the fixpoint argument.

### Discovered — `extractKeys_hideEncrypted_self` is FALSE, not merely unproved [§4.5]

**File:** `SymbolicIndistinguishability.lean` (now carries the counterexample in a comment)

The analysis document classified this as "the one legitimately open lemma" and proposed a
strengthening. That was wrong. `scratch/ExtractKeysSelfCounterexample.lean` computes:

```
e    = Enc (VarK 0) (VarK 1),  keys = {VarK 0}
hideEncrypted keys e             = Enc (VarK 0) (VarK 1)
Y := extractKeys (…)             = {VarK 1}
hideEncrypted Y e                = Hidden (VarK 0)        -- VarK 0 ∉ Y
extractKeys (hideEncrypted Y e)  = ∅
Y ⊆ ∅                            = false
```

The proposed strengthening fails on the same example. The `sorry` is retained and clearly
flagged: its only consumer,
`symbolicToSemanticIndistinguishabilityAdversaryView`, routes its fixpoint step through the
equally false intermediate `H_ext_eq : extractKeys RHS_view = extractKeys (hideEncrypted z expr)`
(also false on that example, with `Hz` satisfied). The *conclusion* of that step,
`hideEncrypted z expr ≈ hideEncrypted (keyRecovery expr z) expr`, is true — it follows from
IND-CPA applied to the key set `z \ keyRecovery expr z` — so the fix is to re-derive the
step that way rather than via `H_ext_eq`. **This is now the highest-priority open item.**

### Added — reproducible checks

* `scratch/TwoGateFixpoint.lean` — builds `Garble(NAnd ⋙ Dup ⋙ NAnd, (0,0))`, unrolls the
  greatest-fixpoint iteration, and prints `adversaryKeys`, `Keys(adversaryView e)`,
  `Roots(…)` and the non-atomic roots. Doubles as a regression test on `exprKeys`,
  `strictYields`, `isAtomicKey` and `keyRecovery`.
* `scratch/ExtractKeysSelfCounterexample.lean` — the counterexample above.

Run either with `lake env lean scratch/<file>.lean`. Neither is imported by the library.

---

## Remaining `sorry`s

| location | status |
|---|---|
| `SymbolicIndistinguishability.lean` `extractKeys_hideEncrypted_self` | statement is **false**; consumer needs restructuring (above) |
| `HidingOnePrgSeed.lean` ×4 | `reductionToPrgOracle` has no body; both world-equivalence lemmas and the final hop are stubs [§4.7-1] |

## Not attempted

* Completing `reductionToPrgOracle` and the PRG idealisation hop [§4.7-1, §6 step 9].
* LM18 Theorem 1 / Lemma 2 — PRG independence and general `𝖦`-preserving key renamings,
  which is what would discharge `hidingSideCondition` [§5.3, §6 step 10].
* Porting `Garbling/**` [§5.4, §6 step 11].
* The `Common` library split and the `Op`-parameterised AST [§7].
