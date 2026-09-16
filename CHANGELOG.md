# Changelog

All notable changes to the proofs and code in this repository.
Section numbers in brackets refer to [`PRGExtension-Analysis.md`](PRGExtension-Analysis.md).

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
