# Changelog

All notable changes to the proofs and code in this repository.
Section numbers in brackets refer to [`PRGExtension-Analysis.md`](PRGExtension-Analysis.md).

## [2026-09-18] — **[Mic09, Lemma 2] complete**: the mixed case closed

The remaining gap from `[2026-09-17e]` — a renaming that *mixes* permutation of the roots
with growth of PRG structure over keys that stay put — is closed.  Both directions of
[Mic09, Lemma 2] now hold for this algebra, so LM18's two generators are **exhaustive** and
`PrgRenameRel` loses nothing by taking them as the definition.

### Added — `Expression/Lemmas/PseudorandomRenaming.lean`

* **`prgRenameRel_substKeys_general`** — every injective renaming of the roots with pairwise
  independent images is a pseudorandom key renaming.  **No freshness hypothesis**: `ρ` may
  send an occurring key to a chain built over another occurring key.

  The proof is the paper's own factorisation.  Shift every occurring root past everything in
  play — a bijection, hence the `atomic` generator — which makes the renaming fresh, then
  grow the structure there with `prgRenameRel_of_freshRenaming`.  Formally `ρ` factors as
  `ρ ∘ r⁻¹` after `r`, with `r n = N + n` on the occurring indices for `N` beyond
  `keySubterms e` and beyond every variable of every image.
* `substKeys_comp` — substitutions compose.
* `keySubterms_substKeys_varK`, `mem_occIdx_substKeys_varK` — renaming the roots renames the
  occurring variables, so `occIdx (substKeys (K ∘ r) e) = r '' occIdx e`.

### Removed

`prgRenameRel_rename_then_grow`, subsumed by the general theorem.

### Status

The symbolic side of the framework has no remaining gaps.  What is left is the cost semantics
for `OracleComp`, which would move `EncReductionPolyTime` and `EvalEfficiencyFromPrimitives`
from assumed to proved, and the §7 refactor.

## [2026-09-17e] — [Mic09, Lemma 2]: the generation direction proved; the earlier statement was wrong

### Corrected — the previous `Mic09Lemma2General` was false as stated

It carried the hypothesis *"distinct occurring keys receive images with distinct atomic
bases"*.  That excludes `growOne t i j`, which sends `i` to `G0(K_t)` and `j` to `G1(K_t)` —
both with base `t` — i.e. it excluded the very generator it was meant to subsume.  Checked
mechanically before replacing it.  The correct condition is that the images are **pairwise
non-yielding** (independent), which is `FreshRenaming.indep`.

### Added — `FreshRenaming` and the generation theorem

* **`FreshRenaming e ρ`** — `ρ` moves each atomic key occurring in `e` onto a key expression
  built entirely over *new* variables (`fresh`), injectively (`inj`), with the images
  pairwise independent (`indep`).  `fresh` is what makes each `idealize` seed absent from the
  expression; `indep` is what stops a seed being revealed alongside a key derived from it.
* **`prgRenameRel_of_freshRenaming`** — every fresh independent renaming is reachable from
  LM18's two generators.  By induction on `∑ keySize (ρ n)`: all-atomic images give the
  `atomic` generator; otherwise idealising at the bottom of one image's chain shortens it by
  exactly one (`keySize_rp`) and preserves all three conditions (via `rp_inj` and
  `strictYields_rp_reflect`), so one `symm idealize` hop plus the induction hypothesis
  finishes.
* **`prgRenameRel_rename_then_grow`** — the composite LM18 actually uses: rename the roots by
  an arbitrary bijection, then grow the PRG structure.

### Added — supporting results

* **`exists_perm_extending`** — extending a finite injection that moves its domain off
  itself to a permutation of `ℕ`, as a product of transpositions with disjoint supports.
  Mathlib's `Equiv.extendSubtype` assumes a `Fintype` and so does not apply to `ℕ`.  This is
  what the base case needs.
* `occIdx` + `mem_occIdx` — the atomic key indices occurring in an expression.
* `substKeys_congr`, `substKeys_id`, `exprKeys_substKeys`, `keySubterms_substKeys`,
  `keySubterms_substKeys_sub`, `substKeys_rp_comm`, `substKeys_key_ne_varK`.
* `atomic_eq_varK`, `keySubterms_baseVar`, `keySize_rp_le`, `rp_eq_varK`.

The `Compose`-style step needed one trick worth recording: `substKeys_rp_comm` wants
`∀ n, ρ n ≠ K_t`, but independence only bounds the *occurring* indices.  The proof first
replaces `ρ` by a copy that maps every non-occurring index above `t` — harmless, since
`substKeys` only reads `ρ` on `occIdx e` (`substKeys_congr`).

### Still not covered

A renaming that *mixes* permutation and growth — one that both permutes occurring keys and
grows structure over keys that stay put.  It should factor as (bijection) ∘ (fresh growth);
the factorisation is not formalised.  Nothing depends on it.

## [2026-09-17d] — Plumb the derived PRG efficiency through to the top

Follow-up to `[2026-09-17a]`: `reductionToPrgOracle_polyTime` was proved but referenced only
in comments, so `garblingSecure` still took `PrgReductionPolyTime` on faith and the
derivation counted for nothing.  Likewise `EfficientPrg` and `EfficientEnc` were stated but
consumed by nothing.  Both fixed.

### Added — `ComputationalSemantics/PolyTime.lean`

* **`EvalEfficiencyFromPrimitives`** — names the one cost-semantics step the abstract model
  cannot take: `EfficientEvalPrg` ought to *follow* from efficiency of the two primitives
  (`evalExpr` does one `encrypt`/`prg0`/`prg1` call per node of a fixed expression), but
  turning "per node" into a polynomial bound needs a cost semantics for that recursion, and
  `PolyFamOracleCompPred` is opaque.  This is the same missing ingredient that keeps
  `EncReductionPolyTime` a hypothesis.
* **`reductionToPrgOracle_polyTime_of_primitives`** — `PrgReductionPolyTime` from LM18
  Definition 1 alone, given that step.  `EfficientPrg`/`EfficientEnc` are now load-bearing
  rather than documentation.

### Added — `ComputationalSemantics/Soundness.lean`

* **`symbolicToSemanticSoundnessFromEfficiency`** — same conclusion as
  `symbolicToSemanticSoundness`, but taking the two claims that *imply*
  `PrgReductionPolyTime` (the sampling prefix is efficient; the scheme evaluates efficiently)
  instead of assuming it.  `Soundness.lean` now imports `PolyTime.lean`.

### Added — `Garbling/Security.lean`

* **`garblingSecureFromEfficiency`** — the recommended entry point.  `garblingSecure` is kept
  for callers who would rather assume `PrgReductionPolyTime` directly.

### Status

`EncReductionPolyTime` remains the only efficiency hypothesis that is assumed rather than
derived, and `EvalEfficiencyFromPrimitives` is the one step that would discharge the rest.
Both come down to the absence of a cost semantics for `OracleComp`.

## [2026-09-17c] — [Mic09, Lemma 2]: factorisation of a pseudorandom key renaming

### Added — `Expression/Lemmas/PseudorandomRenaming.lean` (new)

`PrgRenameRel` *defines* a pseudorandom key renaming by LM18's two generators, because that
is what the soundness proof consumes.  [Mic09, Lemma 2] is the symbolic result behind the
definition — every `𝖦`-preserving `α_K : S → 𝐊*` is the unique extension of a bijection
between `Roots(S)` and `Roots(α_K S)` — and was previously not formalised at all.

* `substKeys ρ` — substitution of a key expression for each atomic key variable.
* `GPreserving α` — `α ∘ G_b = G_b ∘ α`.
* **`gPreserving_eq_substKeys`** — a `𝖦`-preserving map *is* `substKeys` of its restriction
  to the atomic keys, and **`gPreserving_ext`** — two such maps agreeing there are equal.
  Together: existence and uniqueness of the extension, which is [Mic09, Lemma 2]'s first
  half.
* **`rootsOf_keySubterms`** — the roots of a chain-closed key set are exactly its atomic
  members.  This is what makes "determined on `Roots(S)`" the same statement as "determined
  on the atomic keys", so the factorisation above is the paper's.
* `growOne t i j` — the leaf substitution sending `K_i ↦ G0(K_t)`, `K_j ↦ G1(K_t)`: the
  inverse of one `idealize` hop, expressed as a map on the roots.  `rp_substKeys_growOne`
  proves the round trip `replacePRG (K_t) i j ∘ substKeys (growOne t i j) = id`, with the
  side conditions discharged by `keySubterms_substKeys_growOne` and
  `exprKeys_substKeys_growOne_no_t`.
* **`prgRenameRel_substKeys_atomic`** and **`prgRenameRel_substKeys_growOne`** — each of the
  two generators is such an extension.  (The first needed `applyBitRenaming_id` and
  `substKeys_varK` to identify `substKeys (K ∘ r)` with `applyVarRenaming`.)
* `substKeys_atomic_compInd`, `substKeys_growOne_compInd` — the computational consequences,
  through `prgRename`.

### Not proved — `Mic09Lemma2General`

The converse direction: that *every* `𝖦`-preserving extension is reachable from the two
generators.  Stated as a named `Prop` with the intended argument (iterate `growOne`,
shortening `∑ keySize (ρ n)`) and an explicit warning that its hypothesis is this
formalisation's reading of "a bijection between `Roots(S)` and `Roots(α_K S)`" and has not
been checked to be exactly right.  **Nothing depends on it**: the soundness proof only ever
builds renamings from the generators, never analyses an arbitrary one.

### Moved

`keySubterms_self`, `keySubterms_of_G0`, `keySubterms_of_G1` from
`Garbling/SymbolicHiding/GarbleHole.lean` to `Expression/Lemmas/ReplacePRG.lean` — they are
generic expression-layer facts and are now needed on both sides.  `Garbling/Circuits.lean`
imports `ReplacePRG` so the Garbling layer still sees them.

## [2026-09-17b] — `PRGExtension/Garbling` restructured to mirror the original

Pure refactor: files moved and merged, **no proof changed**.  The declaration set is
identical before and after (263 declarations, verified by diff), the build is clean and
`sorry`-free, and axiom footprints are unchanged.

`PRGExtension/Garbling` now has exactly the file and folder layout of
`SymbolicGarbledCircuitsInLean/Garbling`, with content assigned by the same roles:

| File | Was |
|---|---|
| `Circuits.lean` | `Circuits.lean` (unchanged) |
| `GarblingDef.lean` | `GarblingDef.lean` (garbling half) + `Evaluation.lean` — as in the original, `GEval` lives with the scheme definition |
| `Simulate.lean` | the `sim` / `SEnc` / `SMask` / `Simulate` half of `GarblingDef.lean` |
| `Correctness.lean` | `Correctness.lean` (unchanged) |
| `SymbolicHiding/Lemmas.lean` | `Freshness.lean` + `Independence.lean` + `GbStage.lean` + the `LabelValueIn` / `LabelZeroIn` definitions |
| `SymbolicHiding/GarbleProof.lean` | `Lemma5.lean` + `Lemma6.lean` + `GarbleKeys.lean` (garbling side) + `GarbleFixpoint.lean` + `GbStage.hyps` / `GbStage.labelKeys_yielded` |
| `SymbolicHiding/GarbleHole.lean` | `ViewKeys.lean` + `Lemma7.lean` + `lemma7_value` |
| `SymbolicHiding/SimulateProof.lean` | `GarbleKeys.lean` (simulator side) + `Lemma8.lean` + `lemma8_zero` |
| `SymbolicHiding/GarbleHoleBitSwap.lean` | `Alignment.lean` + `Theorem5.lean` |
| `Security.lean` | `Security.lean` (unchanged) |

The roles line up with the original's: `Lemmas.lean` is shared bookkeeping, `GarbleProof`
characterises `adversaryKeys` of the garbled circuit, `GarbleHole` characterises its
`adversaryView`, `SimulateProof` does both for the simulated circuit reusing the garbling
work, and `GarbleHoleBitSwap` is the renaming that maps garbling to simulation.

Two placements are forced by dependencies rather than by role, and are noted in the files:

* `GbStage.hyps` and `GbStage.labelKeys_yielded` use `lemma5core`, so they sit in
  `GarbleProof.lean` while the rest of `GbStage` (including the `Lemma7` / `Lemma8` /
  `Theorem5` statements) is in `Lemmas.lean`.
* `Simulate.lean` comes *before* `SymbolicHiding/` here, whereas the original imports it
  after `GarbleHole.lean`.  `sim_snd_eq_gb_snd` — which is what lets one `GbStage` relation
  serve both Lemmas 7 and 8 — needs `sim`, so the simulator has to be defined first.

Each new module carries a docstring explaining its role; stale cross-file references in
comments were updated, as were the three `scratch/` files that imported removed modules.

## [2026-09-17a] — **`FixpointStepSound` proved; the framework has no remaining obligations**

`fixpointStepSound` is a theorem, so `symbolicToSemanticSoundness` (LM18 Theorem 1 for the
PRG algebra, **no side conditions**) and `garblingSecure` (computational simulation security
of the PRG garbling scheme) follow.  Build is clean and `sorry`-free; everything depends only
on `propext, Classical.choice, Quot.sound`.

### The gap that was closed

`symbolicToSemanticIndistinguishabilityHidingOneKey` can only target a key *variable*: the
IND-CPA reduction has to identify the oracle's uniformly random key with the key it hides.
The fixpoint iteration does not respect that — at an intermediate stage the keys being hidden
can include `G0 K₅` whose root `K₅` has itself been hidden away, so
`Roots(Keys(view)) ⊆ 𝐊` fails (`scratch/GarbleSideCondition.lean`).  That is exactly LM18
Lemma 3's general case, discharged there by a pseudorandom key renaming.

### Added — `Expression/Lemmas/ReplacePRG.lean` (new)

The symbolic bookkeeping for one idealisation hop `replacePRG (K_t) i j`, abbreviated `rp`.

* `rp_G0`, `rp_G1`, `rp_pair`, `rp_perm`, `rp_enc`, `rp_hidden` — the constructor equations.
* `exprKeys_rp`, `extractKeys_rp` — `Keys` and `Parts` transport as **images**.
* `keySubterms_rp` — key subterms only shrink (`K_t` itself disappears), which is what the
  freshness side conditions need.
* `unrp`, `unrp_rp`, `rp_inj` — `unrp` is a left inverse on keys avoiding the two fresh
  variables, giving injectivity.
* **`strictYields_rp_reflect`** — idealisation can *break* a `G`-chain but never *creates*
  one: an ancestor relation in the idealised expression was already there.  This is what
  transports LM18's two conditions across the hop.
* **`rp_hideSelected`** — idealisation commutes with hiding one key.  The only interesting
  case is `Enc c m`, where injectivity gives `c = k ↔ rp c = rp k`.
* `baseVar`, `strictYields_baseVar`, **`keySize_rp`** — the termination measure: each hop
  shortens the chain of the key being hidden by exactly one.
* `exists_fresh_index` — a finite key set leaves infinitely many variable indices unused.
* `keySubterms_trans`, `encKeys_key`.

### Added — `SoundnessProof/HidingOneKeyGen.lean` (new)

**`hideOneKeyGen`** — hiding one key with *no* atomicity restriction.  Its two hypotheses are
LM18's, read off `Keys(expr)`:

* `Hroot` — nothing occurring in `expr` is a strict *ancestor* of `k`, i.e. `k` is a root of
  `Keys(expr)`.  For non-atomic `k` this is precisely what licenses the hop: the atomic
  variable `K_t` at the bottom of `k`'s chain does not occur in `expr`, which is
  `PrgRenameRel.idealize`'s side condition.
* `Hdesc` — nothing occurring in `expr` is a strict *descendant* of `k`.  For atomic `k` this
  is exactly `seedFree`, which the IND-CPA reduction needs.

By induction on `keySize k`.  Atomic `k` is the existing IND-CPA step.  Non-atomic `k`:
idealise at `K_t` (one PRG hop), hide the shortened key by induction, undo the hop.  The
middle step lines up because idealisation commutes with hiding.

### Added — `SoundnessProof/FixpointStep.lean` (new)

* `encKeys_key`, `hideEncryptedEncAux`, `hideSelectedRestrictEnc` — hiding is determined by
  the *encryption* keys alone, the `encKeys` analogue of `hideSelectedRestrict`.
* **`hidingGen`** — the set version of `hideOneKeyGen`, replacing
  `symbolicToSemanticIndistinguishabilityHidingInner`'s atomicity hypothesis by the two
  `Keys` conditions.  Both survive `removeOneKeyProper`, since hiding only shrinks `Keys`.
* **`fixpointStepSound`** — the two conditions come straight off the fixpoint.  The keys the
  step hides are `W = (z \ 𝓕(z)) ∩ encKeys(v)`; restricting to encryption keys is what makes
  them available (a key of `allParts(v)` need not be in `exprKeys(v)`, e.g. `K₅` when only
  `G0 K₅` occurs — and hiding such a key changes nothing anyway).  For `k ∈ W`:
  * no strict **descendant** of `k` occurs in the view — else `k` would be collected by the
    ancestor clause of LM18 Definition 3, hence recovered, hence not in `z \ 𝓕(z)`;
  * no strict **ancestor** `k'` of `k` occurs in the view — such a `k'` is itself in the
    recovery base (directly if it is a part, via the ancestor clause if it is an encryption
    key), and then `k` lies in its PRG closure by `mem_prgClosure_of_strictYields`, so `k` is
    recovered.

### Added — capstones

* `Expression/ComputationalSemantics/Soundness.lean`: **`symbolicToSemanticSoundness`** —
  symbolic indistinguishability implies computational indistinguishability, given only
  IND-CPA security of the encryption scheme and security of the PRG.  No `hidingSideCondition`,
  no atomicity hypothesis.
* `Garbling/Security.lean` (new): **`garblingSecure`** — composing it with `theorem5` gives
  computational simulation security of the PRG-based garbling scheme.

### Status

No obligations remain.  LM18 Lemmas 2–8 and Theorems 1, 4 and 5 are all proved, and the
garbling scheme's computational security follows.

## [2026-09-17] — **LM18 Theorem 5 proved**

`theorem5 : Theorem5` is a theorem:
`symIndistinguishable (Garble c x) (Simulate c (evalCircuit c x))`.
Build is clean and `sorry`-free; it depends only on `propext, Classical.choice, Quot.sound`.

### The witness

`symIndistinguishable` asks for a variable renaming `r` with
`normalizeExpr (applyVarRenaming r (adversaryView (Garble c x)))
 = normalizeExpr (adversaryView (Simulate c (C x)))`.

The witness is `makeVarRenaming f` (which `Expression/Renamings.lean` already provided, with
bijectivity proved), where `f i` is the value carried by the wire whose label has bit index
`i`.  It has to do two things at once:

* the **key** half `makeKeySwap f` exchanges `K_{2i}` and `K_{2i+1}` exactly when wire `i`
  carries `1`, sending each label's *active* key — the one the garbling reveals — to that
  label's key `0`, which is the one the simulation reveals;
* the **bit** half `bitPerm f` negates `B_i` on the same indices, which via `normalizeExpr`'s
  rule `π[¬b](p₀,p₁) ↝ π[b](p₁,p₀)` moves each garbled table's decryptable row to position
  `(0,0)`, where the simulator's is.

At a `NAnd` gate the two effects cancel exactly.  Row `(v_i,v_j)` carries `(¬B_h, K_h¹)`
unless `(v_i,v_j) = (1,1)`, where it carries `(B_h, K_h⁰)`.  In the first case the gate's
output is `1`, so `f` flips index `h`: `¬B_h ↦ ¬¬B_h ↝ B_h` and `K_h¹ ↦ K_h⁰`.  In the second
the output is `0` and `f` fixes `h`.  Either way the row becomes `(B_h, K_h⁰)` — exactly what
`Sim` writes in *all four* rows.  The three undecryptable rows become `Enc k⁰ᵢ ⦃k¹ⱼ⦄` and two
copies of `⦃k¹ᵢ⦄`, matching the simulator's.

### Added — `Garbling/ValueInvariant.lean` (new)

Lemmas 7 and 8 say *exactly one* key of each pair is recovered; the renaming needs to know
**which**.

* `LabelValueIn U S u v` — the recovered key is `key_v`, for the wire's actual value `v`.
* `LabelZeroIn U T u` — the simulator always recovers `key⁰`.
* **`lemma7_value`** and **`lemma8_zero`** — the proofs of `lemma7`/`lemma8_gb` with the case
  analysis on "which key is in `S`" replaced by the value that determines it.  At a `NAnd`
  gate with input values `(v_i,v_j)` exactly row `(v_i,v_j)` decrypts, and its payload is
  `key_{¬(v_i ∧ v_j)}` — the output label's active key.

### Added — `Garbling/Alignment.lean` (new)

* `gbCtr` + `gb_ctr_eq` — the key counter as a function of the circuit alone.
* `SwapCompatible` / `SwapCompatibleB` — a label's two keys are `G^w(K_{2b})` and
  `G^w(K_{2b+1})` for the *same* `w` and `b = l.bit`.  Rather than name `w`, the predicate
  records the consequence: `makeKeySwap f` exchanges the label's keys exactly when `f` flips
  the label's own bit index.  With `makeKeySwap_even`/`makeKeySwap_odd`,
  `swapCompatible_varK`/`_G0`/`_G1`, `gb_swapCompatible`, `makeLabels_swapCompatible`.
* `LabelValues f u v`, `AgreesOn f c v ctr`, `valueMap`.  `AgreesOn` is *structural*: it says
  `f` records the right value at each `NAnd` gate of `c`, and `Compose` splits it along the
  circuit.  That is what keeps the main induction free of freshness reasoning — freshness
  enters exactly once, in `agreesOn_valueMap`, via `valueMap_lt`/`valueMap_ge`/
  `agreesOn_congr`.

### Added — `Garbling/Theorem5.lean` (new)

* `nandPattern` — the shape both sides normalise to at a gate.
* **`nand_pattern_gb`** and **`nand_pattern_sim`** — the two four-row computations.
* **`theorem5_core`** — by induction on the sub-circuit, carrying the `GbStage` hypothesis so
  that `lemma7_value` and `lemma8_zero` are available at the intermediate labels.  Returns
  the pattern equality *and* `LabelValues f (gb c' u' ctr').2.1 (evalCircuit c' v)`, which the
  `Compose` case needs.
* `selKeys` / `unselKeys`, `extractKeys_view_gEnc_eq`, `unsel_notMem_sel` (distinct labels
  never hide a key they also reveal), `labelValueIn_of`, `labelZeroIn_of`, `zeroBundle`,
  `sEnc_eq_gEnc` (`SEnc u = GEnc u 0⃗`, so the simulator reuses the `GEnc` computations).
* `input_sel_mem` / `input_unsel_notMem` and their `sim` counterparts — the base case.  The
  revealed key is in the fixpoint because it is readable off the view; the withheld one is
  not, because it is atomic, too old to come from a gate (`extractKeys_view_range` puts every
  gate's contribution at index `≥ 2·ctr₀`), and distinct from every revealed input key.
* `inputValues` + `inputValues_lt`/`_ge`, `labelValues_congr`, `labelValues_inputValues`.
* `view_gEnc_eq`, `view_mask_eq` — the encoded-input and output-mask halves.
* **`theorem5 : Theorem5`**.

### Status

`FixpointStepSound` (in `AdversaryView.lean`) is the last open obligation.  All of LM18
Lemmas 2 and 4–8 and Theorems 4–5 are now proved.

## [2026-09-16k] — **LM18 Lemmas 7 and 8 proved**

`lemma7 : Lemma7` and `lemma8 : Lemma8` are now theorems.  Build is clean and `sorry`-free;
both depend only on `propext, Classical.choice, Quot.sound`.

### Changed — the `LabelInvariantIn` guard is now a conjunction

`Garbling/Independence.lean`.  Was `(l.key0 ∈ U ∨ l.key1 ∈ U) → …`, now
`(l.key0 ∈ U ∧ l.key1 ∈ U) → …`.

With a disjunction the `Dup` case is **unprovable**.  From `G0 k¹ ∈ U` alone one cannot place
`G0 k⁰` in `U`, and `adversaryKeys_G0_closed` — the lemma that pushes the *known* key through
the PRG — requires exactly that.  One could instead prove that `keySubterms (Garble c x)`
contains both keys of a label or neither (it does, because every construct uses a label
symmetrically), but that is a separate induction for no gain: a conjunction loses nothing,
since wherever a label is actually used — as the pair of encryption keys of a `NAnd` table,
or `G`-applied by `Dup` — both of its keys occur, so the invariant fires exactly where
Theorem 5 needs it.

### Added — `Garbling/ViewKeys.lean` (new)

What the adversary can read out of a garbled circuit, in three groups.

**Atomicity of recovery.**
* `atomic_mem_prgStep`, `atomic_mem_prgClosure` — the PRG closure only ever adds *derived*
  keys, so an atomic key is in `prgClosure U base` only if it was in `base`.
* `hideEncrypted_key` — `hideEncrypted` is the identity on a pure key expression.
* `encKeys_hideEncrypted` — hiding never invents an encryption key.
* `keySubterms_self`, `keySubterms_of_G0`, `keySubterms_of_G1` — `keySubterms` is
  subterm-closed through the PRG constructors.
* `encKeys_gEnc`, `encKeys_maskedLabelToExpr`.
* `lemma6_garble_enc` — **LM18 Lemma 6(1) keyed on encryption keys**, generalising
  `lemma6_garble_cond1` (which only covered non-atomic keys and so did not apply to the
  fresh `VarK` payloads).
* `extractKeys_adversaryView_subset` — everything readable off the view is recovered.
* **`atomic_recovered_garble`** — *an atomic key is recovered only by decryption.*
  `keyRecovery` has two sources, `extractKeys` of the view and Definition 3's ancestor
  clause.  The closure on top adds nothing atomic; and the ancestor clause can only fire on
  a key that occurs in the view, which (by `exprKeys = extractKeys ∪ encKeys`) is either
  already in `extractKeys` or is an *encryption* key — and Lemma 6 forbids a strict
  descendant of an encryption key from occurring, making the clause vacuous.

**Locality.**
* `extractKeys_view_gbEntry` — a table row yields its payload exactly when both its outer and
  inner keys are known.
* `extractKeys_view_range` — every key read out of `gb c u ctr` is one of the payload key
  variables `K_{2n}, K_{2n+1}` minted by a `NAnd` gate *inside* `c`, i.e. has index in
  `[2·ctr, 2·ctr_final)`.
* `GbStage.final_le` — a stage's final counter is bounded by the ambient one.
* **`GbStage.view_extract_iso`** — *no interference between stages.*  A key read out of the
  whole garbled circuit whose index lies in a stage's counter range was read out of **that**
  stage.  Because `Compose` splits the counter range at an even endpoint, the two halves'
  ranges are disjoint and a `{2n, 2n+1}` pair never straddles them.  This is what lets the
  `NAnd` case of Lemma 7 reason locally about its own two fresh keys.

**Plumbing.** `GbStage.trans`, `GbStage.keySubterms_subset`, `GbStage.view_extract_mono`,
`extractKeys_view_gEnc`.

### Added — `Garbling/Lemma7.lean` (new)

* `extractKeys_view_mask`, `extractKeys_adversaryView_garble` (the view of `Garble` splits
  into table + encoded input; the masks contribute no keys), `keySubterms_garble_gb`,
  `fresh_not_input` (a key minted at or after the input counter is not an input label key).
* `nand_view_extract` — the four-row computation of what a `NAnd` table reveals.
* `nand_keySubterms` — both keys of a gate's input labels occur in its table, which is what
  discharges the invariant's guard for `l_i` and `l_j`.
* **`lemma7 : Lemma7`**, by induction on the sub-circuit with the `GbStage` hypothesis
  threaded through `GbStage.trans`.  `NAnd`: exactly one row decrypts, so exactly one fresh
  key is revealed; it is in `S`, and the other is not — if it were, being atomic it would
  have to be readable off the view (`atomic_recovered_garble`), and `view_extract_iso` places
  it in this gate's contribution, which is the singleton just computed.  `Dup`:
  `adversaryKeys_G0_closed` pushes the known key through the PRG,
  `adversaryKeys_G0_seed` keeps the unknown one unknown.

### Added — `Garbling/Lemma8.lean` (new)

* `sim_snd_fst`, `sim_snd_snd`, and the `sim` ports of the locality machinery:
  `extractKeys_view_range_sim`, `GbStage.view_extract_iso_sim`,
  `GbStage.view_extract_mono_sim`, `GbStage.keySubterms_subset_sim`.
* **`encKeys_sim_eq_gb`** and **`exprKeys_sim_subset_gb`** — `Sim` uses the same encryption
  keys as `Gb` and a subset of its key set (its payload is always `K_h⁰`, one of the two keys
  `Gb` uses).  Hence LM18 Lemma 6 transports to the simulator for free: `lemma6_sim_cond1`,
  `lemma6_simulate_enc`.  No separate Lemma 6 proof for `Sim` was needed.
* `atomic_recovered_simulate`, `adversaryKeys_G0_seed_sim`, `adversaryKeys_G1_seed_sim`.
* `extractKeys_view_sEnc`, `extractKeys_view_sMask`, `extractKeys_adversaryView_simulate`,
  `keySubterms_simulate_sim`, `fresh_not_input_sim`, `sim_view_extract`,
  `nand_keySubterms_sim`.
* **`lemma8_gb`** and **`lemma8 : Lemma8`**.  Stated over `gb`'s output labels — they are
  `sim`'s — which makes the `Compose` case chain directly.  The `NAnd` case is easier than
  Lemma 7's: every row of a simulated table carries the same payload `K_h⁰`, so whichever row
  decrypts the recovered key is `K_{2n}`, and `K_{2n+1}` is never recovered at all.

### Status

`Theorem5` and `FixpointStepSound` remain the open obligations.

## [2026-09-16j] — Garbling stages: `GbStage` replaces bare `SubCircuit` in Lemmas 7/8

### Why

`Lemma7`/`Lemma8` were stated over `SubCircuit c' c` together with *arbitrary* input labels
`u` and key counter `ctr`.  As stated they are false.  `gb` takes `u` and `ctr` as
independent arguments, so for an arbitrary `u`/`ctr` the garbling of a sub-circuit `C'` has
no relationship at all to the garbling of `C`:

* `NAnd` at counter `ctr` mints `K_{2·ctr}, K_{2·ctr+1}`.  For an arbitrary `ctr` these need
  not be keys of `Garble C x`, so nothing constrains their membership in
  `adversaryKeys (Garble C x)` and the "exactly one of the pair is in `S`" conclusion fails.
* The `Dup` case of LM18's proof of Lemma 7 argues that `G^h(k^{1-z}) ∉ S` by appealing to
  Lemma 6 *for the whole garbled circuit*.  That step has no counterpart when `u` is
  unrelated to the circuit being garbled.

LM18's prose ("for any sub-circuit `C'` of `C`") implicitly means the labels and counter the
garbling actually reaches.  `GbStage` makes that explicit.  This is a gap in the
formalisation, not in LM18.

### Added — `PRGExtension/Garbling/GbStage.lean` (new)

* `GbStage c u ctr c' u' ctr'` — inductive: garbling `c` from `(u, ctr)` performs, as a
  sub-computation, the garbling of `c'` from `(u', ctr')`.  Constructors `refl`,
  `composeL`, `composeR` (threading `(gb c1 u ctr).2`), `first`.
* `GbStage.subCircuit` — every stage is a sub-circuit, so `GbStage` refines `SubCircuit`.
* `GbStage.ctr_le` — a stage never rewinds the key counter.
* `GbStage.exprKeys_subset`, `GbStage.extractKeys_subset` — a stage's garbled expression
  sits inside the global one, key-wise.  This is what lets fixpoint facts about
  `adversaryKeys (Garble c x)` be used at a sub-circuit.
* `GbStage.hyps` — `StronglyIndependent` and `LabelsBelow` are inherited by every stage
  (via `lemma5core` and `gb_labels_below`), so Lemmas 5 and 6 apply at each stage.
* `GbStage.labelKeys_yielded` — every key of a stage's input labels is yielded by a key
  appearing as a *part* of the global garbling, or by a global input label key.  This is
  LM18 Lemma 5(2) propagated along a stage (`yields_trans` over `lemma5core`'s clause (2)).
* `sim_snd_eq_gb_snd` — `sim` and `gb` thread output labels and counters identically; they
  differ only in the garbled tables.  Hence **one** stage relation serves both Lemma 7 and
  Lemma 8, and no separate `SimStage` is needed.
* `GbStage.exprKeys_subset_sim` — the `sim` analogue of `exprKeys_subset`.
* `gbStage_invariant` — the label invariant propagates along a stage, given only that a
  single `gb` step preserves it.  Stated over an abstract step hypothesis so Lemmas 7 and 8
  share it.
* `lemma7_propagates` — the corollary Theorem 5 consumes: invariant at the input labels ⟹
  invariant at every stage's input *and* output labels.

### Changed

* `Lemma7`, `Lemma8`, `Theorem5` moved from `Garbling/Independence.lean` to
  `Garbling/GbStage.lean` and restated over `GbStage c (makeLabels s 0).1
  (makeLabels s 0).2 c' u' ctr'` instead of `SubCircuit c' c` with arbitrary `u`, `ctr`.
  `SubCircuit` itself is kept in `Independence.lean` (it is still the right notion for
  statements that do not mention labels) with a pointer comment.
* `SymbolicGarbledCircuitsInLean.lean` imports the new module.

### Status

Build is clean and `sorry`-free.  All new lemmas depend only on
`propext, Classical.choice, Quot.sound` (several on strictly fewer).  `Lemma7`, `Lemma8`,
`Theorem5` and `FixpointStepSound` remain the open obligations, all as named, type-checked
`Prop`s that nothing else silently assumes.

## [2026-09-16i] Items 1–2 for Lemmas 7/8; bounded vs unbounded closure

Still `sorry`-free.

### Added — `Garbling/GarbleKeys.lean` (item 2)

`lemma4_garble`, `lemma4_simulate` and the `adversaryView` corollaries: every key appearing
as a *part* of `Garble(C,x)` is atomic.  Supporting: `lemma4_sim`, `extractKeys_gEnc`,
`extractKeys_sEnc`, `extractKeys_maskedLabelToExpr`, `makeLabels_atomic`.

### Added — `Garbling/GarbleFixpoint.lean`

* `keyVarsAbove`, `LabelsAbove`, `makeLabels_above`, and
  **`makeLabels_stronglyIndependent`** — `Label(s)` yields a strongly independent label
  expression, so Lemmas 5 and 6 apply at the top level.  (Disjointness of the two halves
  comes from the counter windows: the first half's key variables are below the middle
  counter, the second half's above it.)
* `nonatomic_mem_encKeys`, **`lemma6_garble_cond1`** — Lemma 6(1) lifted to the whole
  `Garble` expression.
* **`adversaryKeys_G0_seed` / `adversaryKeys_G1_seed`** — the adversary knows a derived key
  only if it knows the seed.  This is the `k_{1-z} ∉ S ⟹ G0 k_{1-z} ∉ S` half of Lemma 7's
  `Dup` case, and it is exactly the combination of items 1 and 2: reflection (item 1) leaves
  two branches, and `lemma4_garble` (item 2) kills one while `lemma6_garble_cond1` kills the
  other.

### Discovered — the bounded `prgClosure` is not LM18's `𝖦*`, and Lemma 7's statement needed relativising

LM18 Definition 3 uses the **unbounded** closure
`𝖦*(S) = {𝖦ʷ(k) | k ∈ S, w ∈ {0,1}*}` — an infinite set.  The Lean `prgClosure` bounds it
by the expression's own `keySubterms`, which is what makes it computable.

That bounding is **sound for computing the pattern** — `p(e,S)` only ever tests keys that
occur in `e` — but it changes membership for keys that do *not* occur, and the label
invariant quantifies over exactly those.  `scratch/DupTrailing.lean` exhibits it: for
`Garble Dup true` the whole expression has key set `{K₁}`, while the output labels are
`(b,(G0 K₀, G0 K₁))` and `(b,(G1 K₀, G1 K₁))`.

* In LM18, `S = 𝖦*(…)` contains `G0 K₁` but not `G0 K₀` — exactly one of the pair, so the
  invariant holds.
* With the bounded closure, `G0 K₁ ∉ S` too, so *neither* is in `S` and the invariant fails.

So `Lemma7`/`Lemma8` are **not provable as I stated them**, not because the paper is wrong
but because of the formalization's bounding.  They now use `LabelInvariantIn`, which asks
for the invariant only of labels at least one of whose keys actually occurs.  LM18 only ever
applies Lemma 7 to labels that are used (as encryption keys at a later gate), so this is
faithful.

This is the third of my obligation statements that needed correcting before it could be
discharged (after Lemmas 5/6 needing `LabelsBelow`, and 7/8 needing the ambient fixpoint).

### Remaining for Lemmas 7/8

3. Lemmas connecting a `SubCircuit`'s garbling to the global one.

---

## [2026-09-16h] `prgClosure` saturation; `adversaryKeys` derivation properties

Still `sorry`-free.  This closes **item 1** of the three things Lemmas 7/8 need.

### Added — the bounded `prgClosure` is a genuine closure

`prgStep_prgClosure : prgStep U (prgClosure U S) = prgClosure U S`.

The proof is the counting argument the definition was designed around but never justified:
each non-stabilising step adds at least one element of the universe
(`prgStep_card_growth`), so the fold stabilises within `|U|` steps
(`exists_prgStep_stable`) and then stays put (`prgStep_stable`).  This was flagged as a gap
in PRGExtension-Analysis.md §4.6 ("worth recording a lemma … so the closure can be reasoned
about as a closure rather than as a fold") and is now closed.

Also `prgClosure_idem`, `iterate_of_stable`.

### Added — `adversaryKeys` is closed under derivation, and reflects it

Both directions, which is exactly what LM18 Lemma 7's `Dup` case needs:

* **closed**: `G0_mem_prgClosure`, `G1_mem_prgClosure`, and
  `adversaryKeys_G0_closed`, `adversaryKeys_G1_closed` — from `k ∈ S` conclude `G0 k ∈ S`
  (within the expression's universe).  This is the `k_z ∈ S ⟹ G0 k_z ∈ S` half.
* **reflects**: `prgClosure_reflects_G0/G1` and `adversaryKeys_reflects_G0/G1` — `G0 k ∈ S`
  only because `G0 k` is directly recoverable from the adversary view, or because `k ∈ S`.
  This is the `k_{1-z} ∉ S ⟹ G0 k_{1-z} ∉ S` half: Lemma 4 will kill the `extractKeys`
  branch (a non-atomic key is never a *part*) and Lemma 6(1) the ancestor branch.

Supporting: `prgClosure_keyRecovery`, `adversaryKeys_prgClosed`, and
`adversaryView_eq_hideEncrypted_closure`, which identifies
`hideEncrypted (prgClosure U (adversaryKeys e)) e` with `adversaryView e`.

### Remaining for Lemmas 7/8

2. Lemma 4 lifted from `gb`'s output to the whole `Garble c x` expression.
3. Lemmas connecting a `SubCircuit`'s garbling to the global one.

---

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
