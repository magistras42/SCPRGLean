# `PRGExtension`: file-by-file guide, and what `prg-fixes` changed

**Branch:** `prg-fixes` (27 commits ahead of `main`, 0 behind; merge base `6c0ca7e`)
**Status:** builds clean, `sorry`-free, no `axiom` declarations. Every headline theorem
depends only on `propext`, `Classical.choice`, `Quot.sound`.

`PRGExtension` is a port of the encryption-only symbolic-garbled-circuits framework in
`SymbolicGarbledCircuitsInLean/` to the PRG-based construction of **LM18** (Li & Micciancio,
*Symbolic security of garbled circuits*, CSF 2018). The difference is one line of the
scheme — `Gb(Dup, ·)` derives the two output labels with a PRG instead of duplicating the
input label — and that one line propagates through the whole symbolic layer, because keys
stop being atomic variables and become `G`-chains `G^w(K_n)`.

---

## 1. Headline result

```
garblingSecure                                    -- Garbling/Security.lean
 ├─ theorem5                                      -- LM18 Thm 5  (symbolic)
 └─ symbolicToSemanticSoundness                   -- LM18 Thm 1  (no side conditions)
     └─ fixpointStepSound                         -- LM18 Lemma 3, general case
```

`garblingSecure` says: for every circuit `C` and input `x`, the distributions of
`Garble(C, x)` and `Simulate(C, C(x))` are computationally indistinguishable, assuming
IND-CPA security of the encryption scheme and security of the PRG.

Proved along the way: LM18 **Lemmas 2, 4, 5, 6, 7, 8** and **Theorems 1, 4, 5**.

---

## 2. What `main` looked like

On `main`, `PRGExtension` was the expression layer only (19 files, no `Garbling/`), with

* **28 `sorry`s** — 15 in `AdversaryView.lean`, 8 in `HidingOneKey.lean`,
  4 in `HidingOnePrgSeed.lean`, 1 in `SymbolicIndistinguishability.lean`;
* **1 `axiom`** — `idealize_PRG_soundness`, which asserted the PRG game hop outright;
* `reductionToPrgOracle` was a stub (`sorry` for its body and for both of its
  correctness lemmas);
* the whole garbling application was absent.

`prg-fixes` adds 13 files, modifies 8, and removes the `sorry`s and the `axiom`.

---

## 3. File-by-file

Legend: **[new]** added on `prg-fixes` · **[mod]** modified · (unmarked = untouched)

### 3.1 `Core/` — general infrastructure

| File | What it does |
|---|---|
| `Core/Fixpoints.lean` | Constructive Knaster–Tarski. `greatestFixpoint f mono fBound HfBound` iterates `f` downward from `fBound`, terminating on `Finset.card`. `fixaccess` is the induction principle the adversary-view proof uses to walk the iteration. **This is why `keyRecovery` must return a `Finset`** — see §4.6. |
| `Core/CardinalityLemmas.lean` | Counting lemmas for functions agreeing on a finite set; used by the resampling arguments in the computational semantics. |

### 3.2 `ComputationalIndistinguishability/` — the crypto plumbing

| File | What it does |
|---|---|
| `…/Def.lean` | The VCVio-based model: `famDistr`, `famSeededOracle`, `withRandom`/`addRandom`, `prodImpl`, `compToDistrGen`, `CompIndistinguishabilityDistr`, `PolyFamOracleCompPred`. |
| `…/Lemmas.lean` | Negligibility algebra (`neglSum`, `neglTriangle`) and the indistinguishability groupoid `indRfl`, `indSym`, `indTrans`, `indTransRev` — the game-hop combinators every proof chains with. |

### 3.3 `Expression/` — the symbolic algebra

| File | What it does |
|---|---|
| `Expression/Defs.lean` | The expression AST: `Shape`, `BitExpr`, and `Expression` with constructors `BitE`, `VarK`, `Pair`, `Perm` (controlled swap `π[b]`), `Enc`, `Hidden` (the pattern hole `⦃s⦄ₖ`), `Eps`, and the PRG nodes **`G0`, `G1`**. |
| `Expression/SymbolicIndistinguishability.lean` **[mod, +999]** | The core symbolic layer: `normalizeExpr`, renamings, `keySubterms`, `extractKeys`, `hideEncrypted`, **`keyRecovery`**, `adversaryKeys`, `adversaryView`, `symIndistinguishable`. Heavily extended — see §4.1, §4.2, §4.5. |
| `Expression/Renamings.lean` | `bitPerm f`, `makeKeySwap f`, `makeVarRenaming f` and their bijectivity. Pre-existing; turns out to be *exactly* the renaming Theorem 5 needs (§5.3). |
| `Expression/Lemmas/HideEncrypted.lean` **[mod, +29]** | `hideEncryptedS`/`hideSelectedS` (the `Set`-valued hiding used by the reductions), `allParts`, and the "restricting to the parts changes nothing" lemmas. Added `allParts_subset_keySubterms`, `hideSelectedRestrict`. |
| `Expression/Lemmas/NormalizeIdempotent.lean` | `normalizeExpr` is idempotent. |
| `Expression/Lemmas/Renaming.lean` | Key and bit renamings commute with each other and with normalisation. |
| `Expression/Lemmas/ReplacePRG.lean` **[new, 338]** | All the symbolic bookkeeping for **one PRG idealisation hop** `replacePRG (K_t) i j` (abbreviated `rp`). See §5.4 — this is the file that unlocks `FixpointStepSound`. |

### 3.4 `Expression/ComputationalSemantics/` — from expressions to distributions

| File | What it does |
|---|---|
| `…/Def.lean` **[mod, +190]** | `encryptionScheme`, **`prgScheme`** (`prg0`, `prg1` on κ-bit seeds), `evalExpr`, `exprToFamDistr`. The added material is the three-variable resampling machinery (`subst3`, `resample3`, `resamplingLemmaPrg`, …) the PRG reduction needs — the two-variable version only supported swapping one key at a time. |
| `…/EncryptionIndCpa.lean` | The IND-CPA game as a seeded oracle; `encryptionSchemeIndCpa`. |
| `…/PrgSecurity.lean` **[mod]** | The PRG game. **Fixed**: see §4.4. |
| `…/NormalizePreserves.lean` | Normalisation does not change the induced distribution. |
| `…/RenamePreserves.lean` | A *valid* variable renaming does not change the induced distribution (`applyRenamePreservesCompSem2`) — this is what makes the `atomic` generator of `PrgRenameRel` free. |
| `…/Soundness.lean` **[mod, +175]** | The top of the expression layer: `PrgRenameRel`, **`prgRename`** (LM18 Lemma 2), `symbolicToSemanticIndistinguishabilityOfStep`, and the capstone **`symbolicToSemanticSoundness`** (LM18 Theorem 1, no side conditions). |

### 3.5 `Expression/ComputationalSemantics/SoundnessProof/` — the game hops

| File | What it does |
|---|---|
| `…/HidingOneKey.lean` **[mod, ±731]** | The IND-CPA hop: hiding a single *atomic* key `VarK n` is undetectable (`symbolicToSemanticIndistinguishabilityHidingOneKey`). All 8 `sorry`s discharged — see §4.2. |
| `…/HidingOnePrgSeed.lean` **[mod, +314]** | The PRG hop: `reductionToPrgOracle` (now with a real body), `prgSimulateReal`/`prgSimulateIdeal`, and `symbolicToSemanticIndistinguishabilityPrgIdealization` — replacing `G0 k, G1 k` by two fresh independent variables is undetectable. Plus `PrgHopChain`/`prgHopChainSound` for composing hops. All 4 `sorry`s discharged. |
| `…/AdversaryView.lean` **[mod, ±459]** | The fixpoint walk: `e ≈ adversaryView e`. All 15 `sorry`s discharged — see §4.3, §4.5. Now also states the isolated obligation `FixpointStepSound` and `symbolicToSemanticIndistinguishabilityAdversaryViewOfStep`. |
| `…/HidingOneKeyGen.lean` **[new, 155]** | **`hideOneKeyGen`** — hiding a single *non-atomic* key, by induction on `keySize`. LM18 Lemma 3's general case. See §5.4. |
| `…/FixpointStep.lean` **[new, 224]** | **`hidingGen`** (the set version) and **`fixpointStepSound`**. The last obligation of the expression layer. See §5.4. |

### 3.6 `Garbling/` — the application **[all new, 3 981 lines]**

Laid out to mirror `SymbolicGarbledCircuitsInLean/Garbling/` exactly.

| File | What it does |
|---|---|
| `Garbling/Circuits.lean` | `WireBundle`, `Circuit` (`NandC`, `DupC`, `SwapC`, `AssocC`, `UnAssocC`, `FirstC`, `ComposeC`), `evalCircuit`, and **`WireLabel = ⟨bit : ℕ, key0, key1 : Expression 𝕂⟩`**. The label carrying key *expressions* rather than a wire index is the structural consequence of the PRG `Dup`. |
| `Garbling/GarblingDef.lean` | The scheme: `makeLabels`, `gbEntry`, **`gb`**, `gEnc`, `gMask`, **`Garble`** — plus symbolic evaluation `gEv`, `decode`, **`GEval`** and the parsers, as in the original. |
| `Garbling/Simulate.lean` | **`sim`**, `sEnc`, `sMask`, **`Simulate`**. `Sim` differs from `Gb` only at `NAnd`, where all four rows carry the same payload `(B_h, K_h⁰)`. |
| `Garbling/Correctness.lean` | **`garbleCorrect`** / `theorem4_holds` — LM18 **Theorem 4**: `GEval(Garble(C,x)) = C(x)`. |
| `Garbling/SymbolicHiding/Lemmas.lean` | Shared bookkeeping: counter freshness (`LabelsBelow`), strong independence (`IndependentKeys`, `DistinctLabels`, `StronglyIndependent`), the invariants `LabelInvariantIn` / `LabelValueIn` / `LabelZeroIn`, the statements of Lemmas 4–8 and Theorems 4–5, and the stage relation **`GbStage`** (§5.1). |
| `Garbling/SymbolicHiding/GarbleProof.lean` | Characterises `adversaryKeys (Garble C x)`: **`lemma5`**, **`lemma6`**, `lemma4_garble`, `lemma6_garble_cond1`, `adversaryKeys_G0_seed`/`_G1_seed`, `makeLabels_stronglyIndependent`. |
| `Garbling/SymbolicHiding/GarbleHole.lean` | Characterises `adversaryView (Garble C x)`: **`atomic_recovered_garble`**, **`GbStage.view_extract_iso`**, **`lemma7`**, `lemma7_value` (§5.2). |
| `Garbling/SymbolicHiding/SimulateProof.lean` | The same for the simulated circuit, reusing the garbling work via `encKeys_sim_eq_gb` / `exprKeys_sim_subset_gb`: **`lemma8`**, `lemma8_zero`, `atomic_recovered_simulate`. |
| `Garbling/SymbolicHiding/GarbleHoleBitSwap.lean` | The renaming that maps garbling to simulation: `SwapCompatible`, `AgreesOn`, `valueMap`, `nandPattern`, **`theorem5`** (§5.3). |
| `Garbling/Security.lean` | **`garblingSecure`** — Theorem 5 composed with Theorem 1. |

---

## 4. Defects found in the inherited code, and the fixes

These were genuine errors in the extension as it stood on `main`, **not** in LM18. The
paper's proofs are correct; what was wrong was the formalisation of them.

### 4.1 `keyRecovery` was missing LM18 Definition 3's ancestor clause — soundness was false

LM18 Definition 3 recovers
`r(e) = 𝖦*({k ∈ Keys(e) | (k ⋐ e) ∨ (∃k' ∈ Keys(e). k ≺ k')})`. The second disjunct — *`k`
has a strict PRG-descendant occurring in `e`* — was absent. Without it, an expression
revealing both `K` and `G0(K)` would treat `K` as unknown, and the IND-CPA reduction would
then be asked to treat a value the adversary can compute as uniformly random.

**Fix.** Added `exprKeys` (LM18's `Keys`, which does *not* decompose `G`-applications),
`strictYields` (`k ≺ k'`), `ancestorKeys`, and the clause itself. `keyRecovery` now closes
`extractKeys view ∪ ancestorKeys (exprKeys view)`. Monotonicity and boundedness re-proved.

### 4.2 Two reduction lemmas were false as stated; the primed versions are the correct ones

`HidingOneKey.lean` carried both unprimed and primed simulate-lemmas; the unprimed ones were
used and are false once `G` nodes exist — the reduction, which does not know the hidden key
`k`, cannot compute `prg0 k`.

**Fix.** Added LM18 Lemma 3's **property 3** as `seedFree n e` ("no `G^w(VarK n)` occurs in
`e`"), threaded it through both inductions, and switched the consumers to the primed
variants. `symbolicToSemanticIndistinguishabilityHidingOneKey` now takes `Hseed`.

### 4.3 The `replacePRG` machinery was at the wrong layer

It had been wired into the *fixpoint* step, where its side condition
`Roots(Keys(e)) ⊆ 𝐊` is not preserved by the iteration. It is a valid pseudorandom key
renaming, so the fix was to **retarget rather than delete**: it now lives under
`PrgRenameRel.idealize` and is consumed per-key by `hideOneKeyGen` (§5.4), where its side
condition is available.

### 4.4 `prgSchemeSecure` was unsatisfiable

The ideal PRG oracle was declared with `Seed := Unit`, so the "ideal" implementation had no
randomness to return and the security predicate could not be met by any scheme — making
every theorem that assumed it vacuous.

**Fix.** The ideal oracle's randomness moved into its seed:
`Seed := BitVector κ × BitVector κ`, drawn uniformly.

### 4.5 `extractKeys_hideEncrypted_self` was **false**

It claimed `extractKeys (hide K e) ⊆ extractKeys (hide (extractKeys (hide K e)) e)`.
Counterexample (machine-checked in `scratch/ExtractKeysSelfCounterexample.lean`):

```
e = Enc (VarK 0) (VarK 1),  K = {VarK 0}
hide K e = Enc (VarK 0) (VarK 1)    Y := extractKeys (…) = {VarK 1}
hide Y e = Hidden (VarK 0)          extractKeys (hide Y e) = ∅        so  {VarK 1} ⊆ ∅  ✗
```

Its only consumer was the fixpoint step, via an equally false intermediate
(`extractKeys (hide K e) = extractKeys (hide z e)`).

**Fix.** Both removed. The fixpoint step now hides `(z \ keyRecovery e z) ∩ encKeys(view)`
in one application of the hiding theorem, with no appeal to either identity.

### 4.6 The axiom `idealize_PRG_soundness`

Removed — it asserted exactly what the PRG game hop is supposed to *prove*. Its content is
now `symbolicToSemanticIndistinguishabilityPrgIdealization`, proved from `prgSchemeSecure`
via `reductionToPrgOracle`.

### 4.7 Bounded vs. unbounded PRG closure — a deliberate divergence, documented

`prgClosure U S` is bounded by `U = keySubterms p`, so it is **not** LM18's unbounded `𝖦*`.
This is forced: `greatestFixpoint` is a terminating recursion on `Finset.card`, so
`keyRecovery` must return a `Finset`, and `𝖦*({k})` is infinite. Because `keySubterms` is
subterm-closed, `prgClosure U base = 𝖦*(base) ∩ U` exactly, and `hideEncrypted` only ever
tests keys that occur — so the computed *pattern* agrees with LM18's. The divergence is only
in membership queries for keys that do not occur, which is why `LabelInvariant` had to be
relativised to `LabelInvariantIn U S` (`scratch/DupTrailing.lean` exhibits the case).

---

## 5. Statement-level corrections, and the four hard proofs

Four results needed their *statements* changed before they could be true. In each case the
paper is right and the formalisation's reading of it was too literal.

### 5.1 `GbStage` — "sub-circuit" needs to mean "stage"

LM18 states Lemmas 7/8 as "for any sub-circuit `C'` of `C` and any label expression `u`".
Taken literally with a bare `SubCircuit` relation this is **false** here: `gb` takes the
labels `u` and counter `ctr` as *independent* arguments, so for arbitrary `u`/`ctr` the keys
`K_{2·ctr}, K_{2·ctr+1}` that a `NAnd` mints need not be keys of `Garble C x` at all — and
LM18's own `Dup` case appeals to Lemma 6 for the *whole* garbled circuit.

`GbStage c u ctr c' u' ctr'` records what the paper means: garbling `c` from `(u, ctr)`
performs the garbling of `c'` from `(u', ctr')` as a sub-computation. It refines
`SubCircuit` and carries `ctr_le`, `exprKeys_subset`, `extractKeys_subset`, `hyps`,
`labelKeys_yielded`. Since `sim` threads labels and counters exactly as `gb`
(`sim_snd_eq_gb_snd`), one relation serves both lemmas.

### 5.2 Lemmas 7 and 8 — locality plus atomic recovery

The blocker was the `NAnd` case: showing the *other* fresh payload key is **not** in the
fixpoint — a negative fact about a greatest fixpoint of the whole expression. Two lemmas
make it local:

* **`atomic_recovered_garble`** — *an atomic key is recovered only by decryption.*
  `keyRecovery` draws from `extractKeys` of the view and from the ancestor clause; the PRG
  closure on top adds only derived keys, and the ancestor clause can only fire on a key
  occurring in the view, which (since `exprKeys = extractKeys ∪ encKeys`) is either already
  in `extractKeys` or is an *encryption* key — and Lemma 6 forbids a strict descendant of an
  encryption key from occurring. This needed `lemma6_garble_enc`, a generalisation of
  `lemma6_garble_cond1` to encryption keys (the old form was keyed on *non-atomic* keys, so
  it never applied to the fresh `VarK` payloads).
* **`GbStage.view_extract_iso`** — *no interference between stages.* Every key read out of
  `gb c u ctr` has index in `[2·ctr, 2·ctr_final)`; `Compose` splits that range at an **even**
  endpoint, so a `{2n, 2n+1}` pair never straddles the two halves. Hence a key whose index
  lies in a stage's range was read out of that stage and nowhere else.

One further statement change: `LabelInvariantIn`'s guard is now `key0 ∈ U ∧ key1 ∈ U`, not a
disjunction. With `∨` the `Dup` case is unprovable — from `G0 k¹ ∈ U` alone one cannot place
`G0 k⁰` in `U`, which `adversaryKeys_G0_closed` requires. `∧` loses nothing: wherever a label
is actually used, both of its keys occur.

### 5.3 Theorem 5 — the renaming

`makeVarRenaming f`, with `f i` the value carried by the wire whose label has bit index `i`,
does two things at once:

* `makeKeySwap f` exchanges `K_{2i}` and `K_{2i+1}` exactly when wire `i` carries `1`,
  sending each label's *active* key (what the garbling reveals) to its key `0` (what the
  simulation reveals). Because a label's two keys share a `G`-prefix (`SwapCompatible`), this
  survives any number of `Dup`s;
* `bitPerm f` negates `B_i` on the same indices, which via `normalizeExpr`'s rule
  `π[¬b](p₀,p₁) ↝ π[b](p₁,p₀)` slides each table's decryptable row to position `(0,0)`.

At a `NAnd` they cancel exactly: row `(v_i,v_j)` carries `(¬B_h, K_h¹)` and the output is `1`
(so `f` flips `h`: `¬¬B_h ↝ B_h`, `K_h¹ ↦ K_h⁰`), or it carries `(B_h, K_h⁰)` and the output
is `0` (so `f` fixes `h`). Either way the row becomes `(B_h, K_h⁰)` — what `Sim` writes in
all four rows.

Two supporting refinements: `LabelValueIn`/`LabelZeroIn` sharpen Lemmas 7/8 from "exactly one
key of the pair" to *which* one; and `AgreesOn` states **structurally** that `f` records the
right value at each gate, so the main induction splits along `Compose` with no freshness
reasoning (freshness is confined to `agreesOn_valueMap`).

### 5.4 `FixpointStepSound` — LM18 Lemma 3's general case

The IND-CPA reduction can only target a key *variable*: it must identify the oracle's uniform
key with the key it hides. The fixpoint iteration does not respect that — at an intermediate
stage the hidden keys can include `G0 K₅` whose root `K₅` has itself been hidden away
(`scratch/GarbleSideCondition.lean` exhibits this on a garbled circuit). LM18 discharges this
with a pseudorandom key renaming; that argument is now formalised.

* `ReplacePRG.lean`: `exprKeys`/`extractKeys` transport as **images**; `unrp` is a left
  inverse on keys avoiding the two fresh variables, giving injectivity; injectivity gives the
  two facts that matter — idealisation can *break* a `G`-chain but never *creates* one
  (`strictYields_rp_reflect`), and it commutes with hiding one key (`rp_hideSelected`);
  `keySize_rp` is the termination measure.
* `hideOneKeyGen`: induction on `keySize k`. Atomic `k` is the existing IND-CPA step.
  Non-atomic `k`: idealise at the `K_t` at the bottom of its chain, hide the shortened key
  inductively, undo the hop.
* `fixpointStepSound`: the two hypotheses come off the fixpoint. For a hidden key `k`, a
  strict descendant in the view would put `k` in the ancestor clause (hence recovered); a
  strict ancestor `k'` is itself in the recovery base, and then `k` is in its PRG closure
  (hence recovered). Either way `k ∈ 𝓕(z)`, contradiction.
  One adjustment: the hidden set is `(z \ 𝓕(z)) ∩ encKeys(v)`, not `∩ allParts(v)`. A key can
  be in `allParts(v)` without being in `exprKeys(v)` — `K₅` when only `G0 K₅` occurs — and for
  such a key the descendant condition genuinely fails. Restricting to encryption keys changes
  nothing (`hideSelectedRestrictEnc`: hiding only ever tests `Enc` keys) but makes
  `k ∈ exprKeys(v)` available.

---

## 6. What is *assumed*, not proved

The honest boundary of `garblingSecure`:

1. `encryptionSchemeIndCpa` and `prgSchemeSecure` — the standard cryptographic assumptions.
2. `Hreduction` and `HreductionPrg` — that the two reductions are polynomial time. These are
   **asserted as hypotheses, not verified against a cost model**; `IsPolyTime` is an abstract
   predicate closed under composition.
3. `PrgRenameRel` takes LM18's generators (`atomic`, `idealize`) as the *definition* of a
   pseudorandom key renaming. The purely symbolic factorisation result
   ([Mic09, Lemma 2] — that every `𝖦`-preserving map arises this way) is not formalised; the
   *computational* content of LM18 Lemma 2 is `prgRename`, which is proved.
4. The bounded-vs-unbounded closure divergence of §4.7, which is sound for the pattern but
   is a real difference from the paper's `𝖦*`.

---

## 7. Verification

```
lake build                                  # clean; only style linter warnings
grep -r "sorry\|^axiom" PRGExtension        # no occurrences outside comments
```

```
#print axioms PRG.garblingSecure            → [propext, Classical.choice, Quot.sound]
#print axioms symbolicToSemanticSoundness   → [propext, Classical.choice, Quot.sound]
#print axioms PRG.fixpointStepSound         → [propext, Classical.choice, Quot.sound]
#print axioms PRG.theorem5                  → [propext, Classical.choice, Quot.sound]
#print axioms PRG.lemma7 / PRG.lemma8       → [propext, Classical.choice, Quot.sound]
#print axioms PRG.garbleCorrect             → [propext, Quot.sound]
```

Executable sanity checks live in `scratch/` (not part of the library; run with
`lake env lean scratch/<f>.lean`): `TwoGateFixpoint.lean` computes `adversaryKeys` on a
two-gate garbled circuit and exhibits a non-atomic root at the fixpoint;
`ExtractKeysSelfCounterexample.lean` refutes §4.5; `GarbleSideCondition.lean` refutes the
old atomicity side condition; `DupTrailing.lean` exhibits the §4.7 divergence;
`GarbleCorrectness.lean` evaluates `GEval(Garble(C,x))`.

Companion documents: `PRGExtension-Analysis.md` (the original defect analysis, with STATUS
markers) and `CHANGELOG.md` (dated, per-change record).
