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
garblingSecureFromEfficiency                      -- Garbling/Security/Security.lean  (entry point)
 ├─ theorem5                                      -- LM18 Thm 5  (symbolic)
 └─ symbolicToSemanticSoundnessFromEfficiency     -- LM18 Thm 1  (no side conditions)
     ├─ fixpointStepSound                         -- LM18 Lemma 3, general case
     └─ reductionToPrgOracle_polyTime             -- PRG reduction's efficiency, derived
```

It says: for every circuit `C` and input `x`, the distributions of `Garble(C, x)` and
`Simulate(C, C(x))` are computationally indistinguishable, assuming IND-CPA security of the
encryption scheme, security of the PRG, and efficiency of the IND-CPA reduction (§6).

Proved along the way: LM18 **Lemmas 2, 3, 4, 5, 6, 7, 8** and **Theorems 1, 4, 5**, plus
[Mic09, Lemma 2] in both directions and the characterisation of the bounded PRG closure.
Alongside security: computational correctness (§5a), projectivity (§5b) and an executable
implementation proved to refine the specification (§5c).

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
| `Core/UniformProduct.lean` **[new, 2026-09-28]** | Uniform distributions along bijections and on products, and **`uniformFinArrow_bind_split`** — drawing `m + n` coins and splitting them is drawing `m` then `n` independently.  Not in Mathlib; no garbling in it. |
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
| `Expression/HoleFree.lean` **[new, 2026-09-28]** | **`HoleFree`** — no `Hidden` node anywhere in the expression — with a `Decidable` instance, `holeFree_key` (*every* `Expression 𝕂` is hole-free, since `Hidden`'s index is always `EncS s`), and `holeFree_enc_exists` (a hole-free ciphertext is a real `Enc`, which is what `decrypt`'s failure arm turns on). Recovers the one guarantee lost by merging LM18's `𝐄𝐱𝐩` and `𝐏𝐚𝐭` into one type. |

### 3.4 `Expression/ComputationalSemantics/` — from expressions to distributions

| File | What it does |
|---|---|
| `…/Def.lean` **[mod, +190]** | `encryptionScheme`, **`prgScheme`** (`prg0`, `prg1` on κ-bit seeds), `evalExpr`, `exprToFamDistr`. The added material is the three-variable resampling machinery (`subst3`, `resample3`, `resamplingLemmaPrg`, …) the PRG reduction needs — the two-variable version only supported swapping one key at a time. |
| `…/Games.lean` **[mod]** | Both primitive games as seeded oracles: `encryptionSchemeIndCpa` (IND-CPA, left-or-right) and `prgSchemeSecure` (real versus ideal). **Fixed**: see §4.4. Merged from `EncryptionIndCpa.lean` + `PrgSecurity.lean`. |
| `…/NormalizePreserves.lean` | Normalisation does not change the induced distribution. |
| `…/RenamePreserves.lean` | A *valid* variable renaming does not change the induced distribution (`applyRenamePreservesCompSem2`) — this is what makes the `atomic` generator of `PrgRenameRel` free. |
| `…/Soundness.lean` **[mod, +175]** | The top of the expression layer: `PrgRenameRel`, **`prgRename`** (LM18 Lemma 2), `symbolicToSemanticIndistinguishabilityOfStep`, and the capstone **`symbolicToSemanticSoundness`** (LM18 Theorem 3, no side conditions). |
| `…/Executable/Executable.lean` **[new, 2026-09-28]** | **`ExecScheme`** (executable encryption: explicit coins, plus `run k m r ∈ (encrypt k m).support`), **`evalExprExec`** — the same recursion as `evalExpr`, computable and `PMF`-free — and the refinement **`evalExprExec_mem_support`**, lifted over the sampled environment by `evalExprRun_mem_support_exprToDistr`. |
| `…/Executable/Executable.lean`, cont. | **`ExecEnc`** — an implementation mentioning no specification, hence computable — with **`ExecEnc.spec`** deriving the specification it denotes (`encrypt` = the uniform distribution on coins pushed through `run`).  That direction is what makes `#eval` possible and what makes the bridge to `garbleCorrectComp` definitional. |
| `…/Executable/ExecutableDistribution.lean` **[new, 2026-09-28]** | **The distributional refinement.**  `encCount` and the two structural lemmas (coin consumption depends on the expression, never on a value), the change-of-variables induction **`execDistr_eq`**, and its lifts `execToDistr_eq` / `ExecEncScheme.toFamDistr_eq`.  This is what transports *security*, which the support-level refinement cannot. |

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
| `Garbling/Correctness/Correctness.lean` | **`garbleCorrect`** / `theorem4_holds` — LM18 **Theorem 4**: `GEval(Garble(C,x)) = C(x)`. |
| `Garbling/SymbolicHiding/Lemmas.lean` | Shared bookkeeping: counter freshness (`LabelsBelow`), strong independence (`IndependentKeys`, `DistinctLabels`, `StronglyIndependent`), the invariants `LabelInvariantIn` / `LabelValueIn` / `LabelZeroIn`, the statements of Lemmas 4–8 and Theorems 4–5, and the stage relation **`GbStage`** (§5.1). |
| `Garbling/SymbolicHiding/GarbleProof.lean` | Characterises `adversaryKeys (Garble C x)`: **`lemma5`**, **`lemma6`**, `lemma4_garble`, `lemma6_garble_cond1`, `adversaryKeys_G0_seed`/`_G1_seed`, `makeLabels_stronglyIndependent`. |
| `Garbling/SymbolicHiding/GarbleHole.lean` | Characterises `adversaryView (Garble C x)`: **`atomic_recovered_garble`**, **`GbStage.view_extract_iso`**, **`lemma7`**, `lemma7_value` (§5.2). |
| `Garbling/SymbolicHiding/SimulateProof.lean` | The same for the simulated circuit, reusing the garbling work via `encKeys_sim_eq_gb` / `exprKeys_sim_subset_gb`: **`lemma8`**, `lemma8_zero`, `atomic_recovered_simulate`. |
| `Garbling/SymbolicHiding/GarbleHoleBitSwap.lean` | The renaming that maps garbling to simulation: `SwapCompatible`, `AgreesOn`, `valueMap`, `nandPattern`, **`theorem5`** (§5.3). |
| `Garbling/Correctness/ExecutableCorrectness.lean` **[new, 2026-09-28]** | **`GarbleExec`** and **`garbleExecCorrect`**: `Evaluate(Garble(C,x)) = C(x)` for code that actually computes, obtained by composing `garbleCorrectComp` — which is stated over the distribution's *support* — with `evalExprExec_mem_support`. Plus `garbleExec_projective`, the offline/online split with coin threading. |
| `Garbling/HoleFree.lean` **[new, 2026-09-28]** | **`garble_holeFree`** / **`simulate_holeFree`**: neither `Gb` nor `Sim` ever emits a hole. In LM18 this is a typing fact; here it is a theorem. |
| `Crypto/ChaCha20.lean` **[new, 2026-09-28]** | ChaCha20 (RFC 8439) in pure Lean, and both primitives instantiated at κ = 256: **`chacha20Enc : ExecEnc 256`** (CTR mode, nonce as coins) and **`chacha20Prg`** (the two halves of one keystream block). Correctness proved; agreement with RFC 8439 validated by test vectors against OpenSSL; security assumed. |
| `Crypto/StreamCipher.lean` **[new, 2026-10-01]** | **`prfFunctions`** — a keyed keystream generator (key, nonce, length), the primitive the cipher is actually built from.  **`prfExecEnc`** / **`prfEnc`** — nonce-prefixed counter mode over it, `decrypt_encrypt` free from **`prfXor_prfXor`**.  **`chacha20Enc_eq`** (by `rfl`): the extracted cipher *is* this construction.  **`prgOfPrf`** and **`chacha20Prg_eq`**: the length-doubling PRG is the same generator at nonce zero — one primitive, two interfaces.  No assumption added; the PRF game is blocked, see `FUTURE-WORK.md`. |
| `Crypto/Ggm.lean` **[new, 2026-10-01]** | **`ggm`** — the GGM tree (`prg0`/`prg1` as the two children), with `ggm_append`.  **`ggmPrf`** — a `prfFunctions` from a `prgFunctions` alone, counter mode over the tree.  **`ggmEnc`** / **`ggmEncScheme`** — an encryption scheme whose only ingredient is the PRG, the object a single-assumption mode would be stated over.  Construction only; GGM's security is future work. |
| `Garbling/EvaluatorTotality.lean` **[new, 2026-09-28]** | `gEv` never fails on a genuine garbling (`gEv_isSome_of_gb`), the simulation lemma without its side condition (`gEvComp_of_gb`), and **`GEvalExpr_eq_EvaluateComp`** — the symbolic and computational evaluators agree on every bit vector a garbled circuit can take. |
| `Garbling/Security/ExecutableSecurity.lean` **[new, 2026-09-28]** | **`garblingSecureExec`** — `garblingSecureRelative` for the distributions an implementation actually produces, by rewriting with the distributional refinement. |
| `Garbling/Security/Security.lean` | **`garblingSecure`** — Theorem 5 composed with Theorem 1. |

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
Counterexample (machine-checked in `scratch/findings/ExtractKeysSelfCounterexample.lean`):

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

### 4.7 Bounded vs. unbounded PRG closure — a forced divergence, now characterised

**STATUS: PROVED.** `Expression/Lemmas/GStar.lean`.

`prgClosure U S` is bounded by `U = keySubterms p`, so it is **not** LM18's unbounded `𝖦*`.
This is forced rather than chosen: `greatestFixpoint` is a constructive recursion on
`Finset.card`, so `keyRecovery` must return a `Finset`, and `𝖦*({k})` is infinite.
Computability and `#eval` are consequences, not the motivation.

Two theorems say exactly what the bound costs. `prgClosure_eq_gStar_inter`: for a
chain-closed bound, `prgClosure U base = 𝖦*(base) ∩ U` **exactly** — `keySubterms p` is
chain-closed (`keySubterms_closed`). And `adversaryView_eq_gStar`: hiding with the bounded
closure yields *the same expression* as hiding with the unbounded `𝖦*`, so the computed
pattern — all that `symIndistinguishable` compares — is the paper's.

What genuinely differs is membership for keys that do **not** occur in the expression.
`scratch/probes/DupTrailing.lean` exhibits it: `Garble Dup true` has `keySubterms = {K₁}` while its
output labels are `(b, G0 K₀, G0 K₁)` and `(b, G1 K₀, G1 K₁)`, so LM18 recovers one key of
each pair and the bounded closure recovers neither. That is why `LabelInvariant S` was
relativised to `LabelInvariantIn U S`; with `adversaryView_eq_gStar` the relativisation is
justified rather than merely explained, since a key occurring nowhere affects no pattern.

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
(`scratch/probes/GarbleSideCondition.lean` exhibits this on a garbled circuit). LM18 discharges this
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

## 5b. Projectivity

`Garble_projective` (2026-09-21i): `Garble c x` factors through `preGarble c`, which does not
mention `x` — the input enters only through `makeProjection`, one wire at a time.  This is the
property the base paper's §3 route from garbling to two-party computation requires, and which
that paper states it formalised; it had been dropped in this extension and is now restored.

The 2PC protocol itself and oblivious transfer remain unformalised — as they are in the base
paper, whose contributions list covers the symbolic framework, the computational framework, the
soundness theorem and symbolic security of garbling, but not 2PC.

## 5a. Correctness

`garbleCorrect` (LM18 Theorem 4) is the *symbolic* statement.  Since 2026-09-21h the
*computational* one is proved too: `garbleCorrectComp`
(`Garbling/Correctness/ComputationalCorrectness.lean`) shows `Evaluate(Garble(C,x)) = C(x)` on real bit
vectors, for every value the garbled circuit can take.

Soundness does not give this and is not meant to — it maps a relation between two expressions
to a relation between two distributions, whereas correctness applies a function to one
distribution.  The missing ingredient was `encryptionFunctions.decrypt_encrypt`; adding it also
closed the degenerate-scheme loophole, so IND-CPA is no longer trivially satisfiable.

For a consolidated account of how the theorems chain together, where the Lean departs from
the pen-and-paper proofs, and what the adversary model is, see `summary.md`.

## 5c. An executable implementation

`garbleCorrectComp` says every bit vector the garbled circuit *can* take evaluates to `C(x)`.
That is exactly the specification an implementation must meet, so since 2026-09-28 there is
one, and it is proved against the same statement rather than against a second correctness
notion.

`ExecScheme` (`Expression/ComputationalSemantics/Executable/Executable.lean`) is the executable
counterpart of a scheme's encryption: explicit coins, plus the law that every output is one the
`PMF` could have produced.  It has to be *required* of a scheme rather than derived —
`encryptionFunctions.encrypt` is an arbitrary `PMF` — and it is the only place randomness
enters, because `evalExpr` is `PMF.pure` at every other node.  `evalExprExec` is then the same
recursion with a coin supply threaded through, computable and `PMF`-free, and
`evalExprExec_mem_support` is the refinement: its output lies in the support of `evalExpr`.
Over the sampled environment the lift is immediate, since a uniform distribution on a nonempty
finite type has full support.

`garbleExecCorrect` (`Garbling/Correctness/ExecutableCorrectness.lean`) composes the two:
`Evaluate(Garble(C,x)) = C(x)` for the code that runs, for every environment and every coin
supply.  `garbleExec_projective` carries §5b across — the coin threading respects the split, so
the garbled tables, the output mask and both labels of every input wire can be computed before
`x` is known, which is what an oblivious-transfer deployment needs.

**Security is transported too**, since 2026-09-28c.  The support-level refinement cannot do it
— an implementation that always returned the same ciphertext satisfies it — so what is proved is
that drawing the coins uniformly and running the code gives *exactly* the specification's
distribution (`execDistr_eq`, lifted to `execToDistr_eq` and `ExecEncScheme.toFamDistr_eq`).
`garblingSecureExec` (`Garbling/Security/ExecutableSecurity.lean`) is then `garblingSecureRelative` for
the distributions an implementation actually produces.  The crux — a uniform distribution on a
product splits into independent uniforms — was not in Mathlib and is proved in
`Core/UniformProduct.lean`, with no garbling in it.  Primitive hardness remains assumed.

The implementation itself **runs under `#eval`**, on real
crypto: `ExecEnc` (`Executable.lean`) is an implementation with the specification *derived* from
it, so nothing `noncomputable` appears in a position the compiler sees, and `shapeLengthOn`
computes the bit-vector lengths — which `vecTake`/`vecDrop` need as data — from the
ciphertext-length function alone.  `Crypto/ChaCha20.lean` instantiates both primitives at
κ = 256: the cipher in CTR form, where `dec_run` is xor involution and needs no property of
ChaCha20, and the length-doubling PRG as the two halves of one keystream block.
`scratch/checks/ExecDemo.lean` garbles and evaluates `notC`, `NAnd`, `andC` and `orC` under them
(2054–5903 bits per garbled circuit); `scratch/checks/ChaCha20Kat.lean` checks the cipher against
OpenSSL on RFC 8439 vectors.

## 6. What is *assumed*, not proved

`garblingSecure` / `garblingSecureFromEfficiency` / `garblingSecureFromCostModel` rest on
**two** kinds of assumption, both on the computational side: hardness of the primitives, and
an *interface* describing what polynomial time is closed under.

### 6.1 Hardness of the primitives

`encryptionSchemeIndCpa enc` and `prgSchemeSecure prg`. These are the point of the exercise,
not a gap.

### 6.2 Efficiency: an interface, not a cost semantics

**As of 2026-09-18c both former efficiency assumptions are theorems.**
`EncReductionPolyTime` (`encReduction_polyTime`) and `EvalEfficiencyFromPrimitives`
(`evalEfficiencyFromPrimitives_holds`) are proved in
`ComputationalSemantics/CostModel.lean`, as is the sampling prefix of the PRG reduction
(`prgEnvSampler_polyTime`).  `garblingSecureFromCostModel`
(`Garbling/Security/SecurityFromPrimitives.lean`) is the entry point in which every efficiency claim
about a *reduction* has been discharged.

They are theorems **relative to an interface**, and the interface is assumed:

* **`PolyTimeModel`** — fifteen closure clauses over a pair of predicates: the existing
  `IsPolyTime` on closed families, and a new `IsPolyTimeFn` on *function* families.  Seven
  are about oracle-free value functions (`valId`, `valFst`, `valSnd`, `valUnit`, `valPair`,
  `precompVal`, `bindVal`), six about oracle computations (`pureFn`, `liftVal`, `bindFn`,
  `precompFn`, `queryFn`, `closeFn`), two about sampling (`uniformBits`, `uniformKeys`).
* **`BitOpsEfficient`** — seven clauses naming the non-cryptographic bit-vector operations
  the semantics performs: `append`, `condAppend`, `bitExpr`, `bitToVec`, `keyVar`,
  `constVec`, `nilVec`.

Nine of the twenty-two carry a `PolySized` side condition on a type family their statement
does not otherwise constrain (`ComputationalSemantics/Def.lean`).  It is load-bearing: a
poly-size circuit family has I/O width bounded by its size, so without it `valId` at
`D κ := BitVector (2 ^ κ)` is false.  `PolySized` carries its `width` as data, so a concrete
cost model's obligations are arithmetic in the widths rather than a restatement.

**As of 2026-09-21b the interface is no longer assumed either.**
`ComputationalSemantics/GeneratedPolyTime.lean` defines `IsPolyTime` concretely, as the
smallest class containing the primitives and closed under the combinators — an inductive
family whose *derivations are the implementations*.  `genPolyTimeModel` and
`genBitOpsEfficient` prove every clause of the interface for it (each is the matching
constructor), LM18 Definition 1 becomes a generator rather than a hypothesis, and
`garblingSecureGenerated` is the security theorem at that concrete predicate.

The route through a *cost function* was attempted first and is impossible: local running time
is not a property of an `OracleComp` term, since the free monad records oracle queries and
nothing else.  `scratch/findings/CostAttempt.lean` proves it two ways.  See `CHECKPOINT.md` §3.1.

Two things are still assumed, and both matter:

* **Superseded 2026-09-21e.**  `garblingSecureRelative` states security against an *arbitrary*
  adversary class `A`, assuming only that `A` is closed under composition and contains the
  generated class (`ClassContained`).  The generated class now certifies the reductions and
  nothing else, so its width no longer bounds the conclusion; read `A` as "all PPT adversaries".
  The paragraph below describes the older `garblingSecureGenerated`, retained as the fully
  concrete instance.

* **The generated class was too narrow for that statement to mean much** (finding F8,
  **fixed 2026-09-21d**).
  No generator took a `BitVector` to a `Bool`, so no distinguisher in `GenPolyTime enc prg`
  could produce an output depending on the challenge.  The widening added bit indexing
  (`index`, `update`), boolean gates (`notB`, `andB`, `select`, `eqBits`, `xorBits`), addressing
  (`bitsToFin`) and bounded iteration (`iterate`, `iterateIdx`) — 19 generators to 33 — with
  `polyFn_indCpaBitAdversary` as the witness that the previously unreachable shape is now in the
  class.  What is still missing is a *completeness* theorem, which is a different thing; that
  part is exactly what
  Hofmann's LFPL and Atkey's polytime QTT address, so the calculus survey in `CHECKPOINT.md`
  §2 should be revisited at that point.
* `PolyTimeClosedUnderComposition` still resists, for exactly the reason finding F6 is about:
  it is phrased with `polyTimeFamComp`, whose "query for your input" encoding is not
  invertible.  Restating it at the value level is the remaining work.

Why a second predicate was needed: `reductionToOracle` recurses over the expression *while
making oracle queries*, so its decomposition needs sequencing of **two oracle computations**,
which `PolyTimeClosedUnderComposition` (oracle-then-pure) does not provide.  Sequencing needs
a continuation, and a continuation is a function.  Two natural-looking weaker formulations
fail, and `CostModel.lean`'s header records why: quantifying `bind`'s continuation pointwise
over arbitrary *semantic* value families is useless at a `Pair` node, and an unconstrained
`pure` clause makes every pure computation free.

The interface bottoms out at the primitives, which is the correct endpoint: `enc.encrypt`,
`prg0`, `prg1`, `List.Vector.append` and `evalBitExpr` are arbitrary Lean functions, so
their cost must remain a parameter.  That parameter is LM18 Definition 1.

### 6.2a Ciphertext growth — a gap that had not been flagged

`encryptionFunctions.encryptLength` was an arbitrary `ℕ → ℕ`.  `encryptLength n = 2 ^ n` was
a legal scheme, and for it the value of a nested `Enc` is exponentially long in the
expression depth — so `shapeLength` is not polynomially bounded, and the pen-and-paper cost
analysis at the end of `HidingOneKey.lean` is **false**, since it assumes the output-length
bound it needs.  Fixed by `LengthPoly` and `shapeLength_poly`
(`ComputationalSemantics/Def.lean`), which formalise that analysis's output-length
induction; `EncS` is the only case that needs anything, and it is exactly where `LengthPoly`
is consumed.

Consequently `EvalEfficiencyFromPrimitives` now carries `LengthPoly enc` and takes
`EfficientEncPoly` (message length a polynomially bounded *family*) rather than
`EfficientEnc` (message length constant in `κ`).  The inherited statement was not provable
as written.

### 6.2b What is still open

* **Non-vacuity.**  `trivialPolyTimeModel` shows the interface is consistent, so the
  theorems are not vacuous for the trivial reason.  It shows nothing else — but *which*
  hypothesis rules it out is not the obvious one, and was audited on 2026-09-18d.

  IND-CPA security is **satisfiable** under `fun _ => True`.  `encryptionFunctions` has no
  correctness field relating `encrypt` to `decrypt`, so a scheme whose ciphertext ignores the
  message is legal, and for it the left and right IND-CPA oracles are literally the same
  function — advantage `0` against every adversary.  `constEnc_indCpa`
  (`scratch/archive/DegenerateEnc.lean`) is the Lean proof.

  The hypothesis that actually binds is **`prgSchemeSecure`**.  The real oracle answers with
  `(prg0 s, prg1 s)` for a κ-bit seed, the ideal with a uniform 2κ-bit pair, so the real
  answer ranges over at most `2 ^ κ` of `2 ^ (2 * κ)` points and the unbounded distinguisher
  "decide membership in the image" wins with advantage at least `1 - 2 ^ (-κ)`.  Unlike
  encryption, there is no entropy-preserving cheat.  (Counting argument; not formalised.)

  So the open witness is: a concrete `IsPolyTime` satisfying the closure clauses for which
  `prgSchemeSecure` is *consistent*.  It cannot be more than consistency — proving
  `∃ prg, prgSchemeSecure concreteIsPolyTime prg` outright would give one-way functions,
  hence `P ≠ NP`.  See `CHECKPOINT.md` §3.0 (F4) and §3.1 step 6.
* **A concrete cost semantics** (`CHECKPOINT.md` §3.1, Design B) would turn the interface's
  clauses into theorems.  Design A deliberately came first: it identifies exactly which
  clauses Design B has to prove — and the 2026-09-18d audit against poly-size circuits found
  that three of them (`valId`, `valFst`, `valSnd`) were **false for arbitrary type families**,
  since a poly-size circuit family has I/O width bounded by its size.  That was a
  satisfiability defect in the interface, not a soundness defect in the proofs above
  (`trivialPolyTimeModel` still satisfied it), and it is **fixed as of 2026-09-18e** by
  `PolySized`, now a side condition on nine clauses.  `CHECKPOINT.md` §3.0 has the four
  findings, and §2 records why ILC, Atkey's polytime QTT and `calf` were each evaluated as
  candidate calculi and rejected.

What is *not* assumed, and worth noting because the inherited code assumed all of it:

* `PrgReductionPolyTime` is **derived** (`reductionToPrgOracle_polyTime`), because the PRG
  reduction is exactly "sample an environment, query once, evaluate"
  (`reductionToPrgOracle_decompose`), so the framework's own composition closure applies.
* `EfficientPrg` / `EfficientEnc` / `EfficientEncPoly` state LM18 Definition 1's efficiency
  requirement, which the inherited model omitted entirely — `prgFunctions` was an arbitrary
  pair of functions with no tie to `IsPolyTime`.
* Both efficiency hypotheses were originally quantified over **all** schemes, which is false
  in any concrete cost model (an inefficient scheme has an inefficient reduction) and would
  have made every downstream theorem vacuous on instantiation. They are now fixed to the
  ambient `enc`/`prg`. See `ComputationalSemantics/PolyTime.lean`.

Entry points, weakest hypotheses last:
`garblingSecure` ⊃ `garblingSecureFromEfficiency` ⊃ `garblingSecureFromCostModel`.

### 6.3 Definitional deviations from the paper (disclosure, not assumptions)

These do not weaken the theorem; they mean it is about a very slightly different model.

* `Hidden k` evaluates to `enc.encrypt key ones` (all-ones) where LM18 writes
  `𝖤(σ(k), 0^{|s|})`. A fixed public constant either way. The length is pinned by
  unification rather than an explicit `shapeLength` argument, which makes some goals harder
  to read.
* ~~`normalizeExpr` does not recurse into `Enc`'s key or into `Hidden`.~~ **Fixed
  (2026-09-18b).** It now recurses into `Enc`'s key, `Hidden`'s key and `G0`/`G1`.  This was
  provably a no-op — `normalizeExpr_key` shows normalising a key is the identity — but
  `normalizeExpr` is part of the definition of `symIndistinguishable`, so under-normalising
  would have made that relation too *strong* and could have broken LM18 Theorem 5 (not
  soundness) had the language gained a key former mentioning bits.

  The invariant it rested on is still worth knowing, because `hideEncrypted_key`,
  `encKeys_key`, `extractKeys_key` and `exprKeys_key` all depend on it: `Expression 𝕂` has
  only the constructors `VarK`, `G0`, `G1` — no `Enc`, no `Hidden`, no `BitE`.

### 6.4 Previously assumed, now proved

Recorded because earlier drafts of this report listed them as assumptions.

* **[Mic09, Lemma 2]** — `Expression/Lemmas/PseudorandomRenaming.lean`. Both directions: the
  factorisation (`gPreserving_eq_substKeys`, `gPreserving_ext`, `rootsOf_keySubterms`) and
  the generation direction in full (`prgRenameRel_substKeys_general` — every injective
  renaming of the roots with pairwise independent images is reachable from LM18's two
  generators, with no freshness hypothesis). So the generators are exhaustive and
  `PrgRenameRel` loses nothing by taking them as its definition.
* **The bounded PRG closure** — `Expression/Lemmas/GStar.lean`; see §4.7.

* **The two efficiency obligations** — `EncReductionPolyTime` and
  `EvalEfficiencyFromPrimitives`, both discharged on 2026-09-18c against the
  `PolyTimeModel` interface (§6.2).

No symbolic-side *assumptions* remain. What is left is computational: hardness of the
primitives (the point of the exercise), LM18 Definition 1 for them, and the poly-time
interface — which still waits on a cost semantics for `OracleComp` to become theorems.

## 7. Verification

```
lake build                                  # clean; only style linter warnings
grep -r "sorry\|^axiom" PRGExtension        # no occurrences outside comments
```

```
#print axioms PRG.garblingSecureFromEfficiency   → [propext, Classical.choice, Quot.sound]
#print axioms PRG.garblingSecure                 → [propext, Classical.choice, Quot.sound]
#print axioms symbolicToSemanticSoundness        → [propext, Classical.choice, Quot.sound]
#print axioms PRG.fixpointStepSound              → [propext, Classical.choice, Quot.sound]
#print axioms PRG.theorem5                       → [propext, Classical.choice, Quot.sound]
#print axioms PRG.lemma7 / PRG.lemma8            → [propext, Classical.choice, Quot.sound]
#print axioms PRG.prgRenameRel_substKeys_general → [propext, Classical.choice, Quot.sound]
#print axioms PRG.adversaryView_eq_gStar         → [propext, Classical.choice, Quot.sound]
#print axioms PRG.garbleCorrect                  → [propext, Quot.sound]
#print axioms PRG.garbleCorrectComp              → [propext, Classical.choice, Quot.sound]
#print axioms PRG.garbleExecCorrect              → [propext, Classical.choice, Quot.sound]
#print axioms PRG.garble_holeFree                → [propext]
#print axioms PRG.execDistr_eq                   → [propext, Classical.choice, Quot.sound]
#print axioms PRG.garblingSecureExec             → [propext, Classical.choice, Quot.sound]
```

Executable sanity checks live in `scratch/`, not part of the library, grouped by role and run
with `lake env lean scratch/<group>/<f>.lean`: `checks/` is what a reader should run,
`findings/` holds machine-checked refutations, `archive/` superseded records, `probes/` one-off
exploration.  `probes/TwoGateFixpoint.lean` computes `adversaryKeys` on a two-gate garbled
circuit and exhibits a non-atomic root at the fixpoint;
`findings/ExtractKeysSelfCounterexample.lean` refutes §4.5; `findings/symgc/` builds LM18's own
Haskell artifact and measures its `Pattern` against Definition 3 (`writeup.md` §22.5); `probes/GarbleSideCondition.lean`
refutes the old atomicity side condition; `probes/DupTrailing.lean` exhibits the §4.7
divergence; `checks/GarbleCorrectness.lean` evaluates `GEval(Garble(C,x))` symbolically;
`checks/ExecDemo.lean` does the same through the *executable* scheme (§5c), garbling and
evaluating real bit vectors under a toy `ExecScheme`.

Companion documents: `PRGExtension-Analysis.md` (the original defect analysis, with STATUS
markers) and `CHANGELOG.md` (dated, per-change record).
