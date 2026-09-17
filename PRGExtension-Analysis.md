# PRGExtension: status, defects, and a plan to finish

*Analysis of `PRGExtension/` against `SymbolicGarbledCircuitsInLean/` (the unmodified DFMS framework) and
against Li–Micciancio, "Symbolic security of garbled circuits", CSF 2018 (`prg.pdf`, cited below as **LM18**).*

> **Implementation status (2026-09-16).** §4.1–§4.5 and §4.7 items 1 and 5 are implemented,
> and the single-seed PRG hop of §5.3 is proved. **`PRGExtension/` is now `sorry`-free**, and
> `#print axioms symbolicToSemanticIndistinguishability` reports only `propext`,
> `Classical.choice`, `Quot.sound`. §4.5 turned out to be a *false statement* rather than an
> open one and is rewritten below. See [`CHANGELOG.md`](CHANGELOG.md) for the per-file
> record. `sorry`-carrying declarations: 9 → 0. The analysis below is kept in its original
> diagnostic form, with a **STATUS** line added to each item.

Build status as originally written: `lake build` **succeeds** (exit 0) with `sorry` warnings in 9 declarations
across 4 files. Nothing is broken syntactically; the problems are semantic.

---

## 1. TL;DR

The port of the *plumbing* (adding `G0`/`G1` to the AST, threading a `prgScheme` through the computational
semantics, generalising `Enc`/`Hidden` to arbitrary key expressions, generalising `fixaccess`) is done well and
is largely reusable. The port of the *security argument* is not yet right, and two of the remaining `sorry`s
cannot be closed because the statements above them are false.

Three things must change before any more proof effort is spent:

| # | Problem | Consequence |
|---|---------|-------------|
| **P0-a** | `keyRecovery` omits LM18's "ancestor" clause of `r(e)` | the top-level soundness theorem is **false**, not merely unproved |
| **P0-b** | `reductionToOracleSimulateEq` is false as stated (its two `sorry`s are unclosable) | `symbolicToSemanticIndistinguishabilityHidingOneKey` is unsound |
| **P1** | `prgSchemeSecure` is unsatisfiable (ideal oracle re-randomises per query) | every theorem assuming it is vacuous |

Fixing P0-a makes the `G0`/`G1` branches of `symbolicToSemanticIndistinguishabilityHidingInner` vacuous
**in the atomic-roots case** — but only there, and that case is not preserved by the fixpoint iteration
(§4.3). The general case needs a pseudorandom key renaming, which needs PRG security, which needs exactly the
oracle machinery in `PrgSecurity.lean` and `HidingOnePrgSeed.lean`. So that machinery is to be **retargeted,
not discarded**; what should go is only its exposure as a constructor of the *symbolic* relation
(`symbolicEquivalence`) and the `idealize_PRG_soundness` axiom.

Separately, the computational model has a number of genuinely unspecified pieces beyond the three defects
above — an empty reduction body, a single-seed oracle with no hybrid-composition lemma, no poly-time
requirement on the PRG, and no vocabulary (`⪯`, `Independent`, `Roots`, `Parts`) in which LM18's key lemmas
can even be stated. These are collected in §4.7.

---

## 2. Inventory of the modifications

Diff sizes (`PRGExtension/` vs `SymbolicGarbledCircuitsInLean/`, diff lines, ignoring import rewrites):

| File | Δ | Nature of change |
|---|---:|---|
| `Core/CardinalityLemmas.lean` | 0 | identical |
| `ComputationalIndistinguishability/{Def,Lemmas}.lean` | 8 / 4 | import paths only |
| `Core/Fixpoints.lean` | 97 | **real generalisation** of `fixaccess` |
| `Expression/Defs.lean` | 34 | `G0`, `G1` constructors; `namespace PRG` |
| `Expression/Renamings.lean` | 20 | namespace + two `apply`→`exact` fixes |
| `Expression/Lemmas/{NormalizeIdempotent,Renaming}.lean` | 8 / 9 | `open PRG` only |
| `Expression/Lemmas/HideEncrypted.lean` | 196 | `hideEncryptedS`/`allParts` recurse into keys |
| `Expression/SymbolicIndistinguishability.lean` | 755 | `keySubterms`, `prgClosure`, new `keyRecovery`, `replacePRG`, `symbolicEquivalence` |
| `.../ComputationalSemantics/Def.lean` | 295 | `prgFunctions`, `evalExpr` for `G0`/`G1`, `Enc`/`Hidden` over key *expressions* |
| `.../NormalizePreserves.lean`, `.../RenamePreserves.lean` | 86 / 88 | mechanical PRG threading — **complete, no `sorry`** |
| `.../EncryptionIndCpa.lean` | 17 | namespace only |
| `.../PrgSecurity.lean` | **new** | PRG oracle pair, `prgSchemeSecure`, one `axiom` |
| `.../SoundnessProof/HidingOneKey.lean` | 1195 | IND-CPA reduction extended to `G0`/`G1` |
| `.../SoundnessProof/HidingOnePrgSeed.lean` | **new** | PRG-idealisation hop — 4 `sorry`s, essentially a stub |
| `.../SoundnessProof/AdversaryView.lean` | 488 | fixpoint argument + 12 `sorry`s in the `G0`/`G1` branches |
| `.../Soundness.lean` | 83 | threads `prg`, `HPrgSecure`, `HreductionPrg` |
| `Garbling/**` | — | **not ported at all** (3157 lines left behind) |

### Design decisions that are correct and should be kept

* **`G0 : Expression 𝕂 → Expression 𝕂`, `G1` likewise** ([Defs.lean:29-30](PRGExtension/Expression/Defs.lean#L29-L30))
  matches LM18 §2.1 `Exp(𝕂) → 𝖪ᵢ ∣ 𝖦₀(Exp(𝕂)) ∣ 𝖦₁(Exp(𝕂))` exactly.
* **No `HiddenG0`/`HiddenG1`.** The commented-out attempt was correctly abandoned: LM18 adds *only*
  `Pat(⦃s⦄) → ⦃s⦄_{Exp(𝕂)}`; PRG outputs are never holes.
* **Generalising `Enc k e` and `Hidden k` to arbitrary key expressions**
  ([Def.lean:218+](PRGExtension/Expression/ComputationalSemantics/Def.lean#L218)) is mandatory — garbled
  circuits encrypt under `G^w(k)` — and the semantics `evalExpr … (G0 e) = prg0 <$> evalExpr … e` is right.
* **`prgFunctions` as a pair `prg0, prg1 : BitVector κ → BitVector κ`** is the right encoding of a
  length-doubling PRG split into halves (LM18 Def. 1).
* **`fixaccess` decoupled into (view generator `f1`, step function `f`, separate `boundSet`)**
  ([Fixpoints.lean:41-115](PRGExtension/Core/Fixpoints.lean#L41-L115)). The original signature forced
  `f = f2 ∘ f1`, which `keyRecovery` no longer satisfies. This generalisation is genuinely needed and is
  proved cleanly (dropping the `Rrfl` hypothesis is a bonus).
* **`KeyRenaming := ℕ → ℕ` was *not* changed.** See §5.3 — this is defensible but incomplete.
* **`RenamePreserves.lean` and `NormalizePreserves.lean` are fully ported with no `sorry`.** Keep.

---

## 3. The `sorry` inventory

```
SymbolicIndistinguishability.lean:805        extractKeys_hideEncrypted_self, Enc branch
HidingOneKey.lean:268, 279                   reductionToOracleSimulateEq,  G0/G1 branches
HidingOneKey.lean:770, 778                   reductionToOracleSimulateEq2, G0/G1 branches
HidingOnePrgSeed.lean:26, 38, 52, 81         the whole file (reduction body + both worlds + final hop)
AdversaryView.lean:171-245 (12 occurrences)  the G0/G1 branches of HidingInner
AdversaryView.lean:350                       dead: in the superseded `…AdversaryView'`
```

**After the 2026-09-16 changes, none remain.** Every item above is either proved or was
removed as a false statement (§4.5).

Note that `HidingOneKey.lean` also contains two **complete, `sorry`-free** lemmas,
`reductionToOracleSimulateEq'` ([:288](PRGExtension/Expression/ComputationalSemantics/SoundnessProof/HidingOneKey.lean#L288))
and `reductionToOracleSimulateEq2'` ([:784](PRGExtension/Expression/ComputationalSemantics/SoundnessProof/HidingOneKey.lean#L784)),
which are **never used**. They differ from the unprimed versions only in taking the hypothesis
`VarK key₀ ∉ keySubterms e` instead of `VarK key₀ ∉ extractKeys e`. That is not a cosmetic difference — see
§4.2.

---

## 4. Defects, in priority order

### 4.1 (P0-a) `keyRecovery` is missing LM18's ancestor clause — the soundness theorem is false

**STATUS: FIXED.** `exprKeys`, `strictYields`, `ancestorKeys` added; `keyRecovery` now closes `extractKeys view ∪ ancestorKeys (exprKeys view)`; `keyRecoveryMonotone`/`Contained` re-proved.

LM18 Definition 3 defines key recovery as

> `r(e) = 𝖦*( { k ∈ Keys(e) | (k ⋐ e) ∨ (∃k' ∈ Keys(e). k ≺ k') } )`

The current Lean definition ([SymbolicIndistinguishability.lean:202-213](PRGExtension/Expression/SymbolicIndistinguishability.lean#L202-L213))
implements only the **first** disjunct:

```lean
def keyRecovery (p) (S) :=
  let univKeys  := keySubterms p
  let expandedS := prgClosure univKeys S
  let view      := hideEncrypted expandedS p
  prgClosure univKeys (extractKeys view)      -- = 𝖦*({k ∈ Keys(view) | k ⋐ view})
```

`extractKeys` is exactly `{k ∈ Keys(e) | k ⋐ e}` (it skips encryption keys and returns `∅` on `Hidden`).
The clause `∃k' ∈ Keys(e). k ≺ k'` — *"if a strict PRG-descendant of `k` occurs anywhere in the expression,
then `k` counts as recovered"* — has no counterpart anywhere in the file.

That clause is not a technicality. It is the **only** thing that rules out the situation in which the
adversary is handed `G0(k)` while a ciphertext under `k` is still supposed to be hidden. LM18's proof of
Lemma 3 derives precisely three properties for every key `k ∈ Keys(e) \ r(e)` that is going to be hidden:

1. `k ∈ 𝐊` — `k` is **atomic**;
2. `𝖦*(k) ∩ Parts(e) = ∅` — neither `k` nor any descendant appears in the clear;
3. `𝖦⁺(k) ∩ Keys(e) = ∅` — **no descendant of `k` is used anywhere in `e`**.

Properties 1 and 3 are exactly what the missing disjunct buys, and property 3 is exactly what the IND-CPA
reduction needs (the reduction never learns `k`, so it must never be required to compute `G0(k)`).

**Concrete counterexample to the current top-level theorem.** Take

```
e₁ = ⟨ G0(K₀) , Enc K₀ (Bit true)  ⟩
e₂ = ⟨ G0(K₀) , Enc K₀ (Bit false) ⟩
```

Running the current `adversaryKeys`: `keySubterms eᵢ = {G0(K₀), K₀}`; the first iteration gives
`extractKeys eᵢ = {G0(K₀)}`; the second gives `hideEncrypted {G0(K₀)} eᵢ = ⟨G0(K₀), Hidden K₀⟩` whose
`extractKeys` is again `{G0(K₀)}` — a fixpoint. So

```
adversaryView e₁ = adversaryView e₂ = ⟨ G0(K₀), Hidden K₀ ⟩
```

and `symIndistinguishable e₁ e₂` holds with the identity renaming. But the two distributions are
**distinguishable** for a perfectly good IND-CPA scheme. Take the textbook PRF-based scheme, keyed by
the *first half of the PRG output* rather than by the key itself:

```
enc'_k(m) :  r ← {0,1}^κ ;  output (r, F_{G0(k)}(r) ⊕ m)
```

`enc'` is IND-CPA: `k` is uniform, so `G0(k)` is pseudorandom by PRG security, so `F_{G0(k)}` is a PRF,
and `(r, F_K(r) ⊕ m)` under a PRF key is the standard CPA-secure construction. But anyone who is *given*
`G0(k)` decrypts outright. So an adversary looking at `e₁`/`e₂` reads `G0(K₀)` off the first component
and decrypts the second, recovering the plaintext bit. Hence
`symbolicToSemanticIndistinguishability` as currently stated is false.

(An earlier draft of this section used `enc'_k(m) = (enc_k(m), G0(k) ⊕ pad(m))`. That scheme is *not*
IND-CPA — the mask `G0(k)` is the same in every ciphertext, so two chosen-plaintext queries reveal
`pad(m_b) ⊕ pad(m'_b)` and hence `b`. The PRF version above repairs the witness; the conclusion is
unchanged.)

Under LM18's `r`, `Keys(⟨G0(K₀), ⦃𝔹⦄_{K₀}⟩) = {G0(K₀), K₀}` and `K₀ ≺ G0(K₀)`, so `K₀ ∈ r`, the fixpoint
contains `K₀`, the ciphertext is *not* hidden, and the two patterns differ. Correct behaviour.

**What to build.** A `Keys`-analogue distinct from both `extractKeys` and `keySubterms`:

```lean
/-- LM18 `Keys(e)`: every key *as used*, without decomposing PRG applications. -/
def exprKeys : Expression s → Finset (Expression 𝕂)
  | .VarK n      => {.VarK n}
  | .G0 e        => {.G0 e}          -- NOT {G0 e} ∪ exprKeys e
  | .G1 e        => {.G1 e}
  | .Pair a b    => exprKeys a ∪ exprKeys b
  | .Perm _ a b  => exprKeys a ∪ exprKeys b
  | .Enc k e     => exprKeys k ∪ exprKeys e
  | .Hidden k    => exprKeys k
  | _            => ∅

/-- `k ≺ k'` : `k'` is a strict PRG-descendant of `k`. -/
def strictYields (k k' : Expression 𝕂) : Bool :=
  match k' with
  | .G0 s | .G1 s => (s == k) || strictYields k s
  | _             => false

def keyRecovery (p) (S) :=
  let U    := keySubterms p
  let view := hideEncrypted (prgClosure U S) p
  let K    := exprKeys view
  let base := extractKeys view ∪ K.filter (fun k => K.any (strictYields k))
  prgClosure U base
```

Note `keySubterms` (which *does* decompose `G0 e` into `{G0 e} ∪ keySubterms e`) is still the right choice
for the finite universe `U` and for `keyRecoveryContained`; it is simply the wrong notion for the
ancestor test. Keeping three key-extraction functions with clearly distinct roles (`extractKeys` = `Parts∩Keys`,
`exprKeys` = `Keys`, `keySubterms` = closure universe) will make the rest of the development legible.

Downstream obligations after this change: re-prove `keyRecoveryMonotone` (the new `filter` is monotone
because both `K` and the predicate grow together — this needs the `ExpressionInclusion`-style argument, not
plain `Finset` monotonicity, so budget real effort here) and `keyRecoveryContained` (easy: `base ⊆ U`).

### 4.2 (P0-b) `reductionToOracleSimulateEq` is false; the primed version is the correct one

**STATUS: FIXED.** `seedFree` (LM18 property 3) added and threaded through both inductions; the `'` variants are now used to discharge the `G` cases. All four `sorry`s gone.

[HidingOneKey.lean:118](PRGExtension/Expression/ComputationalSemantics/SoundnessProof/HidingOneKey.lean#L118)
states, under hypothesis `VarK key₀ ∉ extractKeys e`:

```
simulateQ (indCpaOracle Side.L … oracleKey) (reductionToOracle … e key₀)
  = liftM (evalExpr enc prg (subst2 key₀ oracleKey kVars) bVars e)
```

Take `e = G0 (VarK key₀)`. Then `extractKeys e = {G0 (VarK key₀)}`, so the hypothesis **holds**, but

* LHS `= pure (prg0 (kVars key₀))` — the reduction does not know the oracle key, so it uses `kVars`;
* RHS `= pure (prg0 oracleKey)`.

These differ. The `sorry`s at lines 268 and 279 are `have hk_inner : VarK key₀ ∉ extractKeys e` with the
comment *"apply keys_not_in_seeds … or whatever your invariant lemma is"* — there is no such lemma, because
the property is not implied by the hypothesis. The same holds for `reductionToOracleSimulateEq2`
(lines 770, 778).

Since `reductionToOracleEq`/`reductionToOracleEq2` feed the unprimed lemmas, and those feed
`symbolicToSemanticIndistinguishabilityHidingOneKey` ([:1259](PRGExtension/Expression/ComputationalSemantics/SoundnessProof/HidingOneKey.lean#L1259)),
the IND-CPA half of the development is currently unsound. The same `enc'` counterexample from §4.1 breaks
`symbolicToSemanticIndistinguishabilityHidingOneKey` directly.

**Fix.** Delete the unprimed lemmas; promote `reductionToOracleSimulateEq'` and `reductionToOracleSimulateEq2'`.
Then weaken their hypothesis from `∉ keySubterms e` (too strong — it makes the theorem vacuous, since a key
used for encryption *is* in `keySubterms`) to precisely LM18's properties 2 and 3:

```lean
(H_parts : Expression.VarK key₀ ∉ extractKeys e)          -- k ⋢ e  (property 2, base case)
(H_seeds : ∀ k' ∈ exprKeys e, ¬ strictYields (.VarK key₀) k')  -- 𝖦⁺(k) ∩ Keys(e) = ∅ (property 3)
```

`H_seeds` is exactly the invariant that discharges the `G0`/`G1` branches: if `key₀` had a descendant in the
expression the branch is contradictory, otherwise `kVars key₀` is never consulted under a `G` and the two
sides agree. Both primed proofs should go through with only the `have hk_inner` steps rewritten.

### 4.3 (P0-c) The `replacePRG` machinery is at the wrong layer and too weak — retarget it, do not delete it

**STATUS: PARTLY DONE.** `symbolicEquivalence` and `idealize_PRG_soundness` removed; the 12 `sorry`s replaced by the vacuity argument under an explicit `hidingSideCondition`. `replacePRG`, `PrgSecurity.lean` and `HidingOnePrgSeed.lean` kept for §5.3; items 1, 3 and 4 of the list below are still open.

**The vacuity claim, stated precisely.** Suppose `keyRecovery` has been corrected per §4.1. Let
`k ∈ Keys(e) \ r(e)` and suppose `k` is non-atomic. If `Roots(Keys(e)) ⊆ 𝐊`, then `k ∉ Roots(Keys(e))`, so
`k ∈ 𝖦⁺(Keys(e))`: there is `k' ∈ Keys(e)` with `k' ≺ k`. That `k'` satisfies the ancestor clause of `r`, so
`𝖦*(k') ⊆ r(e)`, and `k ∈ 𝖦*(k')` — contradicting `k ∉ r(e)`. Hence every hidden key is atomic, and the
`case G0 ek` / `case G1 ek` branches at
[AdversaryView.lean:157](PRGExtension/Expression/ComputationalSemantics/SoundnessProof/AdversaryView.lean#L157)
close by contradiction. This is LM18 Lemma 3, property 1.

**But the premise `Roots(Keys(e)) ⊆ 𝐊` is a real side condition, and it is not preserved by the fixpoint.**
`hideEncrypted z expr` can bury an atomic key `K` inside a `Hidden` payload while `G0(K)` survives as an
encryption key; then `Roots(Keys(view)) = {G0(K)}`, which is not atomic. This is exactly what happens in
garbled circuits — LM18 Lemmas 6–7 describe the situation where a wire key occurs only inside a hidden
payload while its `Dup`-child is the next gate's encryption key. So the vacuity argument covers only LM18's
*first* case of Lemma 3.

**Worked example (reproducible).** [`scratch/TwoGateFixpoint.lean`](scratch/TwoGateFixpoint.lean) builds
`Garble(NAnd ⋙ Dup ⋙ NAnd, (0,0))` as a concrete `Expression` — two garbled NAnd tables plus the garbled
input — and unrolls the greatest-fixpoint iteration by hand (`greatestFixpoint` starts at `keySubterms e` and
iterates `keyRecovery e` to stabilisation, so this reproduces `adversaryKeys e` exactly). Run it with
`lake env lean scratch/TwoGateFixpoint.lean`. Wire `h` is the output of gate 1; `Dup` splits it, so gate 2
encrypts under `G0(K_h^j)` and `G1(K_h^j)`.

```
cards        |S₀|=12  |S₁|=10  |S₂|=7  |S₃|=6  |S₄|=6      -- fixpoint at S₃
adversaryKeys e            = { K_i^0, K_j^0, K_h^1, K_m^0, G0(K_h^1), G1(K_h^1) }
Keys(adversaryView e)      = { K_i^0, K_i^1, K_j^0, K_j^1, K_h^1, K_m^0,
                               G0(K_h^0), G1(K_h^0), G0(K_h^1), G1(K_h^1) }
Roots(Keys(adversaryView e)) = { K_i^0, K_i^1, K_j^0, K_j^1, K_h^1, K_m^0,
                               G0(K_h^0), G1(K_h^0) }
NON-ATOMIC ROOTS           = { G0(K_h^0), G1(K_h^0) }          ← the side condition fails
K_h^0 ∈ Keys(adversaryView e)?  false
```

The adversary decrypts the `(0,0)` row of gate 1 and learns `K_h^1`; it never learns `K_h^0`, whose only clear
occurrence is in the payload of the `(1,1)` row, which is hidden. But `G0(K_h^0)` and `G1(K_h^0)` survive as
the *encryption keys* of gate 2's hidden ciphertexts, so they remain in `Keys`. Since `K_h^0` itself has
dropped out of `Keys`, `Roots` picks up `G0(K_h^0)` — non-atomic — and `Roots(Keys(e)) ⊆ 𝐊` is false at the
fixpoint of a two-gate circuit.

Note the last line: because `K_h^0 ∉ Keys(view)`, the ancestor clause of §4.1 **cannot** fire on it. Adding
that clause does not rescue the side condition. The same file re-runs the whole iteration with the corrected
`keyRecovery'` and gets the *identical* fixpoint, the same non-atomic roots, and `K_m^1` still hidden — so the
§4.1 fix is consistent with this example and does not over-recover, but it does not remove the need for §5.3.

**The general case is LM18's second case, and it is a renaming argument.** Let
`Roots(Keys(e)) = {k₁,…,kₙ}` and let `α_K` be the pseudorandom key renaming sending `kᵢ ↦ 𝖪ᵢ` (fresh
atomics). Then

```
⟦e⟧  ≈  ⟦α_K(e)⟧          -- Lemma 2, needs PRG security
     ≈  ⟦p(α_K e, r(α_K e))⟧ -- atomic case, IND-CPA only
     =  ⟦α_K(p(e, r(e)))⟧    -- α commutes with p and r
     ≈  ⟦p(e, r(e))⟧         -- Lemma 2 again
```

Two of those four steps consume PRG security. That is where `prgSchemeSecure` actually enters the soundness
proof.

**`replacePRG` is a special case of that renaming.** `replacePRG k idx0 idx1` sends `G0(k) ↦ 𝖪_{idx0}` and
`G1(k) ↦ 𝖪_{idx1}`; on `S = {G0(k), G1(k)}` — two independent keys mapped to two fresh independent atomics —
this satisfies LM18's `𝖦`-preservation condition `𝖦^w(k₁) = k₂ ⟺ 𝖦^w(α k₁) = α k₂`. It is a correct
pseudorandom key renaming. Four things are wrong with how it is currently packaged, all repairable in place:

1. **Wrong side condition.** `targetSeed ∉ adversaryKeys e`
   ([HidingOnePrgSeed.lean:68](PRGExtension/Expression/ComputationalSemantics/SoundnessProof/HidingOnePrgSeed.lean#L68),
   and the four `by sorry`s at AdversaryView.lean:190–245) is a *semantic* condition the reduction cannot act
   on. The reduction fails exactly when it needs the bit-string value of `targetSeed`; deeper applications
   such as `G0(G0(targetSeed))` are fine, since they factor as `prg0 val0`. The right, syntactically
   checkable hypothesis is `targetSeed ∉ exprKeys e` — `targetSeed` occurs only underneath a `G`.
2. **Wrong layer.** `symbolicEquivalence`
   ([:859](PRGExtension/Expression/SymbolicIndistinguishability.lean#L859)) makes the PRG hop a constructor of
   the *symbolic* relation. That destroys the property that makes the symbolic method worth having — that
   equivalence is decided by normalising and comparing — and it is dead code besides (`Soundness.lean` still
   quantifies over `symIndistinguishable`). **This** is what should be deleted, along with
   `axiom idealize_PRG_soundness`; the hop belongs inside the soundness proof as a lemma.
3. **Depth 1 only.** Chained `Dup` gates produce roots `𝖦^w(k)` at arbitrary depth, so the single hop must be
   iterated over the PRG tree. That iteration *is* LM18 Theorem 1 (§5.3).
4. **Hard-coded fresh indices** (`let idx0 := 9998`) are a latent soundness hole; derive them from
   `getMaxVar e + 1` instead.

**What to keep from `HidingOnePrgSeed.lean`:** all of its structure. `oracleSpecPrg`,
`seededPrgRealOracle`, `seededPrgIdealOracle` (after §4.4), `prgSchemeSecure`, and the
reduction + real-world-equivalence + ideal-world-equivalence + `IndistinguishabilityByReduction` pattern are
the only way to consume a PRG assumption in this framework, and they will be needed verbatim by §5.3. What
changes is the *statement* of the top theorem (hypothesis per item 1), the *body* of `reductionToPrgOracle`
(see §4.7 item 1), and the addition of the hybrid that lifts one hop to a whole PRG tree.

### 4.4 (P1) `prgSchemeSecure` is unsatisfiable

**STATUS: FIXED.** The ideal oracle's randomness moved into its seed.

[PrgSecurity.lean:33-51](PRGExtension/Expression/ComputationalSemantics/PrgSecurity.lean#L33-L51). The real
oracle holds a seed and answers every query with the *same* deterministic pair
`(prg0 seed, prg1 seed)`; the ideal oracle samples **fresh** `(r0, r1)` on every query, because
`famSeededOracle.queryImpl` is stateless and the ideal `Seed` is `Unit`. A distinguisher that queries twice
and tests equality wins with probability `1 − 2^{-2κ}`. So `prgSchemeSecure IsPolyTime prg` is false for every
`prg`, and every theorem taking it as a hypothesis is vacuously true.

**Fix (one line):** make the ideal oracle's randomness part of its seed.

```lean
noncomputable def seededPrgIdealOracle : famSeededOracle (fun κ ↦ oracleSpecPrg κ) := {
  Seed      := fun κ => BitVector κ × BitVector κ
  seedDistr := fun κ => PMF.uniformOfFintype (BitVector κ × BitVector κ)
  queryImpl := fun _ r => { impl | .query _ _ => pure r }
}
```

Compare `seededIndCpaOracleImpl`, which is correct precisely because the left-or-right oracle *is* meant to
be re-invoked. Sanity check to add once fixed: prove `¬ prgSchemeSecure _ (fun κ => ⟨id, id⟩)` — a cheap
regression test that the definition has teeth.

### 4.5 (P0-d) `extractKeys_hideEncrypted_self` is FALSE — and so is the step that uses it

**STATUS: FIXED.** The lemma and its consumer's `H_ext_eq` are gone; the fixpoint step is
now one application of the hiding theorem with removal set `z \ keyRecovery expr z`
(restricted to `allParts`, via the new `hideSelectedRestrict`), exactly as proposed at the
end of this section.

This section originally called the lemma "the one legitimately open lemma", accepted the
in-source comment that it was "mathematically true but not provable with our current
definitions", and proposed a two-sided strengthening. All of that was wrong. Implementing
the strengthening exposed the actual problem: the statement is false.

`scratch/ExtractKeysSelfCounterexample.lean` computes the witness:

```
e    = Enc (VarK 0) (VarK 1),  keys = {VarK 0}
hideEncrypted keys e             = Enc (VarK 0) (VarK 1)
Y := extractKeys (…)             = {VarK 1}
hideEncrypted Y e                = Hidden (VarK 0)      -- because VarK 0 ∉ Y
extractKeys (hideEncrypted Y e)  = ∅
Y ⊆ ∅                            = false
```

The mechanism: `Y` collects the *payload* keys of a ciphertext but not the key that
encrypts it, so re-hiding with `Y` closes the very ciphertext the keys came from. The
proposed strengthening fails on the same example, for the same reason.

Worse, the single consumer is in the same position. In the `Ras` step of
`symbolicToSemanticIndistinguishabilityAdversaryView`, the intermediate

```lean
H_ext_eq : extractKeys RHS_view = extractKeys (hideEncrypted z expr)
```

is also false on that example — with `z = {VarK 0, VarK 1}` we get `keyRecovery expr z =
{VarK 1}`, so `Hz : keyRecovery expr z ⊆ z` is satisfied, `RHS_view = Hidden (VarK 0)`,
and `∅ = {VarK 1}` fails.

The *conclusion* of that step is nevertheless true:

```lean
hideEncrypted z expr ≈ hideEncrypted (keyRecovery expr z) expr
```

On the example this reads `⟦Enc_{k0}(k1)⟧ ≈ ⟦Enc_{k0}(1^κ)⟧`, which is exactly IND-CPA —
`k0` is not extractable. The fix is therefore to re-derive the step directly rather than
through `H_ext_eq`: apply `symbolicToSemanticIndistinguishabilityHidingInner` to
`hideEncrypted z expr` with removal set `z \ keyRecovery expr z`, whose side condition
`extractKeys (hideEncrypted z expr) ∩ (z \ keyRecovery expr z) = ∅` holds because
`extractKeys (hideEncrypted z expr) ⊆ keyRecovery expr z`, and then rewrite
`hideSelectedS (z \ K) (hideEncrypted z expr) = hideEncrypted K expr` using
`twoHideEncryptedS` and `K ⊆ z`.

Until that is done, the `sorry` stands on a statement known to be false, and it is flagged
as such in the source. Nothing else in the library depends on it.

### 4.6 (P2) Smaller items

* `symbolicToSemanticIndistinguishabilityHidingInnerMotive`
  ([AdversaryView.lean:88](PRGExtension/Expression/ComputationalSemantics/SoundnessProof/AdversaryView.lean#L88))
  still carries `_HreductionPrg`/`_HPrgSecure`; both become unused after §4.3 and should be dropped from the
  motive, which will also shorten every call site.
* `Soundness.lean` re-exports the framework theorem with `open PRG` rather than inside the namespace; harmless,
  but it means `PRG.symbolicToSemanticIndistinguishability` does not exist. Pick one convention.
* `allParts` now recurses into `G0`/`G1` ([HideEncrypted.lean:38-45](PRGExtension/Expression/Lemmas/HideEncrypted.lean#L38-L45))
  and so has become a fourth key-extraction function that nearly duplicates `keySubterms`. After §4.1, check
  whether `allParts` can simply *be* `keySubterms` and delete one of them.
* ~~`prgClosure` iterates `univKeys.card + 1` times … worth recording a lemma
  `prgStep U (prgClosure U S) = prgClosure U S`~~ — **done** (`prgStep_prgClosure`), together with the
  reflection direction `prgClosure_reflects_G0/G1` and the `adversaryKeys` corollaries.

---

### 4.7 Unspecified or unproven details in the computational model

**STATUS: items 1 and 5 fixed; 2 and 3 superseded by `PrgHopChain`; 6 and 7 partly
addressed (vocabulary added, renaming still atomic-only); 4, 8 and 9 still open.**

Beyond the three defects above, the computational side of the PRG extension has gaps that will block proofs
as soon as they are attempted. In rough order of how much they hurt:

1. **`reductionToPrgOracle` has no body.**
   [HidingOnePrgSeed.lean:18-26](PRGExtension/Expression/ComputationalSemantics/SoundnessProof/HidingOnePrgSeed.lean#L18-L26)
   queries the oracle for `(val0, val1)` and then `sorry`s — the answer is discarded. Both world-equivalence
   lemmas below it are therefore statements about a function that does not exist yet. What is needed is an
   `evalExpr` variant that evaluates `replacePRG targetSeed idx0 idx1 e` in an environment where `idx0 ↦ val0`
   and `idx1 ↦ val1`, i.e. the analogue of `subst2`
   ([Def.lean:652](PRGExtension/Expression/ComputationalSemantics/Def.lean#L652)) for two indices at once.
   Write `subst3 idx0 v0 idx1 v1 kVars` and the two lemmas should follow the shape of
   `reductionToOracleSimulateEq'` closely.
2. **Single-seed oracle, no hybrid composition.** `oracleSpecPrg κ : OracleSpec Unit` idealizes exactly one
   seed per hop. A hybrid over the `n` internal nodes of a PRG tree needs (a) an `n`-fold `indTrans` chain and
   (b) the reduction to sample the *other* seeds itself — neither is stated. Compare `oracleSpecIndCpa`, which
   is indexed by `ℕ` and so supports many queries.
3. **The hybrid's seeds are not uniform.** `prgSchemeSecure` is phrased over a `famSeededOracle` whose seed is
   *uniformly random*. In a PRG tree, the seed of an internal node is itself only pseudorandom. Bridging that
   is the whole content of LM18 Theorem 1, and nothing in the repo addresses it.
4. **The PRG is not required to be efficiently computable.** LM18 Def. 1 demands polynomial-time
   computability; `prgFunctions`
   ([Def.lean:35](PRGExtension/Expression/ComputationalSemantics/Def.lean#L35)) is an arbitrary pair of
   functions, and nothing ties it to `IsPolyTime`. Consequently `HreductionPrg` — the assumption that the PRG
   reduction is polynomial-time — has no justification at all, whereas the IND-CPA counterpart `Hreduction`
   at least has the prose analysis at the end of `HidingOneKey.lean`. That analysis was also not extended to
   the `G0`/`G1` cases of `reductionToOracle`.
5. **No purity lemma for key evaluation.** `evalExpr … (k : Expression 𝕂)` is provably a Dirac distribution
   (`VarK` is `PMF.pure`, `G0`/`G1` are `PMF.pure ∘ prgᵢ`), but this is nowhere recorded. Since `Enc k e` now
   does `let key ← evalExpr … k`
   ([Def.lean:218-224](PRGExtension/Expression/ComputationalSemantics/Def.lean#L218-L224)), every downstream
   proof has to push a monadic bind through a computation that is deterministic. Adding
   ```lean
   def keyVal (kVars : ℕ → BitVector κ) (prg : prgFunctions κ) : Expression 𝕂 → BitVector κ
   lemma evalExpr_key (k : Expression 𝕂) : evalExpr enc prg kVars bVars k = PMF.pure (keyVal kVars prg k)
   ```
   would shorten `HidingOneKey.lean` substantially and is probably the single highest
   effort-to-benefit item in this list.
6. **The independence vocabulary does not exist.** There is no `⪯`/`≺`, no `Independent`, no `Roots`, and no
   `Parts`/`⋐`. LM18 Theorem 1, Lemma 2, and properties 1–3 of Lemma 3 cannot be *stated* against the current
   library, let alone proved. Definitions are sketched in §4.1 and §5.3.
7. **Renamings cannot express what LM18 needs.** `KeyRenaming := ℕ → ℕ` with
   `validKeyRenaming := Function.Bijective`
   ([SymbolicIndistinguishability.lean:50-52](PRGExtension/Expression/SymbolicIndistinguishability.lean#L50-L52))
   captures only bijections of atomic indices, with no `𝖦`-preservation condition — so a pseudorandom key
   renaming such as `G0(K₁) ↦ K₁` is inexpressible. See §5.3.
8. **`Hidden k` evaluates to `enc.encrypt key ones`** where LM18 uses `𝖤(σ(k), 0^{|s|})`. Immaterial to
   security, but it is an unstated deviation, and `ones`'s length is fixed by unification rather than by an
   explicit `shapeLength` argument, which makes several goals harder to read than they need to be.
9. **`normalizeExpr` does not recurse into encryption keys or `Hidden`**
   ([SymbolicIndistinguishability.lean:27-44](PRGExtension/Expression/SymbolicIndistinguishability.lean#L27-L44)).
   That is harmless today (key expressions contain no bit expressions) but it is an invariant worth recording,
   since it would silently break if the language ever gained a key former that mentions bits.

## 5. What remains to be proved

Listed in dependency order. Items marked ★ are new mathematics, not present in the encryption-only framework.

### 5.1 Layer 1 — symbolic layer (no cryptography)

| Obligation | Status |
|---|---|
| `keyRecoveryMonotone` for the corrected `keyRecovery` | must be redone (§4.1) |
| `keyRecoveryContained` for the corrected `keyRecovery` | must be redone (easy) |
| `extractKeys_hideEncrypted_self` | open (§4.5) |
| `prgClosure` is idempotent / is a genuine closure | not stated |
| ★ `adversaryKeysOnlyAtomic` — under the side condition `Roots (exprKeys e) ⊆ atomics` | not stated — LM18 Lemma 3 property 1, the keystone of §4.3. Note the side condition is **not** preserved by the fixpoint; discharging it is §5.3 |
| ★ `noDescendantOfHidden : k ∉ adversaryKeys e → ∀ k' ∈ exprKeys (adversaryView e), ¬ strictYields k k'` | not stated — LM18 property 3, feeds §4.2 |
| `hideEncrypted`/`normalizeExpr`/renaming commutation for `G0`/`G1` | done |

### 5.2 Layer 2 — IND-CPA hiding (`HidingOneKey.lean`)

| Obligation | Status |
|---|---|
| `reductionToOracleSimulateEq` under the corrected hypotheses | primed version exists; hypothesis needs adjusting (§4.2) |
| `reductionToOracleSimulateEq2` ditto | same |
| `reductionToOracleEq`/`Eq2` | mechanical once the above land |
| `symbolicToSemanticIndistinguishabilityHidingOneKey` | mechanical once the above land |
| polynomial-time accounting for `reductionToOracle` over `G0`/`G1` | the prose proof at the end of the file was **not updated** for the PRG case; add the `Expression.G0/G1` cases (one `prg0` call, output length κ — trivially polynomial) so the `Hreduction` axiom stays justified |

### 5.3 ★ Layer 3 — PRG independence

**STATUS: the single-seed hop is proved, and `PrgHopChain`/`prgHopChainSound` compose hops
into a finite sequence — this is LM18 Theorem 1 (⇒) in the form the soundness proof uses.
What remains is LM18 Lemma 2 (general `𝖦`-preserving renamings), which would discharge
`hidingSideCondition`.**

> **How Lemma 2 now decomposes.** `⟦e⟧ ≈ ⟦α_K(e)⟧` for a pseudorandom key renaming `α_K`
> follows from three pieces that are now all in place or clearly delimited:
> 1. a `PrgHopChain` idealising every internal PRG node of `e`, ending in an expression
>    whose keys are all atomic (`prgHopChainSound` gives `⟦e⟧ ≈ ⟦e°⟧`);
> 2. the same for `α_K(e)`, giving `⟦α_K(e)⟧ ≈ ⟦α_K(e)°⟧`;
> 3. `e°` and `α_K(e)°` differ only by a **bijection of atomic key indices**, so
>    `applyRenamePreservesCompSem2` — which is an *exact equality* and already proved —
>    finishes it.
> The remaining work is entirely (1)/(2): constructing the chain for a given expression,
> i.e. ordering the PRG tree and discharging each hop's freshness bookkeeping. No new
> cryptographic content is needed.

This is where PRG security is actually consumed. `PrgSecurity.lean` and `HidingOnePrgSeed.lean` already
provide the *single-seed* hop that this layer is built from; what is missing is the induction that lifts one
hop to a whole PRG tree, and the independence vocabulary needed to state the result.

**Mic09 Theorem 1 (LM18 Theorem 1).** For symbolic keys `k₁,…,kₙ ∈ 𝐊*`, the following are equivalent: the
`kᵢ` are pairwise *independent* (`kᵢ ⪯ kⱼ ⟺ i = j`); and `⟦k₁,…,kₙ⟧ ≈ ⟦r₁,…,rₙ⟧` for distinct atomic `rᵢ`.

Only the (⇒) direction is needed. Its proof is a hybrid over the finite PRG-tree spanned by the `kᵢ`: order
the internal nodes by depth, and at each node replace `(G0(s), G1(s))` by a fresh independent pair, each hop
justified by one invocation of `prgSchemeSecure`. **One such hop is exactly
`symbolicToSemanticIndistinguishabilityPrgIdealization`** — so `HidingOnePrgSeed.lean` is the base case of
this theorem, not a competing approach. Completing it (§4.7 item 1) and then iterating it is the work.
Note the ordering matters: at a node whose seed is itself pseudorandom, the hop is justified by the *previous*
hop having already replaced that seed with a fresh uniform key, which is the point raised in §4.7 item 3.

Suggested Lean shape:

```lean
def yields (k k' : Expression 𝕂) : Prop            -- k ⪯ k'
def Independent (S : Finset (Expression 𝕂)) : Prop -- pairwise ¬yields
def roots (S : Finset (Expression 𝕂)) : Finset (Expression 𝕂) := S \ strictDescendants S

★ theorem independentKeysPseudorandom
  (IsPolyTime) (prg) (HPrg : prgSchemeSecure IsPolyTime prg)
  (S : Finset (Expression 𝕂)) (hS : Independent S) (freshIdx : … ) :
  CompIndistinguishabilityDistr IsPolyTime
    (famDistrLift (exprToFamDistr enc prg (tupleOf S)))
    (famDistrLift (exprToFamDistr enc prg (tupleOf (freshAtomsFor S))))
```

**Why this is unavoidable.** LM18's Lemma 3 proves the atomic case
(`Roots(Keys(e)) ⊆ 𝐊`) directly from IND-CPA, and reduces the general case to it via a pseudorandom key
renaming `α_K : Roots(Keys(e)) → 𝐊`. The general case genuinely arises for garbled circuits: at the fixpoint,
a wire key `K_h^1` occurs only inside a hidden payload while its child `G0(K_h^1)` is still used as an
encryption key, so `Roots(Keys(p(e,S))) ∋ G0(K_h^1)` is *not* atomic. Hence:

* `replacePRG` must be generalised from "the two children of one seed" to "the roots of an arbitrary finite
  key set", which is what makes it a pseudorandom key renaming in LM18's sense rather than a one-off hop;
* the Lean notion of renaming must be generalised from `KeyRenaming := ℕ → ℕ` (a bijection on atomic indices,
  [SymbolicIndistinguishability.lean:52](PRGExtension/Expression/SymbolicIndistinguishability.lean#L50)) to a
  `𝖦`-preserving map on key *expressions* (LM18: `𝖦^w(k₁) = k₂ ⟺ 𝖦^w(α_K k₁) = α_K k₂`); and
* `applyRenamePreservesCompSem2`, today an **equation** between distributions, becomes a *computational
  indistinguishability* statement (LM18 Lemma 2) that consumes `independentKeysPseudorandom`.

This is the single largest remaining piece of work, and the one that most changes the shape of the existing
proof. A pragmatic staging: keep the current exact-equality `applyRenamePreservesCompSem2` for the
index-bijection renamings (which is all the garbling proof of LM18 Theorem 5 uses — `α_K` there is explicitly
"the bijection on 𝐊" mapping `K_i^{z_i} ↦ K_i^0`), and add the general `𝖦`-preserving renaming, with its
weaker computational-indistinguishability conclusion, as a *separate* lemma used only inside Lemma 3. Keeping
the two apart matters: collapsing them would downgrade the garbling proof's exact equality into an
indistinguishability step for no reason.

### 5.4 Layer 4 — the garbling application

`Garbling/**` (3157 lines) is untouched and currently unbuildable against `PRGExtension` for a structural
reason, not a cosmetic one: in the original framework
[`Circuits.lean:27`](SymbolicGarbledCircuitsInLean/Garbling/Circuits.lean#L27) sets `labelType := bundleType ℕ`
— a wire label is a *natural number*, keys are `VarK (2n + b)`, and
[`GarblingDef.lean:80-81`](SymbolicGarbledCircuitsInLean/Garbling/GarblingDef.lean#L80-L81) implements
`Gb(Dup, x) = (ε, (x, x))`: the encryption-only scheme duplicates the wire label outright.

LM18 instead has `Gb(𝐃𝐮𝐩, (b,(k₀,k₁))) = ε, ((b, G0(k₀), G0(k₁)), (b, G1(k₀), G1(k₁)))`. So the port requires
`labelType := bundleType (Expression 𝔹 × Expression 𝕂 × Expression 𝕂)` — labels carry key *expressions*, not
indices — which ripples through `GarblingDef`, `Simulate`, `Correctness`, `Security` and all five
`SymbolicHiding/` files. Expect this to be a rewrite rather than a port. The counterpart LM18 results are
Lemmas 5–8 (strong independence of label expressions is preserved by `Gb`) and Theorems 4–5.

**STATUS: the port is done and Lemmas 4–6 and Theorem 4 are proved.** `labelType` now carries
`WireLabel = ⟨bit : ℕ, key0 key1 : Expression 𝕂⟩`, `Gb(Dup)` applies `G0`/`G1`, and
`Garbling/{Circuits,GarblingDef,Evaluation,Correctness,Freshness,Independence,Lemma5,Lemma6,GarbleKeys,GarbleFixpoint,GbStage}.lean`
build `sorry`-free.

One statement-level correction was needed beyond the port. LM18 states Lemmas 7 and 8 as "for
any sub-circuit `C'` of `C` and any label expression `u` …". Taken literally that is **false**
here, because `gb` takes the input labels `u` and the key counter `ctr` as *independent*
arguments: for arbitrary `u`/`ctr` the keys `K_{2·ctr}, K_{2·ctr+1}` that `NAnd` mints need not
be keys of `Garble C x` at all, so nothing constrains their membership in the fixpoint; and
LM18's own `Dup` case appeals to Lemma 6 *for the whole garbled circuit*, a step with no
counterpart when `u` is unrelated to `C`. The paper's prose evidently means the labels and
counter the garbling actually reaches. `Garbling/GbStage.lean` makes that explicit with
`GbStage c u ctr c' u' ctr'` ("garbling `c` from `(u, ctr)` performs the garbling of `c'` from
`(u', ctr')` as a sub-computation"), which refines `SubCircuit` and supplies the structural
facts the proofs need: `ctr_le`, `exprKeys_subset`/`extractKeys_subset` (a stage's expression
sits inside the global one, so fixpoint facts about `adversaryKeys (Garble c x)` transfer),
`hyps` (`StronglyIndependent` and `LabelsBelow` are inherited), and `labelKeys_yielded`
(Lemma 5(2) propagated by `yields_trans`). `sim_snd_eq_gb_snd` shows `Sim` threads labels and
counters exactly as `Gb` does, so one stage relation serves both Lemma 7 and Lemma 8.
Again: the defect is in the formalisation's reading, not in LM18.

**Lemmas 7 and 8 are now proved** (`Garbling/Lemma7.lean`, `Garbling/Lemma8.lean`), on top of
`Garbling/ViewKeys.lean`.  The key new fact is `atomic_recovered_garble`: *an atomic key is
recovered only by decryption*.  `keyRecovery` has two sources — `extractKeys` of the view and
Definition 3's ancestor clause — and the PRG closure on top adds only derived keys; the
ancestor clause can only fire on a key occurring in the view, which is either already in
`extractKeys` or is an *encryption* key, and LM18 Lemma 6 forbids a strict descendant of an
encryption key from occurring.  Paired with `GbStage.view_extract_iso` (a key whose index
lies in a stage's counter range was read out of that stage and nowhere else — the counter
ranges of `Compose`'s two halves split at an even endpoint, so a `{2n, 2n+1}` pair never
straddles them), this makes the `NAnd` case of Lemma 7 a local argument: exactly one of the
four rows decrypts, revealing exactly one of the gate's two fresh keys, and the other cannot
be in the fixpoint because nothing else in the circuit could have supplied it.

One statement change was forced: `LabelInvariantIn`'s guard is now `l.key0 ∈ U ∧ l.key1 ∈ U`
rather than a disjunction.  With a disjunction the `Dup` case is unprovable — from
`G0 k¹ ∈ U` alone one cannot place `G0 k⁰` in `U`, which `adversaryKeys_G0_closed` requires
— and a conjunction loses nothing, since wherever a label is actually used both of its keys
occur.

Lemma 8 needed no separate Lemma 6 proof: `encKeys_sim_eq_gb` and `exprKeys_sim_subset_gb`
show `Sim` uses the same encryption keys as `Gb` and a subset of its key set, so Lemma 6
transports to the simulator directly.

**Theorem 5 is now proved** (`Garbling/Theorem5.lean`, on `Garbling/ValueInvariant.lean` and
`Garbling/Alignment.lean`).  The renaming that witnesses it is `makeVarRenaming f`, with
`f i` the value carried by the wire whose label has bit index `i`: its key half sends each
label's active key to that label's key `0`, and its bit half moves each garbled table's
decryptable row to position `(0,0)`.  At a `NAnd` gate the two cancel exactly — the row
`(v_i,v_j)` carries `(¬B_h, K_h¹)` and the output value is `1` (so `f` flips `h`, giving
`¬¬B_h ↝ B_h` and `K_h¹ ↦ K_h⁰`), or it carries `(B_h, K_h⁰)` and the output value is `0` (so
`f` fixes `h`).  Either way the result is `(B_h, K_h⁰)`, which is what `Sim` writes in all
four rows.

Two supporting refinements were needed.  `LabelValueIn`/`LabelZeroIn` sharpen Lemmas 7 and 8
from "exactly one key of the pair is recovered" to *which* one — the value's key for the
garbling, always key `0` for the simulation.  And `AgreesOn` states structurally that `f`
records the right value at each gate, so the main induction splits along `Compose` with no
freshness reasoning; freshness is confined to `agreesOn_valueMap`.

**Nothing remains.**  `FixpointStepSound` is proved (`SoundnessProof/FixpointStep.lean`), so
`symbolicToSemanticSoundness` carries no side conditions and `garblingSecure`
(`Garbling/Security.lean`) gives computational simulation security of the PRG-based garbling
scheme from IND-CPA security of the encryption scheme plus PRG security.

The last gap was LM18 Lemma 3's general case.  `hideOneKeyGen`
(`SoundnessProof/HidingOneKeyGen.lean`) hides a *non-atomic* key by idealising the PRG node
at the bottom of its chain (`replacePRG`), hiding the shortened key by induction on
`keySize`, and undoing the hop — which works because idealisation commutes with hiding
(`rp_hideSelected`) and never creates an ancestor relation (`strictYields_rp_reflect`), both
in `Expression/Lemmas/ReplacePRG.lean`.  `fixpointStepSound` then reads the two hypotheses
off the fixpoint: a key the step hides has neither a strict ancestor nor a strict descendant
occurring in the view, since either would place it in the recovery set.  One adjustment was
needed — the hidden set is restricted to `encKeys(v)` rather than `allParts(v)`, which
changes nothing (`hideSelectedRestrictEnc`) but is what makes `k ∈ exprKeys(v)` available.

All of LM18 Lemmas 2–8 and Theorems 1, 4 and 5 are proved.

---

## 6. Recommended order of work

> Steps 1–9 were carried out on 2026-09-16 (see [`CHANGELOG.md`](CHANGELOG.md)); step 7
> revealed §4.5 to be a false statement rather than an open one, and was resolved by
> re-deriving the fixpoint step instead. The library is `sorry`-free. **Remaining: step 10
> (LM18 Lemma 2 — see the box in §5.3 for how it now decomposes) and step 11 (Garbling).**

1. **Fix `prgSchemeSecure`** (§4.4). Ten minutes, and it stops you from proving vacuous theorems.
2. **Add `exprKeys`/`strictYields`, correct `keyRecovery`** (§4.1), re-prove `keyRecoveryMonotone` and
   `keyRecoveryContained`. Everything else depends on this.
3. **Prove `adversaryKeysOnlyAtomic`** (LM18 Lemma 3 property 1) and the no-descendant invariant
   (property 3). *Done only in the weak sense:* both are now stated as the explicit
   `hidingSideCondition` and consumed; deriving them from `Roots(Keys(·)) ⊆ 𝐊` is step 10.
4. **Delete `symbolicEquivalence` and `axiom idealize_PRG_soundness`** (wrong layer, both dead code), and the
   superseded `…AdversaryView'`. Keep `replacePRG`, `PrgSecurity.lean` and `HidingOnePrgSeed.lean`.
5. **Add the atomic-roots side condition** to `symbolicToSemanticIndistinguishabilityHidingInner` and close
   its `G0`/`G1` branches by contradiction using step 3. *This removes the 12 `sorry`s in `AdversaryView.lean`.*
6. **Promote the primed reduction lemmas** with the corrected hypotheses (§4.2); delete the unprimed ones.
   *Removes 4 more.*
7. ~~**Close `extractKeys_hideEncrypted_self`** (§4.5)~~ — **it is false**; instead re-derive the
   `Ras` step of the fixpoint argument without `H_ext_eq`, as described in §4.5. Do this first.
8. Add `keyVal` and `evalExpr_key` (§4.7 item 5) before touching `HidingOnePrgSeed.lean` — it will make
   step 9 markedly easier.
9. **Complete `reductionToPrgOracle`** (§4.7 item 1) with the corrected `∉ exprKeys` hypothesis, and prove its
   two world-equivalence lemmas. *Removes the last 4 `sorry`s.* At this point `Soundness.lean` is
   `sorry`-free, but conditional on the atomic-roots side condition from step 5.
10. **Formalise `independentKeysPseudorandom`** (§5.3) by iterating step 9 over the PRG tree, then the general
    `𝖦`-preserving renaming and LM18 Lemma 2; discharge the side condition from step 5. This is the real PRG
    content of the extension.
11. **Then** port `Garbling/` (§5.4).

Steps 1–9 are, I think, reachable and make the library `sorry`-free; step 10 is a project in itself; step 11 is another.

---

## 7. Refactoring: one framework, two instantiations

The two libraries are today 90 % copy-paste. Three files (`Core/CardinalityLemmas.lean`,
`ComputationalIndistinguishability/Def.lean`, `ComputationalIndistinguishability/Lemmas.lean`) differ **only**
in import paths, and `Renamings.lean`, `NormalizeIdempotent.lean`, `Lemmas/Renaming.lean` differ only by a
namespace line. The divergence is real in exactly four places: `Expression`, `evalExpr`, `keyRecovery`, and
the hiding reduction.

### 7.1 Immediate, zero-risk step

Move the genuinely shared material into a third library, `Common`:

```
lean_lib «Common»      -- VCVio2 re-exports, Core/, ComputationalIndistinguishability/
lean_lib «SymbolicGarbledCircuitsInLean»
lean_lib «PRGExtension»
```

That removes ~500 duplicated lines today and stops the two copies drifting further apart (they already have:
`Core/Fixpoints.lean` is genuinely different, which is fine, but the `apply`→`exact` fixes in `Renamings.lean`
exist only in one copy).

### 7.2 The real refactor: parameterise the key algebra

The author's own note in `ideas.txt` ("parameterized AST approach … `CustomOp : Op s → Expression Op s`") is
the right instinct; here is a version specialised to what actually varies. **Only the key layer differs
between the two schemes** — bits, pairs, `Perm`, `Enc`, `Hidden` and `Eps` are identical. So parameterise by a
type of unary key operations:

```lean
inductive Expression (Op : Type) : Shape → Type
  | BitE   : BitExpr → Expression Op 𝔹
  | VarK   : Nat → Expression Op 𝕂
  | KeyOp  : Op → Expression Op 𝕂 → Expression Op 𝕂      -- ← the only new constructor
  | Pair   : Expression Op s₁ → Expression Op s₂ → Expression Op (PairS s₁ s₂)
  | Perm   : Expression Op 𝔹 → Expression Op s → Expression Op s → Expression Op (PairS s s)
  | Enc    : Expression Op 𝕂 → Expression Op s → Expression Op (EncS s)
  | Hidden : Expression Op 𝕂 → Expression Op (EncS s)
  | Eps    : Expression Op EmptyS
```

* **Encryption-only instantiation:** `Op := Empty`. The `KeyOp` constructor is uninhabited, every `match` on
  it closes with `exact absurd op (by cases op)` or `nomatch`, `Expression Empty 𝕂` is isomorphic to `ℕ`, and
  `keySubterms`/`prgClosure` collapse to the identity — recovering the original framework's definitions up to
  propositional equality.
* **PRG instantiation:** `Op := Bool`, with `G0 k := KeyOp false k`, `G1 k := KeyOp true k`. Notation
  abbreviations keep the source readable.

The interpretation side is parameterised the same way:

```lean
structure keyOpFunctions (Op : Type) (κ : ℕ) where
  apply : Op → BitVector κ → BitVector κ
def keyOpScheme (Op) : Type := (κ : ℕ) → keyOpFunctions Op κ
```

`evalExpr` gains a single uniform clause `| .KeyOp o e => (ops.apply o) <$> evalExpr … e`. For `Op = Empty`
the whole `prgScheme` argument is a unit-like parameter that can be defaulted.

The security side is parameterised by a **typeclass of assumptions**, which is what makes the two
instantiations share a soundness proof:

```lean
class KeyAlgebra (Op : Type) where
  derived        : Op → Expression Op 𝕂 → Expression Op 𝕂 := .KeyOp
  /-- the finite set of key expressions the closure may reach -/
  universe       : ∀ {s}, Expression Op s → Finset (Expression Op 𝕂)
  /-- LM18 Thm 1(⇒): symbolically independent keys are computationally pseudorandom. -/
  independentPseudorandom : …
```

For `Op = Empty`, `independentPseudorandom` is *trivial* — distinct atomic keys are literally i.i.d. uniform,
so it is `indRfl` — and the generic soundness proof degenerates to the original one with no PRG hypothesis
anywhere. For `Op = Bool` it is discharged from `prgSchemeSecure` by the hybrid of §5.3. That single
typeclass field is precisely the difference between the two developments.

### 7.3 Cost/benefit

Honest assessment: doing §7.2 *now*, before the soundness proof is correct, is a bad trade — you would be
refactoring a proof that is broken. Doing it *never* means maintaining two copies of a 4000-line development
forever. The sequencing I would suggest:

* do §7.1 (shared `Common` lib) immediately — it is pure win;
* finish steps 1–7 of §6 in `PRGExtension` as a standalone library;
* then do §7.2 as a deliberate refactor, using the now-correct PRG development as the general case and
  re-deriving the encryption-only library as `Op := Empty`. The dependent-type pain (`Expression Op s` in
  place of `Expression s` everywhere, and `Op`-generic `DecidableEq`) is real but mechanical, and the payoff
  is that `Garbling/` gets written once, parameterised over the `Dup` gate's behaviour.

One warning for §7.2: `deriving DecidableEq` on a parameterised inductive needs `[DecidableEq Op]` and,
because of the `Shape`-indexing, still requires the hand-rolled `ExpressionInclusion`-style machinery that
already exists. Budget for that rather than assuming `deriving` will cope.

---

## 8. File-by-file verdict

| File | Verdict |
|---|---|
| `Expression/Defs.lean` | ✅ correct, matches LM18 §2.1 |
| `Expression/ComputationalSemantics/Def.lean` | ✅ correct; `keyVal`, `subst3` and the two-index resampling chain added |
| `Expression/ComputationalSemantics/{Normalize,Rename}Preserves.lean` | ✅ complete; `Rename` needs generalising later (§5.3) |
| `Core/Fixpoints.lean` | ✅ good generalisation |
| `Expression/Lemmas/HideEncrypted.lean` | ✅ mostly; `allParts` likely redundant with `keySubterms` |
| `Expression/SymbolicIndistinguishability.lean` | ✅ `keyRecovery` corrected; `symbolicEquivalence` and the false `extractKeys_hideEncrypted_self` removed; `seedFree` and the LM18 independence vocabulary (`yields`, `IndependentKeys`, `rootsOf`, …) added |
| `Expression/ComputationalSemantics/PrgSecurity.lean` | ✅ ideal oracle fixed, axiom removed, definitions kept |
| `.../SoundnessProof/HidingOneKey.lean` | ✅ `sorry`-free; `seedFree` hypothesis added, `'` variants promoted |
| `.../SoundnessProof/HidingOnePrgSeed.lean` | ✅ reduction implemented, both world lemmas and the hop proved; `PrgHopChain`/`prgHopChainSound` added |
| `.../SoundnessProof/AdversaryView.lean` | ✅ `sorry`-free; game hops replaced by the vacuity argument under `hidingSideCondition`; `'` copy deleted |
| `.../Soundness.lean` | ✅ `sorry`-free; carries `Hatomic1`/`Hatomic2`, which §5.3 would discharge |
| `Garbling/**` | ❌ not started (§5.4) |
