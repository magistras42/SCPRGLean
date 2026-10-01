# Changelog

All notable changes to the proofs and code in this repository.
Section numbers in brackets refer to [`PRGExtension-Analysis.md`](PRGExtension-Analysis.md).

## [2026-10-01l] — Review item R2: domain separation between the cipher and the PRG

`PRGExtension/Crypto/DomainSeparation.lean`, 7 theorems, `sorry`-free, within the three standard
axioms (the separation facts need only `propext`).

**The gap.**  The ledger presents `encryptionSchemeIndCpa A enc` and `prgSchemeSecure A prg` as
hypotheses about separate objects, but the development proves they are not separate in the only
instantiation it offers.  `chacha20Prg_eq` identifies the PRG with the cipher's keystream
generator, and `keystream_zeroNonce` shows that at nonce zero that keystream *is* `prg0 k ‖ prg1 k`.
Since `chacha20Enc.randLen = 96 = nonceLen`, the cipher's coins ranged over **all** nonces — the
PRG's among them, at `2⁻⁹⁶` per encryption.  Nothing was unsound (each hop reduces to one game and
the hybrid chains transitively) but a reader wanting to believe the two assumptions jointly had to
supply a domain-separation argument that was not in the development.

**The fix.**  Reserve one nonce bit.  `dsNonce tag r` tags a body with a reserved bit; encryption
draws `ν` bits and runs at `dsNonce false r`, the generator runs at `dsPrgNonce ν = dsNonce true 0`.
`dsNonceDisjoint : dsNonce false r ≠ dsPrgNonce ν` is then a theorem, with
`dsPrgNonce_not_mem_range` as the coin-space form.  That is exactly the hypothesis a PRF-based
reduction needs — the two uses query the underlying function at **disjoint inputs** — and it is an
equality-level fact rather than a new assumption.

`dsExecEnc` / `dsEnc` / `dsPrg` are the generic constructions, taking the generator as a bare
function so `nonceLen = ν + 1` holds *by definition* and nothing needs a cast; `decrypt_encrypt`
comes from `prfXor_prfXor` exactly as for `prfExecEnc`, using nothing about the generator or the
separation.  `chacha20EncDS` and `chacha20PrgDS` instantiate at `ν = 95` — still RFC 8439 counter
mode, with the nonce space halved.

**Scope, stated honestly in the file.**  This does *not* prove the keystreams differ; two distinct
nonces could give the same keystream, and ruling that out is PRF security itself. The result is
separation at the query points, which is what the reduction consumes.

**Nothing is replaced.**  `chacha20Enc`, `chacha20Prg` and every theorem about them are untouched
and the extracted binary still runs on them.  `oldNonceSpacesOverlap` records the original gap as
a one-line `rfl` witness so it cannot be quietly forgotten.  Two costs are recorded in the file:
the coin space halves (`2⁹⁶ → 2⁹⁵`, one bit on the birthday term), and `chacha20Enc_eq` has no
analogue for the separated cipher, since its `randLen` and `nonceLen` differ.

## [2026-10-01k] — Review item R5b: the ChaCha20 known-answer suite, 2 vectors to 11

Two known-answer tests cannot catch an error conditional on a particular counter or key pattern.
`scratch/checks/ChaCha20Kat.lean` now carries **eleven** vectors and **four** cross-checks, chosen
so each can fail independently: the all-zero input and its complement (all-ones key *and* nonce);
RFC 8439 §2.4.2's published block; counters `255`, `256` and `2³² − 1`, testing the carry out of
the low counter byte and the top of the range; `80 00 … 00` as a key and again as a nonce, pinning
the bit *and* byte order of `keyWords` and `nonceWords`; a 100-byte stream, not a block multiple,
exercising the tail truncation; and a 320-byte five-block stream.

Counters 255 and above go through `block` at an explicit counter — the only route there without
generating gigabytes of keystream.  The four cross-checks are properties, not vectors, and tie the
two routes together: `keystream`'s first two blocks are `block` at counters 0 and 1, truncation is
a prefix, and the PRG's halves are the halves of one block.  Vector C's value also appears as
vector B's second block, which cross-checks the `block` and `keystream` paths against each other.

All generated with OpenSSL 3.0.13.  The suite prints `11`, `[]`, and five `true`s.  A hex parser
(`bytesOfHex`) replaced the hand-written byte lists, and the file now states plainly that this is
testing and stays so until an independent RFC specification exists in Lean.

The standing axiom check went from 73 to **80** `#print axioms` entries, covering the seven new
domain-separation results; all counts in `writeup.md` updated.

## [2026-10-01j] — Review item R5a: the trusted base, characterised (`writeup.md` §8.5)

`garbleExecCorrect` is a theorem about code that runs, so the review asked what has to be trusted
for the *binary* to inherit it.  New §8.5 answers in four parts: the kernel and the three axioms
(pinned by `AxiomCheck.lean`, toolchain `v4.20.0-rc5`); **Lean's code generator, unverified and on
the critical path** — no theorem connects the Lean term to the emitted C, which is the largest gap
between "proved" and "what ran", and is the standard limit of Lean extraction rather than anything
specific here; the link script, whose "no Mathlib runs" claim is established by symbol inspection
rather than by proof; and the ChaCha20 transcription, tested at eleven points.

The ordering is stated plainly: the cryptographic content is proved, the mode is proved, the
transcription is tested, the path from term to binary is trusted.  The section closes by scoping
what would close the last item — an independent RFC 8439 specification written from the document
rather than from this code, over a different representation so a shared misreading cannot survive
both, plus `block_eq_spec`, at roughly 300 lines.

## [2026-10-01i] — Review item R4: what the symbolic route cost (`writeup.md` §23)

The implicit thesis of a computational-soundness framework is that a symbolic layer costs less
than direct game hopping.  New §23 tests it with measured line counts, and the numbers do not
flatter the symbolic route.

**41% of the development — 7,649 of 18,529 lines — is machinery a direct proof would not need at
all**: the expression algebra (4,007) and the soundness bridge (3,642).  A further 3,429 lines
(`Garbling/SymbolicHiding/`) are the garbling-specific symbolic argument, which a direct proof
would replace with a hybrid rather than eliminate.

What was bought is real and is one thing: that 3,429-line argument is **entirely free of
probability** — `grep` for `PMF`, `Distr`, `negl`, `advantage` across the symbolic layer returns
zero — so the hard part of the garbling proof is pure syntax and the probabilistic content is
confined to a bridge proved once.  But the saving amortises over protocols that reuse the bridge,
and **there is one protocol**: at n = 1 the symbolic route lost, and it can only win at n ≥ 2,
which the missing congruence property (§11) and the narrow `symIndistinguishable` (§20, §22.2) both
obstruct.  §23.4 positions the work against Almeida et al.'s verified SFE stack (CCS 2017), which
is ahead on oblivious transfer, the 2PC protocol, verified compilation and the adversary model,
and behind only on the symbolic treatment itself.

The claim §23 ends up supporting is narrower than "symbolic methods reduce effort": that the
probabilistic content of a garbling proof can be confined to a reusable bridge.  A second protocol
is now the most valuable next step for the framework claim.

## [2026-10-01h] — `summary.tex`: a general overview for cryptographers

A new top-level document, written for the same audience as `writeup.tex` but at a higher level and
in roughly a third of the space (9 pages).  Ten sections: what is proved, the symbolic model,
computational soundness and its two forced game hops, the garbling scheme and the two refinements
down to running code, the ChaCha20 instantiation and the two additive single-primitive routes, the
assumption ledger, the defects found in the inherited development, what is not proved, conformance
with LM18 including the paper's errata and the SymGC measurements, and how to re-verify.

Typeset rather than wrapped: the results table and the assumption ledger are `tabularx`, the
expression constructors a two-column `tabular`, and the notation is set properly — `⟦e₁⟧ ≈ ⟦e₂⟧`,
`κ`, display math for Definition 3's ancestor clause and for `Gb(Dup, ·)`.

**It compiles under any engine.**  Unlike `writeup.tex` this file loads no `fontspec` and contains
**zero non-ASCII bytes** — every symbol is a LaTeX command — so there is no font to mis-cover and
no project Compiler setting to change.  Verified at 9 pages with 0 errors, 0 missing-character
warnings, 0 overfull boxes and 0 undefined references under **pdfLaTeX, LuaLaTeX and XeLaTeX**
alike.  `iftex` loads `fontenc`/`inputenc` only under pdfTeX.

Every theorem name and figure it cites was checked against the library: all seventeen names
resolve in `PRGExtension/`, the garbled-circuit bit range is 2054–5903, and the SymGC figure (the
paper's own `andCircuit` losing five of its eight open ciphertexts) matches `writeup.md` §22.5.

A plain-text draft (`summary.txt`) preceded this file and was dropped; the `.tex` is the only
general overview.  **Note on naming:** `summary.md` is a *different* document — it classifies the
deviations from the pen-and-paper proofs into disclosures, repairs and gaps — and the two are
cross-referenced so the proximity does not mislead.

## [2026-10-01f] — `writeup.tex`: astral-plane characters moved out of the preamble

`\newunicodechar{𝐄}` failed with *"The first argument to `\newunicodechar` is either too long
or an invalid sequence of bytes"* on Overleaf's TeX Live.  Nine characters in the file are
outside the BMP — `𝐄 𝐏 𝐚 𝐩 𝐭 𝐱 𝔹 𝕂 𝖤` (U+1D404, U+1D40F, U+1D41A, U+1D429, U+1D42D, U+1D431,
U+1D539, U+1D542, U+1D5A4) — and `\newunicodechar` will not take an astral-plane argument there.

All nine occur only in prose, never inside a code block, so the fix is at the source level: an
`ASTRAL` substitution table in the converter maps each to its LaTeX equivalent
(`\ensuremath{\mathbf{E}}` and so on), applied in both the prose and the code paths, and they
are removed from the preamble's `newunicodechar` and `listings` `literate` tables.  73 mappings
remain.  A general `COMBINING` rule was added alongside it for U+0303 and friends, which
`Keys(C̃)` in §22.3 needs and which no font or `newunicodechar` entry can fix.

Verified: 0 astral characters anywhere in `writeup.tex`, 0 unmapped non-ASCII in the body, and
both LuaLaTeX and XeLaTeX build at 23 pages with 0 errors and 0 missing-character warnings.

## [2026-10-01e] — `writeup.tex`: glyphs no longer depend on the installed fonts

Several symbols rendered as `?` on Overleaf while building cleanly here.  **The cause was a
testing error on my side.**  On this machine TeX Live's `gnu-freefont` directory is a set of
symlinks into Debian's `fonts-freefont-otf` package, so every glyph-coverage check I ran
validated against a FreeFont build that Overleaf does not ship.  `kpsewhich` reported the TeX
Live path and I took that at face value; the file is 55 bytes.

* **Every non-ASCII character now comes from a LaTeX command, not from a font.**  82 mappings,
  applied twice because the two contexts need different mechanisms: `\newunicodechar` for prose
  and inline `\code{...}`, and `listings`' `literate` table for displayed code blocks, where
  catcode changes put verbatim text out of `\newunicodechar`'s reach.
* **Code blocks moved from `fancyvrb` to `listings`** for that reason.  `columns=fixed` with one
  cell per literate entry preserves the ASCII diagrams, which were laid out by counting
  codepoints.  Box-drawing glyphs come from `pmboxdraw`; `stmaryrd` supplies `\llbracket` and
  friends.  A side benefit: the `─` runs in the §21 chain diagram now actually join, which they
  did not when they were font glyphs.
* **Verified by swapping the font out.**  Rebuilt with Latin Modern, which lacks 64 of the 83
  characters: 0 errors, 0 missing-character warnings.  The document no longer cares which
  FreeFont build is installed.  Also checked under XeLaTeX: 23 pages, clean.
* FreeFont is still the text font and LuaLaTeX still the engine, so the page looks as before.
* **Follow-up: the combining tilde.**  `Keys(C̃)` in §22.3 is `C` followed by U+0303, and that
  one cannot be fixed by any font or `\newunicodechar` mapping — a combining mark has to be
  attached to the preceding character, so it needs `\~{C}`.  The converter now rewrites
  base+mark sequences into the LaTeX accent command, on both the prose and the inline-code
  paths (the first attempt missed inline code, where this instance actually lives).  The
  check that caught it is worth keeping: compare the set of non-ASCII characters in the
  generated `.tex` body against the set the preamble maps, and require the difference to be
  empty.  `Missing character` warnings do **not** catch this case.

## [2026-10-01d] — SymGC vendored at `scratch/findings/symgc/`

The build behind §22.5 moved out of a session scratch directory and into the repository, so the
measurement is reproducible rather than reported.

* **`scratch/findings/symgc/`** — `Circuit.hs`, `Expr.hs`, `Garble.hs`, `Proof.hs`, `Check.hs`
  vendored from LM18's artifact (`github.com/b5li/SymGC`), plus `Det.hs` (the comparison driver,
  ours), `build.sh` and `README.md`.  `bash scratch/findings/symgc/build.sh` installs the three
  Hackage dependencies into a local package environment, compiles, and prints the table in §22.5.
* **Provenance is flagged, not assumed.**  The five vendored files are not ours and their licence
  has not been checked; `README.md` says so and says to check it before redistributing.
* **Four adaptations, all documented in `README.md`**: a `MonadFail WireM` instance (GHC ≥ 8.6
  desugars the failable pattern in `getInputRenamings` through it, and that pattern cannot fail);
  `return` dropped from `instance Monad WireM` (GHC ≥ 9.0 removed it from the class, and the
  inherited `return = pure` is the same function); `FlexibleInstances` added to `Proof.hs`; and
  two `Show` instances restored from mojibake to `"ε"` / `"◦"`.  None touches a definition the
  comparison depends on, and the output is unchanged by the restorations.
* **`.gitignore`** gained `*.hi`, `*.o`, `.ghc.environment.*` and the `det` binary.
* Indexes updated: `writeup.md` §22.5 now gives the build command, and `report.md` /
  `CHECKPOINT.md` list `findings/symgc/` alongside the other machine-checked refutations.

## [2026-10-01c] — The SymGC Haskell artifact built and run; `writeup.md` §22.5

LM18's companion implementation (`github.com/b5li/SymGC`) was compiled under GHC 9.6.7 and
exercised.  One adaptation, touching no logic: a `MonadFail WireM` instance, which GHC ≥ 8.6
requires for the failable pattern in `getInputRenamings`.

**The scheme is faithful.**  `gbTable`/`simTable` match LM18 p. 15 / p. 18 row for row;
`gb`/`sim` at `DUP`, `ginput`/`gmask`/`simInput`/`simMask`, `getWireLabel`'s key indexing
(identical to `makeLabels`), `unmask`, the renamings, and the `garble`/`gbRenamings` counter
alignment all agree.  `gEv` at `UNASSOC` is correct in the code where the paper's prose is not.

**Two defects, both in the pattern machinery.**  `normalizePerm` carries the §22.4 swap — so §6's
listing describes the code accurately rather than being a transcription slip — but it never
executes, since a `Perm` control is always `VarB i` or `Not (VarB i)`.  More seriously,
`pr`/`recoveryKeys` compute Definition 3's inner set and **never apply `G*`** (the code comment
concedes it), so a ciphertext under a derived key is hidden even when its root is recoverable.

Measured open/hole counts in `Pattern(Garble)`, SymGC versus the same code with `G*` restored:
`notC = CAT DUP NAND` 0/4 vs 3/3; `CAT NAND DUP` 3/3 vs 3/3; `andCircuit` 3/15 vs 8/14;
`c_example` 0/4 vs 3/3.  Whenever a `NAnd` consumes a `Dup` output the whole table becomes holes.
`prop_garble` passes under both — the property is true, but as shipped it is checked on patterns
that are entirely holes exactly where the PRG does its work, so Theorem 5's payload comparison
never happens there.

Note the symmetry with §10: the defect repaired in this development was the mirror image — the
ancestor clause missing while `G*` was present.  Both shrink the recovered key set, both hide
more, and both therefore make a positive-only equivalence test *more* likely to pass.

Recorded as `writeup.md` §22.5, kept separate from §22.4 (errata in the paper) because this is a
claim about the artifact.  Also noted there: non-termination in `Eq (Exp s)`'s catch-all for
`Pair` vs `Perm`, a missing catch-all in `Eq (Pat s)`, `renameBit` at `PPerm` bypassing
`applyBitRenaming`, `finalRecoverableKeys` terminating on cardinality rather than set equality,
and `genUniformCircuit` being a critical branching process with infinite expected size.

## [2026-10-01b] — Conformance re-checked against the actual LM18 paper

The paper (ePrint 2018/141) was read directly against the *implementation* rather than against
the docs.  No proof or definition changed; this entry records what the check found.

### Verified exact

`Expression` against the `Exp`/`Pat` grammar of §2.1, including `Perm`'s same-shape restriction
and the `Pat(𝔹)=Exp(𝔹)` / `Pat(𝕂)=Exp(𝕂)` coincidence; `exprKeys` = `Keys` and `extractKeys` =
`{k ∈ Keys(e) ∣ k ⋐ e}` against Fig. 2, including the two details most likely to drift (the
encryption key of `⦃e⦄_k` is *not* a `Part`; `Keys(k)` returns the whole `G`-chain, not its
seeds); `hideEncrypted` = `p` against Fig. 1; `keyRecovery` = `F_e(S) = r(p(e,S))` against
**Definition 3**, with `strictYields k k'` implementing `k ≺ k'` in the right direction;
`normalizeB` / `normalizeExpr` against the six rules of `≡`; `evalExpr`'s `Perm` against p. 7;
`gbEntry` + `gb`'s `NAnd` against p. 15 (four rows, `(¬B_h,K¹_h)` except at `(1,1)`, outer `π`
keyed by the first wire); `sim`'s `NAnd` against p. 18; `makeLabels`/`gEnc`/`gMask`/`sEnc`/
`sMask`/`Garble`/`Simulate`; `gEv` and `decode`; `validBitRenaming` against the α′_B bijection
condition.

### Found — the Lean takes the right branch where the paper contradicts itself

Recorded as `writeup.md` §22.4.  §6's Haskell `norm` swaps the two `Bit` cases of `π` relative to
§2.1's `≡` and the semantics on p. 7; **this one is load-bearing**, since normalisation is how `≡`
is decided, and the §6 convention would make `normalizeExpr` fail to preserve the denotation.
p. 16's `GEv(Unassoc, …)` repeats `Assoc`'s clause, contradicting Definition 4.  p. 15 writes
`Gb(Dup,·)`'s output labels as triples where `Sim`'s identical clause on p. 18 has the inner
parentheses.  The Lean follows §2.1, Definition 4, and the label shape respectively.

### Found — one undocumented deviation, conservative

`symIndistinguishable` quantifies over `validVarRenaming`, a bijection `ℕ → ℕ` on atomic key
indices.  LM18's `≈` quantifies over a pseudorandom key renaming, which by [Mic09, Lemma 2] is a
bijection between arbitrary *independent* sets and need not land on atomic keys — `K₁ ↦ G₀(K₂)`
is legal in the paper and inexpressible here.  So `symIndistinguishable` is a strictly smaller
relation: `theorem5` is **stronger** than LM18 Theorem 5, `symbolicToSemanticSoundness` is **less
general** than LM18 Theorem 3, and `garblingSecure` is unaffected.  The full class already exists
as `PrgRenameRel` (generators proved exhaustive by `prgRenameRel_substKeys_general`); widening
`symIndistinguishable` to it is scoped in `FUTURE-WORK.md`.

Also recorded: `keyRecovery` closes its argument under the PRG before hiding, which
`F_e(S) = r(p(e,S))` does not — a no-op at every fixpoint, since `keyRecovery` always returns a
`G`-closed set.

Documentation touched: `writeup.md` §20, §22.2, new §22.4; `summary.md` Part 1(a);
`FUTURE-WORK.md`; regenerated `writeup.tex`.

## [2026-10-01a] — The primitive behind the cipher: `prfFunctions`, GGM, and one-primitive identification

Additive.  Two new modules, no existing statement touched, no assumption added; `lake build`
clean at 2381 modules.  The two-primitive theorems (`garblingSecure` and relatives) remain the
general form — they take `enc` and `prg` as independent parameters and hold for any IND-CPA
scheme, including ones with no PRG inside.

### Added — `Crypto/StreamCipher.lean`

* **`prfFunctions`** — a keyed keystream generator: key, nonce, length.  Strictly more than
  `prgFunctions`, and the strengthening is forced: a cipher built from a length-doubling PRG
  alone is deterministic, hence not IND-CPA.  The nonce is the per-message randomness.
* **`prfExecEnc`** / **`prfEnc`** — nonce-prefixed counter mode, as an `ExecEnc` (so computable,
  and `ExecEnc.spec` makes `encrypt` the push-forward of the uniform distribution on nonces,
  which is the law the distributional refinement needs).  `decrypt_encrypt` comes free from
  **`prfXor_prfXor`**, which uses nothing about the generator — correctness is a property of the
  mode, exactly as for `xorStream_xorStream`.
* **`chacha20Enc_eq`**, **`chacha20Enc_spec_eq`** — both by `rfl`.  The cipher the development
  runs and extracts to C *is* the generic construction applied to ChaCha20's keystream, not a
  lookalike.  So a reduction proved about `prfEnc prf` will land on `chacha20Enc` itself.
* **`prgOfPrf`**, **`chacha20Prg_eq`** — the length-doubling PRG is the keystream generator at
  nonce zero.  This answers, as a theorem rather than a reading, whether the development is still
  PRG-based: the binary contains **one** block function, and the PRF interface adds not a second
  primitive but more access to the same one.

### Added — `Crypto/Ggm.lean`

* **`ggm`** — the GGM tree.  `prg0`/`prg1` are exactly the two child functions, which is very
  likely why LM18 specifies a length-doubling generator rather than a PRF.  **`ggm_append`**: the
  tree is the action of the free monoid on paths.
* **`ggmPrf`**, **`ggmEnc`**, **`ggmEncScheme`** — counter mode over the tree, giving a
  `prfFunctions`, and hence an `encryptionScheme`, from a `prgScheme` **alone**.  This is the
  object a single-assumption mode would be stated over.
* Construction only.  GGM's security is future work, and cannot yet be *stated*: see below.

### Not added — and why

The PRF security game.  Its ideal oracle is a random function, `famSeededOracle` is stateless
with all randomness in the seed, and `seedDistr` is `uniformOfFintype` — so the random function
must be the seed and its type must be a `Fintype`.  `BitVector ν × ℕ → BitVector L` is not, and
`(n : ℕ) → BitVector ν → BitVector n` is the infinite dependent product already recorded as an
obstruction for `randLen`.  The game therefore needs a bounded PRF domain, which is realistic
(ChaCha20-CTR has a `2 ^ 32` block limit; `ggmPrf`'s `cw` is the same bound) but puts a
message-length side condition in the eventual reduction.  Scoped in `FUTURE-WORK.md`.

### Corrected — a stale limitation

`writeup.md` §6 and `report.md` §6 both still asserted finding F8 in the present tense: that no
`GenPolyTime` generator takes a `BitVector` to a `Bool`, so no distinguisher in the class can
depend on the challenge.  **That was fixed on 2026-09-21d** — `PolyVal` went from 19 generators
to 33, and `polyFn_indCpaBitAdversary` is the witness.  `CHECKPOINT.md` had it right.  Both
documents now record the repair and state the weaker thing that is actually still true: there is
no *completeness* theorem, so `garblingSecureRelative` stays the form to cite — not because the
generated class is contentless, but because it is not provably everything.

## [2026-09-30a] — File layout: scratch grouped, the two games merged, four new subfolders

Organisation only.  No proof, statement, hypothesis or definition changed; `lake build` is
clean at 2379 modules, all 14 scratch files elaborate, and the extracted C binary still garbles
and evaluates `notC`, `NAnd`, `andC`, `orC` over ChaCha20 with every output matching
`evalCircuit`.

* **`scratch/` grouped by role**, since a flat directory of 15 files did not say which were
  meant to be run and which were kept as evidence.  `checks/` (`AxiomCheck`,
  `GarbleCorrectness`, `ChaCha20Kat`, `ExecDemo`, `GarbleMain`, `extract-c/`) is what `writeup.md`
  §12 and §18 tell a reader to run; `findings/` (`CostAttempt`,
  `ExtractKeysSelfCounterexample`) holds the machine-checked refutations the text still cites as
  authority; `archive/` (`DegenerateEnc`, `GenClass`, `PrngFeasibility`) holds the three files
  that already described themselves as historical, preserved or superseded; `probes/`
  (`DupTrailing`, `GarbleSideCondition`, `TwoGateFixpoint`, `Instance`) holds one-off exploration.
* **`extract-c/build.sh` fixed for its new depth.**  `ROOT` was computed as `dirname $0`/../..,
  which was the repository root from `scratch/extract-c/` and is `scratch/` from
  `scratch/checks/extract-c/`.  Now `../../..`.  Every relative path in the script depends on it.
* **`EncryptionIndCpa.lean` + `PrgSecurity.lean` merged into
  `Expression/ComputationalSemantics/Games.lean`.**  144 lines between them, always imported
  together, both stating a pair of seeded oracles the adversary class cannot separate, and the
  seed-placement argument (`CHANGELOG.md [2026-09-16]`) is one argument told twice.  All ten
  declarations carried over unchanged.
* **`Expression/ComputationalSemantics/` split** into `Efficiency/` (`PolyTime`, `CostModel`,
  `GeneratedPolyTime` — 1 680 lines, one subject, two importers outside the group) and
  `Executable/` (`Executable`, `ExecutableDistribution`, `SeededEnvironment` — the refinement
  story of `writeup.md` §7).
* **`Garbling/` split** into `Security/` (`Security`, `SecurityFromPrimitives`,
  `ExecutableSecurity` — nothing in the library imports these; they are leaves) and
  `Correctness/` (`Correctness`, `ComputationalCorrectness`, `ExecutableCorrectness` — the
  symbolic / computational / executable ladder).  `Circuits`, `GarblingDef`, `Simulate` stay at
  the top as the definitions, with `HoleFree` and `EvaluatorTotality` as syntactic side results.
  `Executable/Executable.lean`, `Security/Security.lean` and `Correctness/Correctness.lean`
  repeat their directory name; that was accepted rather than renaming files the docs cite.
* **Documentation caught up**: `README.md` (which also still named `Simulation.lean` for
  `Simulate.lean` and `SimulateG` for `Simulate` — inherited from the base paper's README, now
  corrected), `report.md`, `CHECKPOINT.md`, `FUTURE-WORK.md`, `summary.md`, `writeup.md` and the
  regenerated `writeup.tex`, plus the `scratch/` path in 16 library docstrings.  `CHECKPOINT.md`'s
  claim that two scratch files do not build was stale — both were repaired on 2026-09-29 — and
  now records the repair instead.
  `SymbolicGarbledCircuitsInLean.lean` describes the encryption-only twin, whose
  `Garbling/Security.lean` and `Garbling/Correctness.lean` did **not** move; its text is unchanged.

## [2026-09-29f] — Clearing the residue of the soundness repairs

A sweep of what was left behind by the defect fixes catalogued in `writeup.md` §10.  No
cryptographic content changed; nothing was commented out, and no definition was retired.

* **Deleted** the commented-out `symbolicToSemanticIndistinguishabilityHidingOneKey` block in
  `SoundnessProof/HidingOneKey.lean` (an earlier version quantifying over all key shapes, with
  `sorry` in the `G0`/`G1` cases).  A `sorry` inside a comment is not checked and reads like a
  theorem; the live version immediately below it restricts to base keys, which is what the proof
  needs and what LM18 Lemma 6 supplies.  Replaced by a three-line note saying so.
* **`scratch/probes/Instance.lean` builds again.**  It still imported the encryption-only root
  `SymbolicGarbledCircuitsInLean`, which has no `decrypt_encrypt` and no `LengthPoly`, so it had
  been failing since those were added.  One-line import fix; also recorded that its closing
  remark ("the computational layer is not executable") has since been answered by `ExecEnc`.
* **`scratch/findings/ExtractKeysSelfCounterexample.lean` rewritten as theorems.**  It had degraded to
  partial output when `Finset.toList` became noncomputable.  The refutation of
  `extractKeys_hideEncrypted_self` is now kernel-checked
  (`not_forall_extractKeys_hideEncrypted_self`, by `decide`) rather than printed — strictly
  stronger than what it replaced, and the witness is `Enc (VarK 0) (VarK 1)` with
  `Y = {VarK 1}`.
* **Citation corrections** (`writeup.md` §22.3), in the library and in `report.md` / `summary.md`:
  `symbolicToSemanticSoundness` is **LM18 Theorem 3**, not Theorem 1 (Theorem 1 is the
  independent-keys characterisation, and `HidingOnePrgSeed.lean`'s citations of it are correct
  and were left alone); the side conditions cited as "Lemma 3, properties 1 and 3" are **Lemma 4**
  (atomicity) and **Lemma 6, property 1** (seed-freeness).  `PRGExtension-Analysis.md` is left as
  written — it is a dated audit record, not a live document.
* **Dead-code sweep, negative result.**  Of 962 declarations in `PRGExtension/`, 53 have no
  reference outside their own definition; all 53 are headline results, deliberate API surface, or
  consistency witnesses.  `garblingSecureGenerated` and `EfficientEnc` are narrower than one
  would want rather than useless, and already say so in their docstrings.

`writeup.md` §10.1 records the same, and §10's bullet on the two reduction lemmas was corrected:
they were repaired in place by adding `seedFree`, not replaced by the primed variants (which are
the `keySubterms` sublemmas their proofs call).

`lake build` clean on both roots, `sorry`-free, 73 axiom checks passing with no `sorryAx`.

## [2026-09-29e] — Seeded deployments are covered: `garblingSecureExecSeeded`

The composition, and the last step of the PRF hybrid.  Expanding one seed into the wire keys and
garbling is computationally indistinguishable from the simulator.

* `ExecEnc.garblePost` — everything the evaluator does once the keys are fixed; `execToDistr_eq_bind`
  pulls the key draw to the front of `execToDistr` (one `PMF.bind_comm`).
* `ExecEnc.execToDistrSeeded` / `ExecEncScheme.toFamDistrSeeded` — what a seeded deployment
  computes.
* **`garblingSecureExecSeeded`** — `indTrans` of the expansion step with `garblingSecureExec`.

**Kept as a separate theorem on purpose.**  `garblingSecureExec` covers an implementation that
draws its whole environment uniformly — the driver's default mode — and assumes nothing beyond
primitive hardness.  The seeded theorem needs `prgSchemeSecure` a second time (for the expansion)
and a poly-time hypothesis on the expansion reduction.  Generalising the original would have made
the honest mode pay for the convenient one, which is the hypothesis creep that made the inherited
efficiency assumptions vacuous (`report.md` §6.2).  The two modes of `scratch/checks/GarbleMain.lean` now
correspond exactly to the two theorems.

**No new closure assumption.**  Indistinguishability had to survive *using* the expanded keys.
Rather than assume "indistinguishability is preserved by poly-time post-processing",
`expandRedWith` puts the continuation inside the reduction, so what is assumed remains a
poly-time statement about a concrete computation (`ExpandReductionWithPolyTime`), in the same
form as `PrgReductionPolyTime`.

## [2026-09-29d] — Variable stretch is proved from length doubling

`Expression/ComputationalSemantics/Executable/SeededEnvironment.lean`.  The PRF hybrid's own hard part is
done: expanding a uniform seed with the sequential construction is **computationally
indistinguishable from a uniform environment**, proved from `prgSchemeSecure` and nothing new.

* `expandRed` — the reduction: draw the first `i` blocks, query the PRG oracle once, expand from
  the answer.  `expandSimulateReal` / `expandSimulateIdeal` compute what it does against each
  oracle; `expandRedRealEq` / `expandRedIdealEq` show those are hybrid `i` and hybrid `i + 1`.
* **`hybridStep`** — one step, via `IndistinguishabilityByReduction` applied to
  `prgSchemeSecure`.
* **`expandKeys_indist_uniform`** — the `n` steps composed with `indTrans`.

Supporting lemmas worth naming: `hybridSeeded_succ` (one more ideal step at the head, where the
drawn state becomes the shorter hybrid's *initial* seed — which is why a single query suffices),
`liftM_pure_pmf` and `liftM_bind_pmf` (`liftM` is a monad morphism on the fragment the reduction
uses), and `idealSeedDistr_eq` (the ideal oracle's two draws are the uniform distribution on
pairs — `uniformOfFintype_prod` again).

A correction to the earlier scoping: `VariableStretchSecure`, the named obligation added in
`[2026-09-29c]`, was stated over a **fixed** seed and is therefore false as written — with a
known seed the real expansion is a point mass the distinguisher can recompute.  It is removed;
the correct statement quantifies over a uniformly drawn seed, which is what `hybridSeeded` and
the theorems above use.

Still assumed: `ExpandReductionPolyTime`, that the reduction is polynomial time — the same
cost-model obligation as `PrgReductionPolyTime` and `EncReductionPolyTime`, and of the same
standing.  Still to do: composing this with `garblingSecureExec`, which needs the environment
substituted into `execToDistr`.

## [2026-09-29c] — Variable stretch from length doubling: construction and both endpoints

`Expression/ComputationalSemantics/Executable/SeededEnvironment.lean`, plus `uniformFinArrow_cons` in
`Core/UniformProduct.lean`.  The start of the PRF hybrid, by the route that adds no new
assumption: build a variable-stretch generator out of the length-doubling `prg0`/`prg1` the
framework already has.

* `expandKeys` — the sequential construction: emit `prg0 s`, carry `prg1 s`.  Computable.
* `idealExpand` and **`idealExpand_eq_uniform`** — the ideal expansion *is* the uniform
  distribution.  The far endpoint of the hybrid argument, and an equality rather than an
  indistinguishability.  It needed `uniformFinArrow_cons`: a uniform block of `n+1` draws is one
  draw followed by an independent block of `n` — the recursive form of the product split, built
  on an equiv `(Fin (n+1) → B) ≃ B × (Fin n → B)` that Mathlib does not have either.
* `hybridExpand`, with **both endpoints proved**: `hybridExpand_zero` (no ideal steps is the real
  construction) and `hybridExpand_full` (all ideal is uniform).

`VariableStretchSecure` names what remains — consecutive hybrids indistinguishable, `n` steps
composing — in the style of `Theorem4`, so the obligation is in the development rather than only
in prose.  No `sorry`; the four new theorems are on the standard three axioms.

### Changed — a third randomness mode in the driver

`scratch/checks/GarbleMain.lean` gains `--seeded`: a 256-bit seed from the OS, expanded with ChaCha20 —
what a deployment actually does.  It shares the expansion code with `--fixed-seed`, deliberately:
**the fixedness was never what put that mode outside the theorems, the expansion is**, and both
now say so.  The default (everything from `IO.getRandomBytes`) remains the mode the theorems
cover.

Worth recording against a misreading: ChaCha20 is used in *all three* modes, in two distinct
roles — as the encryption of every garbled table entry, and as LM18's `G` at every `Dup` gate,
which is the entire point of the PRG extension.  Only the source of the initial environment
differs between modes.

## [2026-09-29b] — The driver draws real randomness, and the PRF gap is written down

`scratch/checks/GarbleMain.lean` no longer hardcodes its seed.

* **Default**: every wire key, mask bit and nonce is drawn from `IO.getRandomBytes`.  This is an
  instance of the sampling `execToDistr` quantifies over, so the running binary is now *inside*
  the theorems rather than one unproved step outside them.
* **`--fixed-seed`**: the old reproducible path — one 256-bit seed expanded with ChaCha20 — kept
  for demonstrations, and it prints that it is outside what is proved.
* The binary reports the garbled circuit's Hamming weight.  Across OS-entropy runs it varies
  (2982 / 2999 / 2948 of 5903 bits) while every output still matches `evalCircuit`; under
  `--fixed-seed` it is identical run to run.  That is `garbleExecCorrect` visible at the command
  line: it quantifies over every environment and coin supply.

**`FUTURE-WORK.md` now scopes the PRF hybrid** — the theorem needed to cover seed expansion, the
three files it would touch, and why the difficulty is the *assumption* (a variable-stretch PRG)
rather than the reduction.

Incidental: the extraction script's invariant check earned its keep.  Writing the fingerprint
with `List.filter` made a Mathlib tactic module's list specialisation reachable, and the check
caught it at once; a fold avoids it.  The script also now passes `--error-limit=0`, since lld
stops at 20 undefined symbols by default and the stub list was silently truncated.

## [2026-09-29] — A standalone C binary extracts, with no Mathlib at run time

`scratch/checks/extract-c/build.sh` and `scratch/checks/GarbleMain.lean`.  Lean's code generator already emits
C for every module on each `lake build`; this compiles it and links a native binary that garbles
and evaluates `notC`, `NAnd`, `andC` and `orC` over ChaCha20, checking every answer against
`evalCircuit`.  100 ms, versus 2.6 s in the interpreter.  `ldd` reports libc, pthread, dl and rt
— no Lean, no Mathlib.

**This supersedes the earlier assessment.**  A full binary was thought to require compiling
Mathlib's 138 MB of emitted C.  It does not: after `--gc-sections` exactly **18 symbols remain
undefined and all are module `initialize_Mathlib_…`** — no Mathlib code or data is reachable
from `main`, because Mathlib sits on the *specification* path only.  Stubbing those initialisers
links.  The script re-checks that invariant on every run and aborts if anything other than an
initialiser appears.

Caveats kept in view: the stubbing is hand-rolled rather than something `lake` does, and the
principled version remains the module split (a computable core that imports no Mathlib); the
125 MB binary is almost all statically linked Lean core, the project's own objects being 2.3 MB.

Incidental finding: linking both library roots at once fails with duplicate symbols — the
two-copy divergence, showing up at link time rather than in the build.

## [2026-09-28e] — The executable scheme is 33× faster; the cipher was never the problem

Profiling the ChaCha20 demo (`scratch/checks/ExecDemo.lean`) rather than guessing.  ChaCha20 itself
costs 2.7 ms for 4096 keystream bits and was never the bottleneck; three operations on the
`List.Vector Bool` representation were quadratic.  All three are replaced by linear ones with
the same specifications, so **no proof changed** beyond the two characterising lemmas.

| | before | after |
|---|---|---|
| `vecTake` 2048 of 4096 | 403 ms | 0.03 ms |
| `xorStream` 4096 bits | 1.62 s | 3.8 ms |
| evaluate `orC` | 6.91 s | 5.1 ms |
| garble `orC` | 586 ms | 28 ms |
| whole demo, wall clock | 85 s | 2.6 s |

* **`vecTake` / `vecDrop`** (`ComputationalSemantics/Def.lean`) were
  `ofFn (fun i => v.get …)`, and `List.Vector.get` walks one cons cell at a time.  Now
  `List.take` / `List.drop` on the underlying list.  `vecTake_append` / `vecDrop_append` are
  re-proved from `List.take_left` / `List.drop_left`; every other proof consumes only those two
  lemmas, so nothing else moved.
* **`xorStream`** (`Crypto/ChaCha20.lean`) indexed the message per bit.  Now `List.mapIdx`.
  `xorStream_xorStream` is re-proved by `List.ext_getElem`.  The known-answer tests against
  OpenSSL still pass, so the rewrite is semantics-preserving.
* **`List.Vector.ofFn` is itself quadratic** — Mathlib defines it as
  `ofFn f = cons (f 0) (ofFn fun i => f i.succ)`, so reaching element `k` goes through `k`
  closures.  New `bvOfFn` (`Def.lean`) uses the linear `List.ofFn`; `chacha20Prg` and the demo's
  environment use it.  This was the single largest factor.

`scratch/checks/ExecDemo.lean` no longer needs `lake env lean -s 65536`; the deep recursion is gone.

Not done, and now decided against: changing the representation.  Swapping `BitVector` to core
`Vector Bool n` was tried and produces 75 errors in `Def.lean` alone — 22 of them instance
failures, because Mathlib gives core `Vector` no `Fintype` instance and no cardinality lemma,
which the sampling semantics and every counting argument depend on.  `ByteArray` is worse: the
bit lengths here are never byte multiples, so `append` — the most-used operation in the
development — would become bit-shifting.  `FUTURE-WORK.md` records the measurement.

## [2026-09-28d] — The symbolic evaluator's partiality never bites

`Garbling/EvaluatorTotality.lean`.  `FUTURE-WORK.md` flagged `gEvComp_sim`'s
`gEv c g i = some ov` hypothesis as "doing work a type could have done" and scoped removing it
at 2–3 days.  It took three statements, because the invariant it needs — "is in the image of
`gb`" — was already proved as `gEvCorrect`.

* `gEv_isSome_of_gb` — `gEv` never fails on a genuine garbling.
* `gEvComp_of_gb` — the computational simulation lemma with no symbolic side condition.
* `GEvalExpr_eq_EvaluateComp` — **the two evaluators agree**: on every bit vector a garbled
  circuit can take, symbolic evaluation succeeds and returns what computational evaluation
  computes.

A separate inductive well-formedness predicate would have been strictly weaker: it could not
relate the table's keys to the input labels without re-deriving `gEvCorrect`.  Recorded because
the scoping error is the interesting part.

`gEv`'s two failure modes are now separately accounted for: a **hole** (excluded for any
garbling by `garble_holeFree`, and the dangerous one — the computational evaluator does not fail
there, it returns `ones`) and the **wrong structure** (excluded by being a genuine garbling).

## [2026-09-28c] — Security of the code, not of the specification

`FUTURE-WORK.md` Half 2, the distributional refinement.  Estimated 1–2 weeks and 600–900 lines;
came to 650.  `sorry`-free, `[propext, Classical.choice, Quot.sound]` only.  No existing
statement or proof changed.

### Why it was needed

`evalExprExecOn_mem_support` says the implementation's output is *in the support* of the
specification's distribution.  That transports correctness, which is about individual outputs.
It cannot transport security, which is about distributions: an implementation that always
returned the same ciphertext satisfies the support law and is obviously insecure.

### Added — the lemma that was not in Mathlib (`PRGExtension/Core/UniformProduct.lean`)

* `map_equiv_uniformOfFintype` — a uniform transported along a bijection is uniform.
* `uniformOfFintype_prod` — a uniform on `α × β` is two *independent* uniforms; the point mass
  `(card (α × β))⁻¹` factoring as `(card α)⁻¹ * (card β)⁻¹` is the whole content.
* **`uniformFinArrow_bind_split`** / `uniformFinArrow_map_split` — drawing `m + n` coins and
  splitting them is drawing `m` and then, independently, `n`.  This is what the induction
  consumes at every node with two subexpressions.

There is no garbling in this file; it could be upstreamed as it stands.

### Added — the refinement (`…/ComputationalSemantics/ExecutableDistribution.lean`)

* `encCount`, `evalExprExecOn_counter`, `evalExprExecOn_coins_congr` — **coin consumption is
  structural**: the counter advances by exactly `encCount e` regardless of any value, and the
  result depends only on the coins in the window `[i, i + encCount e)`.  That is what lets the
  supply be split between subexpressions.
* **`execDistr_eq`** — the change-of-variables induction: drawing the coins uniformly and
  running the code gives *exactly* `evalExpr` of the denoted specification.
* `execToDistr` / `execToDistr_eq` — the same over the sampled environment, against
  `exprToDistr`; `ExecEncScheme` / `toFamDistr_eq` — the family form, against `exprToFamDistr`.

The strengthened law the refinement needs — `(uniform coins).map (run k m) = encrypt k m`
rather than support membership — cost nothing: `ExecEnc.spec` *defines* `encrypt` that way, so
`ExecEnc.spec_encrypt` is `rfl`.  Doing the `#eval` work first paid for itself here.

### Added — `garblingSecureExec` (`PRGExtension/Garbling/Security/ExecutableSecurity.lean`)

`garblingSecureRelative` for the distributions an implementation actually produces.  Once the
two families of distributions are *equal*, the transfer is a rewrite.

### Changed — `randLen` is a constant

Forced, not preferred: a coin supply of type `(n : ℕ) → BitVector (randLen n)` is an infinite
dependent product, so no distribution over it is expressible and the theorem could not be
stated.  This excludes schemes whose coin count grows with the message length; every real scheme
has a fixed nonce or IV, and ChaCha20's is 96 bits.

### Still assumed

`encryptionSchemeIndCpa` and `prgSchemeSecure`, for the scheme family the implementation
denotes.  The refinement removes the *specification* from the security statement and says
nothing about the primitives.  `ExecEncScheme` is an implementation at every security parameter,
so `chacha20Enc : ExecEnc 256` cannot instantiate it — the concrete-versus-asymptotic mismatch,
recorded rather than papered over.

## [2026-09-28b] — The implementation runs under `#eval`, on ChaCha20

`FUTURE-WORK.md` item 1.  The executable layer added earlier the same day ran only by kernel
reduction; it now compiles and runs.  No existing statement changed; `gEvComp_sim` and
`garbleCorrectComp` were not restated.

### Changed — `shapeLength` now depends only on the ciphertext-length function

**This was the actual blocker.**  `vecTake` / `vecDrop` consume `shapeLength κ enc …` as *data*,
so compiled code needs `enc.encryptLength`; but `PMF.pure` has no executable code, so every
concrete `encryptionFunctions` is `noncomputable`, and Lean erases only `Sort`- and
`Prop`-valued arguments.  `ComputationalSemantics/Def.lean` now defines **`shapeLengthOn`** over
`encLen : ℕ → ℕ` alone, with `shapeLength` as that at `scheme.encryptLength` — hence
*delta*-equal, so nothing downstream changed except five `simp` sites in `shapeLength_poly`.

The same generalisation, same pattern, for the evaluators: `evalExprExecOn`, `gEvCompOn`,
`parseEncodedValOn`, `parseMaskValOn`, `EvaluateCompOn`, with the originals redefined as
wrappers.  Five mechanical edits inside `gEvComp_sim` / `garbleCorrectComp`, because unfolding a
wrapper leaves the induction hypotheses in the old form.

### Added — `ExecEnc`: an implementation, with the specification derived from it

`ComputationalSemantics/Executable.lean`.  `ExecScheme` asks "here is a specification, can it be
run?"; **`ExecEnc`** answers the question an implementer has, and mentions no specification, so
it compiles.  **`ExecEnc.spec`** derives the specification, with `encrypt` the push-forward of
the uniform distribution on coins.  Because its `encryptLength` and `decrypt` are projections of
a structure literal, `EvaluateComp ex.spec` *is* `EvaluateExec ex` definitionally:
**`ExecEnc.garbleExecCorrect`** (`Garbling/Correctness/ExecutableCorrectness.lean`) is `garbleCorrectComp`
applied, with no bridge lemma and no casts.

A bonus for the still-unbuilt Half 2: the strengthened `ExecScheme` law
`(uniform coins).map (run k m) = encrypt k m` now holds by `rfl` for any implementation.

### Added — ChaCha20 (`PRGExtension/Crypto/ChaCha20.lean`)

Both primitives instantiated at κ = 256, in pure Lean: the RFC 8439 block function, the CTR-mode
stream cipher (`chacha20Enc : ExecEnc 256`, nonce as coins, `encryptLength n = 96 + n`), and the
length-doubling PRG (`chacha20Prg`) as the two halves of one keystream block.

ChaCha20 rather than AES because the proof burden is smaller in three ways: ARX means no S-box
and no `GF(2⁸)`; a native stream cipher means `dec_run` is *xor involution*
(`xorStream_xorStream`, three lines) needing no property of the cipher; and `prg0`/`prg1` are a
block call rather than a construction.

Agreement with RFC 8439 is validated by known-answer tests against OpenSSL 3.0.13
(`scratch/checks/ChaCha20Kat.lean`, two vectors, 128 bytes each, covering the counter increment) — a
test claim, not a proof, exactly as `libcrux` and `lean-crypto` do it.  Security remains
assumed, and at a fixed key size the asymptotic statement is false rather than merely unproved;
`FUTURE-WORK.md` says why.

### Added — `scratch/checks/ExecDemo.lean` now runs real crypto

`notC`, `NAnd`, `andC` and `orC` garbled and evaluated under ChaCha20, by `#eval`: every answer
matches `evalCircuit`, and the garbled circuits run 2054–5903 bits.  Needs
`lake env lean -s 65536` — `List.Vector.ofFn` recurses once per bit.  `scratch/checks/AxiomCheck.lean`
gains 7 checks.

## [2026-09-28] — An executable garbling scheme, and hole-freeness

Both items `FUTURE-WORK.md` recommended, implemented.  No existing statement, proof or
definition changed; four new modules, all `sorry`-free and on `[propext, Classical.choice,
Quot.sound]` only.

### Added — the executable implementation (`FUTURE-WORK.md` Half 1)

The computational semantics is `PMF`-valued and therefore `noncomputable`; until now nothing
below the symbolic layer could be run.  It can now.

* **`Expression/ComputationalSemantics/Executable/Executable.lean`** — `ExecScheme`, the executable
  counterpart of a scheme's encryption (explicit coins, plus `run k m r ∈ (encrypt k m).support`);
  `evalExprExec` / `evalExprRun`, the same recursion as `evalExpr` with a coin supply threaded
  through, computable and `PMF`-free; **`evalExprExec_mem_support`**, the refinement — every
  value it produces lies in the support of `evalExpr`; and `evalExprRun_mem_support_exprToDistr`
  / `…FamDistr`, the same over the sampled environment.
* **`Garbling/Correctness/ExecutableCorrectness.lean`** — `GarbleExec`, and **`garbleExecCorrect`**:
  `Evaluate(Garble(C,x)) = C(x)` for the code that runs.  Plus `garbleExec_mem_support` (what
  it computes is a sample of `exprToDistr`, so no second correctness notion was introduced) and
  `garbleExec_projective` (the coin threading respects the offline/online split, so everything
  but the input-label selection can be computed before `x` is known).
* **`scratch/checks/ExecDemo.lean`** — a toy `ExecScheme` (key-stream XOR, **not secure**) and ten
  end-to-end evaluations of `notC`, `NAnd`, `andC`, `orC` against literal answers.

This works because `garbleCorrectComp` is stated over the distribution's *support*, which is
exactly the specification an implementation must meet.  Security is **not** transported: that
needs the distributional refinement, still unbuilt and still scoped in `FUTURE-WORK.md`.

**Known limitation, newly discovered.**  The demo runs by *kernel reduction*, not `#eval`.
`PMF.pure` has no executable code, so every concrete `encryptionFunctions` is `noncomputable`,
and `enc` is a runtime argument of `evalExprExec` / `gEvComp` / `EvaluateComp` — not merely
formally, since `vecTake` / `vecDrop` consume `shapeLength κ enc …` as data.  `FUTURE-WORK.md`
scopes the fix (a standalone `ExecEnc` with the specification derived from it, ~120 lines).

### Added — hole-freeness (`FUTURE-WORK.md` cost C2)

`Expression` merges LM18's `𝐄𝐱𝐩` and `𝐏𝐚𝐭` into one type, which costs a typing fact: in LM18
"a garbled circuit contains no holes" holds by construction.  Here it held by accident of the
definitions and was checkable only by grep.

* **`Expression/HoleFree.lean`** — `HoleFree` with a `Decidable` instance; `holeFree_key`
  (*every* `Expression 𝕂` is hole-free — `Hidden`'s index is always `EncS s`), `holeFree_bit`,
  `holeFree_encLabel`; and `holeFree_enc_exists`, which states positively what `decrypt`'s
  failure arm depends on: a hole-free ciphertext is a real `Enc`.
* **`Garbling/HoleFree.lean`** — `gb_holeFree`, `sim_holeFree`, and the headline
  **`garble_holeFree`** / **`simulate_holeFree`**.

An edit that starts emitting holes from `Gb` now breaks the build instead of silently
desynchronising the symbolic evaluator (which refuses on a hole) from the computational one
(which by `evalExpr_hidden_decrypt` would return `ones` — a wrong wire label, not a failure).
`ComputationalCorrectness.lean` cites it where `gEvComp`'s totality is discussed.  Dropping
`gEvComp_sim`'s `gEv … = some ov` hypothesis needs more than hole-freeness and was not
attempted; `FUTURE-WORK.md` says why.

### Changed

* `PRGExtension.lean` imports the four new modules and lists `garbleExecCorrect` among the
  entry points.
* `scratch/checks/AxiomCheck.lean` — 12 new checks, all `[propext, Classical.choice, Quot.sound]` or
  less.

## [2026-09-22] — `summary.md`

Reference document, no code changes.  Three things that were hard to reconstruct from the
source, now written down in one place.

* **Deviations from the pen-and-paper proofs**, split into three kinds whose significance is
  opposite and which are easy to conflate: *disclosures* (a slightly different model, same
  strength — the hole's payload, `negl`'s bounded form, the abstract adversary class);
  *repairs*, where the Lean is more correct than the prose (the false `EncS` step in the cost
  analysis, the missing `decrypt`/`encrypt` relation, three inherited defects); and *gaps*
  (2PC and oblivious transfer, executability).
* **The proof chain** — symbolic side up to `theorem5`, the soundness bridge with its two
  atomic hops and where they meet the adversary class, and the computational side for security
  and (separately) correctness.
* **Uniform versus non-uniform adversaries** — what the distinction is, that it is inherited
  from the base paper's types rather than introduced here, and that it constrains neither the
  theorems nor a uniform-PPT user, since the reductions never use non-uniform advice.

Cross-linked from `report.md` §6 and `CHECKPOINT.md`.

## [2026-09-21j] — Two schemes, two roots: the encryption-only library builds again

The repository is meant to offer a choice — an encryption-only garbling scheme (the base
paper's) or a PRG-based one (this extension).  **The encryption-only chain did not build.**
Nothing in the default target referenced it, so it had rotted unnoticed.

### Fixed — six import lines

`SymbolicGarbledCircuitsInLean/{ComputationalIndistinguishability/Def,
Expression/ComputationalSemantics/EncryptionIndCpa}.lean` imported
`SymbolicGarbledCircuitsInLean.VCVio2.…`, from when VCVio2 was vendored inside that directory;
it now lives at the repository root.  That was the entire breakage — the proofs were intact.
The encryption-only chain builds and is `sorry`-free.

### Changed — two roots, both default targets

The two libraries **cannot share an import graph**: both declare the same names in the same
namespaces (`lengthOfBit` and friends), so importing both into one file fails outright.  That
settles the architecture, and it is the most decoupled one available:

* **`PRGExtension.lean`** (new) — root of the PRG + encryption scheme, holding what
  `SymbolicGarbledCircuitsInLean.lean` used to import.
* **`SymbolicGarbledCircuitsInLean.lean`** — now the root of the *encryption-only* scheme,
  which is what its name always suggested.  Previously it imported `PRGExtension` modules,
  which was backwards.
* `lakefile.lean` marks **both** as `@[default_target]`, so `lake build` checks both and
  neither can rot again.

No proof, statement or definition changed.  `scratch/checks/AxiomCheck.lean` now imports
`PRGExtension`; all 30 checks pass unchanged.

### Where the two actually differ

Worth recording, because it is much less than the two copies suggest.  The circuit language
(`Circuit`, `WireBundle`) is **identical**.  The expression algebras differ by exactly two
constructors — the extension adds `G0`, `G1`.  The schemes differ by exactly one gate: how
`DupC` derives its output labels (duplicate the label, versus derive both with `G0`/`G1`).
Everything else is the same argument carried out twice.

Sharing the substrate would mean renaming into disjoint namespaces across 27 files — a much
larger change than this one, and a separate decision.  See `CHECKPOINT.md` §3.2.

## [2026-09-21i] — Projectivity restored

The base paper states it implemented `preGarble` "as required by the definition of a projective
scheme"; this extension had dropped it.  A scheme must be projective before it can be used for
two-party computation — the input labels have to be deliverable one wire at a time by oblivious
transfer, without the garbler learning the input.

### Added — `Garbling/GarblingDef.lean`

* **`projectionLabelType`**, **`gInputToProjection`** — both encodings of a wire label,
  computed without reference to any input.
* **`makeProjection`** — the base paper's `proj`: select one label per wire by the input bits.
* **`preGarble`** — the garbled circuit, the output mask, and the input label pairs.
* **`gEncCorrect`** — selecting from both encodings agrees with encoding directly.
* **`Garble_projective`** — `Garble c x` factors through `preGarble c`, which does not mention
  `x`.

Adapted from the authors' `SymbolicGarbledCircuitsInLean/Garbling/GarblingDef.lean`, but the
adaptation runs the other way round: they *define* `Garble` via `preGarble` and recover the
direct form as `GarbleExprNoProjection`; here `Garble` is already the direct form, so
`preGarble` is defined separately and the factorisation is the theorem.  The property was
always true by construction — `makeLabels` and `gb` never see the input — it simply was not
stated.

`Garble_projective` and `gEncCorrect` depend on `[propext]` alone.

### Recorded — executable implementation as a future project

`CHECKPOINT.md` §3.2 now scopes the PRNG-based sampling monad plus refinement proof: an
executable interpretation of `evalExpr`, and a proof that it refines `exprToFamDistr`.  Note
that `garbleCorrectComp` is already stated over the distribution's *support*, which is exactly
what an implementation must satisfy, so support-level refinement suffices to transport
correctness; security would need the distributional version.

## [2026-09-21h] — F9 complete: computational correctness of the garbling scheme

`Garbling/Correctness/ComputationalCorrectness.lean`.  The development now proves computational
**security** *and* computational **correctness**; previously correctness was symbolic only.

### Added — `garbleCorrectComp`

`∀ v ∈ (evalExpr enc prg kVars bVars (Garble c x)).support,
  EvaluateComp enc prg c v = evalCircuit c x` — the base paper's correctness definition,
`Evaluate(Garble(C,x)) = C(x)`, on real bit vectors.

### Added — the machinery

* **`gEvComp`** — the computational evaluator mirroring `gEv`.  Total, where `gEv` returns
  `Option`: the symbolic partiality is pattern-match failure on expressions that cannot arise.
  Uses a structured value type (`encodedValType`) rather than raw bit vectors, which removes
  every associativity cast.
* **`perm_select`** — point-and-permute, formally: `Perm` stores `c_B` first and the encoded
  bit is `B xor x`, so the row for the true input bit sits at index `β`.
* **`xorVarB_eq_xor_val`** — the symbolic name-and-parity comparison equals XOR of the two
  bits' actual values.  This is what lets the evaluator select a row without knowing the
  environment.
* **`gEvComp_sim`** — the simulation lemma, by induction on the circuit, mirroring
  `gEvCorrect` case for case.  `NandC` consumes `evalExpr_decrypt` twice.
* `decodeComp` / `decodeComp_correct`, `parseEncodedVal`, `parseMaskVal`, `extractPair_eq`,
  `extractPerm_fst`, `decrypt_eq`, `EvaluateComp`.

### Note on two landmines

Both `CHECKPOINT.md` §5 notation traps fired: `o` (for `WireBundle.SimpleB`) cannot be used as
a variable name, and `(x, y)` is `WireBundle.PairB`, so `Prod.mk` has to be written out in
statements about pairs.  Also `cases` cannot eliminate `Expression (PairS s₁ s₂)`'s `Perm`
constructor (it would need `s₁ = s₂`), so `extractPair_eq` is stated with explicit match arms —
the §5 recommendation.

## [2026-09-21g] — F9 steps 1–2: encryption correctness, and the F4 loophole closed

### Added — `encryptionFunctions.decrypt_encrypt`

`decrypt_encrypt : ∀ {n} (key) (msg), ∀ c ∈ (encrypt key msg).support, decrypt key c = msg`.
The two fields were previously unrelated, which blocked any computational correctness
statement and left a degenerate-scheme loophole.

### Added — the cryptographic content of F9 (`ComputationalSemantics/Def.lean`)

* **`evalExpr_decrypt`** — computational decryption of an `Enc` node lands in the support of
  the plaintext's semantics.  The symbolic evaluator decrypts by pattern-matching
  `Enc k e ↦ e`; this is the statement that its computational counterpart agrees.
* **`evalExpr_hidden_decrypt`** — a hole decrypts to the public constant, carrying nothing.

### Added — the structural half

`vecTake`, `vecDrop`, `vecTake_append`, `vecDrop_append`, on top of `get_append_left` and
`get_append_right` (Mathlib supplies only the `cons` cases).  `Pair` and `Perm` build their
values with `List.Vector.append`; a computational evaluator has to undo it.

### Closed — F4, as a side effect

The degenerate scheme whose ciphertext ignores the message is no longer constructible: its
`decrypt_encrypt` obligation reduces to `ones = msg`.  `scratch/archive/DegenerateEnc.lean` is rewritten
to demonstrate that (`degenerateScheme_obligation_false`) and to record what the file used to
show.  **IND-CPA is therefore no longer trivially satisfiable**, and every hypothesis of
`garblingSecureRelative` is now genuine — which strengthens the earlier non-vacuity analysis.

### Still open — F9 step 3

The computational evaluator itself (`gEvComp`, `decodeComp`, the simulation lemma mirroring
`gEvCorrect`, and assembly into `Evaluate (Garble c x) = evalCircuit c x`).  Estimated 300–500
lines; `CHECKPOINT.md` §3.2 has the three-step plan.  Both hard-to-find ingredients — the
decryption lemma and the vector-split lemmas — are now in place; what remains is index
bookkeeping in the `Perm` and `Dup` cases, not cryptography.

## [2026-09-21f] — Stale documentation corrected; F9 (no computational correctness) recorded

### Fixed — three claims that were two sessions out of date

* `Soundness.lean` said [Mic09, Lemma 2]'s symbolic factorisation was "not formalised".  It
  is, in both directions: `gPreserving_eq_substKeys`, `gPreserving_ext`, `rootsOf_keySubterms`
  for the factorisation and `prgRenameRel_substKeys_general` for the generation direction, all
  in `Expression/Lemmas/PseudorandomRenaming.lean`.
* `AdversaryView.lean` said "what is missing is the bookkeeping: that this iteration terminates
  and commutes with `hideEncrypted`/`keyRecovery`".  `fixpointStepSound` proves
  `FixpointStepSound` outright, which is exactly why `symbolicToSemanticSoundness` carries
  neither `hidingSideCondition` nor an atomicity hypothesis.
* `HidingOneKey.lean` carried four planning `TODO`s from an earlier phase, all long resolved.

### Recorded — F9, replacing the understated F4 note

There is **no computational correctness theorem**, and the soundness bridge cannot supply one.
`garbleCorrect` is symbolic: `testGarbleEval` decrypts by pattern-matching `Enc k e ↦ e` on
expressions.  Soundness maps a relation *between two expressions* to a relation *between two
distributions*; correctness says a function applied to *one* distribution yields a value, which
is not of that shape.  The base paper defines correctness separately
(`Evaluate(Garble(C,x)) = C(x)`, `Evaluate` explicit and efficient) and claims only security.

The concrete obstruction is that `encryptionFunctions` relates `encrypt` and `decrypt` by
nothing.  `CHECKPOINT.md` §3.2 now has the three-step fix, flagged to be done **before** any
refactor: it changes a structure every scheme instance depends on, and the only instances today
are in `scratch/`.

## [2026-09-21e] — `garblingSecureRelative`: the adversary-class gap closed

The generated class was doing two jobs that never had to be done by the same class: containing
the *reductions* (proved) and bounding the *adversaries* (where its narrowness hurt, F8).
Splitting them removes the gap rather than narrowing it.

### Added — `Garbling/Security/SecurityFromPrimitives.lean`

* **`ClassContained R A`** — every member of `R` is a member of `A`.
* **`garblingSecureRelative`** — simulation security against an **arbitrary** adversary class
  `A`.  What is assumed about `A` is only structural: closure under composition (the
  development's original hypothesis) and `ClassContained (GenPolyTime enc prg) A`.  The
  security hypotheses — IND-CPA and PRG security — are stated at `A`, so read `A` as "all
  probabilistic polynomial-time adversaries" and the conclusion is the intended one.

`ClassContained` is exactly the content "the reductions are efficient", factored so it can be
checked one generator at a time (33 of them) whenever `A` is made concrete.  Neither structural
hypothesis mentions the garbling scheme and neither is a security assumption.

This is the ordinary structure of a cryptographic proof: one never characterises PPT, one shows
the reduction is efficient and relies on the adversary class absorbing it.  The completeness
question left open in `[2026-09-21d]` is thereby sidestepped rather than answered — it was only
load-bearing while one class had to play both roles.

Consequence for F7: `PolyTimeClosedUnderComposition` remains a hypothesis, but of the
*abstract* class, where one would not expect to prove it.  It only looked like a defect while
the same class served both purposes.

**`garblingSecureRelative` is now the statement to cite.**  `garblingSecureGenerated` is
retained as the fully concrete instance, with its narrowness caveat intact.

## [2026-09-21d] — F8 fixed: the adversary class widened; completeness assessed

`PolyVal` goes from 19 generators to 33.  Nothing broke — adding constructors can only add
ways to be in the class, so `genPolyTimeModel`, `genBitOpsEfficient`, `gen_encReduction_polyTime`
and `gen_efficientEvalPrg` are unchanged, as is the axiom profile.

### Added — bit-level computation

`index` and `update` (random access, with the position taken **as input** rather than fixed per
κ), `bitsToFin` (compute an address from a register), `notB`, `andB`, `select` (branch at any
poly-sized result type), `eqBits`, `xorBits`, `finSucc`, `constBits`, `constFin`, `constBool`.

### Added — bounded iteration

`iterate` runs a step a *declared* `p.eval κ` times over a fixed `PolySized` state;
`iterateIdx` is the same with the step able to see the loop counter, which inner loops over bit
positions (a ripple-carry increment, a memory scan) require.  Helpers `pmfIterate`, `pmfFold`,
`bitsToNat`.  Sound by construction: poly-many passes, each poly, and the state cannot widen
because its type pins the width.

### Added — membership witnesses

`polyVal_readBit` and `polyFn_indCpaBitAdversary`: reading a bit of a bit vector, and a
distinguisher that queries the left-or-right oracle and reports a bit of the ciphertext — the
exact shape F8 said was unreachable.  Deliberately *positive* statements; formalising F8's
negative claim was rejected as effort spent proving something the widening makes false.

### Completeness for PTIME — assessed, not achieved

**No formal completeness theorem, and the obstruction is structural.**  "Contains every
poly-time function" presupposes a formalised machine model to be complete with respect to,
which is exactly the cost that generating the class was meant to avoid.
Soundness-by-construction and completeness pull opposite ways.

`GeneratedPolyTime.lean`'s header now carries an informal RAM-simulation argument — one machine
step is a constant number of generators; `poly(κ)` steps is one `iterate` — concluding that the
class plausibly contains `P/poly` and more, explicitly marked as not formalised, alongside the
list of what *is* proved.

**Correction to `[2026-09-21c]`.**  That entry said bounded iteration "is precisely the problem
Hofmann's LFPL and Atkey's polytime QTT exist to solve", implying the machinery had to be
adopted.  More precisely: LFPL exists to **infer** a polynomial bound from a typing discipline;
generating the class lets us **declare** it.  The payment discipline is unnecessary, and the
trap it guards against — data growth under iteration — is closed for free by requiring the
iteration state to be a fixed `PolySized` family.  The rejection of Atkey in `CHECKPOINT.md` §2
stands; that entry should be read as "relevant reference, not machinery to adopt".

## [2026-09-21c] — Module docstrings for every file; F8 (the generated class is too narrow)

### Added — module overview docstrings

Every one of the 39 files in `PRGExtension/` now carries a `/-! ... -/` module docstring
saying what it is for and what to watch out for in it.  Twenty were written for this entry;
the rest already had one.  The notation-shadowing traps (`⊆` in
`SymbolicIndistinguishability.lean`, tuple syntax and `o` in `Garbling/Circuits.lean`) and the
indexed-family pitfalls in `Expression/Defs.lean` are now flagged where someone opening the
file will see them, not only in `CHECKPOINT.md` §5.

### Finding — F8: the generated adversary class is near-contentless

**This supersedes the "weaker but sound and non-vacuous" framing in `[2026-09-21b]`, which was
too generous.**

Reading off the nineteen `PolyVal` constructors: the only generator whose output is `Bool` is
`bitExpr`, whose domain is a *sampled bit environment*, obtainable only from `uniformBits`,
which ignores its input.  No generator takes a `BitVector` to a `Bool`.  So no distinguisher in
`GenPolyTime enc prg` can produce a Boolean depending on a bit vector — hence none can depend
on the IND-CPA challenge or on the garbled expression at all.  `garblingSecureGenerated` is
sound but says very little.

Two causes.  The generator set was chosen for the *reductions* and then reused as the
*adversary* class, which is a category error — fixable by adding bit indexing, boolean gates
and equality.  Deeper: derivations are finite trees independent of κ, so members are
*constant*-size compositions, while a real adversary takes κ-many steps.  Fixing that needs a
bounded-iteration generator — which is precisely the problem Hofmann's LFPL and Atkey's
polytime QTT exist to solve, so §2's rejection of Atkey should be revisited when the class is
widened.

Recorded in `CHECKPOINT.md` §3.1 as F8, with the widening promoted to the top of "what is
left".  The observation is a syntactic check over nineteen constructors, not a formalised
theorem; formalising it is an induction over `PolyVal` with a "no information flows from
`BitVector` to `Bool`" invariant.

### Added — `scratch/probes/Instance.lean`

A concrete instantiation, to check the plumbing end to end: a concrete `encryptionScheme` and
`prgScheme`, `LengthPoly` discharged, a one-NAND circuit, and `garblingSecureGenerated` applied
to give simulation security with exactly three hypotheses left open
(`PolyTimeClosedUnderComposition`, IND-CPA, PRG security).  It also shows that the *symbolic*
layer is executable (`#eval` on `Garble` and `evalCircuit` both run) while the computational
layer is not, being `PMF`-valued and therefore `noncomputable`.

## [2026-09-21b] — `IsPolyTime` is now a concrete predicate; the interface is a theorem

Implements the replacement for Design B step 1 recorded in `[2026-09-21]`.  `PolyTimeModel`,
`BitOpsEfficient` and LM18 Definition 1 stop being assumptions and become theorems about a
defined class.  Axiom profile unchanged; no `sorry` or `axiom` in `PRGExtension/`.

### Fixed — F6: `PolyTimeModel` gets its own value predicate

`PolyTimeVal IsPolyTime f` used to abbreviate `polyTimeFamComp IsPolyTime f`, i.e.
`IsPolyTime` applied to the computation that *queries for its input*.  That encoding is not
invertible, so every clause that **takes** a value-level hypothesis was undischargeable for
any concrete model.  Found only by attempting an instantiation.

* **`PolyFamCompPred`** — the predicate type for value functions.
* `PolyTimeModel` gains **`IsPolyTimeVal`** (all value clauses restated against it) and
  **`valToFamComp`**, the one-directional link to the framework's `polyTimeFamComp`, carrying
  the `PolySized` conditions on *domain and output* that finding F5 asked for.  F5 needed no
  clause-level change once F6 moved the value clauses off the encoding.
* **`EfficientEncVal` / `EfficientPrgVal`** — LM18 Definition 1 against a value predicate.
* `BitOpsEfficient` is now parameterised by a `PolyFamCompPred` rather than a
  `PolyFamOracleCompPred`.
* `evalEfficiencyFromPrimitives_holds` now takes a **`ValFromFamComp`** hypothesis (the
  backward direction), since `EvalEfficiencyFromPrimitives`'s own hypotheses are in the
  encoded form.  **`efficientEvalPrg_holds`** is the version that needs no such thing, and is
  what the capstone uses.

### Added — `ComputationalSemantics/GeneratedPolyTime.lean`

`IsPolyTime` as the smallest class containing the primitives and closed under the
combinators — an inductive family whose **derivations are the implementations**.
Realizability with derivation trees as programs; no machine model.

* **`PolyVal enc prg`**, **`PolyFn enc prg`**, **`GenPolyTime enc prg`**.
* **`polyVal_to_famComp`** — the bridge.
* **`genPolyTimeModel`** — `PolyTimeModel (GenPolyTime enc prg)`, every clause the matching
  constructor.
* **`genBitOpsEfficient`**, **`genEfficientEncVal`**, **`genEfficientPrgVal`** — LM18
  Definition 1 becomes a *generator* rather than a hypothesis.
* **`gen_encReduction_polyTime`** (O1), **`gen_efficientEvalPrg`** (O2),
  **`gen_prgEnvSampler_polyTime`** — all at the concrete predicate.

### Added — `garblingSecureGenerated` (`Garbling/Security/SecurityFromPrimitives.lean`)

The security theorem at a concrete `IsPolyTime`, with the interface discharged.  What remains
assumed: `LengthPoly`, IND-CPA, PRG security, and `PolyTimeClosedUnderComposition`.

**Two caveats, both in the docstring and both load-bearing.**

1. `GenPolyTime enc prg` is the class generated by *these* primitives, so security against it
   is a weaker hypothesis than security against all probabilistic polynomial-time adversaries
   — the usual algebraic-adversary trade.  Sound and non-vacuous, and a strict improvement on
   an assumed interface, but not the same statement.
2. **F7 (new).**  `PolyTimeClosedUnderComposition` is stated with `polyTimeFamComp` and so
   inherits exactly the non-invertibility of F6; it stays a hypothesis where the interface's
   own clauses no longer are.  Fixing it means restating it at the value level in
   `ComputationalIndistinguishability/Def.lean`.

### Changed — `scratch/archive/GenClass.lean`

Reduced to the F6 demonstration: the clause that discharges under the old encoding, the one
that does not (two deliberate `sorry`s marking where inversion would be needed), and the same
clause after the refactor as a single constructor.

## [2026-09-21] — Design B step 1 attempted: impossible as written; replacement prototyped

No library changes.  Step 1 ("define `cost : OracleComp spec α → ℕ` over the free-monad
structure, charging for local computation") was attempted and **cannot be done**.  Two
scratch artifacts, a rewritten `CHECKPOINT.md` §3.1, and two new findings.

### Why step 1 is impossible — `scratch/findings/CostAttempt.lean`

* **Obstruction A (fixable).**  `oracleSpecForRand` makes a randomness query's response type
  an arbitrary `Type`, so `⨆ u, cost (k u)` ranges over an infinite family — and Mathlib's
  `⨆` silently returns `0` there (`(⨆ n : ℕ, n) = 0`).  A `ℕ`-valued `cost` is quietly wrong,
  not merely partial.
* **Obstruction B (fatal).**  Local running time is not a property of an `OracleComp` term.
  `cost_blind` proves that **any** cost function, structural or not, is invariant under
  replacing a continuation by an extensionally equal one — in Lean a brute-force search and a
  lookup table with the same graph are the same function.  And `cost₁ (pure x) = 0` for every
  `x`, however expensive.  So a structurally-defined cost *is* a query count, which is exactly
  the vacuity trap `CHECKPOINT.md` §3.1 already warned about.

### The replacement — `scratch/archive/GenClass.lean`

Since cost cannot be read off a term, supply it with the term: define `IsPolyTime` as the
smallest class containing the primitives and closed under the combinators, an inductive family
whose **derivations are the implementations**.  Realizability with derivation trees as
programs; no machine model needed.

* **`PolyVal enc prg`** — generated value functions (`id`, `fst`, `snd`, `unit`, `pair`,
  `precomp`, `bind`, `uniformBits`, `uniformKeys`, the seven bit primitives, and
  `encrypt`/`prg0`/`prg1`).  LM18 Definition 1 becomes a *generator* rather than a hypothesis.
* **`PolyFn enc prg`** — generated oracle computations (`ofPure`, `ofSample`, `bind`,
  `precomp`, `query`).
* **`GenPolyTime enc prg : PolyFamOracleCompPred`**.
* **`polyVal_to_famComp`** — proved: `PolyVal f → polyTimeFamComp (GenPolyTime enc prg) f`.

Both inductives elaborate over indices in `Type` and `ℕ → Type` (the viability risk) and the
bridge closes.

### Findings

* **F5 — `PolySized` is needed on outputs, not just domains.**  The bridge requires
  `PolySized Output` as well as `PolySized Input`.  `[2026-09-18e]` added the condition to
  nine clauses' domains only.
* **F6 — `PolyTimeModel`'s value-level clauses must not be phrased via `polyTimeFamComp`.**
  The blocker for the pivot, and a defect in the *interface* found only by trying to
  instantiate it.  `PolyTimeVal IsPolyTime f` unfolds to `IsPolyTime` applied to the
  computation that *queries for its input*.  Clauses with no `PolyTimeVal` hypothesis
  (`valFst`) discharge through the bridge; clauses that **take** `PolyTimeVal` hypotheses
  (`valPair`, `precompVal`, `bindVal`, `pureFn`, `liftVal`, `precompFn`, `queryFn`) need the
  *converse* of the bridge — an inversion of `PolyFn` on a term whose constructors are Lean
  functions.  Both cases are demonstrated at the end of `scratch/archive/GenClass.lean`.

  Fix: give `PolyTimeModel` a third field, an explicit `IsPolyTimeVal`, instead of reusing
  `polyTimeFamComp`.  Reusing it was economical while the interface was assumed — nothing ever
  had to be proved about it — and stops being so the moment you build a model.

Also recorded: if the derivations are later indexed by a cost, they must be `Type`-valued
rather than `Prop`-valued, since `PolySized` carries its width as data and a `Prop` derivation
cannot yield it by large elimination.  `GenPolyTime` would become `Nonempty (PolyFn …)`, which
also reads correctly as "there exists an implementation".

## [2026-09-18e] — `PolySized`: the audit's blocker fixed; three calculi evaluated

Implements `CHECKPOINT.md` §3.0 finding F1, and records the evaluation of three published
calculi as candidates to adopt.  No change to any theorem statement's *content* — the nine
affected clauses gain a side condition that every use site already satisfied — and no change
to the axiom profile.

### Fixed — F1: nine clauses were false for arbitrary type families

A poly-size circuit family has I/O width bounded by its size, so `valId` at
`D κ := BitVector (2 ^ κ)` demanded a poly-size circuit with `2 ^ κ` output wires.  A
satisfiability defect in the interface, not a soundness defect in the proofs, but it meant no
cost-charging model could ever discharge the interface.

`ComputationalSemantics/Def.lean` gains:

* **`PolySized D`** — a structure carrying `width : ℕ → ℕ`, `widthPoly : PolyLength width`,
  `finite`, and `card_le : Nat.card (D κ) ≤ 2 ^ width κ`.  The width is **data, not an
  existential**: this is the `calf`-style "carry the bound" formulation, so a concrete cost
  model's obligations become arithmetic in `width` rather than a re-derivation of the
  statements.
* Constructors **`bitVector`, `bool`, `unit`, `bitEnv`, `keyEnv`, `prod`**.

`CostModel.lean`:

* The side condition is added to nine clauses — `valId`, `valFst`, `valSnd`, `valUnit`,
  `queryFn`, `uniformBits`, `uniformKeys` in `PolyTimeModel`, and `constVec`, `nilVec` in
  `BitOpsEfficient`.  **`queryFn` was not in the original finding**: its *output* family
  `(Spec κ).range (i κ)` is not constrained by the `t`-is-poly-time hypothesis either, and
  that surfaced only while implementing.
* Size witnesses **`sizedKey`, `sizedShape`, `sizedRedEnv`, `sizedPrgEnv`**.  `sizedShape` is
  where `LengthPoly` enters the size discipline: without it `shapeLength` is not polynomially
  bounded, so the value family of a shape is not poly-sized at all.
* `encryptStep_polyTime` and `evalExpr_polyTime` take a `PolySized` for their generic domain;
  `valFstFst`, `valSndFst` and `weakenFn` take witnesses for the components they project.

The remaining thirteen clauses need nothing: every family they touch either comes from a
hypothesis that is already a poly-time claim or carries `PolyLength`.

### Added — `CHECKPOINT.md` §2, "Calculi considered and rejected"

* **ILC** (Liao–Hammer–Miller, PLDI '19) — no.  Its `PPT` is metatheoretic by the authors'
  own statement, defined only for closed whole systems, and its affine-write-token machinery
  solves concurrent scheduling, which `OracleComp` does not have.
* **Atkey**, *Polynomial Time and Dependent Types* (POPL '24) — right problem, wrong
  instrument.  Sound *and* complete for PTIME, which is what non-vacuity wants, but it is a
  type theory rather than a predicate on existing terms, Lean is not QTT, the primitives would
  have to become syntax, and it is uniform where F2 commits us to non-uniform.  His case
  against cost-as-effect does not bite here, since §3.1 already concedes that primitive costs
  are parameters.
* **calf** (Niu–Sterling–Grodin–Harper, POPL '22) — closest; read it, don't adopt it.  Its
  conclusion names exactly the difficulty that forced `IsPolyTimeFn` into existence, and its
  `isBounded` rules are the shape ours converge to.  But it has **no probabilistic or oracle
  effects at all**, it is axiomatic (failing §1's no-`axiom` check), and its phase distinction
  solves a problem we avoid by stratification — §1.8.3 of the paper says as much.

Two things were taken.  Atkey's "cost each branch, not the tree" now fixes how
`cost (query i t >>= k)` must be defined (added to §3.1's constraint box); calf's
carry-the-bound formulation is why `PolySized.width` is data.

## [2026-09-18d] — Audit of the poly-time interface against poly-size circuits

No proof changes.  Before building a concrete cost semantics (`CHECKPOINT.md` §3.1, Design
B), the 22 clauses of `PolyTimeModel` + `BitOpsEfficient` were checked against the textbook
notion Design B has to instantiate — families of poly-size oracle circuits.  Four findings,
recorded in `CHECKPOINT.md` §3.0; 14 of the 22 clauses need nothing, and no clause admits
recursion or iteration, so the interface cannot build a brute-forcing distinguisher.

* **F1 (blocker).** `valId`, `valFst` and `valSnd` are **false for arbitrary type families**:
  a poly-size circuit family has I/O width bounded by its size, and nothing in those clauses
  constrains the domain.  Five more (`valUnit`, `uniformBits`, `uniformKeys`, `constVec`,
  `nilVec`) are generic in a domain they only discard.  A *satisfiability* defect in the
  interface, not a soundness defect in the proofs — `trivialPolyTimeModel` still satisfies it
  — but no cost-charging model can discharge the interface until a poly-size measure on type
  families is added.  This reorders Design B: the size measure becomes step 0.
* **F2.** `queryFn`'s oracle index carries no computability condition, committing the model
  to non-uniformity.  Nothing is lost (both reductions use an index fixed by `κ`), but `cost`
  must be non-uniform to match.
* **F3.** `oracleSpecForRand` gives the randomness oracle an entire `PMF` as its query
  payload, so `cost` must decide what constructing that argument costs.
* **F4.** The non-vacuity target was misstated, here and in `report.md`.

### Fixed — an incorrect claim in `CostModel.lean` and `report.md` §6.2b

Both said that under `IsPolyTime := fun _ => True` no scheme is IND-CPA secure, and therefore
that `trivialPolyTimeModel` makes the security theorems vacuous.  **The first half is false.**
`encryptionFunctions` has no correctness field relating `encrypt` to `decrypt`, so a scheme
whose ciphertext ignores the message is legal; its left and right IND-CPA oracles are
literally the same function, giving advantage `0` against *every* adversary.

The hypothesis that actually binds is **`prgSchemeSecure`**: the real oracle answers with
`(prg0 s, prg1 s)` for a κ-bit seed against a uniform 2κ-bit ideal answer, so the unbounded
distinguisher "decide membership in the image" wins with advantage at least `1 - 2 ^ (-κ)`,
and unlike encryption there is no entropy-preserving cheat.  The conclusion — that the
trivial model is not the witness — survives; the reason changes.

### Added — `scratch/archive/DegenerateEnc.lean` (sanity-check script, not part of the library)

* **`constEnc`** — a legal `encryptionScheme` whose ciphertext ignores the message.
* **`constEnc_indCpa`** — it is IND-CPA secure against *every* adversary class.
* **`constEnc_lengthPoly`** — and satisfies `LengthPoly`.

Together with `trivialPolyTimeModel` / `trivialBitOpsEfficient` this satisfies every
hypothesis of `garblingSecureFromCostModel` except PRG security, which is what makes the
restatement of the non-vacuity target in `CHECKPOINT.md` §3.1 step 6 necessary.

### Recorded — the cost-charging constraint

`CHECKPOINT.md` §3.1 now opens with the one design decision that determines whether Design B
is worth doing: **`cost` must charge for local computation, not only for oracle queries.**
The `IsQueryBound`/`PolyQueries` shortcut satisfies `PolyTimeClosedUnderComposition` *and*
all 22 clauses — `polyTimeFamComp` degenerates to "makes one query" — while making IND-CPA
unsatisfiable for any non-degenerate scheme.  Neither step 4 nor step 5 of Design B catches
this, so it has to be a constraint adopted up front.

## [2026-09-18c] — The two efficiency hypotheses become theorems; `encryptLength` is bounded

Implements `CHECKPOINT.md` §6 (the ciphertext-growth gap) and §7 Design A (an auditable
poly-time interface).  Both remaining efficiency assumptions — `EncReductionPolyTime` (O1)
and `EvalEfficiencyFromPrimitives` (O2) — are now **proved**, relative to an interface whose
clauses are one line each.  This is *not* a cost semantics, and the new file says so at the
top: it replaces two opaque assumptions about two large recursive terms with a set of small
ones about `bind`, `query` and `append`.

### Fixed — a real modelling gap: `encryptLength` was unconstrained

`encryptionFunctions.encryptLength : ℕ → ℕ` admitted `encryptLength n = 2 ^ n`.  For such a
scheme the value of a nested `Enc` is *exponentially* long in the expression depth, so
`shapeLength` is not polynomially bounded and the pen-and-paper cost analysis at the end of
`HidingOneKey.lean` is false as written — it assumes the bound when it says "since
`encrypt (k, n)` runs in time `p (n + κ)`, its output length is also bounded by `p (n + κ)`".
Same class of defect as the `Seed := Unit` bug of `[2026-09-16]`: a type that silently
permits the degenerate case.

`ComputationalSemantics/Def.lean` gains:

* **`PolyLength d`** — `∃ p : Polynomial ℕ, ∀ κ, d κ ≤ p.eval κ`, with `const`/`id`/`add`.
* **`LengthPoly enc`** — LM18 Definition 1's length half:
  `∃ p, ∀ κ n, (enc κ).encryptLength n ≤ p.eval (n + κ)`.
* **`shapeLength_poly`** — the prose argument's output-length induction, formalised: for a
  fixed shape, `shapeLength κ (enc κ) s` is polynomially bounded in `κ`.  `EncS` is the only
  case that needs anything, and it is exactly where `LengthPoly` is consumed.
* `polyEvalMono` — monotonicity of `Polynomial.eval` over `ℕ`.

`prgFunctions` needs no analogue: `prg0`/`prg1` are `BitVector κ → BitVector κ`.

### Added — `ComputationalSemantics/CostModel.lean`

* **`famOracleFn` / `PolyFamOracleFnPred`** — the predicate on *function* families that
  sequencing needs and that `famOracleComp` cannot express.
* **`PolyTimeModel`** — fifteen closure clauses over the pair of predicates: `valId`,
  `valFst`, `valSnd`, `valUnit`, `valPair`, `precompVal`, `bindVal` at the value level;
  `pureFn`, `liftVal`, `bindFn`, `precompFn`, `queryFn`, `closeFn` at the oracle level;
  `uniformBits`, `uniformKeys` for sampling.  `pureFn` is the *constrained* `ret` — the
  returned value must come from a poly-time function, so no work can hide in it.
* **`BitOpsEfficient`** — seven clauses naming the non-cryptographic bit-vector operations
  the semantics performs (`append`, `condAppend`, `bitExpr`, `bitToVec`, `keyVar`,
  `constVec`, `nilVec`), each carrying the `PolyLength` side condition that makes it honest.
* **`redFn_polyTime`** (O1 core) — induction over `reductionToOracle`'s arms, one proof arm
  per reduction arm.  `encNode_polyTime` and `encryptStep_polyTime` factor out the `Enc` and
  `Hidden` nodes, where the target key is either queried or encrypted locally.
* **`encReduction_polyTime`** — **`EncReductionPolyTime` is now a theorem.**
* **`evalExpr_polyTime`**, **`evalEfficiencyFromPrimitives_holds`** — **(O2) is now a
  theorem.**  Environment access is quantified per *variable* (`∀ n, …`) rather than over
  whole functions `ℕ → BitVector κ`, which is what makes the hypothesis statable.
* **`prgEnvSampler_polyTime`** — the PRG reduction's sampling prefix, previously a
  hypothesis of `garblingSecureFromEfficiency`, is also derived.
* **`trivialPolyTimeModel` / `trivialBitOpsEfficient`** — the interface is consistent, so
  the theorems above are not vacuous for that reason.  Deliberately *not* the non-vacuity
  witness the development wants; the docstring says why (under `fun _ => True` no scheme is
  IND-CPA secure).

### Added — `Garbling/Security/SecurityFromPrimitives.lean`

* **`garblingSecureFromCostModel`** — the security theorem with every efficiency claim about
  the *reductions* discharged.  What remains: `PolyTimeClosedUnderComposition`, the
  interface, `LengthPoly`, LM18 Definition 1 for the two primitives, IND-CPA, PRG security.

### Changed — `ComputationalSemantics/PolyTime.lean`

* **`EfficientEncPoly`** (new) — LM18 Definition 1 for `enc` over message-length *families*.
  `EfficientEnc` fixes `n` independently of `κ`, which is too weak for any induction over an
  expression: at an `Enc` node the message length is `shapeLength κ (enc κ) s`, which grows
  with `κ`.  `EfficientEncPoly.toEfficientEnc` shows it is the stronger of the two.
* **`EvalEfficiencyFromPrimitives` now carries `LengthPoly enc` and takes `EfficientEncPoly`.**
  The inherited statement was **not provable as written** — for a scheme with exponential
  ciphertext growth its conclusion is false in any cost model.  Its one caller,
  `reductionToPrgOracle_polyTime_of_primitives`, is updated to match.

### Regression

`lake build` clean and warning-free; no `sorry` or `axiom` outside comments; every `#print
axioms` check of `CHECKPOINT.md` §1 unchanged, and the new results depend only on
`[propext, Classical.choice, Quot.sound]`.

## [2026-09-18b] — `normalizeExpr` now recurses into the key positions

Removes a latent trap.  `normalizeExpr` left `Enc`'s key, `Hidden`'s key, and `G0`/`G1`
untouched.  That is harmless today — `Expression 𝕂` has only `VarK`, `G0`, `G1`, so a key
contains no bit expression and normalising one is the identity — but it is fragile in a
specific and unpleasant way: `normalizeExpr` is part of the *definition* of
`symIndistinguishable`.  Under-normalising would make that relation too **strong**, so
soundness would survive (a weaker theorem, still true) while **LM18 Theorem 5 could become
false**, since Theorem 5 is the side that has to establish indistinguishability.  A key
former mentioning bits would trigger exactly that, silently.

### Changed — `Expression/SymbolicIndistinguishability.lean`

```
| Expression.G0 k     => Expression.G0 (normalizeExpr k)          -- new
| Expression.G1 k     => Expression.G1 (normalizeExpr k)          -- new
| Expression.Enc k e  => Expression.Enc (normalizeExpr k) (normalizeExpr e)
| Expression.Hidden k => Expression.Hidden (normalizeExpr k)      -- new
```

### Added

* **`normalizeExpr_key`** (`@[simp]`) — normalising a key expression is the identity.
* `normalizeExpr_enc`, `normalizeExpr_hidden` (`@[simp]`) — the equations as they read
  *before* the change, so downstream proofs are unaffected.

### Fallout

One call site: `nand_pattern_sim`'s `simp only` list in
`Garbling/SymbolicHiding/GarbleHoleBitSwap.lean` needed `normalizeExpr_key` added.  Nothing
else in the development noticed.

### Verification

The four new equations hold by `rfl`; `normalizeExpr (Enc k e) = Enc k (normalizeExpr e)`
still holds `by simp`; and `normalizeIdempotent`, `normalizeExprToDistr`, `theorem5` and
`garblingSecureFromEfficiency` have unchanged axiom footprints.

## [2026-09-18a] — The bounded closure is proved to be LM18's `𝖦*`, restricted

Closes the last symbolic-side item: the two claims that justified the bounded `prgClosure`
were argued in prose only and are now theorems.

### Added — `Expression/Lemmas/GStar.lean` (new)

* **`GStar S`** — LM18's `𝖦*(S)`, as an inductive predicate.  Genuinely unbounded, hence
  `Prop`-valued rather than a `Finset`.
* `keySubterms_closed` — `keySubterms p` is chain-closed: it contains every key subterm of
  every key it contains.
* `prgClosure_subset_gStar` / `gStar_inter_subset_prgClosure` — the two inclusions.
* **`prgClosure_eq_gStar_inter`** — for a chain-closed bound `U` and `base ⊆ U`,
  `prgClosure U base = 𝖦*(base) ∩ U`, **exactly**; and
  `prgClosure_keySubterms_eq_gStar`, the instance the development uses.
* `hideEncryptedS_congr_allParts` — key sets agreeing on `allParts p` hide identically.
* **`hideEncrypted_prgClosure_eq_gStar`** and **`adversaryView_eq_gStar`** — hiding with the
  bounded closure yields *the same expression* as hiding with the unbounded `𝖦*`.  So
  `adversaryView` — the pattern, which is all `symIndistinguishable` compares — is the
  paper's, not an approximation of it.

### Why the bound is forced, recorded in the module docstring

`adversaryKeys` is a `greatestFixpoint`, and `greatestFixpoint` is a constructive
Knaster–Tarski iterating downward with `termination_by S.card`.  So `keyRecovery` must be
`Finset → Finset`, and `𝖦*({k})` is infinite — an unbounded closure cannot be typed there.
Computability and `#eval` are consequences, not the motivation.

### What remains different, and why it is harmless

Membership for keys that do **not** occur in `p`.  Real rather than hypothetical:
`scratch/probes/DupTrailing.lean` computes `Garble Dup true`, whose `keySubterms` is `{K₁}` while
its output labels are `(b, G0 K₀, G0 K₁)` and `(b, G1 K₀, G1 K₁)` — LM18 recovers exactly
one key of each pair, the bounded closure recovers neither.  That is why `LabelInvariant S`
was relativised to `LabelInvariantIn U S`.  With `adversaryView_eq_gStar` in hand the
relativisation is now *justified* rather than merely explained: a key occurring nowhere
affects no pattern, so the guard costs nothing.

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

### Added — `Garbling/Security/Security.lean`

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
`Roots(Keys(view)) ⊆ 𝐊` fails (`scratch/probes/GarbleSideCondition.lean`).  That is exactly LM18
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
* `Garbling/Security/Security.lean` (new): **`garblingSecure`** — composing it with `theorem5` gives
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
invariant quantifies over exactly those.  `scratch/probes/DupTrailing.lean` exhibits it: for
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

`PRGExtension/Garbling/Correctness/Correctness.lean`: `parseEncodedBundleCorrect`,
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
`scratch/probes/GarbleSideCondition.lean` now confirms the general case is genuinely reached:
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

`scratch/checks/GarbleCorrectness.lean` checks `Theorem4` by `#eval` on *every* input of `notC`,
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

`scratch/probes/GarbleSideCondition.lean` computes `Garble andC (true,true)` (a `NAnd` feeding a
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

**File:** `PRGExtension/Expression/ComputationalSemantics/Games.lean`

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
(`scratch/probes/TwoGateFixpoint.lean`): the fixpoint, the recovered key set and the hidden
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

`scratch/probes/TwoGateFixpoint.lean` exhibits a two-gate garbled circuit whose fixpoint has the
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
strengthening. That was wrong. `scratch/findings/ExtractKeysSelfCounterexample.lean` computes:

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

* `scratch/probes/TwoGateFixpoint.lean` — builds `Garble(NAnd ⋙ Dup ⋙ NAnd, (0,0))`, unrolls the
  greatest-fixpoint iteration, and prints `adversaryKeys`, `Keys(adversaryView e)`,
  `Roots(…)` and the non-atomic roots. Doubles as a regression test on `exprKeys`,
  `strictYields`, `isAtomicKey` and `keyRecovery`.
* `scratch/findings/ExtractKeysSelfCounterexample.lean` — the counterexample above.

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
