# Symbolic Cryptography in Lean

This project provides a **PRG-based symbolic cryptography library in Lean** (modeled on the original Lean framework and following the pen-and-paper formalization by [LM18]).

This repository is based on the paper:

> *Computationally-Sound Symbolic Cryptography in Lean*  
> S. Dziembowski, G. Fabiański, D. Micciancio, and R. Stefański  
> (accepted to CSF 2026; a preprint available at [Cryptology ePrint Archive](https://eprint.iacr.org/2025/1700))

We recommend reading the project report and the paper it was based on as it provides the high-level overview and the intuition behind the formalization.

Documents, shortest first:

| file | what it is |
| --- | --- |
| [`summary.tex`](summary.tex) | general overview of the whole development, for cryptographers — 9 pages; builds with **any** engine |
| [`summary.md`](summary.md) | deviations from the pen-and-paper proofs, the proof chain, and the adversary model |
| [`report.md`](report.md) | file-by-file guide and the defect analysis |
| [`writeup.tex`](writeup.tex) / [`writeup.md`](writeup.md) | the full report: proof structure, worked example, LM18 conformance, SymGC measurements |
| [`FUTURE-WORK.md`](FUTURE-WORK.md) | what is not done, with cost estimates |
| [`CHANGELOG.md`](CHANGELOG.md) | dated record of every change |

`writeup.tex` builds with **LuaLaTeX or XeLaTeX** (not pdfLaTeX — it loads `fontspec`); on
Overleaf set the compiler in *Menu → Compiler*.

## Building the Project

To build the project (i.e. to verify the proofs), run `lake build` from the root directory of this repository.

## File Structure

Below is a brief description of the main files in this directory, along with their dependencies.

### VCVio2

Our project depends on the VCVio library, introduced in [TH24], to define computations that can query an oracle. The `VCVio2` folder contains a fragment of this library, specifically the part that defines such computations. We had some troubles building the original library, so 
we have modified the original code by removing parts that we did not need for our project, and making small fixes to make it compatible with our versions of Lean and Mathlib.

### PRGExtension/ComputationalIndistinguishability

This folder defines computational indistinguishability and develops some basic properties.

1. `Def.lean` defines computational indistinguishability between two oracles. It also defines indistinguishability between two families of distributions. These definitions rely on an abstract notion of complexity which captures all allowed adversarial behavior(called PolynomialTime, as commonly assumed in cryptography). For more details, see the original paper.
2. `Lemmas.lean` proves basic properties of indistinguishability, such as transitivity and symmetry. It also includes the lemma
   `IndistinguishabilityByReduction`, which shows how to use reductions to prove indistinguishability.

### PRGExtension/Core

This folder contains general mathematical results used in the project:

1. `Fixpoints.lean` proves a constructive version of the Knaster–Tarski theorem, showing the existence of fixpoints in
   a lattice of finite sets.
2. `CardinalityLemmas.lean` contains auxiliary lemmas about the cardinality of sets.

### PRGExtension/Expression

This module defines the expression language used in symbolic cryptography, based on [LM18]:

1. `Defs.lean` defines expressions (type `Expression`).
2. `Renamings.lean` defines the valid variable renaming.
3. `SymbolicIndistinguishability.lean` defines symbolic indistinguishability between expressions (in particular it defines the `normalizeExpr` function that computes the normal form of an expression, and `adversaryView` which hides the parts of an expression that are not available to the adversary).

The `Expression/Lemmas` submodule contains various auxiliary lemmas:

1. `NormalizeIdempotent.lean` proves that expression normalization is idempotent.
2. `Renaming.lean` contains lemmas about commuting renaming and normalization.
3. `HideEncrypted.lean` focuses on properties of `adversaryKeys`, such as bounds and dependence only on the keys used in an expression.

The `Expression/ComputationalSemantics` submodule contains the following files:

1. `Def.lean` defines the computational semantics of an expression, i.e. a function that maps an expression (and an encryption scheme) to a distribution over bitstrings.
2. `NormalizePreserves.lean` and `RenamePreserves.lean` prove that normalization and renaming do not change the computational semantics.
3. `Games.lean` defines the two primitive security games: IND-CPA security for encryption schemes (`encryptionSchemeIndCpa`) and security of the PRG (`prgSchemeSecure`).
4. `Soundness.lean` proves the soundness theorem: if two expressions are symbolically indistinguishable, then their computational semantics (distributions over bitstrings)  are computationally indistinguishable. The technical details of this proof are in `SoundnessProof`.
5. `Efficiency/` holds the efficiency layer — `PolyTime.lean`, `CostModel.lean` and `GeneratedPolyTime.lean` — which discharges the reductions' poly-time hypotheses.
6. `Executable/` holds the refinement to running code — `Executable.lean` (`ExecEnc`, and the support refinement), `ExecutableDistribution.lean` (the distributional refinement `execDistr_eq`) and `SeededEnvironment.lean` (expanding wire keys from one seed).

### (Omitted) Symbolic Security of Garbled Circuits

This showcases the symbolic approach to cryptography by proving the security of a garbled circuit scheme (following the lines of [LM18]).
Thanks to the soundness theorem, this boils down to proving symbolic indistinguishability. See original framework.

1. `Circuits.lean` – Defines circuits inductively. The main definitions are the `Circuit` type and the `evalCircuit` function.
2. `GarblingDef.lean` – Defines the garbling scheme. The main definitions are:
   * `Garble`: garbles the circuit,
   * `GEval`: evaluates the garbled circuit symbolically.
3. `Simulate.lean` – Defines the simulation procedure (`Simulate`), used to establish the security of garbling.
4. `Security/` – Proves the security of the garbling scheme. Thanks to the soundness theorem, the main goal here is to prove symbolic indistinguishability. `Security/Security.lean` has the main lemma `garblingSecure`; `Security/SecurityFromPrimitives.lean` has `garblingSecureRelative`, the statement to cite; `Security/ExecutableSecurity.lean` carries it to the distributions an implementation actually produces.
5. `Correctness/` – Proves correctness at three levels: `Correctness/Correctness.lean` symbolically (`garbleCorrect`), `Correctness/ComputationalCorrectness.lean` over bit strings (`garbleCorrectComp`), and `Correctness/ExecutableCorrectness.lean` for code that runs (`garbleExecCorrect`).

The proof of symbolic security depends on the results from  `SymbolicHiding/` submodule:

* `GarbleProof.lean` characterizes the output of `adversaryKeys garbledCircuit`.
* `GarbleHole.lean` characterizes the output of `adversaryView garbledCircuit`.
* `SimulateProof.lean` analogous to `GarbleProof.lean` and `GarbleHole.lean`, but for the simulated garbled circuit.
* `GarbleHoleBitSwap.lean` constructs explicitly a variable renaming maps from the actual garbled circuit to the simulated one.

### PRGExtension/Crypto

Concrete instantiations, so that the interfaces are inhabited by something real rather than a toy.

1. `ChaCha20.lean` gives ChaCha20 (RFC 8439) in pure Lean and instantiates both primitives at κ = 256: `chacha20Enc` (counter mode, nonce as coins) and `chacha20Prg` (the two halves of one keystream block). Correctness is proved; agreement with RFC 8439 is validated by test vectors against OpenSSL (`scratch/checks/ChaCha20Kat.lean`); security is assumed.
2. `StreamCipher.lean` isolates `prfFunctions`, the keyed keystream generator the cipher is built from, and shows `chacha20Enc` *is* the generic counter-mode construction over it (`chacha20Enc_eq`, by `rfl`). `prgOfPrf` and `chacha20Prg_eq` show the length-doubling PRG is that same generator at nonce zero — one primitive seen through two interfaces.
3. `Ggm.lean` gives the Goldreich–Goldwasser–Micali tree, which turns a `prgFunctions` into a `prfFunctions` and hence into an encryption scheme built from the PRG alone. Construction only — the security theorems for both routes are scoped in `FUTURE-WORK.md`.
4. `DomainSeparation.lean` reserves one nonce bit so that the cipher and the PRG — which `StreamCipher.lean` proves are one primitive — provably query it at disjoint inputs. `dsNonceDisjoint` is the theorem; `chacha20EncDS` / `chacha20PrgDS` are the instance. See `FUTURE-WORK.md` R2.

Neither file adds an assumption or changes an existing statement: `garblingSecure` and its relatives still take the encryption scheme and the PRG as independent parameters.

## DEMO
This artifact is essentially a library for computationally-sound, symmetric-key cryptography. Garbling/ is complete with symbolic security, symbolic and computational correctness, projectivity, and an executable implementation.

## Bibliography

[LM18]: Li, Baiyu, and Daniele Micciancio. "Symbolic security of garbled circuits." 2018 IEEE 31st Computer Security Foundations Symposium (CSF). IEEE, 2018.
[TH24] Devon Tuma and Nicholas Hopper. 2024. VCVio: A Formally Verified Forking Lemma and Fiat-Shamir Transform, via a
Flexible and Expressive Oracle Representation. IACR Cryptol. ePrint Arch. (2024), 1819. <https://eprint.iacr.org/2024/1819>

## License

This project is distributed under the MIT License.  
However, the `VCVio2/` directory contains modified code from the
[VCVio library](https://github.com/Verified-zkEVM/VCV-io), introduced in [TH24], which is
licensed under the Apache License 2.0 (see `VCVio2/LICENSE-APACHE`).
