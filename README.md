# Symbolic Cryptography in Lean

This project provides a **symbolic cryptography library in Lean**, together with a **formally verified computational soundness theorem** and a **formally verified symbolic proof of security for the garbled circuit scheme** (based on [LM18]).

This repository accompanies the paper:

> *Computationally-Sound Symbolic Cryptography in Lean*  
> S. Dziembowski, G. Fabiański, D. Micciancio, and R. Stefański  
> (under submission; a preprint available at [Cryptology ePrint Archive](https://eprint.iacr.org/2025/1700))

We recommend reading the paper as it provides the high-level overview and the intuition behind the formalization.

## Building the Project

To build the project (i.e. to verify the proofs), run `lake build` from the root directory of this repository.

## File Structure

Below is a brief description of the main files in this directory, along with their dependencies.

### VCVio2

Our project depends on the VCVio library, introduced in [TH24], to define computations that can query an oracle. The `VCVio2` folder contains a fragment of this library, specifically the part that defines such computations. We had some troubles building the original library, so 
we have modified the original code by removing parts that we did not need for our project, and making small fixes to make it compatible with our versions of Lean and Mathlib.

### ComputationalIndistinguishability

This folder defines computational indistinguishability and develops some basic properties.

1. `Def.lean` defines computational indistinguishability between two oracles. It also defines indistinguishability between two families of distributions. These definitions rely on an abstract notion of complexity which captures all allowed adversarial behavior(called PolynomialTime, as commonly assumed in cryptography). For more details, see our paper.
2. `Lemmas.lean` proves basic properties of indistinguishability, such as transitivity and symmetry. It also includes the lemma
   `IndistinguishabilityByReduction`, which shows how to use reductions to prove indistinguishability.

### Core

This folder contains general mathematical results used in the project:

1. `Fixpoints.lean` proves a constructive version of the Knaster–Tarski theorem, showing the existence of fixpoints in
   a lattice of finite sets.
2. `CardinalityLemmas.lean` contains auxiliary lemmas about the cardinality of sets.

### Expression

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
3. `EncryptionIndCpa.lean` defines the notion of IND-CPA security for encryption schemes.
4. `Soundness.lean` proves the soundness theorem: if two expressions are symbolically indistinguishable, then their computational semantics (distributions over bitstrings)  are computationally indistinguishable. The technical details of this proof are in `SoundnessProof`.

### Symbolic Security of Garbled Circuits

This showcases the symbolic approach to cryptography by proving the security of a garbled circuit scheme (following the lines of [LM18]).
Thanks to the soundness theorem, this boils down to proving symbolic indistinguishability.

1. `Circuits.lean` – Defines circuits inductively. The main definitions are the `Circuit` type and the `evalCircuit` function.
2. `GarblingDef.lean` – Defines the garbling scheme. The main definitions are:
   * `Garble`: garbles the circuit,
   * `GEval`: evaluates the garbled circuit symbolically.
3. `Simulation.lean` – Defines the simulation procedure (`SimulateG`), used to establish the security of garbling.
4. `Security.lean` – Proves the security of the garbling scheme. Thanks to the soundness theorem, the main goal here is to prove symbolic indistinguishability. The main lemma is `garblingSecure`.
5. `Correctness.lean` – Proves the correctness of the garbling scheme at the symbolic level. The main lemma is `garbleCorrect`.

The proof of symbolic security depends on the results from  `SymbolicHiding/` submodule:

* `GarbleProof.lean` characterizes the output of `adversaryKeys garbledCircuit`.
* `GarbleHole.lean` characterizes the output of `adversaryView garbledCircuit`.
* `SimulateProof.lean` analogous to `GarbleProof.lean` and `GarbleHole.lean`, but for the simulated garbled circuit.
* `GarbleHoleBitSwap.lean` constructs explicitly a variable renaming maps from the actual garbled circuit to the simulated one.

## Bibliography

[LM18]: Li, Baiyu, and Daniele Micciancio. "Symbolic security of garbled circuits." 2018 IEEE 31st Computer Security Foundations Symposium (CSF). IEEE, 2018.
[TH24] Devon Tuma and Nicholas Hopper. 2024. VCVio: A Formally Verified Forking Lemma and Fiat-Shamir Transform, via a
Flexible and Expressive Oracle Representation. IACR Cryptol. ePrint Arch. (2024), 1819. <https://eprint.iacr.org/2024/1819>

## License

This project is distributed under the MIT License.  
However, the `VCVio2/` directory contains modified code from the
[VCVio library](https://github.com/Verified-zkEVM/VCV-io), introduced in [TH24], which is
licensed under the Apache License 2.0 (see `VCVio2/LICENSE-APACHE`).
