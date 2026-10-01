import PRGExtension.Garbling.Correctness.ComputationalCorrectness
import PRGExtension.Expression.ComputationalSemantics.Executable.Executable

/-!
# A runnable, verified-correct garbling scheme

`garbleCorrectComp` (`Garbling/Correctness/ComputationalCorrectness.lean`) says every bit vector the
garbled circuit *can* take evaluates to `C(x)`.  That is exactly the specification an
implementation has to meet, and `evalExprExec` (`ComputationalSemantics/Executable.lean`)
produces such bit vectors.  Composing the two gives `Garble` and `Evaluate` as functions that
actually run, with correctness proved rather than tested:

* `GarbleExec` — garble, computably, given a key/bit environment and a coin supply.
* `EvaluateComp` — already computable (`ComputationalCorrectness.lean`); nothing to add.
* `garbleExecCorrect` — **`Evaluate(Garble(C,x)) = C(x)`, for the code that runs.**
* `garbleExec_mem_support` — and what it computes is a sample the specification's distribution
  could have produced, so no separate correctness notion has been introduced.
* `garbleExec_projective` — the offline/online split an implementation wants: everything but
  the input-label selection can be computed before `x` is known.

`scratch/checks/ExecDemo.lean` instantiates all of this with a toy `ExecScheme` and `#eval`s it end to
end, which is the point: before this file nothing below the symbolic layer could be run at all.

**Correctness only.**  The randomness here is the caller's to supply, and nothing in
`ExecScheme` constrains how `run` uses its coins beyond landing in the right support — a
scheme with `randLen = 0` and a constant ciphertext satisfies it.  Security remains a
statement about `exprToFamDistr` (`garblingSecureRelative`), i.e. about the specification;
transporting it to the code needs the distributional refinement scoped in `FUTURE-WORK.md`,
and a concrete secure `ExecScheme` needs a real block cipher whose IND-CPA security would be
assumed exactly as it is today.
-/

namespace PRG

variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}
  {kVars : ℕ → BitVector κ} {bVars : ℕ → Bool}

/-- **`Garble`, executably.**  Build the symbolic garbling and run the executable evaluator on
it, with the caller's environment and coins. -/
def GarbleExec (ex : ExecScheme enc) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    BitVector (shapeLength κ enc (garbleShapeFull c)) :=
  evalExprRun ex prg kVars bVars coins (Garble c x)

/-- **Correctness of the executable scheme.**  `Evaluate(Garble(C,x)) = C(x)`, where both
sides are computable functions of the coins.  This is `garbleCorrectComp` discharged at the
one bit vector the implementation actually produces. -/
theorem garbleExecCorrect (ex : ExecScheme enc) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    EvaluateComp enc prg c (GarbleExec ex prg kVars bVars coins c x) = evalCircuit c x :=
  garbleCorrectComp c x _ (evalExprExec_mem_support ex prg kVars bVars coins (Garble c x) 0)

/-- What the implementation computes is a sample of the distribution the specification
assigns to `Garble c x` — the implementation has not been given its own semantics. -/
theorem garbleExec_mem_support (ex : ExecScheme enc) (prg : prgFunctions κ)
    (coins : ℕ → BitVector ex.randLen)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    (kvars : Fin (getMaxVar (Garble c x) + 1) → BitVector κ)
    (bvars : Fin (getMaxVar (Garble c x) + 1) → Bool) :
    GarbleExec ex prg (extendFin ones kvars) (extendFin false bvars) coins c x
      ∈ (exprToDistr enc prg (Garble c x)).support :=
  evalExprRun_mem_support_exprToDistr ex prg (Garble c x) kvars bvars coins

/-- **The executable scheme is projective**, in the form an implementation consumes it: the
garbled tables, the output mask, and both labels of every input wire are computed from the
circuit alone — `x` enters only through `makeProjection`, one wire at a time, which is what
lets the input labels be delivered by oblivious transfer.  The symbolic content is
`Garble_projective`; what this adds is that the *coin threading* respects the split, so the
offline half can be computed and stored before `x` is known. -/
theorem garbleExec_projective (ex : ExecScheme enc) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    GarbleExec ex prg kVars bVars coins c x =
      let g := evalExprExec ex prg kVars bVars coins (preGarble c).1 0
      let i := evalExprExec ex prg kVars bVars coins
        (encodedLabelToExpr (makeProjection (preGarble c).2.2 x)) g.2
      let m := evalExprExec ex prg kVars bVars coins
        (maskedLabelToExpr (preGarble c).2.1) i.2
      List.Vector.append g.1 (List.Vector.append i.1 m.1) := by
  rw [GarbleExec, evalExprRun, Garble_projective c x]
  rfl


/-!
## The `#eval`-able pipeline

Everything above is stated at an `ExecScheme`, i.e. at a *specification* with an executable
encryption attached, and therefore takes an `encryptionFunctions` as a runtime argument — which
no compiled call can supply.  The same results at an `ExecEnc` (an implementation, with the
specification derived from it) mention no specification in any position the compiler sees, so
they run.  Nothing is reproved: `ExecEnc.spec`'s `encryptLength` and `decrypt` are projections
of a structure literal, so `EvaluateComp ex.spec` *is* `EvaluateExec ex` definitionally, and
`garbleCorrectComp` applies unchanged.
-/

namespace ExecEnc

variable {κ : ℕ}

/-- **`Garble`, executably.**  Computable: every argument is data the implementation has. -/
def GarbleExec (ex : ExecEnc κ) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    BitVector (shapeLengthOn κ ex.encryptLength (garbleShapeFull c)) :=
  ex.evalExprRun prg kVars bVars coins (Garble c x)

/-- **`Evaluate`, executably.**  Definitionally `EvaluateComp` at the denoted specification. -/
def EvaluateExec (ex : ExecEnc κ) (prg : prgFunctions κ) {s t : WireBundle} (c : Circuit s t)
    (v : BitVector (shapeLengthOn κ ex.encryptLength (garbleShapeFull c))) : bundleBool t :=
  EvaluateCompOn ex.encryptLength ex.dec prg c v

/-- **Correctness of the executable scheme**: `Evaluate(Garble(C,x)) = C(x)`, where both sides
compute.  The proof is `garbleCorrectComp` at the specification `ex` denotes — no bridge lemma,
because there is no gap to bridge. -/
theorem garbleExecCorrect (ex : ExecEnc κ) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    ex.EvaluateExec prg c (ex.GarbleExec prg kVars bVars coins c x) = evalCircuit c x :=
  garbleCorrectComp (enc := ex.spec) c x _
    (ex.evalExprRun_mem_support prg kVars bVars coins (Garble c x))

/-- And what it computes is a sample of the distribution the denoted specification assigns. -/
theorem garbleExec_mem_support (ex : ExecEnc κ) (prg : prgFunctions κ)
    (coins : ℕ → BitVector ex.randLen)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    (kvars : Fin (getMaxVar (Garble c x) + 1) → BitVector κ)
    (bvars : Fin (getMaxVar (Garble c x) + 1) → Bool) :
    ex.GarbleExec prg (extendFin ones kvars) (extendFin false bvars) coins c x
      ∈ (exprToDistr ex.spec prg (Garble c x)).support :=
  ex.evalExprRun_mem_support_exprToDistr prg (Garble c x) kvars bvars coins

end ExecEnc

end PRG
