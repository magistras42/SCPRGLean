import PRGExtension.Garbling.Correctness.ComputationalCorrectness

/-!
# Feasibility probe: PRNG monad + refinement (CHECKPOINT §3.2)

**Superseded 2026-09-28.**  The estimate below was acted on: `ExecScheme`, `evalExprExec` and
`evalExprExec_mem_support` now live in
`PRGExtension/Expression/ComputationalSemantics/Executable/Executable.lean`, the lift over the sampled
environment and the composition with `garbleCorrectComp` in
`PRGExtension/Garbling/Correctness/ExecutableCorrectness.lean`, and `scratch/checks/ExecDemo.lean` runs the result.
This file is kept only as the record of the probe.

Not part of the library.  Evidence for the effort estimate on the executable-implementation
project.  Run with `lake env lean scratch/archive/PrngFeasibility.lean`.

**What this file establishes.**  The *support-level* half of the refinement is easy, and is
done here end to end in under a hundred lines:

* `ExecScheme` — the executable counterpart of a scheme's encryption: explicit coins plus the
  law that each output is one the `PMF` could have produced.  This has to be *required* of a
  scheme, not derived: `encryptionFunctions.encrypt` is an arbitrary `PMF`, and it is the only
  source of randomness in `evalExpr` (every other case is `PMF.pure`).
* `evalExprExec` — the same recursion as `evalExpr` with a coin supply threaded through.
  **Computable**: no `noncomputable` marker, no `PMF`.
* `evalExprExec_mem_support` — every value it produces lies in the support of `evalExpr`.

Since `garbleCorrectComp` is stated over the *support*, that is already enough to transport
correctness to an executable implementation.

**What it does not establish.**  The *distributional* refinement — needed for security, which
is a statement about distributions — is a different order of work.  Its crux, that a uniform
distribution on a product splits into independent uniforms, is **not in Mathlib** (checked);
the closest precedent is this repo's own `resampleIsTrivial` / `extendRenameRestrictKUniform`
in `RenamePreserves.lean`, each about a hundred lines of `ENNReal` and cardinality arithmetic.
-/

namespace PRG

/-- An executable counterpart of a scheme's encryption: explicit coins, plus the law that the
result is one the `PMF` could have produced. -/
structure ExecScheme {κ : ℕ} (enc : encryptionFunctions κ) where
  randLen : ℕ → ℕ
  run : {n : ℕ} → BitVector κ → BitVector n → BitVector (randLen n) → BitVector (enc.encryptLength n)
  mem_support : ∀ {n : ℕ} (k : BitVector κ) (m : BitVector n) (r : BitVector (randLen n)),
    run k m r ∈ (enc.encrypt k m).support

variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}

/-- Executable evaluator: same recursion as `evalExpr`, with a coin supply indexed by node and
a counter threaded through.  Computable — no `PMF` anywhere. -/
def evalExprExec (ex : ExecScheme enc) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → (n : ℕ) → BitVector (ex.randLen n)) :
    {s : Shape} → Expression s → ℕ → BitVector (shapeLength κ enc s) × ℕ
  | _, Expression.Eps, i => (List.Vector.nil, i)
  | _, Expression.BitE b, i => (List.Vector.cons (evalBitExpr bVars b) List.Vector.nil, i)
  | _, Expression.VarK k, i => (kVars k, i)
  | _, Expression.Pair e₁ e₂, i =>
      let r₁ := evalExprExec ex prg kVars bVars coins e₁ i
      let r₂ := evalExprExec ex prg kVars bVars coins e₂ r₁.2
      (List.Vector.append r₁.1 r₂.1, r₂.2)
  | _, Expression.G0 k, i =>
      let r := evalExprExec ex prg kVars bVars coins k i
      (prg.prg0 r.1, r.2)
  | _, Expression.G1 k, i =>
      let r := evalExprExec ex prg kVars bVars coins k i
      (prg.prg1 r.1, r.2)
  | _, Expression.Perm (Expression.BitE b) e₁ e₂, i =>
      let r₁ := evalExprExec ex prg kVars bVars coins e₁ i
      let r₂ := evalExprExec ex prg kVars bVars coins e₂ r₁.2
      (if evalBitExpr bVars b then List.Vector.append r₂.1 r₁.1
       else List.Vector.append r₁.1 r₂.1, r₂.2)
  | _, Expression.Enc k e, i =>
      let re := evalExprExec ex prg kVars bVars coins e i
      let rk := evalExprExec ex prg kVars bVars coins k re.2
      (ex.run rk.1 re.1 (coins rk.2 _), rk.2 + 1)
  | _, Expression.Hidden k, i =>
      let rk := evalExprExec ex prg kVars bVars coins k i
      (ex.run rk.1 ones (coins rk.2 _), rk.2 + 1)


/-- **Support refinement.**  Every value the executable evaluator produces is one the
distribution could have produced. -/
theorem evalExprExec_mem_support (ex : ExecScheme enc) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → (n : ℕ) → BitVector (ex.randLen n)) :
    ∀ {s : Shape} (e : Expression s) (i : ℕ),
      (evalExprExec ex prg kVars bVars coins e i).1
        ∈ (evalExpr enc prg kVars bVars e).support
  | _, Expression.Eps, i => by simp [evalExprExec, evalExpr]
  | _, Expression.BitE b, i => by simp [evalExprExec, evalExpr]
  | _, Expression.VarK k, i => by simp [evalExprExec, evalExpr]
  | _, Expression.Pair e₁ e₂, i => by
      refine (mem_support_pair_iff e₁ e₂ _).mpr ⟨_, ?_, _, ?_, rfl⟩
      · exact evalExprExec_mem_support ex prg kVars bVars coins e₁ i
      · exact evalExprExec_mem_support ex prg kVars bVars coins e₂
          (evalExprExec ex prg kVars bVars coins e₁ i).2
  | _, Expression.G0 k, i => by
      have ih := evalExprExec_mem_support ex prg kVars bVars coins k i
      simp only [evalExprExec, evalExpr, Bind.bind, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Pure.pure]
      exact ⟨_, ih, rfl⟩
  | _, Expression.G1 k, i => by
      have ih := evalExprExec_mem_support ex prg kVars bVars coins k i
      simp only [evalExprExec, evalExpr, Bind.bind, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Pure.pure]
      exact ⟨_, ih, rfl⟩
  | _, Expression.Perm (Expression.BitE b) e₁ e₂, i => by
      have ih₁ := evalExprExec_mem_support ex prg kVars bVars coins e₁ i
      have ih₂ := evalExprExec_mem_support ex prg kVars bVars coins e₂
        (evalExprExec ex prg kVars bVars coins e₁ i).2
      simp only [evalExprExec, evalExpr, Bind.bind, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Pure.pure]
      refine ⟨_, ih₁, _, ih₂, ?_⟩
      show (if evalBitExpr bVars b then _ else _) ∈ _
      split <;> simp
  | _, Expression.Enc k e, i => by
      have ihe := evalExprExec_mem_support ex prg kVars bVars coins e i
      have ihk := evalExprExec_mem_support ex prg kVars bVars coins k
        (evalExprExec ex prg kVars bVars coins e i).2
      simp only [evalExprExec, evalExpr, Bind.bind, PMF.mem_support_bind_iff]
      exact ⟨_, ihe, _, ihk, ex.mem_support _ _ _⟩
  | _, Expression.Hidden k, i => by
      have ihk := evalExprExec_mem_support ex prg kVars bVars coins k i
      simp only [evalExprExec, evalExpr, Bind.bind, PMF.mem_support_bind_iff]
      exact ⟨_, ihk, ex.mem_support _ _ _⟩

end PRG
