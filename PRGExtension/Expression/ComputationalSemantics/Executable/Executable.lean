import PRGExtension.Expression.ComputationalSemantics.Def

/-!
# An executable interpretation of the computational semantics

`evalExpr` is `PMF`-valued and `PMF` is `ENNReal`-valued, so the computational semantics is
`noncomputable` — not by choice but by the decision to model distributions measure-
theoretically.  Nothing at that layer can be `#eval`'d.  This file gives the semantics a
second, **computable** interpretation and proves it refines the first.

* `ExecScheme` — the executable counterpart of a scheme's encryption: explicit coins, plus the
  law that each output is one the `PMF` could have produced.  This has to be *required* of a
  scheme rather than derived: `encryptionFunctions.encrypt` is an arbitrary `PMF`.
* `evalExprExec` / `evalExprRun` — the same recursion as `evalExpr` with a coin supply threaded
  through.  Computable: no `noncomputable` marker, no `PMF`.
* `evalExprExec_mem_support` — **the refinement.**  Every value the executable evaluator
  produces lies in the support of the distribution the specification assigns.
* `evalExprRun_mem_support_exprToDistr` — the same statement one level up, against
  `exprToDistr` / `exprToFamDistr`, which close `evalExpr` over a uniformly sampled
  environment.

Two structural facts make this cheap, and both are visible in the recursion below.  `evalExpr`
is deterministic **except** at `enc.encrypt` — every other case is `PMF.pure` — so the only
randomness to thread is the encryption coins plus the environment.  And `garbleCorrectComp` is
stated over the distribution's *support*, so this support-level refinement is already enough to
transport correctness to running code; see `Garbling/Correctness/ExecutableCorrectness.lean`.

**What this does not give: security.**  Security is a statement about distributions, not about
individual outputs, so transporting it needs a *distributional* refinement —
`(uniform coins).map (ex.run k m) = enc.encrypt k m` in place of `ExecScheme.mem_support`, a
coin-count measure on expressions, and a change-of-variables induction whose crux (a uniform
distribution on a product splits into independent uniforms) is not in Mathlib.  `FUTURE-WORK.md`
scopes that; `garblingSecureRelative` remains a theorem about `exprToFamDistr`, i.e. about the
specification rather than about the code.
-/

namespace PRG

/-- An executable counterpart of a scheme's encryption: explicit coins, plus the law that the
result is one the `PMF` could have produced.

`randLen` is how many coins one encryption consumes — a constant, not a function of the message
length.  That is what every real scheme looks like (a nonce or IV is a scheme parameter), and it
is forced if the coins are ever to be *drawn*: a supply of type `(n : ℕ) → BitVector (randLen n)`
is an infinite dependent product, so no distribution over it is expressible.  A deterministic
scheme takes `randLen = 0`.  This is a genuine, if modest, strengthening of what a scheme must
supply — `encryptionFunctions.encrypt` is an arbitrary `PMF`, so nothing derives it. -/
structure ExecScheme {κ : ℕ} (enc : encryptionFunctions κ) where
  /-- Coins consumed by one encryption of an `n`-bit message. -/
  randLen : ℕ
  /-- Encryption as a function of key, message and coins. -/
  run : {n : ℕ} → BitVector κ → BitVector n → BitVector randLen →
    BitVector (enc.encryptLength n)
  /-- Every output is one the specification's `PMF` could have produced. -/
  mem_support : ∀ {n : ℕ} (k : BitVector κ) (m : BitVector n) (r : BitVector randLen),
    run k m r ∈ (enc.encrypt k m).support

variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}

/-- **The executable evaluator**, over the data it actually needs: a ciphertext-length
function, a coin count, and encryption as a function of key, message and coins.

Phrased this way rather than over an `encryptionFunctions` because it has to *run*: no concrete
`encryptionFunctions` is computable (`encrypt` is `PMF`-valued and `PMF.pure` has no executable
code), and the lengths are not merely type decoration — `vecTake` / `vecDrop` consume them as
data.  `ExecEnc` below packages exactly these fields, and `evalExprExec` is this at a
specification scheme.

The counter is incremented once per `Enc`/`Hidden` node and never reused, so distinct
encryptions draw distinct coins; that is what a caller must arrange for the result to be worth
anything, and what the distributional refinement would have to reason about. -/
def evalExprExecOn {κ : ℕ} (encLen : ℕ → ℕ) (randLen : ℕ)
    (run : {n : ℕ} → BitVector κ → BitVector n → BitVector randLen → BitVector (encLen n))
    (prg : prgFunctions κ) (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector randLen) :
    {s : Shape} → Expression s → ℕ → BitVector (shapeLengthOn κ encLen s) × ℕ
  | _, Expression.Eps, i => (List.Vector.nil, i)
  | _, Expression.BitE b, i => (List.Vector.cons (evalBitExpr bVars b) List.Vector.nil, i)
  | _, Expression.VarK k, i => (kVars k, i)
  | _, Expression.Pair e₁ e₂, i =>
      let r₁ := evalExprExecOn encLen randLen run prg kVars bVars coins e₁ i
      let r₂ := evalExprExecOn encLen randLen run prg kVars bVars coins e₂ r₁.2
      (List.Vector.append r₁.1 r₂.1, r₂.2)
  | _, Expression.G0 k, i =>
      let r := evalExprExecOn encLen randLen run prg kVars bVars coins k i
      (prg.prg0 r.1, r.2)
  | _, Expression.G1 k, i =>
      let r := evalExprExecOn encLen randLen run prg kVars bVars coins k i
      (prg.prg1 r.1, r.2)
  | _, Expression.Perm (Expression.BitE b) e₁ e₂, i =>
      let r₁ := evalExprExecOn encLen randLen run prg kVars bVars coins e₁ i
      let r₂ := evalExprExecOn encLen randLen run prg kVars bVars coins e₂ r₁.2
      (if evalBitExpr bVars b then List.Vector.append r₂.1 r₁.1
       else List.Vector.append r₁.1 r₂.1, r₂.2)
  | _, Expression.Enc k e, i =>
      let re := evalExprExecOn encLen randLen run prg kVars bVars coins e i
      let rk := evalExprExecOn encLen randLen run prg kVars bVars coins k re.2
      (run rk.1 re.1 (coins rk.2), rk.2 + 1)
  | _, Expression.Hidden k, i =>
      let rk := evalExprExecOn encLen randLen run prg kVars bVars coins k i
      (run rk.1 ones (coins rk.2), rk.2 + 1)

/-- The executable evaluator at a specification scheme; *delta*-equal to `evalExprExecOn`. -/
def evalExprExec (ex : ExecScheme enc) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen) :
    {s : Shape} → Expression s → ℕ → BitVector (shapeLength κ enc s) × ℕ :=
  evalExprExecOn enc.encryptLength ex.randLen ex.run prg kVars bVars coins

/-- Run the executable evaluator from a fresh counter and keep the value. -/
def evalExprRun (ex : ExecScheme enc) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen) {s : Shape} (e : Expression s) :
    BitVector (shapeLength κ enc s) :=
  (evalExprExec ex prg kVars bVars coins e 0).1

/-- **The refinement.**  Every value the executable evaluator produces is one the distribution
could have produced.  Structural recursion over the expression; the only interesting arms are
`Enc`/`Hidden`, where the implementation's support law is consumed. -/
theorem evalExprExecOn_mem_support {κ : ℕ} (enc : encryptionFunctions κ) (randLen : ℕ)
    (run : {n : ℕ} → BitVector κ → BitVector n → BitVector randLen →
      BitVector (enc.encryptLength n))
    (hrun : ∀ {n : ℕ} (k : BitVector κ) (m : BitVector n) (r : BitVector randLen),
      run k m r ∈ (enc.encrypt k m).support)
    (prg : prgFunctions κ) (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector randLen) :
    ∀ {s : Shape} (e : Expression s) (i : ℕ),
      (evalExprExecOn enc.encryptLength randLen run prg kVars bVars coins e i).1
        ∈ (evalExpr enc prg kVars bVars e).support
  | _, Expression.Eps, i => by simp [evalExprExecOn, evalExpr]
  | _, Expression.BitE b, i => by simp [evalExprExecOn, evalExpr]
  | _, Expression.VarK k, i => by simp [evalExprExecOn, evalExpr]
  | _, Expression.Pair e₁ e₂, i => by
      have ih₁ := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins e₁ i
      have ih₂ := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins e₂
        (evalExprExecOn enc.encryptLength randLen run prg kVars bVars coins e₁ i).2
      simp only [evalExprExecOn, evalExpr, Bind.bind, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Pure.pure]
      exact ⟨_, ih₁, _, ih₂, rfl⟩
  | _, Expression.G0 k, i => by
      have ih := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins k i
      simp only [evalExprExecOn, evalExpr, Bind.bind, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Pure.pure]
      exact ⟨_, ih, rfl⟩
  | _, Expression.G1 k, i => by
      have ih := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins k i
      simp only [evalExprExecOn, evalExpr, Bind.bind, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Pure.pure]
      exact ⟨_, ih, rfl⟩
  | _, Expression.Perm (Expression.BitE b) e₁ e₂, i => by
      have ih₁ := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins e₁ i
      have ih₂ := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins e₂
        (evalExprExecOn enc.encryptLength randLen run prg kVars bVars coins e₁ i).2
      simp only [evalExprExecOn, evalExpr, Bind.bind, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Pure.pure]
      refine ⟨_, ih₁, _, ih₂, ?_⟩
      show (if evalBitExpr bVars b then _ else _) ∈ _
      split <;> simp
  | _, Expression.Enc k e, i => by
      have ihe := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins e i
      have ihk := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins k
        (evalExprExecOn enc.encryptLength randLen run prg kVars bVars coins e i).2
      simp only [evalExprExecOn, evalExpr, Bind.bind, PMF.mem_support_bind_iff]
      exact ⟨_, ihe, _, ihk, hrun _ _ _⟩
  | _, Expression.Hidden k, i => by
      have ihk := evalExprExecOn_mem_support enc randLen run hrun prg kVars bVars coins k i
      simp only [evalExprExecOn, evalExpr, Bind.bind, PMF.mem_support_bind_iff]
      exact ⟨_, ihk, hrun _ _ _⟩

/-- The refinement at an `ExecScheme`. -/
theorem evalExprExec_mem_support (ex : ExecScheme enc) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen) :
    ∀ {s : Shape} (e : Expression s) (i : ℕ),
      (evalExprExec ex prg kVars bVars coins e i).1
        ∈ (evalExpr enc prg kVars bVars e).support :=
  fun e i =>
    evalExprExecOn_mem_support enc ex.randLen ex.run ex.mem_support prg kVars bVars coins e i

/-!
### Lifting the refinement over the environment

`evalExpr` takes the environment as a parameter; `exprToDistr` samples it uniformly over the
variables the expression actually mentions (`getMaxVar e + 1` of each kind) and `exprToFamDistr`
does that at every security parameter.  An implementation supplies the environment from real
randomness, so the statement it needs is that *any* such environment lands in the support —
which is immediate, since a uniform distribution on a nonempty finite type has full support.
-/

/-- **The refinement against `exprToDistr`.**  Whatever key/bit environment and coins an
implementation draws, the value it computes is one `exprToDistr` could have produced. -/
theorem evalExprRun_mem_support_exprToDistr (ex : ExecScheme enc) (prg : prgFunctions κ)
    {s : Shape} (e : Expression s)
    (kvars : Fin (getMaxVar e + 1) → BitVector κ) (bvars : Fin (getMaxVar e + 1) → Bool)
    (coins : ℕ → BitVector ex.randLen) :
    evalExprRun ex prg (extendFin ones kvars) (extendFin false bvars) coins e
      ∈ (exprToDistr enc prg e).support := by
  simp only [exprToDistr, evalExprVarsL, Bind.bind, PMF.mem_support_bind_iff]
  exact ⟨bvars, PMF.mem_support_uniformOfFintype _, kvars, PMF.mem_support_uniformOfFintype _,
    evalExprExec_mem_support ex prg _ _ coins e 0⟩

/-- The same at a fixed security parameter of a scheme *family*, which is the form
`exprToFamDistr` — and hence every security statement in the development — is stated in. -/
theorem evalExprRun_mem_support_exprToFamDistr {encF : encryptionScheme} {prgF : prgScheme}
    (κ : ℕ) (ex : ExecScheme (encF κ)) {s : Shape} (e : Expression s)
    (kvars : Fin (getMaxVar e + 1) → BitVector κ) (bvars : Fin (getMaxVar e + 1) → Bool)
    (coins : ℕ → BitVector ex.randLen) :
    evalExprRun ex (prgF κ) (extendFin ones kvars) (extendFin false bvars) coins e
      ∈ (exprToFamDistr encF prgF e κ).support :=
  evalExprRun_mem_support_exprToDistr ex (prgF κ) e kvars bvars coins

/-!
## An implementation, and the specification derived from it

`ExecScheme` above answers "here is a specification; can it be run?".  `ExecEnc` answers the
question an implementer actually has: "here is running code; what does it specify?".  The
difference is not cosmetic — it is what makes `#eval` possible.

`ExecScheme enc` is a structure *over* a scheme, so every function taking one also takes `enc`,
and Lean erases only `Sort`- and `Prop`-valued arguments.  Since no concrete
`encryptionFunctions` is computable, no compiled call can be handed one.  `ExecEnc` mentions no
specification at all, so it compiles; and `ExecEnc.spec` derives the specification from it, with
`encryptLength` and `decrypt` as *projections of a structure literal*.  Those reduce
definitionally, so `shapeLength κ ex.spec s` is the length computed from `ex` alone and the two
layers agree with no casts anywhere.

The derived `encrypt` is the push-forward of the uniform distribution on coins — which is the
textbook definition of a randomised scheme, and is also exactly the *distributional* law the
security refinement would need (`FUTURE-WORK.md`, Half 2), obtained here by construction rather
than assumed.
-/

/-- **An executable encryption scheme**: no specification mentioned, so it is computable and
`#eval`-able.  `dec_run` is ordinary decryption correctness, which is all that
`decrypt_encrypt` needs. -/
structure ExecEnc (κ : ℕ) where
  /-- Ciphertext length for an `n`-bit message. -/
  encryptLength : ℕ → ℕ
  /-- Coins consumed by one encryption of an `n`-bit message. -/
  randLen : ℕ
  /-- Encryption, as a function of key, message and coins. -/
  run : {n : ℕ} → BitVector κ → BitVector n → BitVector randLen → BitVector (encryptLength n)
  /-- Decryption. -/
  dec : {n : ℕ} → BitVector κ → BitVector (encryptLength n) → BitVector n
  /-- Decryption inverts encryption, whatever coins were used. -/
  dec_run : ∀ {n : ℕ} (k : BitVector κ) (m : BitVector n) (r : BitVector randLen),
    dec k (run k m r) = m

namespace ExecEnc

variable {κ : ℕ}

/-- **The specification an implementation denotes**: encrypt by drawing coins uniformly and
running the code.  `noncomputable` because `PMF` is, but its `encryptLength` and `decrypt` are
projections of a structure literal, so they still reduce. -/
noncomputable def spec (ex : ExecEnc κ) : encryptionFunctions κ where
  encryptLength := ex.encryptLength
  encrypt := fun {n} k m => (PMF.uniformOfFintype (BitVector ex.randLen)).map (ex.run k m)
  decrypt := ex.dec
  decrypt_encrypt := by
    intro n key msg c hc
    simp only [PMF.mem_support_map_iff] at hc
    obtain ⟨r, -, rfl⟩ := hc
    exact ex.dec_run key msg r

/-- The denoted scheme's encryption, in the form the distributional refinement uses: the
push-forward of the uniform distribution on coins.  True by `rfl` — that *is* the definition —
which is why the refinement needs no hypothesis here. -/
theorem spec_encrypt (ex : ExecEnc κ) {n : ℕ} (k : BitVector κ) (m : BitVector n) :
    ex.spec.encrypt k m = (PMF.uniformOfFintype (BitVector ex.randLen)).map (ex.run k m) := rfl

/-- An implementation is an `ExecScheme` for the specification it denotes.  Proof-only: it is
never run, which is why the `noncomputable` marker (forced by `spec` appearing in its type)
costs nothing. -/
noncomputable def toExecScheme (ex : ExecEnc κ) : ExecScheme ex.spec where
  randLen := ex.randLen
  run := ex.run
  mem_support k m r := by
    show _ ∈ (PMF.map _ _).support
    simp only [PMF.mem_support_map_iff]
    exact ⟨r, PMF.mem_support_uniformOfFintype r, rfl⟩

/-- **Evaluate an expression, executably.**  Computable: every argument is data the
implementation has. -/
def evalExprRun (ex : ExecEnc κ) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen) {s : Shape} (e : Expression s) :
    BitVector (shapeLengthOn κ ex.encryptLength s) :=
  (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars coins e 0).1

/-- **The refinement, for running code.**  What the implementation computes is a value the
specification it denotes could have produced. -/
theorem evalExprRun_mem_support (ex : ExecEnc κ) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector ex.randLen) {s : Shape} (e : Expression s) :
    ex.evalExprRun prg kVars bVars coins e ∈ (evalExpr ex.spec prg kVars bVars e).support :=
  evalExprExecOn_mem_support ex.spec ex.randLen ex.run ex.toExecScheme.mem_support
    prg kVars bVars coins e 0

/-- And in the support of `exprToDistr`, for an environment drawn over the variables the
expression mentions. -/
theorem evalExprRun_mem_support_exprToDistr (ex : ExecEnc κ) (prg : prgFunctions κ)
    {s : Shape} (e : Expression s)
    (kvars : Fin (getMaxVar e + 1) → BitVector κ) (bvars : Fin (getMaxVar e + 1) → Bool)
    (coins : ℕ → BitVector ex.randLen) :
    ex.evalExprRun prg (extendFin ones kvars) (extendFin false bvars) coins e
      ∈ (exprToDistr ex.spec prg e).support := by
  simp only [exprToDistr, evalExprVarsL, Bind.bind, PMF.mem_support_bind_iff]
  exact ⟨bvars, PMF.mem_support_uniformOfFintype _, kvars, PMF.mem_support_uniformOfFintype _,
    ex.evalExprRun_mem_support prg _ _ coins e⟩

end ExecEnc

end PRG
