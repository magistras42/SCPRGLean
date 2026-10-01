import PRGExtension.Garbling.Security.SecurityFromPrimitives
import PRGExtension.Expression.ComputationalSemantics.Executable.ExecutableDistribution
import PRGExtension.Expression.ComputationalSemantics.Executable.SeededEnvironment

/-!
# Security of the implementation

`garblingSecureRelative` is a theorem about `exprToFamDistr` — about the *specification*.  This
file says the same thing about the distributions an implementation actually produces, which is
the point of the distributional refinement.

The transfer is a rewrite and nothing more: `ExecEncScheme.toFamDistr_eq` says the two families
of distributions are **equal**, so every security statement about one is a security statement
about the other.  That equality is where the work is
(`ComputationalSemantics/ExecutableDistribution.lean`), and it is what the support-level
refinement could not give: `evalExprExecOn_mem_support` would be satisfied by an implementation
that always returned the same ciphertext.

What is *not* claimed.  The hypotheses are unchanged — `encryptionSchemeIndCpa` and
`prgSchemeSecure` for the denoted scheme family, plus the adversary-class conditions — and they
remain assumptions about the primitives.  Note also what an `ExecEncScheme` is: an
implementation at *every* security parameter.  `chacha20Enc` is an `ExecEnc 256` and cannot be one, since ChaCha20's key size is
fixed — which is the concrete-versus-asymptotic mismatch `FUTURE-WORK.md` records, not an
oversight.  What this theorem gives is that the refinement has removed the *specification* from
the security statement; the primitives' hardness is assumed exactly as before.
-/

namespace PRG

/-- **Security of the executable garbling scheme.**  For an implementation family `E`, the
distributions `E` produces on `Garble c x` and on `Simulate c (C x)` are computationally
indistinguishable — under exactly the hypotheses `garblingSecureRelative` needs, about the
scheme family `E` denotes.

This is the statement `FUTURE-WORK.md` called "security of the code rather than security of the
specification". -/
theorem garblingSecureExec
    (A : PolyFamOracleCompPred)
    (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => A))
    (E : ExecEncScheme) (prg : prgScheme) (Hlen : LengthPoly E.spec)
    (Hcontain : ClassContained (fun {_ _ _} => GenPolyTime E.spec prg) (fun {_ _ _} => A))
    (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => A) E.spec)
    (HPrgSecure : prgSchemeSecure (fun {_ _ _} => A) prg)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    CompIndistinguishabilityDistr (fun {_ _ _} => A)
      (famDistrLift (E.toFamDistr prg (Garble c x)))
      (famDistrLift (E.toFamDistr prg (Simulate c (evalCircuit c x)))) := by
  rw [E.toFamDistr_eq, E.toFamDistr_eq]
  exact garblingSecureRelative A HPolyTime E.spec prg Hlen Hcontain HEncIndCpa HPrgSecure c x

/-! ## The seeded deployment

`garblingSecureExec` above covers an implementation that draws its whole environment uniformly —
which `scratch/checks/GarbleMain.lean`'s default mode does, and which assumes nothing beyond primitive
hardness.  A deployment that expands a short seed instead is a *different* statement with
*strictly more* hypotheses, so it is a separate theorem: `garblingSecureExec` must not acquire
them, or the honest mode would pay for the convenient one.
-/

namespace ExecEnc

variable {κ : ℕ}

/-- Everything the evaluator does once the wire keys are fixed: draw the mask bits and the coins,
then run.  This is the post-processing the reduction carries. -/
noncomputable def garblePost (ex : ExecEnc κ) (prg : prgFunctions κ) {s : Shape}
    (e : Expression s) (kvars : Fin (getMaxVar e + 1) → BitVector κ) :
    PMF (BitVector (shapeLengthOn κ ex.encryptLength s)) :=
  (PMF.uniformOfFintype (Fin (getMaxVar e + 1) → Bool)).bind fun bvars =>
    (PMF.uniformOfFintype (Fin (encCount e) → BitVector ex.randLen)).map fun c =>
      (evalExprExecOn ex.encryptLength ex.randLen ex.run prg
        (extendFin ones kvars) (extendFin false bvars) (coinsAt 0 c) e 0).1

/-- `execToDistr` is "draw the keys, then do everything else" — the keys pulled to the front. -/
theorem execToDistr_eq_bind (ex : ExecEnc κ) (prg : prgFunctions κ) {s : Shape}
    (e : Expression s) :
    execToDistr ex prg e
      = (PMF.uniformOfFintype (Fin (getMaxVar e + 1) → BitVector κ)).bind
          (ex.garblePost prg e) :=
  PMF.bind_comm _ _ _

/-- **What a seeded deployment computes**: draw one seed, expand it into the wire keys, garble. -/
noncomputable def execToDistrSeeded (ex : ExecEnc κ) (prg : prgFunctions κ) {s : Shape}
    (e : Expression s) : PMF (BitVector (shapeLengthOn κ ex.encryptLength s)) :=
  ((PMF.uniformOfFintype (BitVector κ)).bind fun sd =>
      PMF.pure (expandKeys prg sd (getMaxVar e + 1))).bind (ex.garblePost prg e)

end ExecEnc

namespace ExecEncScheme

/-- The seeded distributions of an implementation family. -/
noncomputable def toFamDistrSeeded (E : ExecEncScheme) (prg : prgScheme) {s : Shape}
    (e : Expression s) : (κ : ℕ) → PMF (BitVector (shapeLength κ (E.spec κ) s)) :=
  fun κ => ExecEnc.execToDistrSeeded (E κ) (prg κ) e

end ExecEncScheme

/-- **Security of the seeded deployment.**  Expanding one seed into the wire keys and garbling is
indistinguishable from the simulator — the statement that covers
`scratch/checks/GarbleMain.lean --seeded`.

Two hypotheses beyond `garblingSecureExec`: `prgSchemeSecure` is used a *second* time (for the
expansion, not only inside the scheme), and the expansion reduction must be polynomial time.
That is why this is a separate theorem rather than a generalisation — the uniform-environment
mode pays neither. -/
theorem garblingSecureExecSeeded
    (A : PolyFamOracleCompPred)
    (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => A))
    (E : ExecEncScheme) (prg : prgScheme) (Hlen : LengthPoly E.spec)
    (Hcontain : ClassContained (fun {_ _ _} => GenPolyTime E.spec prg) (fun {_ _ _} => A))
    (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => A) E.spec)
    (HPrgSecure : prgSchemeSecure (fun {_ _ _} => A) prg)
    {s t : WireBundle} (c : Circuit s t) (x : bundleBool s)
    (Hred : ExpandReductionWithPolyTime (fun {_ _ _} => A) prg
      (getMaxVar (Garble c x) + 1) (fun κ => (E κ).garblePost (prg κ) (Garble c x))) :
    CompIndistinguishabilityDistr (fun {_ _ _} => A)
      (famDistrLift (ExecEncScheme.toFamDistrSeeded E prg (Garble c x)))
      (famDistrLift (E.toFamDistr prg (Simulate c (evalCircuit c x)))) := by
  refine indTrans _ ?_ (garblingSecureExec A HPolyTime E prg Hlen Hcontain HEncIndCpa HPrgSecure
    c x)
  have h := expandKeys_indist_uniform_post (fun {_ _ _} => A) HPolyTime prg HPrgSecure
    (getMaxVar (Garble c x) + 1) (fun κ => (E κ).garblePost (prg κ) (Garble c x)) Hred
  have hrw : (fun κ => execToDistr (E κ) (prg κ) (Garble c x))
      = (fun κ => (PMF.uniformOfFintype (Fin (getMaxVar (Garble c x) + 1) → BitVector κ)).bind
          ((E κ).garblePost (prg κ) (Garble c x))) :=
    funext fun κ => ExecEnc.execToDistr_eq_bind (E κ) (prg κ) (Garble c x)
  show CompIndistinguishabilityDistr _
    (famDistrLift (fun κ => ExecEnc.execToDistrSeeded (E κ) (prg κ) (Garble c x)))
    (famDistrLift (fun κ => execToDistr (E κ) (prg κ) (Garble c x)))
  rw [hrw]
  exact h

end PRG
