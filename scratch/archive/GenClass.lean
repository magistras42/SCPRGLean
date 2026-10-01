import PRGExtension.Expression.ComputationalSemantics.Efficiency.GeneratedPolyTime

/-!
# Finding F6, preserved as a demonstration

The definitions this file used to prototype now live in
`ComputationalSemantics/GeneratedPolyTime.lean`.  What remains here is the demonstration that
motivated the F6 refactor, kept because it is the cheapest way to see why `PolyTimeModel`
needs its own value predicate.

**Before the refactor**, `PolyTimeVal IsPolyTime f` was `polyTimeFamComp IsPolyTime f` — the
oracle computation that *queries for its input* and then runs `f`.  Under that definition:

* a clause with no `PolyTimeVal` hypothesis discharged fine through the bridge;
* a clause that *took* `PolyTimeVal` hypotheses did not, because the hypotheses arrived in the
  encoded form and getting back to `PolyVal` needs the **converse** of the bridge — an
  inversion of `PolyFn` on a term whose constructors are Lean functions.

The second case is reproduced below against the *old* encoding, with `sorry` marking exactly
where it stops.  Run with `lake env lean scratch/archive/GenClass.lean`.
-/

namespace PRG

variable {enc : encryptionScheme} {prg : prgScheme}

/-- Fine either way: no hypothesis in the encoded form. -/
example {D E : ℕ → Type} (hD : PolySized D) (hE : PolySized E) :
    polyTimeFamComp (GenPolyTime enc prg) (Input := fun κ => D κ × E κ) (Output := D)
      (fun _ (p : D _ × E _) => PMF.pure p.1) :=
  polyVal_to_famComp (hD.prod hE) hD _ (PolyVal.fst hD hE)

/-- **The blocker.**  With the hypotheses in the encoded form there is no route back. -/
example {D A B : ℕ → Type} (hD : PolySized D) (hA : PolySized A) (hB : PolySized B)
    (f : (κ : ℕ) → D κ → A κ) (g : (κ : ℕ) → D κ → B κ)
    (hf : polyTimeFamComp (GenPolyTime enc prg) (fun κ d => PMF.pure (f κ d)))
    (hg : polyTimeFamComp (GenPolyTime enc prg) (fun κ d => PMF.pure (g κ d))) :
    polyTimeFamComp (GenPolyTime enc prg) (Output := fun κ => A κ × B κ)
      (fun κ d => PMF.pure (f κ d, g κ d)) := by
  refine polyVal_to_famComp hD (hA.prod hB) _ (PolyVal.pair f g ?_ ?_)
  · sorry   -- `hf` is `PolyFn` of the input-querying encoding; inversion unavailable
  · sorry   -- likewise `hg`

/-- After the refactor the same clause is one constructor, because `PolyTimeModel` carries
`IsPolyTimeVal` and the hypotheses arrive as `PolyVal`. -/
example {D A B : ℕ → Type} (f : (κ : ℕ) → D κ → A κ) (g : (κ : ℕ) → D κ → B κ)
    (hf : PolyVal enc prg (fun κ d => PMF.pure (f κ d)))
    (hg : PolyVal enc prg (fun κ d => PMF.pure (g κ d))) :
    PolyVal enc prg (O := fun κ => A κ × B κ) (fun κ d => PMF.pure (f κ d, g κ d)) :=
  PolyVal.pair f g hf hg

end PRG
