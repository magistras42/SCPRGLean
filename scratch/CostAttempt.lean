import PRGExtension.Expression.ComputationalSemantics.CostModel

/-! Attempt at Design B step 1: a structural `cost` on `OracleComp`. -/

namespace PRG
open OracleComp

universe u v

-- ATTEMPT 1: cost as a ℕ-valued structural recursion, "branch not tree".
noncomputable def cost₁ {ι : Type u} {spec : OracleSpec ι} {α : Type v} :
    OracleComp spec α → ℕ :=
  fun oa => OracleComp.construct' (C := fun _ => ℕ)
    (fun _ => 0)                         -- pure x  ↦  0   (see below: should be "output width")
    (fun _ _ _ ih => 1 + ⨆ u, ih u)      -- query   ↦  1 + sup over branches
    0                                    -- failure ↦  0
    oa

-- The supremum is over `spec.range i`, which for the randomness oracle is an ARBITRARY Type.
example : (oracleSpecForRand).range (ℕ) = ℕ := rfl

-- ROADBLOCK A: `⨆` over an unbounded family in ℕ is junk, silently.
example : (⨆ n : ℕ, n) = 0 := by simp

end PRG

namespace PRG
open OracleComp
universe u' v'

/-- **ROADBLOCK B (fatal).**  Any cost function on `OracleComp` — structural or not — is
invariant under replacing a continuation by an *extensionally equal* one.

In Lean, a brute-force search and a table lookup with the same graph are the **same
function**.  So no `cost : OracleComp spec α → ℕ` can tell them apart: local running time is
simply not a property of an `OracleComp` term.  The free monad records oracle queries; every
local computation lives inside a Lean function (a query payload, a continuation, or the value
under `pure`) and is invisible to structural recursion. -/
theorem cost_blind {ι : Type u'} {spec : OracleSpec ι} {α : Type v'}
    (cost : OracleComp spec α → ℕ) (i : ι) (t : spec.domain i)
    (f g : spec.range i → α) (h : ∀ u, f u = g u) :
    cost (OracleSpec.query i t >>= fun u => pure (f u))
      = cost (OracleSpec.query i t >>= fun u => pure (g u)) := by
  simp only [funext h]

/-- The same point, one line: **any** value sits under `pure` at cost `0`, however expensive
it was to compute.  `x` may be the result of searching all `2 ^ κ` keys. -/
example {ι : Type} {spec : OracleSpec ι} {α : Type} (x : α) :
    cost₁ (pure x : OracleComp spec α) = 0 := by
  simp [cost₁, OracleComp.construct', OracleComp.construct_pure]

end PRG
