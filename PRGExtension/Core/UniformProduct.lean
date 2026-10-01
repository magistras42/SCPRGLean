import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Uniform distributions on products, and splitting a block of coins

The fact that a uniform distribution on a product is a pair of *independent* uniforms is the
crux of the distributional refinement (`FUTURE-WORK.md`, Half 2), and it is **not in Mathlib**:
`Probability/Distributions/Uniform.lean` has `uniformOfFintype_apply` and its support, and
nothing relating a uniform distribution to a product or to a bijection.  This file supplies the
three facts, in a form with no garbling in it, so it could be upstreamed as it stands.

* `map_equiv_uniformOfFintype` — transporting a uniform along a bijection gives the uniform.
* `uniformOfFintype_prod` — a uniform on `α × β` is a uniform on `α` followed by an independent
  uniform on `β`.
* **`uniformFinArrow_bind_split`** — the form the induction consumes: drawing `m + n` coins at
  once and splitting them is drawing `m` and then, independently, `n`.

The arithmetic is where the effort is, exactly as predicted: the two `PMF.ext` proofs go through
`tsum_eq_single` and `ENNReal.mul_inv`, and `ENNReal` inverses need their side conditions
supplied (`Fintype.card` is neither `0`, by nonemptiness, nor `∞`, being a `Nat` cast).
-/

namespace PRG

open PMF
open scoped ENNReal

variable {α β γ : Type*}

/-! ### Uniform distributions along bijections and products -/

/-- **A uniform distribution transported along a bijection is uniform.**  Both sides assign
`(card α)⁻¹` to every point, and `Fintype.card_congr` identifies the two cardinalities. -/
theorem map_equiv_uniformOfFintype [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) : (uniformOfFintype α).map e = uniformOfFintype β := by
  refine PMF.ext fun b => ?_
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm b) ?_]
  · simp [Fintype.card_congr e]
  · intro a ha
    simp only [ite_eq_right_iff]
    intro hb
    exact absurd (by rw [hb]; simp) ha

/-- **A uniform distribution on a product is two independent uniforms.**  The point mass
`(card (α × β))⁻¹` factors as `(card α)⁻¹ * (card β)⁻¹`; that factorisation *is* independence
here, and it is the whole content of the lemma. -/
theorem uniformOfFintype_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    uniformOfFintype (α × β)
      = (uniformOfFintype α).bind fun a => (uniformOfFintype β).map fun b => (a, b) := by
  refine PMF.ext fun x => ?_
  obtain ⟨a₀, b₀⟩ := x
  rw [PMF.bind_apply, tsum_eq_single a₀ ?_]
  · -- the diagonal term: the two point masses multiply
    rw [PMF.map_apply, tsum_eq_single b₀ ?_]
    · have hα : (Fintype.card α : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
      have hβ : (Fintype.card β : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
      simp only [uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul, if_pos rfl]
      exact ENNReal.mul_inv (Or.inl hα) (Or.inr hβ)
    · intro b hb
      simp only [ite_eq_right_iff, Prod.mk.injEq]
      rintro ⟨-, rfl⟩
      exact absurd rfl hb
  · -- off the diagonal every term vanishes, since the first coordinate cannot match
    intro a ha
    rw [PMF.map_apply]
    simp [Prod.ext_iff, Ne.symm ha]

/-! ### Splitting a block of coins

`Fin (m + n) → B` is the shape a finite coin supply takes: one draw per encryption node.  The
evaluator reads the first `m` for one subexpression and the last `n` for the other, so this is
the form the induction needs.
-/

/-- Reading a block of `m + n` coins as an initial `m` and a final `n`. -/
def finArrowSplit (m n : ℕ) (B : Type*) : (Fin (m + n) → B) ≃ (Fin m → B) × (Fin n → B) where
  toFun c := (fun j => c (Fin.castAdd n j), fun j => c (Fin.natAdd m j))
  invFun p := Fin.append p.1 p.2
  left_inv c := by
    funext j
    refine Fin.addCases ?_ ?_ j <;> intro i <;> simp
  right_inv p := by
    obtain ⟨u, v⟩ := p
    simp

/-- **Drawing `m + n` coins at once, then splitting them, is drawing `m` and then `n`
independently.**  This is the statement the refinement's `Pair`, `Perm` and `Enc` cases consume:
each has two subexpressions drawing disjoint blocks of coins, and this is what lets the
induction hypotheses be applied one after the other. -/
theorem uniformFinArrow_bind_split {B : Type*} [Fintype B] [Nonempty B] (m n : ℕ)
    (F : (Fin m → B) → (Fin n → B) → PMF γ) :
    ((uniformOfFintype (Fin (m + n) → B)).bind fun c =>
        F (fun j => c (Fin.castAdd n j)) (fun j => c (Fin.natAdd m j)))
      = (uniformOfFintype (Fin m → B)).bind fun a =>
          (uniformOfFintype (Fin n → B)).bind fun b => F a b := by
  have hmap := map_equiv_uniformOfFintype (finArrowSplit m n B)
  have h1 : ((uniformOfFintype (Fin (m + n) → B)).bind fun c =>
        F (fun j => c (Fin.castAdd n j)) (fun j => c (Fin.natAdd m j)))
      = ((uniformOfFintype (Fin (m + n) → B)).map (finArrowSplit m n B)).bind
          fun p => F p.1 p.2 := by
    rw [PMF.bind_map]
    rfl
  rw [h1, hmap, uniformOfFintype_prod, PMF.bind_bind]
  simp only [PMF.bind_map]
  rfl

/-- The `map` form of the split, which is how the refinement's induction meets it: the value
computed from `m + n` coins is a function of the two halves. -/
theorem uniformFinArrow_map_split {B : Type*} [Fintype B] [Nonempty B] (m n : ℕ)
    (g : (Fin m → B) → (Fin n → B) → γ) :
    ((uniformOfFintype (Fin (m + n) → B)).map fun c =>
        g (fun j => c (Fin.castAdd n j)) (fun j => c (Fin.natAdd m j)))
      = (uniformOfFintype (Fin m → B)).bind fun a =>
          (uniformOfFintype (Fin n → B)).map fun b => g a b :=
  uniformFinArrow_bind_split m n fun a b => PMF.pure (g a b)

/-- **Drawing a block of one coin is drawing a coin.**  `Fin 1 → B` is `B` up to the unique
bijection, and a uniform transported along it is uniform. -/
theorem uniformFinOne_bind {B : Type*} [Fintype B] [Nonempty B] (G : B → PMF γ) :
    ((uniformOfFintype (Fin 1 → B)).bind fun c => G (c 0)) = (uniformOfFintype B).bind G := by
  rw [← map_equiv_uniformOfFintype (Equiv.funUnique (Fin 1) B), PMF.bind_map]
  rfl

/-- Splitting off the *first* index: `Fin (n+1) → B` is `B` paired with `Fin n → B`.  Mathlib has
no such equiv, so it is built here from `Fin.cons` / `Fin.succ`. -/
def finSuccArrow (n : ℕ) (B : Type*) : (Fin (n + 1) → B) ≃ B × (Fin n → B) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i <;> intros <;> simp
  right_inv p := by
    obtain ⟨a, g⟩ := p
    simp

/-- **A uniform block of `n+1` draws is one draw followed by an independent block of `n`.**  The
recursive form of the split, which is what an expansion built one block at a time needs. -/
theorem uniformFinArrow_cons {B : Type*} [Fintype B] [Nonempty B] (n : ℕ) :
    uniformOfFintype (Fin (n + 1) → B)
      = (uniformOfFintype B).bind fun a =>
          (uniformOfFintype (Fin n → B)).map fun r => Fin.cons a r := by
  rw [← map_equiv_uniformOfFintype (finSuccArrow n B).symm, uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp]
  rfl

/-- Drawing one coin, in `map` form. -/
theorem uniformFinOne_map {B : Type*} [Fintype B] [Nonempty B] (g : B → γ) :
    ((uniformOfFintype (Fin 1 → B)).map fun c => g (c 0)) = (uniformOfFintype B).map g :=
  uniformFinOne_bind fun b => PMF.pure (g b)

end PRG
