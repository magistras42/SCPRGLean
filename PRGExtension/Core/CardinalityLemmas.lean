import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Basic


instance {n : Nat} : Fintype (Fin n) := by
  infer_instance

instance {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] : Fintype (X → Y) := by
  infer_instance

lemma cardinalityCount {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (v: X -> Y) (S : Finset X) : Fintype.card { f : X -> Y // ∀ i : S, f i = v i} = (Fintype.card Y) ^ (Fintype.card X - Finset.card S) := by
  let free := Finset.univ \ S
  rw [@Fintype.card_congr _ (free → Y)]
  · simp [free, Finset.card_sdiff]
  · exact {
      toFun := by
        rintro ⟨f, hf⟩ ⟨x, hx⟩
        exact (f x)
      invFun := by
        rintro f
        constructor
        swap
        · intro x
          if Hx : x ∈ free then
            exact f ⟨x, Hx⟩
          else
            exact (v x)
        · intro i
          simp
          intro hi
          simp [free] at hi
      left_inv := by
        simp [Function.LeftInverse]
        intro f hf
        ext x
        simp
        intro hx
        simp [free] at hx
        rw [hf]
        assumption
      right_inv := by
        simp [Function.RightInverse, Function.LeftInverse]
    }

def subtype_prod_equiv {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {px : X → Prop} {py : Y → Prop} :
  { p : X × Y // px p.1 ∧ py p.2 } ≃ {x // px x } × {y // py y } where
    toFun := fun ⟨⟨x, y⟩, hpx, hpy⟩ => ⟨⟨x, hpx⟩, ⟨y, hpy⟩⟩
    invFun := fun ⟨⟨x, hpx⟩, ⟨y, hpy⟩⟩ => ⟨⟨x, y⟩, hpx, hpy⟩
    left_inv := by
      rintro ⟨⟨x, y⟩, hpx, hpy⟩
      simp
    right_inv := by
      rintro ⟨⟨x, hpx⟩, ⟨y, hpy⟩⟩
      simp
