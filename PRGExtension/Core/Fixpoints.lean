import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

-- Tis file proves a constructive version of the Knaster–Tarski theorem, showing the existence of fixpoints in a lattice of finite sets.

def greatestFixpoint {α : Type} [DecidableEq α] (f : Finset α → Finset α) (f_monotone : ∀ X Y, X ⊆ Y -> f X ⊆ f Y ) (fBound : Finset α) (HfBound : forall X, f X ⊆ fBound) : Finset α :=
  let rec gfix (S : Finset α) (_ : S ⊆ fBound) (h2 : f S ⊆ S) : Finset α :=
    if _ : f S = S then S else gfix (f S) (HfBound S) (f_monotone _ _ h2)
  termination_by S.card
  decreasing_by (
    apply Finset.card_lt_card
    apply HasSubset.Subset.ssubset_of_ne
    apply h2
    assumption
    )
  gfix fBound (refl fBound) (HfBound fBound)

-- This next lemma says that this is indeed a fixpoint -- it follows the line fo the definition
lemma greatestFixpointIsFixpoint : ∀ {α : Type} [DecidableEq α] (f : Finset α → Finset α) (f_monotone : ∀ X Y, X ⊆ Y -> f X ⊆ f Y ) (fBound : Finset α) (HfBound : forall X, f X ⊆ fBound),
  f (greatestFixpoint f f_monotone fBound HfBound) =  greatestFixpoint f f_monotone fBound HfBound := by
  intros a inst f Hfm fBound Hfu
  simp[greatestFixpoint]
  let rec gfixL (S : Finset a) (X : S ⊆ fBound) (Y : f S ⊆ S) :
    f (greatestFixpoint.gfix f Hfm fBound Hfu S X Y) = greatestFixpoint.gfix f Hfm fBound Hfu S X Y :=
    if h2 : f S = S then by simp[greatestFixpoint.gfix, h2] else (by
      have Htmp := gfixL (f S) (Hfu S) (Hfm _ _ Y)
      rw [greatestFixpoint.gfix]
      simp [h2]
      assumption
    )
  termination_by S.card
  decreasing_by (
      apply Finset.card_lt_card
      apply HasSubset.Subset.ssubset_of_ne
      apply Y
      assumption
    )
  apply gfixL


-- This next lemma says we can access fixpoint via any relation R that is transitive and satified on each step of fixpoint computation.
lemma fixaccess {α : Type} [DecidableEq α] (f1 : Finset α → Z) (f2 : Z -> Finset α)
  (f_monotone : ∀ X Y, X ⊆ Y -> f2 (f1 X) ⊆ f2 (f1 Y)) (fBound : Z) (HfBound : forall x, f2 (f1 x) ⊆ f2 fBound)
  (R : Z -> Z -> Prop) (RTrans : forall {x y z}, R x y -> R y z -> R x z)
  (Rrfl: forall z, R z z) (Ras : forall x, f2 (f1 x) ⊆ x -> R (f1 x) (f1 (f2 (f1 x)))) (Rsup : R fBound (f1 (f2 fBound))):
  R fBound (f1 (greatestFixpoint (fun x => f2 (f1 x)) f_monotone (f2 fBound) HfBound)) :=
by
  simp [greatestFixpoint]
  let rec gfixL2 (S : Finset α) (X : S ⊆ (f2 fBound)) (Y : f2 (f1 S) ⊆ S) (Hnew : R fBound (f1 S)) :
  R fBound (f1 (greatestFixpoint.gfix (fun x => f2 (f1 x)) f_monotone (f2 fBound) HfBound S X Y))
  := by
    -- apply (RTrans Hnew)
    rw [greatestFixpoint.gfix]
    if h2 : f2 (f1 S) = S then
      apply (RTrans Hnew)
      simp [h2]
      apply Rrfl
    else
      simp [h2]
      have Htmp := gfixL2 (f2 (f1 S)) (HfBound S) (f_monotone _ _ Y) (
        by
          apply RTrans Hnew
          apply Ras S Y
          )
      assumption
  termination_by S.card
  decreasing_by (
      apply Finset.card_lt_card
      apply HasSubset.Subset.ssubset_of_ne
      apply Y
      assumption
    )
  apply gfixL2
  assumption
