import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability

--  This file defines renamings of boolean and key variables.

def bitPerm (f : ℕ -> Bool) (x : ℕ) : VarOrNegVar :=
  if f x then VarOrNegVar.NegVar x else VarOrNegVar.Var x

--- We show that this is a good bit renaming
def bitPermInjective (f : ℕ → Bool) : validBitRenaming (bitPerm f) := by
  simp [validBitRenaming]
  have : (fun n ↦ castVarOrNegVar (bitPerm f n)) = id := by
    ext n
    simp [castVarOrNegVar, bitPerm]
    cases (f n) <;> simp
  have : castVarOrNegVar ∘ (bitPerm f) = id := by
    rw [← this]; ext x; simp
  simp [this]
  exact Function.bijective_id



--- Now we define key renaming from function `f : ℕ → Bool`, which states the value of each wire.
--- (It will typically be the result of `evalOut`).

def notNat (n : ℕ) := if n = 0 then 1 else 0
def yesNat (n : ℕ) := if n = 0 then 0 else 1
def condNotNat (b : Bool) (n : ℕ) := if b then notNat n else yesNat n

-- This is the key renaming function.
def makeKeySwap (f : ℕ → Bool) (x : ℕ) : ℕ :=
  let idx := x / 2
  let md := x % 2
  2*idx + condNotNat (f idx) md

def idxSame (x y : ℕ) (b : Bool ) : (2 * (x / 2) + condNotNat b y ) / 2 = x / 2 := by
  simp [condNotNat, notNat, yesNat]
  cases b <;> (cases y <;> simp; try omega)

-- We need to show that the key renaming function is bijective, but we can show that it is even involutive.
lemma makeKeySwapInv (f : ℕ → Bool) (x : ℕ) :
  makeKeySwap f (makeKeySwap f x) = x := by
    simp [makeKeySwap, idxSame]
    simp [condNotNat]
    generalize Hval : f (x / 2) = val
    generalize Hmd : x % 2 = md
    cases val
    case false =>
      simp [yesNat]
      cases md
      case zero => simp; omega
      case succ x' =>
        have : x' = 0 := by omega
        subst x'
        simp
        have : 2 * (x / 2) + 1 = x := by omega
        simp [this]
        -- simp [Hmd]
        -- omega
    case true =>
      simp [notNat]
      cases md
      case zero =>
        simp
        have : (2 * (x/2)) = x := by omega
        simp [this]
        -- omega
      case succ x' =>
        have : x' = 0 := by omega
        simp [this]
        omega


-- And here the injectivity
def keySwapBijective (f : ℕ → Bool) : Function.Bijective (makeKeySwap f) := by
  constructor
  · apply Function.LeftInverse.injective
    apply makeKeySwapInv
  · apply Function.RightInverse.surjective
    apply makeKeySwapInv

def makeVarRenaming (f : ℕ → Bool) : varRenaming  :=
  ⟨bitPerm f, makeKeySwap f⟩

def makeTotalRenamingCorrect (f : ℕ → Bool) : validVarRenaming (makeVarRenaming f) := by
  simp [validVarRenaming]
  exact ⟨bitPermInjective f, keySwapBijective f⟩
