namespace PRG

inductive Shape where
  | BitS : Shape
  | KeyS : Shape
  | PairS : Shape → Shape → Shape
  | EncS : Shape → Shape
  | EmptyS : Shape
deriving DecidableEq, Repr

notation "𝔹" => Shape.BitS
notation "𝕂" => Shape.KeyS
notation "⦃"s₁"⦄" => Shape.EncS s₁

-- First, we define all possible expressions of type 𝔹 (BitS).
inductive BitExpr : Type
| Bit : Bool → BitExpr -- A constant bit value.
| VarB : Nat → BitExpr -- A bit variable identified by a natural number.
| Not : BitExpr → BitExpr -- Negation of a bit expression.
deriving DecidableEq, Repr

open Shape

-- Extension of Expression including PRG primitives: G0(k) and G1(k)
inductive Expression : Shape → Type
| BitE : BitExpr → Expression 𝔹 -- Cast bit expression.
| VarK : Nat → Expression 𝕂 -- Key variable identified by a natural number.
| Pair : Expression s₁ → Expression s₂ → Expression (PairS s₁ s₂) -- Pair of expressions. Denoted as ⸨x, y⸩.
-- PRG Primitives: G0(k) and G1(k)
| G0 : Expression 𝕂 → Expression 𝕂
| G1 : Expression 𝕂 → Expression 𝕂
  -- Controlled-Swap Operator (π[b](e0, e1))
| Perm : Expression 𝔹 → Expression s → Expression s → Expression (PairS s s) -- Conditional swap of two values based on a bit expression.
| Enc : Expression 𝕂 → Expression s → Expression (EncS s) -- Encrypt a value with a given key.
| Hidden : Expression 𝕂 → Expression (EncS s) -- A hole, that represents a value encrypted with a key unaccessible to the adversary.
| Eps : Expression EmptyS -- Empty expression
deriving DecidableEq, Repr

notation "⸨" x "," y "⸩" => Expression.Pair x y

instance : Coe BitExpr (Expression 𝔹) :=
  ⟨Expression.BitE⟩

instance : Coe (Expression 𝔹) BitExpr :=
  ⟨ λ e ↦  match e with
  | Expression.BitE b => b
  ⟩

end PRG
