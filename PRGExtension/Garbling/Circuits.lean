import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability

-- Circuits, defined inductively (LM18 §3).  The circuit language itself is independent of
-- the expression language; what changes in the PRG setting is `labelType`: a wire label
-- now carries key *expressions* rather than variable indices, because a `Dup` gate
-- produces `G0 k` / `G1 k` rather than reusing its input key.

namespace PRG

inductive WireBundle : Type
| SimpleB : WireBundle
| PairB : WireBundle -> WireBundle -> WireBundle
deriving DecidableEq, Repr

notation "o" => WireBundle.SimpleB
notation "(" o1 "," o2 ")" => WireBundle.PairB o1 o2

inductive Circuit : (input : WireBundle) -> (output : WireBundle) -> Type
| NandC : Circuit (o, o) o
| AssocC : (u v w : WireBundle) -> Circuit (u, (v, w)) ((u, v), w)
| UnAssocC : (u v w : WireBundle) -> Circuit ((u, v),w) (u, (v, w))
| SwapC : (u v: WireBundle) -> Circuit (u, v) (v, u)
| DupC : Circuit o (o, o)
| ComposeC : {u v w : WireBundle} -> Circuit u v -> Circuit v w -> Circuit u w
| FirstC : {v₁ v₂ : WireBundle} -> Circuit v₁ v₂ -> (u : WireBundle) -> Circuit (v₁, u) (v₂, u)
deriving DecidableEq, Repr

@[simp]
def bundleType (t : Type) : WireBundle -> Type
| o => t
| (o1, o2) => bundleType t o1 × bundleType t o2

@[simp]
def bundleBool : WireBundle -> Type := bundleType Bool

/--
  LM18 §4: a wire label is `(b, (k⁰, k¹))` of shape `⦇𝔹, ⦇𝕂,𝕂⦈⦈`.

  This is where the PRG language diverges from the encryption-only framework, in which
  `labelType := bundleType ℕ` and the two keys of wire `n` were fixed to be
  `VarK (2n)` / `VarK (2n+1)`.  Here the keys are arbitrary key expressions, because
  `Gb(Dup, (b,(k⁰,k¹))) = ε, ((b,(G0 k⁰, G0 k¹)), (b,(G1 k⁰, G1 k¹)))`.
-/
structure WireLabel where
  /-- LM18 labels always carry an *atomic* bit symbol `B_h` (this is the first clause of
      the paper's Condition 1), so we store its index rather than a general `BitExpr`. -/
  bit : ℕ
  key0 : Expression Shape.KeyS
  key1 : Expression Shape.KeyS
deriving DecidableEq, Repr

/-- The label's bit symbol `B_h`. -/
def WireLabel.bitE (l : WireLabel) : BitExpr := BitExpr.VarB l.bit

@[simp]
def labelType : WireBundle -> Type := bundleType WireLabel

def evalCircuit (c : Circuit input output) (b : bundleBool input) : bundleBool output :=
match c, b with
| Circuit.NandC, (x, y) => not (x && y)
| Circuit.AssocC _ _ _, (x, (y, z)) => ((x, y), z)
| Circuit.UnAssocC _ _ _ , ((x, y), z) => (x, (y, z))
| Circuit.SwapC _ _, (x, y) => (y, x)
| Circuit.DupC , x => (x, x)
| Circuit.ComposeC c1 c2, x => evalCircuit c2 (evalCircuit c1 x)
| Circuit.FirstC c _, (x, y) => (evalCircuit c x, y)

notation x ">>>" y => Circuit.ComposeC x y

def notC : Circuit o o := (Circuit.DupC) >>> (Circuit.NandC)
def andC : Circuit (o, o) o := (Circuit.NandC) >>> notC
def prodC {u₁ u₂ v₁ v₂ : WireBundle}  (c₁ : Circuit u₁ v₁) (c₂ : Circuit u₂ v₂) : Circuit (u₁, u₂) (v₁, v₂) :=
  (Circuit.FirstC c₁ u₂) >>>
  Circuit.SwapC v₁ u₂  >>>
  (Circuit.FirstC c₂ v₁) >>>
  Circuit.SwapC v₂ v₁
def orC : Circuit (o, o) o :=
  prodC notC notC >>>
  Circuit.NandC

-- ---------------------------------------------------------------------------------
-- Shapes of the expressions a garbling produces.
-- ---------------------------------------------------------------------------------

@[simp]
def wireBundle2Shape (t : Shape) : WireBundle -> Shape
| o => t
| (o1, o2) => Shape.PairS (wireBundle2Shape t o1) (wireBundle2Shape t o2)

/-- Shape of one garbled NAnd table: `π[·](π[·](⦃⦃⦇𝔹,𝕂⦈⦄⦄, ⦃⦃⦇𝔹,𝕂⦈⦄⦄), π[·](…, …))`. -/
def nandTableShape : Shape :=
  let one := Shape.EncS (Shape.EncS (Shape.PairS Shape.BitS Shape.KeyS))
  let two := Shape.PairS one one
  Shape.PairS two two

def garbledShapeGen (nandT : Shape) : {input output : WireBundle} -> Circuit input output -> Shape
| _, _, Circuit.SwapC _ _ => Shape.EmptyS
| _, _, Circuit.AssocC _ _ _ => Shape.EmptyS
| _, _, Circuit.UnAssocC _ _ _ => Shape.EmptyS
| _, _, Circuit.DupC => Shape.EmptyS
| .(_), .(_), Circuit.ComposeC c1 c2 => Shape.PairS (garbledShapeGen nandT c1) (garbledShapeGen nandT c2)
| _, _, Circuit.FirstC c _ => garbledShapeGen nandT c
| _, _, Circuit.NandC => nandT

def garbledShape : {input output : WireBundle} -> Circuit input output -> Shape :=
  garbledShapeGen nandTableShape

/-- Shape of an encoded input/output bundle: one `(bit, key)` pair per wire. -/
def encodedShape : WireBundle -> Shape := wireBundle2Shape (Shape.PairS Shape.BitS Shape.KeyS)
/-- Shape of an output-mask bundle: one bit per wire. -/
def maskShape : WireBundle -> Shape := wireBundle2Shape Shape.BitS
abbrev encodedLabelType : WireBundle -> Type :=
  bundleType (Expression (Shape.PairS Shape.BitS Shape.KeyS))
abbrev maskedLabelType : WireBundle -> Type := bundleType (Expression Shape.BitS)

/-- Shape of a label expression: one `(b,(k⁰,k¹))` per wire. -/
def labelShape : WireBundle -> Shape :=
  wireBundle2Shape (Shape.PairS Shape.BitS (Shape.PairS Shape.KeyS Shape.KeyS))

end PRG
