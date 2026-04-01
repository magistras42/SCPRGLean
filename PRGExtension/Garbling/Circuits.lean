-- This file defines circuits inductively.

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
def labelType : WireBundle -> Type :=
  bundleType Nat

@[simp]
def bundleBool : WireBundle -> Type := bundleType Bool

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
