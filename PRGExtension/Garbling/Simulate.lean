import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleHole

-- import Mathlib.Data.Finset.Lattice

-- This file defines the simulation procedure (`SimulateG`), used to establish the security of garbling.
-- Simulator that takes a garbled cicuit, its output (but not the input@)
-- and outputs a cryptographic expression symIndistinguishable from the garbled circuit.

-- This correspond to the `gb` function from the `Garbling` module.
def sim : {input output : WireBundle} ->  (c : Circuit input output)  -> (inlbl : labelType input) -> (i : ℕ) -> ((Expression (garbledShape c)) × (labelType output) × ℕ)
| .(WireBundle.PairB _ _), .(WireBundle.PairB _ _), Circuit.SwapC _ _, (i1, i2), i => (Expression.Eps, (i2, i1), i)
| _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), i => (Expression.Eps, ((i1, i2), i3), i)
| _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), i => (Expression.Eps, (i1, (i2, i3)), i)
| _, _, Circuit.DupC, n, i =>
  (Expression.Eps, (n, n), i)
| _, _, Circuit.FirstC c _, ⟨b₁, b₂⟩, i =>
  let (c', b₁', i2) := sim c b₁ i
  (c', (b₁', b₂), i2)
| _, _, Circuit.ComposeC c1 c2, b, i0 =>
  let (c₁', b', i1) := sim c1 b i0
  let (c₂', b'', i2) := sim c2 b' i1
  (Expression.Pair c₁' c₂', b'', i2)
| _, _, Circuit.NandC, (nl, nr), i =>
  let h := i
  let Bh := BitExpr.VarB h
  let khf := Expression.VarK (makeKeyLabel h false)
  let c00 := gb_entry (makeKey nl false) (makeKey nr false) khf Bh
  let c01 := gb_entry (makeKey nl false) (makeKey nr true) khf Bh
  let c10 := gb_entry (makeKey nl true) (makeKey nr false) khf Bh
  let c11 := gb_entry (makeKey nl true) (makeKey nr true) khf Bh
  let bl := Expression.BitE (BitExpr.VarB nl)
  let br := Expression.BitE (BitExpr.VarB nr)
  let c := Expression.Perm bl (Expression.Perm br c00 c01) (Expression.Perm br c10 c11)
  (c, h, i+1)


def simHole : {input output : WireBundle} ->  (c : Circuit input output)  -> (inlbl : labelType input) -> (i : ℕ) -> ((Expression (garbledShape c)) × (labelType output) × ℕ)
| .(WireBundle.PairB _ _), .(WireBundle.PairB _ _), Circuit.SwapC _ _, (i1, i2), i => (Expression.Eps, (i2, i1), i)
| _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), i => (Expression.Eps, ((i1, i2), i3), i)
| _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), i => (Expression.Eps, (i1, (i2, i3)), i)
| _, _, Circuit.DupC, n, i =>
  (Expression.Eps, (n, n), i)
| _, _, Circuit.FirstC c _, ⟨b₁, b₂⟩, i =>
  let (c', b₁', i2) := simHole c b₁ i
  (c', (b₁', b₂), i2)
| _, _, Circuit.ComposeC c1 c2, b, i0 =>
  let (c₁', b', i1) := simHole c1 b i0
  let (c₂', b'', i2) := simHole c2 b' i1
  (Expression.Pair c₁' c₂', b'', i2)
| _, _, Circuit.NandC, (nl, nr), i =>
  let h := i
  let Bh := BitExpr.VarB h
  let khf := Expression.VarK (makeKeyLabel h false)
  let c00 := makeHoleEntry true true (makeKey nl false) (makeKey nr false) khf Bh
  let c01 := makeHoleEntry true false (makeKey nl false) (makeKey nr true) khf Bh
  let c10 := makeHoleEntry false true (makeKey nl true) (makeKey nr false) khf Bh
  let c11 := makeHoleEntry false false (makeKey nl true) (makeKey nr true) khf Bh
  let bl := Expression.BitE (BitExpr.VarB nl)
  let br := Expression.BitE (BitExpr.VarB nr)
  let c := Expression.Perm bl (Expression.Perm br c00 c01) (Expression.Perm br c10 c11)
  (c, h, i+1)


def generateFalseInput : {bundle : WireBundle} -> labelType bundle -> bundleBool bundle
  | o, _n => false
  | (_, _), (l1, l2) => (generateFalseInput l1, generateFalseInput l2)

  -- Now we simulate the input encoding. Since we dont have the input, we assume that everything is true.
  def sEnc {bundle : WireBundle} (input : labelType bundle) : encodedLabelType bundle := gEnc input (generateFalseInput input)

  -- Next, we show how to compute the output bundle, since the input bundle is
  -- simulated, we need to use the circuit's output to compute hte correct masked output.
  def sMask : {bundle : WireBundle} -> labelType bundle -> bundleBool bundle -> maskedLabelType bundle
  | o, n, b => Expression.BitE (negatedBit n b)
  | (_, _), (l1, l2), (b1, b2) => (sMask l1 b1, sMask l2 b2)

  def generateLabel (f : ℕ -> Bool) : {bundle : WireBundle} -> labelType bundle -> bundleBool bundle
  | o, n => f n
  | (_, _), (n1, n2) => (generateLabel f n1, generateLabel f n2)


  def simulateAux {inputBundle outputBundle : WireBundle}  (c : Circuit inputBundle outputBundle) (output : bundleBool outputBundle) : (garbleOutputTypeAfterProjection c) :=
    let (inlbl, im) := makeLabelExp inputBundle 0
    let (c', outlbl, _ifi) := sim c inlbl im
    let encodedInput := sEnc inlbl
    let maskedOutput := sMask outlbl output
    ((c', maskedOutput), encodedInput)

  def SimulateG {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (output : bundleBool outputBundle)
    : Expression (Shape.PairS (garbledCircuitShape c) (garbledInputShape inputBundle)) :=
      garbleOutputToExpr (simulateAux c output)
