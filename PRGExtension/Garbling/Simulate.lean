import PRGExtension.Garbling.GarblingDef

/-!
# The simulator

`Sim` (LM18 §5) is identical to `Gb` except at `NAnd`, where all four table entries carry the
same payload `(B_h, K_h⁰)` — it has no input, so there is nothing for the entries to depend
on.  `SEnc` always hands out the first key and `SMask` adjusts the output masks by the
circuit's output value.

`Simulate(C, y)` is what the security proof compares `Garble(C, x)` against.
-/

namespace PRG
/--
  `Sim` (LM18 §5).  Identical to `Gb` except at `NAnd`, where every one of the four
  entries carries the same payload `(B_h, K_h⁰)`.
-/
def sim : {input output : WireBundle} -> (c : Circuit input output) -> labelType input -> ℕ ->
    (Expression (garbledShape c) × labelType output × ℕ)
  | _, _, Circuit.SwapC _ _, (i1, i2), ctr => (Expression.Eps, (i2, i1), ctr)
  | _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), ctr => (Expression.Eps, ((i1, i2), i3), ctr)
  | _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), ctr => (Expression.Eps, (i1, (i2, i3)), ctr)
  | _, _, Circuit.DupC, l, ctr =>
      (Expression.Eps,
       (⟨l.bit, Expression.G0 l.key0, Expression.G0 l.key1⟩,
        ⟨l.bit, Expression.G1 l.key0, Expression.G1 l.key1⟩), ctr)
  | _, _, Circuit.FirstC c _, (b1, b2), ctr =>
      let (c', b1', ctr') := sim c b1 ctr
      (c', (b1', b2), ctr')
  | _, _, Circuit.ComposeC c1 c2, b, ctr =>
      let (c1', b', ctr1) := sim c1 b ctr
      let (c2', b'', ctr2) := sim c2 b' ctr1
      (Expression.Pair c1' c2', b'', ctr2)
  | _, _, Circuit.NandC, (li, lj), ctr =>
      let Bh : BitExpr := BitExpr.VarB ctr
      let Kh0 : Expression Shape.KeyS := Expression.VarK (2*ctr)
      let Kh1 : Expression Shape.KeyS := Expression.VarK (2*ctr+1)
      let e00 := gbEntry li.key0 lj.key0 Kh0 Bh
      let e01 := gbEntry li.key0 lj.key1 Kh0 Bh
      let e10 := gbEntry li.key1 lj.key0 Kh0 Bh
      let e11 := gbEntry li.key1 lj.key1 Kh0 Bh
      (Expression.Perm (Expression.BitE li.bitE)
         (Expression.Perm (Expression.BitE lj.bitE) e00 e01)
         (Expression.Perm (Expression.BitE lj.bitE) e10 e11),
       ⟨ctr, Kh0, Kh1⟩, ctr+1)
/-- `SEnc` (LM18 §5): the simulator has no input, so it always takes the first key. -/
def sEnc : {b : WireBundle} -> labelType b -> encodedLabelType b
  | WireBundle.SimpleB, l => Expression.Pair (Expression.BitE l.bitE) l.key0
  | WireBundle.PairB _ _, (l1, l2) => (sEnc l1, sEnc l2)
/-- `SMask` (LM18 §5): the masks are adjusted by the circuit's output value. -/
def sMask : {b : WireBundle} -> labelType b -> bundleBool b -> maskedLabelType b
  | WireBundle.SimpleB, l, y =>
      cond y (Expression.BitE (BitExpr.Not l.bitE)) (Expression.BitE l.bitE)
  | WireBundle.PairB _ _, (l1, l2), (y1, y2) => (sMask l1 y1, sMask l2 y2)
/-- `Simulate(C, y)` (LM18 §5). -/
def Simulate {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    Expression (garbleShapeFull c) :=
  let u := (makeLabels s 0).1
  let r := sim c u (makeLabels s 0).2
  Expression.Pair r.1
    (Expression.Pair (encodedLabelToExpr (sEnc u)) (maskedLabelToExpr (sMask r.2.1 y)))

end PRG
