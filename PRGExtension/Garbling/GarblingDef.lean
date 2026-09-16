import PRGExtension.Garbling.Circuits

-- The PRG-based garbling scheme and symbolic simulator of LM18 §4 and §5.
--
-- Difference from the encryption-only framework: `Gb(Dup, ·)` derives the two output wire
-- labels with the PRG instead of duplicating the input label, which is what makes fan-out
-- possible without a fresh key per copy.

namespace PRG

/-- `Label(s)` (LM18 §4): a fresh atomic label per wire.  Wire `h` gets bit variable
    `B_h = VarB h` and keys `K_h⁰ = VarK (2h)`, `K_h¹ = VarK (2h+1)`. -/
def makeLabels : (input : WireBundle) -> ℕ -> labelType input × ℕ
  | WireBundle.SimpleB, i =>
      (⟨BitExpr.VarB i, Expression.VarK (2*i), Expression.VarK (2*i+1)⟩, i+1)
  | WireBundle.PairB o1 o2, i =>
      let (l1, i1) := makeLabels o1 i
      let (l2, i2) := makeLabels o2 i1
      ((l1, l2), i2)

/-- One garbled-table entry `⦃⦃(b, k)⦄_{kInner}⦄_{kOuter}`. -/
def gbEntry (kOuter kInner kPayload : Expression Shape.KeyS) (b : BitExpr) :
    Expression (Shape.EncS (Shape.EncS (Shape.PairS Shape.BitS Shape.KeyS))) :=
  Expression.Enc kOuter (Expression.Enc kInner
    (Expression.Pair (Expression.BitE b) kPayload))

/--
  `Gb` (LM18 §4).  The `Dup` case is the PRG one:
  `Gb(Dup, (b,(k⁰,k¹))) = ε, ((b,(G0 k⁰, G0 k¹)), (b,(G1 k⁰, G1 k¹)))`.
-/
def gb : {input output : WireBundle} -> (c : Circuit input output) -> labelType input -> ℕ ->
    (Expression (garbledShape c) × labelType output × ℕ)
  | _, _, Circuit.SwapC _ _, (i1, i2), ctr => (Expression.Eps, (i2, i1), ctr)
  | _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), ctr => (Expression.Eps, ((i1, i2), i3), ctr)
  | _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), ctr => (Expression.Eps, (i1, (i2, i3)), ctr)
  | _, _, Circuit.DupC, l, ctr =>
      (Expression.Eps,
       (⟨l.bit, Expression.G0 l.key0, Expression.G0 l.key1⟩,
        ⟨l.bit, Expression.G1 l.key0, Expression.G1 l.key1⟩), ctr)
  | _, _, Circuit.FirstC c _, (b1, b2), ctr =>
      let (c', b1', ctr') := gb c b1 ctr
      (c', (b1', b2), ctr')
  | _, _, Circuit.ComposeC c1 c2, b, ctr =>
      let (c1', b', ctr1) := gb c1 b ctr
      let (c2', b'', ctr2) := gb c2 b' ctr1
      (Expression.Pair c1' c2', b'', ctr2)
  | _, _, Circuit.NandC, (li, lj), ctr =>
      let Bh := BitExpr.VarB ctr
      let Kh0 : Expression Shape.KeyS := Expression.VarK (2*ctr)
      let Kh1 : Expression Shape.KeyS := Expression.VarK (2*ctr+1)
      let c00 := gbEntry li.key0 lj.key0 Kh1 (BitExpr.Not Bh)
      let c01 := gbEntry li.key0 lj.key1 Kh1 (BitExpr.Not Bh)
      let c10 := gbEntry li.key1 lj.key0 Kh1 (BitExpr.Not Bh)
      let c11 := gbEntry li.key1 lj.key1 Kh0 Bh
      (Expression.Perm (Expression.BitE li.bit)
         (Expression.Perm (Expression.BitE lj.bit) c00 c01)
         (Expression.Perm (Expression.BitE lj.bit) c10 c11),
       ⟨Bh, Kh0, Kh1⟩, ctr+1)

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
      let Bh := BitExpr.VarB ctr
      let Kh0 : Expression Shape.KeyS := Expression.VarK (2*ctr)
      let Kh1 : Expression Shape.KeyS := Expression.VarK (2*ctr+1)
      let e00 := gbEntry li.key0 lj.key0 Kh0 Bh
      let e01 := gbEntry li.key0 lj.key1 Kh0 Bh
      let e10 := gbEntry li.key1 lj.key0 Kh0 Bh
      let e11 := gbEntry li.key1 lj.key1 Kh0 Bh
      (Expression.Perm (Expression.BitE li.bit)
         (Expression.Perm (Expression.BitE lj.bit) e00 e01)
         (Expression.Perm (Expression.BitE lj.bit) e10 e11),
       ⟨Bh, Kh0, Kh1⟩, ctr+1)

-- ---------------------------------------------------------------------------------
-- Encoding, masks, and the two top-level algorithms.
-- ---------------------------------------------------------------------------------

/-- `GEnc` (LM18 §4). -/
def gEnc : {b : WireBundle} -> labelType b -> bundleBool b -> Expression (encodedShape b)
  | WireBundle.SimpleB, l, x =>
      cond x (Expression.Pair (Expression.BitE (BitExpr.Not l.bit)) l.key1)
             (Expression.Pair (Expression.BitE l.bit) l.key0)
  | WireBundle.PairB _ _, (l1, l2), (x1, x2) => Expression.Pair (gEnc l1 x1) (gEnc l2 x2)

/-- `GMask` (LM18 §4). -/
def gMask : {b : WireBundle} -> labelType b -> Expression (maskShape b)
  | WireBundle.SimpleB, l => Expression.BitE l.bit
  | WireBundle.PairB _ _, (l1, l2) => Expression.Pair (gMask l1) (gMask l2)

/-- `SEnc` (LM18 §5): the simulator has no input, so it always takes the first key. -/
def sEnc : {b : WireBundle} -> labelType b -> Expression (encodedShape b)
  | WireBundle.SimpleB, l => Expression.Pair (Expression.BitE l.bit) l.key0
  | WireBundle.PairB _ _, (l1, l2) => Expression.Pair (sEnc l1) (sEnc l2)

/-- `SMask` (LM18 §5): the masks are adjusted by the circuit's output value. -/
def sMask : {b : WireBundle} -> labelType b -> bundleBool b -> Expression (maskShape b)
  | WireBundle.SimpleB, l, y =>
      cond y (Expression.BitE (BitExpr.Not l.bit)) (Expression.BitE l.bit)
  | WireBundle.PairB _ _, (l1, l2), (y1, y2) => Expression.Pair (sMask l1 y1) (sMask l2 y2)

/-- A label expression, viewed as an `Expression`.  LM18 writes `(C̃, u)` for the pairing of
    a garbled circuit with a label expression; this is the `u` half. -/
def labelToExpr : {b : WireBundle} -> labelType b -> Expression (labelShape b)
  | WireBundle.SimpleB, l =>
      Expression.Pair (Expression.BitE l.bit) (Expression.Pair l.key0 l.key1)
  | WireBundle.PairB _ _, (l1, l2) => Expression.Pair (labelToExpr l1) (labelToExpr l2)

def garbleShapeFull {s t : WireBundle} (c : Circuit s t) : Shape :=
  Shape.PairS (garbledShape c) (Shape.PairS (encodedShape s) (maskShape t))

/-- `Garble(C, x)` (LM18 §4). -/
def Garble {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    Expression (garbleShapeFull c) :=
  let (u, ctr) := makeLabels s 0
  let r := gb c u ctr
  Expression.Pair r.1 (Expression.Pair (gEnc u x) (gMask r.2.1))

/-- `Simulate(C, y)` (LM18 §5). -/
def Simulate {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    Expression (garbleShapeFull c) :=
  let (u, ctr) := makeLabels s 0
  let r := sim c u ctr
  Expression.Pair r.1 (Expression.Pair (sEnc u) (sMask r.2.1 y))

end PRG
