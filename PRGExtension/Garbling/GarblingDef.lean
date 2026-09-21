import PRGExtension.Garbling.Circuits

/-!
# The PRG-based garbling scheme

`Garble` garbles a circuit and `GEval` evaluates a garbled circuit symbolically, following
LM18 §4.

The one difference from the encryption-only framework: `Gb(Dup, ·)` derives the two output
wire labels with the PRG rather than duplicating the input label, which is what makes fan-out
possible without a fresh key per copy.  That single change is why a wire label here carries
key *expressions* `(B_h, K_h⁰, K_h¹)` rather than a wire index.
-/

namespace PRG

/-- `Label(s)` (LM18 §4): a fresh atomic label per wire.  Wire `h` gets bit variable
    `B_h = VarB h` and keys `K_h⁰ = VarK (2h)`, `K_h¹ = VarK (2h+1)`. -/
def makeLabels : (input : WireBundle) -> ℕ -> labelType input × ℕ
  | WireBundle.SimpleB, i =>
      (⟨i, Expression.VarK (2*i), Expression.VarK (2*i+1)⟩, i+1)
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
      let Bh : BitExpr := BitExpr.VarB ctr
      let Kh0 : Expression Shape.KeyS := Expression.VarK (2*ctr)
      let Kh1 : Expression Shape.KeyS := Expression.VarK (2*ctr+1)
      let c00 := gbEntry li.key0 lj.key0 Kh1 (BitExpr.Not Bh)
      let c01 := gbEntry li.key0 lj.key1 Kh1 (BitExpr.Not Bh)
      let c10 := gbEntry li.key1 lj.key0 Kh1 (BitExpr.Not Bh)
      let c11 := gbEntry li.key1 lj.key1 Kh0 Bh
      (Expression.Perm (Expression.BitE li.bitE)
         (Expression.Perm (Expression.BitE lj.bitE) c00 c01)
         (Expression.Perm (Expression.BitE lj.bitE) c10 c11),
       ⟨ctr, Kh0, Kh1⟩, ctr+1)
-- ---------------------------------------------------------------------------------
-- Encoding, masks, and the two top-level algorithms.
-- ---------------------------------------------------------------------------------

/-- `GEnc` (LM18 §4). -/
def gEnc : {b : WireBundle} -> labelType b -> bundleBool b -> encodedLabelType b
  | WireBundle.SimpleB, l, x =>
      cond x (Expression.Pair (Expression.BitE (BitExpr.Not l.bitE)) l.key1)
             (Expression.Pair (Expression.BitE l.bitE) l.key0)
  | WireBundle.PairB _ _, (l1, l2), (x1, x2) => (gEnc l1 x1, gEnc l2 x2)
/-- `GMask` (LM18 §4). -/
def gMask : {b : WireBundle} -> labelType b -> maskedLabelType b
  | WireBundle.SimpleB, l => Expression.BitE l.bitE
  | WireBundle.PairB _ _, (l1, l2) => (gMask l1, gMask l2)
def encodedLabelToExpr : {b : WireBundle} -> encodedLabelType b -> Expression (encodedShape b)
  | WireBundle.SimpleB, x => x
  | WireBundle.PairB _ _, (l1, l2) =>
      Expression.Pair (encodedLabelToExpr l1) (encodedLabelToExpr l2)
def maskedLabelToExpr : {b : WireBundle} -> maskedLabelType b -> Expression (maskShape b)
  | WireBundle.SimpleB, x => x
  | WireBundle.PairB _ _, (m1, m2) =>
      Expression.Pair (maskedLabelToExpr m1) (maskedLabelToExpr m2)
/-- A label expression, viewed as an `Expression`.  LM18 writes `(C̃, u)` for the pairing of
    a garbled circuit with a label expression; this is the `u` half. -/
def labelToExpr : {b : WireBundle} -> labelType b -> Expression (labelShape b)
  | WireBundle.SimpleB, l =>
      Expression.Pair (Expression.BitE l.bitE) (Expression.Pair l.key0 l.key1)
  | WireBundle.PairB _ _, (l1, l2) => Expression.Pair (labelToExpr l1) (labelToExpr l2)
def garbleShapeFull {s t : WireBundle} (c : Circuit s t) : Shape :=
  Shape.PairS (garbledShape c) (Shape.PairS (encodedShape s) (maskShape t))
/-- `Garble(C, x)` (LM18 §4). -/
def Garble {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    Expression (garbleShapeFull c) :=
  let u := (makeLabels s 0).1
  let r := gb c u (makeLabels s 0).2
  Expression.Pair r.1
    (Expression.Pair (encodedLabelToExpr (gEnc u x)) (maskedLabelToExpr (gMask r.2.1)))

/-! ## Projectivity

LM18 and the base paper require a garbling scheme to be *projective* before it can be used for
two-party computation: `Garble` must factor as a function of the circuit alone, followed by a
selection of one label per wire according to the input bits.  Only then can the input labels be
handed over by oblivious transfer, one wire at a time, without the garbler learning the input.

The base paper defines `Garble` *through* `preGarble` and recovers the direct form as a lemma.
Here `Garble` is the direct form, so the adaptation runs the other way: `preGarble` is defined
separately and `Garble_projective` proves that `Garble` factors through it.  The content is the
same, and it is already true by construction — `makeLabels` and `gb` never see the input. -/

/-- A pair of encoded labels per wire: the one to hand over for `true` and the one for
`false`. -/
def projectionLabelType : WireBundle -> Type :=
  bundleType (Expression (Shape.PairS Shape.BitS Shape.KeyS)
    × Expression (Shape.PairS Shape.BitS Shape.KeyS))

/-- Both encodings of a wire label, computed without reference to any input. -/
def gInputToProjection : {b : WireBundle} -> labelType b -> projectionLabelType b
  | WireBundle.SimpleB, l =>
      (Expression.Pair (Expression.BitE (BitExpr.Not l.bitE)) l.key1,
       Expression.Pair (Expression.BitE l.bitE) l.key0)
  | WireBundle.PairB _ _, (l1, l2) => (gInputToProjection l1, gInputToProjection l2)

/-- `proj` (base paper §3): select one label per wire according to the input bits.  This is the
part an oblivious transfer delivers. -/
def makeProjection : {b : WireBundle} -> projectionLabelType b -> bundleBool b ->
    encodedLabelType b
  | WireBundle.SimpleB, l, t => cond t l.1 l.2
  | WireBundle.PairB _ _, (l1, l2), (t1, t2) => (makeProjection l1 t1, makeProjection l2 t2)

/-- **`preGarble`**: everything `Garble` produces that does not depend on the input — the
garbled circuit, the output mask, and both labels for each input wire. -/
def preGarble {s t : WireBundle} (c : Circuit s t) :
    Expression (garbledShape c) × maskedLabelType t × projectionLabelType s :=
  let u := (makeLabels s 0).1
  let r := gb c u (makeLabels s 0).2
  (r.1, gMask r.2.1, gInputToProjection u)

/-- Selecting from both encodings agrees with encoding directly. -/
lemma gEncCorrect : ∀ {b : WireBundle} (l : labelType b) (x : bundleBool b),
    makeProjection (gInputToProjection l) x = gEnc l x
  | WireBundle.SimpleB, l, x => by cases x <;> simp [gInputToProjection, makeProjection, gEnc]
  | WireBundle.PairB u w, l, x => by
      obtain ⟨l1, l2⟩ := l; obtain ⟨x1, x2⟩ := x
      simp only [gInputToProjection, makeProjection, gEnc]
      rw [gEncCorrect l1 x1, gEncCorrect l2 x2]

/-- **The scheme is projective.**  `preGarble c` does not mention `x`; the input enters only
through `makeProjection`, one wire at a time.  This is the property the base paper's §3 route
from garbling to two-party computation requires. -/
theorem Garble_projective {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    Garble c x =
      Expression.Pair (preGarble c).1
        (Expression.Pair (encodedLabelToExpr (makeProjection (preGarble c).2.2 x))
          (maskedLabelToExpr (preGarble c).2.1)) := by
  simp [Garble, preGarble, gEncCorrect]

/-! ## Symbolic evaluation of a garbled circuit -/

def extractPair : {s1 s2 : Shape} -> (e : Expression (Shape.PairS s1 s2)) ->
    Option (Expression s1 × Expression s2)
  | _, _, Expression.Pair e1 e2 => some (e1, e2)
  | _, _, _ => none
def condSwap {T : Type} (b : Bool) (x y : T) : (T × T) := if b then (y, x) else (x, y)
def castVarOrNegVar2Bool (v : VarOrNegVar) : Bool :=
  match v with | VarOrNegVar.Var _ => true | VarOrNegVar.NegVar _ => false
def exprToVarOrNegVar2 (v : BitExpr) : Option VarOrNegVar :=
  match normalizeB v with
  | BitExpr.VarB n => some (VarOrNegVar.Var n)
  | BitExpr.Not (BitExpr.VarB n) => some (VarOrNegVar.NegVar n)
  | _ => none
def exprToVarOrNegVar : Expression Shape.BitS -> Option VarOrNegVar
  | Expression.BitE b => exprToVarOrNegVar2 b
/-- Are two bit expressions the same variable, and do they agree or differ by a negation? -/
def xorVarB (var1 var2 : Expression Shape.BitS) : Option Bool := do
  let v1 <- exprToVarOrNegVar var1
  let v2 <- exprToVarOrNegVar var2
  if castVarOrNegVar v1 = castVarOrNegVar v2 then
    xor (castVarOrNegVar2Bool v1) (castVarOrNegVar2Bool v2)
  else none
/-- Select the half of a `π[b](·,·)` indicated by the encoded bit. -/
def extractPerm (var : Expression Shape.BitS) : {s1 : Shape} ->
    (e : Expression (Shape.PairS s1 s1)) -> Option (Expression s1 × Expression s1)
  | _, Expression.Perm b e1 e2 => do
      let isSwap <- xorVarB b var
      some (condSwap isSwap e1 e2)
  | _, _ => none
def decrypt (key : Expression Shape.KeyS) : {s : Shape} ->
    (ciphertext : Expression (Shape.EncS s)) -> Option (Expression s)
  | _, Expression.Enc keyReal plaintext => if keyReal = key then plaintext else none
  | _, Expression.Hidden _ => none
/-- `GEv` (LM18 §4).  `Dup` is the PRG case. -/
def gEv : {inputBundle outputBundle : WireBundle} -> (c : Circuit inputBundle outputBundle) ->
    (c' : Expression (garbledShape c)) -> (input : encodedLabelType inputBundle) ->
    Option (encodedLabelType outputBundle)
  | .((_x, _y)), .(_), Circuit.SwapC _x _y, Expression.Eps, (i1, i2) => some (i2, i1)
  | .((_x, (_y, _z))), .(_), Circuit.AssocC _x _y _z, Expression.Eps, (w1, (w2, w3)) =>
      some ((w1, w2), w3)
  | .(((_x, _y), _z)), .(_), Circuit.UnAssocC _x _y _z, Expression.Eps, ((w1, w2), w3) =>
      some (w1, (w2, w3))
  -- LM18: GEv(Dup, ε, (b,k)) = ((b, G0 k), (b, G1 k))
  | .(_), .(_), Circuit.DupC, Expression.Eps, Expression.Pair b k =>
      some (Expression.Pair b (Expression.G0 k), Expression.Pair b (Expression.G1 k))
  | .((o, o)), .(_), Circuit.NandC, c',
      ((Expression.Pair b₀' k₀), (Expression.Pair b₁' k₁)) => do
      let (c1, _) <- extractPerm b₀' c'
      let (c2, _) <- extractPerm b₁' c1
      let c3 <- decrypt k₀ c2
      let c4 <- decrypt k₁ c3
      some c4
  | .((_, _u)), .(_), Circuit.FirstC c _u, c', (b₁, b₂) => do
      let b₁' <- gEv c c' b₁
      some (b₁', b₂)
  | .(_), .(_), Circuit.ComposeC c1 c2, c', b => do
      have Heq : garbledShape (Circuit.ComposeC c1 c2)
          = Shape.PairS (garbledShape c1) (garbledShape c2) := by
        simp [garbledShape, garbledShapeGen]
      let (c1', c2') <- extractPair (Heq ▸ c')
      let b' <- gEv c1 c1' b
      gEv c2 c2' b'
/-- `Decode` (LM18 §4): compare each encoded bit against its output mask. -/
def decode {bundle : WireBundle} (input : encodedLabelType bundle) (mask : maskedLabelType bundle) :
    Option (bundleBool bundle) :=
  match bundle, input, mask with
  | WireBundle.SimpleB, (Expression.Pair bl _), bm => xorVarB bl bm
  | WireBundle.PairB _ _, (l1, l2), (m1, m2) => do
      let x <- decode l1 m1
      let y <- decode l2 m2
      some (x, y)
def GEval {s t : WireBundle} (c : Circuit s t) (c' : Expression (garbledShape c))
    (input : encodedLabelType s) (mask : maskedLabelType t) : Option (bundleBool t) := do
  let encodedOutput <- gEv c c' input
  decode encodedOutput mask
def parseEncodedBundle : {b : WireBundle} -> Expression (encodedShape b) -> Option (encodedLabelType b)
  | WireBundle.SimpleB, e => some e
  | WireBundle.PairB _ _, e => do
      let (l', r') <- extractPair e
      let l'' <- parseEncodedBundle l'
      let r'' <- parseEncodedBundle r'
      some (l'', r'')
def parseMaskedBundle : {b : WireBundle} -> Expression (maskShape b) -> Option (maskedLabelType b)
  | WireBundle.SimpleB, e => some e
  | WireBundle.PairB _ _, e => do
      let (l', r') <- extractPair e
      let l'' <- parseMaskedBundle l'
      let r'' <- parseMaskedBundle r'
      some (l'', r'')
/-- Take apart the `Expression` produced by `Garble`/`Simulate`. -/
def parseGarbleOutput {s t : WireBundle} (c : Circuit s t) (e : Expression (garbleShapeFull c)) :
    Option (Expression (garbledShape c) × encodedLabelType s × maskedLabelType t) := do
  let (garbled, rest) <- extractPair e
  let (encoded, masked) <- extractPair rest
  let encoded' <- parseEncodedBundle encoded
  let masked' <- parseMaskedBundle masked
  some (garbled, encoded', masked')
def GEvalExpr {s t : WireBundle} (c : Circuit s t) (e : Expression (garbleShapeFull c)) :
    Option (bundleBool t) := do
  let (c', input, mask) <- parseGarbleOutput c e
  GEval c c' input mask
/-- Garble then evaluate, for testing. -/
def testGarbleEval {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) : Option (bundleBool t) :=
  GEvalExpr c (Garble c x)
/--
  **LM18 Theorem 4 (correctness).**  `GEval(C, Garble(C,x)) = C(x)`.

  Written as a named proposition; `scratch/GarbleCorrectness.lean` checks it by `#eval` on
  every input of several small circuits, including ones with `Dup` (so the PRG path in both
  `Gb` and `GEv` is exercised).
-/
def Theorem4 : Prop :=
  ∀ {s t : WireBundle} (c : Circuit s t) (x : bundleBool s),
    testGarbleEval c x = some (evalCircuit c x)

end PRG
