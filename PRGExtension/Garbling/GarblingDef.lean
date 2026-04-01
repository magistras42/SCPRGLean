import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.SymbolicIndistinguishability

-- This file fefines the garbling scheme. The main definitions are:
--   * `Garble`: garbles the circuit,
--   * `GEval`: evaluates the garbled circuit symbolically.

def makeKeyLabel (n : ℕ) (v : Bool) : ℕ :=
  2 * n + cond v 1 0

def makeKey (n : ℕ) (b : Bool) : Expression Shape.KeyS :=
  Expression.VarK (makeKeyLabel n b)

def getKeyTruth : (x : Expression Shape.KeyS) -> Bool
| Expression.VarK k => k%2 == 1

def getKeyIndex : (x : Expression Shape.KeyS) -> ℕ
| Expression.VarK k => k/2

@[simp]
def wireBundle2Shape (t : Shape) : WireBundle ->  Shape
| o => t
| (o1, o2) => Shape.PairS (wireBundle2Shape t o1) (wireBundle2Shape t o2)


def castVarOrNegVar2Bool (v : VarOrNegVar) : Bool :=
   match v with
   | VarOrNegVar.Var _ => true
   | VarOrNegVar.NegVar _ => false

def exprToVarOrNegVar2 (v : BitExpr) : Option VarOrNegVar :=
  match normalizeB v with
  | BitExpr.VarB n => some (VarOrNegVar.Var n)
  | BitExpr.Not (BitExpr.VarB n) => some (VarOrNegVar.NegVar n)
  | _ => none

def exprToVarOrNegVar (v : Expression Shape.BitS) : Option VarOrNegVar :=
  exprToVarOrNegVar2 v

-- Since we use identifiers of type ℕ×{0,1} we need to define an injective function that transforms them into ℕ used by the Expression module.
-- Next, let us start with a function that defines the shape of the label expression for the given wire bundle.
-- Next, we define a function that returns the type of the garbled circuit for the given circuit.
-- This is a little weird, hopefully we can show that the type depends only on topology of the circuit.
def garbledShapeGen (nandT : Shape) : {input output : WireBundle} -> Circuit input output -> Shape
| _, _, Circuit.SwapC _ _ => Shape.EmptyS
| _, _, Circuit.AssocC _ _ _ => Shape.EmptyS
| _, _, Circuit.UnAssocC _ _ _ => Shape.EmptyS
| _, _, Circuit.DupC => Shape.EmptyS
| .(_), .(_), Circuit.ComposeC c1 c2 => Shape.PairS (garbledShapeGen nandT c1) (garbledShapeGen nandT c2)
| _, _, Circuit.FirstC c _ => garbledShapeGen nandT c
| _, _, Circuit.NandC =>
  nandT

-- Next, we define a function that returns the type of the garbled circuit for the given circuit.
-- This is a little weird, hopefully we can show that the type depends only on topology of the circuit.
def garbledShape : {input output : WireBundle} -> Circuit input output -> Shape :=
  garbledShapeGen
  (let one := Shape.EncS (Shape.EncS (Shape.PairS Shape.BitS Shape.KeyS))
  let two := Shape.PairS one one
  Shape.PairS two two)


def getFreshLabel : StateM ℕ ℕ := do
  let n ← get
  modify (λ x => x + 1)
  pure n


def gb_entry (kl₀ kr₀ kht : Expression Shape.KeyS) (Bh : BitExpr) :=
  Expression.Enc kl₀ (Expression.Enc kr₀ (Expression.Pair (Expression.BitE Bh) kht))

-- Next, we define a function that garbles the given circuit.
-- We need the monad to generate fresh labels.
def gb :  {input output : WireBundle} ->
  (c : Circuit input output)  -> (inlbl : labelType input) -> (ctr : ℕ) -> ((Expression (garbledShape c)) × (labelType output) × ℕ)
| .(WireBundle.PairB _ _), .(WireBundle.PairB _ _), Circuit.SwapC _ _, (i1, i2), ctr => (Expression.Eps, (i2, i1), ctr)
| _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), ctr => (Expression.Eps, ((i1, i2), i3), ctr)
| _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), ctr => (Expression.Eps, (i1, (i2, i3)), ctr)
| _, _, Circuit.DupC, x, ctr =>
  (Expression.Eps, (x, x), ctr)
| _, _, Circuit.FirstC c _, ⟨b₁, b₂⟩, ctr =>
  let (c', b₁', i1) := gb c b₁ ctr
  (c', (b₁', b₂), i1)
| _, _, Circuit.ComposeC c₁ c₂, b, ctr₀ =>
  let (c₁', b', ctr₁) := gb c₁ b ctr₀
  let (c₂', b'', ctr₂) := gb c₂ b' ctr₁
  (Expression.Pair c₁' c₂', b'', ctr₂)
| _, _, Circuit.NandC, (nl, nr), ctr =>
  let Bh := BitExpr.VarB ctr
  let khf := Expression.VarK (makeKeyLabel ctr false)
  let kht := Expression.VarK (makeKeyLabel ctr true)
  let c00 := gb_entry (makeKey nl false) (makeKey nr false) kht (BitExpr.Not Bh)
  let c01 := gb_entry (makeKey nl false) (makeKey nr true) kht (BitExpr.Not Bh)
  let c10 := gb_entry (makeKey nl true) (makeKey nr false) kht (BitExpr.Not Bh)
  let c11 := gb_entry (makeKey nl true) (makeKey nr true) khf (Bh)
  let bl := Expression.BitE (BitExpr.VarB nl)
  let br := Expression.BitE (BitExpr.VarB nr)
  let c := Expression.Perm bl (Expression.Perm br c00 c01) (Expression.Perm br c10 c11)
  (c, ctr, ctr+1)


-- The function Label(s) from the paper.
def makeLabelExp : (input : WireBundle) -> (i : ℕ) -> labelType input × ℕ
  | (o1, o2), i =>
    let (l1, i1) := makeLabelExp o1 i
    let (l2, i2) := makeLabelExp o2 i1
    ((l1, l2), i2)
  | o, i =>
    (i, i+1)

-- Each input wire should be 'encoded', i.e.
-- for each wire we should have one bit and one key.

@[simp]
def wireInfoShape := (Shape.PairS Shape.BitS Shape.KeyS)

@[simp]
def inputTokenType := Expression wireInfoShape

-- projection scheme generates a pair of values for each wire
@[simp]
def projectionLabelType : WireBundle -> Type :=
  bundleType (inputTokenType × inputTokenType)

@[simp]
def encodedLabelType : WireBundle -> Type :=
  bundleType inputTokenType

-- It is also useful to have shape for this type ...
def garbledInputShape : WireBundle -> Shape := wireBundle2Shape wireInfoShape

-- ... and a function that converts a value to an expression.
def encodedLabelToExpr : {bundle : WireBundle} -> encodedLabelType bundle -> Expression (garbledInputShape bundle)
| o, x => x
| (_, _), (l1, l2) => Expression.Pair (encodedLabelToExpr l1) (encodedLabelToExpr l2)

def negatedBit (n : ℕ) (b : Bool) : BitExpr :=
  if b then BitExpr.Not (BitExpr.VarB n) else BitExpr.VarB n

def makeEntryForWire (n : ℕ) (truth : Bool) : inputTokenType :=
  Expression.Pair (Expression.BitE (negatedBit n truth)) (makeKey n truth)

-- in projective scheme, garbling generate pair of values for every input wire
def gInputToProjection :  {bundle : WireBundle} -> labelType bundle -> projectionLabelType bundle
| o, n => (makeEntryForWire n true, makeEntryForWire n false)
| (_, _), (l1, l2) => (gInputToProjection l1, gInputToProjection l2)

-- projection is done by choosing one entry for each input wire
def makeProjection : {bundle : WireBundle} -> projectionLabelType bundle -> (bundleBool bundle) -> encodedLabelType bundle
| o, (a,b), truth =>
  let t : Bool := truth
  if t then a else b
| (_, _), (l1, l2), (t1, t2) => (makeProjection l1 t1, makeProjection l2 t2)


-- The outut labels should be masked, i.e. we they should only store the bit value,
-- of each output wire.
@[simp]
def maskedLabelType : WireBundle -> Type := bundleType (Expression Shape.BitS)

-- It is also useful to have shape for this type ...
def maskedLabelShape : WireBundle -> Shape := wireBundle2Shape Shape.BitS

-- ... and a function that converts a value to an expression.
def maskedLabelToExpr : {bundle : WireBundle} -> maskedLabelType bundle -> Expression (maskedLabelShape bundle)
| o, bl => bl
| (_, _), (l1, l2) => Expression.Pair (maskedLabelToExpr l1) (maskedLabelToExpr l2)

-- The function GMask from the paper. It maks the output bundle.
def gMask : (bundle : WireBundle) -> labelType bundle -> maskedLabelType bundle
| o, (n) => Expression.BitE (BitExpr.VarB n)
| (o1, o2), (l1, l2) => (gMask o1 l1, gMask o2 l2)

-- We are now ready to combine all the parts together and compute the preGarble function.

def garbleOutputType {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) : Type :=
  (Expression (garbledShape c) × maskedLabelType outputBundle) × projectionLabelType inputBundle

def garbledCircuitType {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) : Type :=
  Expression (garbledShape c) × maskedLabelType outputBundle

def garbleOutputTypeAfterProjection {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) : Type :=
  (Expression (garbledShape c)  × maskedLabelType outputBundle) × encodedLabelType inputBundle

abbrev garbleOutputShape {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) : Shape :=
  Shape.PairS (Shape.PairS (garbledShape c) (maskedLabelShape outputBundle)) (garbledInputShape inputBundle)

abbrev garbledCircuitShape {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) : Shape :=
  Shape.PairS (garbledShape c) (maskedLabelShape outputBundle)

def garbleOutputToExpr {inputBundle outputBundle : WireBundle} {c : Circuit inputBundle outputBundle} : garbleOutputTypeAfterProjection c -> Expression (garbleOutputShape c)
| ((c, out), input) => ⸨⸨c, maskedLabelToExpr out⸩, encodedLabelToExpr input ⸩

def preGarble (c : Circuit inputBundle outputBundle) :
  (garbledCircuitType c) × (projectionLabelType inputBundle) :=
    let (inlbl, i) := makeLabelExp inputBundle 0
    let (c', outlbl, _) := gb c inlbl i
    let encodedInput := gInputToProjection inlbl
    let maskedOutput := gMask outputBundle outlbl
    ((c', maskedOutput), encodedInput)


-- main function of this module - definition of Garbling
def Garble (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle)
  : Expression (Shape.PairS (garbledCircuitShape c) (garbledInputShape inputBundle)) :=
  let (garbledCircuit, inputPairs) := preGarble c
  garbleOutputToExpr (garbledCircuit, makeProjection inputPairs input)


-- it is convenient to elide projection step, as follows:


-- The function GEnc from the paper. It encodes the input bundle,
-- given the label expression and the input value.
def gEnc : {bundle : WireBundle} -> labelType bundle -> (bundleBool bundle) -> encodedLabelType bundle
| o, n, truth => makeEntryForWire n truth
| (_, _), (l1, l2), (b1, b2) => (gEnc l1 b1, gEnc l2 b2)

lemma gEncCorrect {bundle : WireBundle} (label : labelType bundle) (input : bundleBool bundle) :
  makeProjection (gInputToProjection label) input = gEnc label input :=
by
  induction bundle <;> simp [gInputToProjection, makeProjection, gEnc]
  case SimpleB =>
    simp [makeEntryForWire]
    cases input <;> simp []
  case PairB Ha Hb =>
    cases label with | mk l1 l2 =>
    cases input with | mk i1 i2 =>
    simp [gInputToProjection, makeProjection, gEnc, Ha, Hb]

-- The main function that garbles the circuit in one step (no explicit)
def GarbleNoProjection {inputBundle outputBundle : WireBundle}  (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle) : Expression (garbleOutputShape c) :=
  let (inlbl, i) := makeLabelExp inputBundle 0
  let (c', outlbl, _) := gb c inlbl i
  let encodedInput := gEnc inlbl input
  let maskedOutput := gMask outputBundle outlbl
  garbleOutputToExpr ((c', maskedOutput), encodedInput)


lemma GarbleExprNoProjection {c : Circuit inputBundle outputBundle} (input : bundleBool inputBundle) :
  Garble c input = GarbleNoProjection c input :=
by
  simp [Garble, preGarble, GarbleNoProjection, gEncCorrect]

-- --- === EVALUATING GARBLED CIRCUITS ===


-- To make sure that everything is working correctly, we implement a decode function.
-- But first, we define some useful operations.

def extractPair : {s1 s2 : Shape} -> (e : Expression (Shape.PairS s1 s2)) -> Option (Expression s1 × Expression s2)
| _, _, Expression.Pair e1 e2 =>
  some (e1, e2)
| _, _, _ => none

def condSwap {T : Type} (b : Bool) (x y : T) : (T × T) :=
  if b then (y, x) else (x, y)

def xorVarB (var1 var2 : Expression Shape.BitS) : Option Bool := do
  let v1 <- exprToVarOrNegVar var1
  let v2 <- exprToVarOrNegVar var2
  if castVarOrNegVar v1 = castVarOrNegVar v2 then
    xor (castVarOrNegVar2Bool v1) (castVarOrNegVar2Bool v2)
  else none

def extractPerm (var : Expression Shape.BitS) : {s1 : Shape} -> (e : Expression (Shape.PairS s1 s1)) -> Option (Expression s1 × Expression s1)
| _, Expression.Perm b e1 e2 => do
  let isSwap <- xorVarB b var
  some (condSwap isSwap e1 e2)
| _, _ => none

def decrypt (key : Expression Shape.KeyS) : {s : Shape} -> (ciphertext : Expression (Shape.EncS s)) -> Option (Expression s)
| _, Expression.Enc keyReal plaintext =>
  if keyReal = key then plaintext else none
| _, Expression.Hidden _ => none

def gEv : {inputBundle outputBundle : WireBundle} -> (c : Circuit inputBundle outputBundle) -> (c' : Expression (garbledShape c)) -> (input : encodedLabelType inputBundle) -> Option (encodedLabelType outputBundle)
| .((_x, _y)),  .(_), Circuit.SwapC _x _y , Expression.Eps, (i1, i2) =>
  some (i2, i1)
| .((_x, (_y, _z))), .(_), Circuit.AssocC _x _y _z, Expression.Eps, (w1, (w2, w3)) => some ((w1, w2), w3)
| .(((_x, _y), _z)), .(_), Circuit.UnAssocC _x _y _z, Expression.Eps, ((w1, w2), w3) => some (w1, (w2, w3))
| .(_), .(_), Circuit.DupC, Expression.Eps, x => some (x, x)
| .((o, o)), .(_), Circuit.NandC, c', ((Expression.Pair b₀' k₀), (Expression.Pair b₁' k₁)) => do
  let (c1, _) <- extractPerm b₀' c'
  let (c2, _) <- extractPerm b₁' c1
  let c3 <- decrypt k₀ c2
  let c4 <- decrypt k₁ c3
  some c4
| .((_, _u)), .(_), Circuit.FirstC c _u, c', (b₁, b₂) => do
  let b₁' <- gEv c c' b₁
  some (b₁', b₂)
| .(_), .(_), Circuit.ComposeC c1 c2, c' , b => do
  have Heq : garbledShape (c1>>>c2) = Shape.PairS (garbledShape c1) (garbledShape c2) := by simp [garbledShape, garbledShapeGen]
  let (c1', c2') <- extractPair (Heq ▸ c')
  let b' <- gEv c1 c1' b
  gEv c2 c2' b'

  def decode {bundle : WireBundle} (input : encodedLabelType bundle) (mask : maskedLabelType bundle) : Option (bundleBool bundle) :=
  match bundle, input, mask with
  | o, (Expression.Pair bl _), bm =>
    xorVarB bl bm
  | (_, _), (l1, l2), (m1, m2) => do
    let x <- decode l1 m1
    let y <- decode l2 m2
    some (x, y)

  def GEval {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (c' : Expression (garbledShape c)) (input : encodedLabelType inputBundle) (mask : maskedLabelType outputBundle) : Option (bundleBool outputBundle) := do
    let encodedOutput <- gEv c c' input
    decode encodedOutput mask

  def parseEncodedBundle {b : WireBundle} (e : Expression (garbledInputShape b)) : Option (encodedLabelType b) :=
    match b with
    | o =>
      some e
    | (_, _) => do
      let (l', r') <- extractPair e
      let l'' <- parseEncodedBundle l'
      let r'' <- parseEncodedBundle r'
      some (l'', r'')

  def parseMaskedBundle {b : WireBundle} (e : Expression (maskedLabelShape b)) : Option (maskedLabelType b) :=
    match b with
    | o => some e
    | (_, _) => do
      let (l', r') <- extractPair e
      let l'' <- parseMaskedBundle l'
      let r'' <- parseMaskedBundle r'
      some (l'', r'')


  def parseGarbleOutput {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (garbleOutputExpr : Expression (garbleOutputShape c)) : Option (Expression (garbledShape c) × encodedLabelType inputBundle × maskedLabelType outputBundle) := do
    let (l, encodedLabel) <- extractPair garbleOutputExpr
    let (garble, maskedLabel) <- extractPair l
    let encodedLabel <- parseEncodedBundle encodedLabel
    let maskedLabel <- parseMaskedBundle maskedLabel
    some (garble, encodedLabel, maskedLabel)


  def GEvalExpr {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (garbleOutputExpr : Expression (garbleOutputShape c)) : Option (bundleBool outputBundle) := do
    let (c', input, mask) <- parseGarbleOutput c garbleOutputExpr
    GEval c c' input mask

  -- Now, we can compose garbling with evaluation, and test if the garbling and evaluation are correct.
  def testGarbleEval {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle) : Option (bundleBool outputBundle) :=
    GEvalExpr c (Garble c input)
