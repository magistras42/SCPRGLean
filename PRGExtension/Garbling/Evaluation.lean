import PRGExtension.Garbling.GarblingDef

/-!
# Evaluating PRG-based garbled circuits (LM18 §4, `GEv` / `Decode` / `GEval`)

Ported from the encryption-only framework.  The only case that differs is `Dup`:
`GEv(Dup, ε, (b,k)) = ((b, G0 k), (b, G1 k))` — the evaluator re-derives the two output
wire keys with the PRG, mirroring `Gb(Dup, ·)`.
-/

namespace PRG

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
