import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleProof

--This file characterizes `adversaryView garbledCircuit`, by proving equivalence with `GarbleExprHole`.

def makeHoleEntry (b1 b2 : Bool) (kl kr kht: Expression Shape.KeyS) (B : BitExpr) : Expression (Shape.BitS.PairS Shape.KeyS).EncS.EncS :=
  if not b1 then
    Expression.Hidden (kl)
  else
    if not b2 then
      Expression.Enc kl (Expression.Hidden kr)
    else
      Expression.Enc kl (Expression.Enc kr (Expression.Pair (Expression.BitE B) kht))



def gbHole :  {input output : WireBundle} -> (f : ℕ -> Bool) -> (c : Circuit input output)  -> (inlbl : labelType input) -> (i : ℕ)  -> ((Expression (garbledShape c)) × (labelType output) × ℕ)
| .(WireBundle.PairB _ _), .(WireBundle.PairB _ _), _, Circuit.SwapC _ _, (i1, i2), i =>
  (Expression.Eps, (i2, i1), i)
| _, _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), i => (Expression.Eps, ((i1, i2), i3), i)
| _, _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), i => (Expression.Eps, (i1, (i2, i3)), i)
| _, _, _, Circuit.DupC, n, i =>
  let w := (n, n)
  (Expression.Eps, w, i)
| _, _, f, Circuit.FirstC c _, ⟨b₁, b₂⟩, i =>
  let (c', b₁', i2) := gbHole f c b₁ i
  (c', (b₁', b₂), i2)
| _, _, f, Circuit.ComposeC c1 c2, b, i0 =>
  let (c₁', b', i1) := gbHole f c1 b i0
  let (c₂', b'', i2) := gbHole f c2 b' i1
  (Expression.Pair c₁' c₂', b'', i2)
| _, _, f, Circuit.NandC, (nl, nr), i =>
  let h := i
  let Bh := BitExpr.VarB h
  let khf := makeKey h false
  let kht := makeKey h true
  let c00 := makeHoleEntry (not (f nl)) (not (f nr)) (makeKey nl false) (makeKey nr false) kht (BitExpr.Not Bh)
  let c01 := makeHoleEntry (not (f nl)) ((f nr)) (makeKey nl false) (makeKey nr true) kht (BitExpr.Not Bh)
  let c10 := makeHoleEntry ((f nl)) (not (f nr)) (makeKey nl true) (makeKey nr false) kht (BitExpr.Not Bh)
  let c11 := makeHoleEntry ((f nl)) ((f nr)) (makeKey nl true) (makeKey nr true) khf (Bh)
  let bl := Expression.BitE (BitExpr.VarB nl)
  let br := Expression.BitE (BitExpr.VarB nr)
  let c := Expression.Perm bl (Expression.Perm br c00 c01) (Expression.Perm br c10 c11)
  (c, h, i+1)

def eval_gbHole_i : forall {input output : WireBundle} (f₁ f₂ : ℕ -> Bool) (c : Circuit input output) (inlbl : labelType input) (i : ℕ),
  (evalTotal c inlbl f₁ i).2 = (gbHole f₂ c inlbl i).2 := by
    intros input output f₁ f₂  c
    revert f₁ f₂
    induction c <;> (intros f₁ f₂ inlbl i; simp at inlbl; simp [evalTotal, gbHole])
    case ComposeC c₁ c₂ hc₁ hc₂ =>
      simp [hc₁ f₁ f₂]
      rw [hc₂]
    case FirstC c1 hc1 =>
      simp [hc1 f₁ f₂]

def makeHoleEntryCorrect (f : ℕ -> Bool) (ifi : ℕ) (keys : Finset (Expression Shape.KeyS)) (kl kr kht: Expression Shape.KeyS) (B : BitExpr) :
  let gbc := gb_entry kl kr kht B
  let holec := makeHoleEntry (f (getKeyIndex kl) = getKeyTruth kl) (f (getKeyIndex kr) = getKeyTruth kr) kl kr kht B
  (getKeyIndex kl) < ifi ->
  (getKeyIndex kr) < ifi ->
  keysAs keys f 0 ifi ->
  hideEncrypted keys gbc = holec
  := by
  intro gbc holec H1 H2 Has
  simp [gbc, gb_entry, hideEncrypted]
  have Xl : kl ∈ keys <-> (f (getKeyIndex kl) = getKeyTruth kl) := (by
    nth_rw 1 [getToMakeKey kl]
    have Y := (Has (getKeyIndex kl) (by omega) H1)
    simp [makeKey]
    apply Y)
  have Xr : kr ∈ keys <-> (f (getKeyIndex kr) = getKeyTruth kr) := (by
    nth_rw 1 [getToMakeKey kr]
    have Y := (Has (getKeyIndex kr) (by omega) H2)
    simp [makeKey]
    apply Y)
  simp [Xl, Xr, holec, makeHoleEntry]
  rw [apply_ite (fun x => Expression.Enc kl x)]

def gbHoleCorrect {input output : WireBundle} (f : ℕ -> Bool) (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (keys : Finset (Expression Shape.KeyS)) :
  let (gbc, _gbL, ifi) := gb c inlbl i
  let (holec, _gbHoleL, _ifi') := gbHole f c inlbl i
  keysAs keys f 0 ifi ->
  inputLessThen i inlbl ->
  hideEncrypted keys gbc = holec
  := by
  revert inlbl i keys
  induction c <;> (
    intro inlbl i keys;
    simp at inlbl
  )
  case NandC =>
    intro Hkey Hinlbl
    simp [inputLessThen] at Hinlbl
    have ⟨_Hinlbl1, _Hinlbl2⟩ := Hinlbl
    -- repeat rw [toExpressionPush]
    repeat rw [hideEncryptedPush]
    repeat rw [makeHoleEntryCorrect f (i+1)] <;> (
        (try assumption)
        try (rw [getIndexMakeKey]; omega))
    repeat rw [getTruthMakeKey, getIndexMakeKey]
    congr <;> simp
  case AssocC =>
    intro _a
    simp [hideEncrypted]
  case UnAssocC =>
    intro _a
    simp [hideEncrypted]
  case SwapC =>
    intro _a
    simp [hideEncrypted]
  case DupC =>
    intro _a
    simp [hideEncrypted]
  case ComposeC c1 c2 Ha Hb =>
    intro Hkeys Hinlbl
    simp [hideEncrypted]
    congr
    · apply Ha <;> try assumption
      intro k Hr1 Hr2
      apply Hkeys <;> try omega
      suffices X : (gb c1 inlbl i).2.2 <= (gb c2 (gb c1 inlbl i).2.1 (gb c1 inlbl i).2.2).2.2 from (by
        exact Nat.lt_of_lt_of_le Hr2 X)
      exact gb_i_monotone c2 (gb c1 inlbl i).2.1 (gb c1 inlbl i).2.2 rfl
    · have X : (gb c1 inlbl i).2 = (gbHole f c1 inlbl i).2 := by
        rw [<-eval_gb_i]
        exact eval_gbHole_i f _ c1 inlbl i
      simp [<-X]
      apply Hb (gb c1 inlbl i).2.1 (gb c1 inlbl i).2.2
      · intro k Hr1 Hr2
        apply Hkeys <;> try omega;
      · exact outLabelLessThenLemma c1 inlbl i Hinlbl
  case FirstC c1 Hc =>
    intro a Hinlbl
    apply Hc
    assumption
    simp [inputLessThen] at Hinlbl
    apply Hinlbl.1

-- Each input wire should be 'encoded', i.e.
-- for each wire we should only have one key.
def encodedLabelTypeP : WireBundle -> Type := bundleType (Expression Shape.BitS × Expression Shape.KeyS)

-- ... and a function that converts a value to an expression.
def encodedLabelToExprP : {bundle : WireBundle} -> encodedLabelTypeP bundle -> Expression (garbledInputShape bundle)
| o, (bl, kl) => Expression.Pair bl kl
| (_o1, _o2), (l1, l2) => Expression.Pair (encodedLabelToExprP l1) (encodedLabelToExprP l2)

-- The outut labels should be masked, i.e. we they should only store the bit value,
-- of each output wire.
def maskedLabelTypeP : WireBundle -> Type := bundleType (Expression Shape.BitS)

-- ... and a function that converts a value to an expression.
def maskedLabelToExprP : {bundle : WireBundle} -> maskedLabelTypeP bundle -> Expression (maskedLabelShape bundle)
| o, bl => bl
| (_, _), (l1, l2) => Expression.Pair (maskedLabelToExprP l1) (maskedLabelToExprP l2)

-- We are now ready to combine all the parts together and compute the Garble function.

def garbleOutputTypeP {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) : Type :=
  (Expression (garbledShape c) × encodedLabelTypeP inputBundle × maskedLabelTypeP outputBundle)

def garbleOutputToExprP {inputBundle outputBundle : WireBundle} {c : Circuit inputBundle outputBundle} : garbleOutputTypeP c -> Expression (garbleOutputShape c)
| (c, l, r) => Expression.Pair (Expression.Pair c (maskedLabelToExprP r)) (encodedLabelToExprP l)

-- The main function that garbles the circuit.
def GarbleExprHole {inputBundle outputBundle : WireBundle} (f : ℕ -> Bool) (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle) : Expression (garbleOutputShape c) :=
  let (inlbl, i2) := makeLabelExp inputBundle 0
  let (c', outlbl, _) := gbHole f c inlbl i2
  let encodedInput := gEnc inlbl input
  let maskedOutput := gMask outputBundle outlbl
  let encodedInputP := encodedLabelToExpr encodedInput
  let maskedOutputP := maskedLabelToExpr maskedOutput
  Expression.Pair (Expression.Pair c' maskedOutputP) encodedInputP

def hideEncryptedairPush {a b : Shape} (keys : Finset (Expression Shape.KeyS)) (x : Expression a) (y : Expression b) :
  hideEncrypted keys (Expression.Pair x y) = Expression.Pair (hideEncrypted keys x) (hideEncrypted keys y)
  := by
    simp [hideEncrypted, hideEncrypted]

def hideEncodedLabel (encodedInput : encodedLabelType inputBundle) (keys : Finset (Expression Shape.KeyS)) :
 hideEncrypted keys (encodedLabelToExpr encodedInput) = encodedLabelToExpr encodedInput
  := by
    induction inputBundle
    case SimpleB =>
      simp [encodedLabelType, bundleType] at encodedInput
      let ⸨a, b⸩ := encodedInput
      simp [encodedLabelToExpr, hideEncrypted]
    case PairB o1 o2 ih1 ih2 =>
      simp at encodedInput
      simp [encodedLabelToExpr, hideEncryptedairPush, ih1, ih2]

def hideMaskedLabel {outputBundle : WireBundle} (maskedInput : maskedLabelType outputBundle) (keys : Finset (Expression Shape.KeyS)) :
 hideEncrypted keys (maskedLabelToExpr maskedInput) = maskedLabelToExpr maskedInput
  := by
  induction outputBundle
  case SimpleB =>
      simp [hideEncrypted, hideEncrypted, maskedLabelToExpr]
      cases maskedInput; simp [hideEncrypted]
  case PairB o1 o2 ih1 ih2 =>
      simp at maskedInput
      simp [maskedLabelToExpr, hideEncryptedairPush, ih1, ih2]

def GarbleExprHoleCorrect {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle) (keys : Finset (Expression Shape.KeyS)) :
  let (inlbl, im) := makeLabelExp inputBundle 0
  let (f2, _) := input2f input (fun _x => false) 0
  let (f3, _, _) := evalTotal c inlbl f2 im
  let gbf := GarbleNoProjection c input
  keyRecovery gbf keys = keys ->
  hideEncrypted keys gbf = GarbleExprHole f3 c input
  := by
  split
  next inlbl im' Hinlbl =>
  split
  next inputRes f2 im Hinput  =>
  split
  next f3 _x ifi Heval  =>
  intro gbf Hfix
  simp [gbf, GarbleNoProjection, garbleOutputToExpr, hideEncrypted, hideEncrypted, GarbleExprHole]
  · have Him : (makeLabelExp inputBundle 0).2 = im := by
      rw [makeLabelLength, Hinput]
    have Hhole := gbHoleCorrect f3 c (makeLabelExp inputBundle 0).1 im keys
    simp at Hhole
    rw [Him]
    constructor <;> try constructor
    apply Hhole
    · have X := (finalLemma c input keys (fun _x => false) Hfix).2
      simp [Hinlbl, Hinput, Heval] at X
      suffices Y : (gb c (makeLabelExp inputBundle 0).1 im).2.2 = ifi from (by rw [Y]; assumption)
      have Z := eval_gb_i c inlbl im f2
      have Him : im'=im := (by
        have : im = (input2f input (fun _x ↦ false) 0).2 := by rw [Hinput]
        rw [this, ← makeLabelLength, Hinlbl])
      simp [Hinlbl, <-Z]
      simp [<-Him, Heval]
    · rw [<-Him]
      exact makeLabelExpSpec inputBundle 0
    nth_rw 2 [<-hideMaskedLabel _ keys]
    -- simp [hideEncrypted]
    congr
    generalize (makeLabelExp inputBundle 0).1 = x
    generalize (makeLabelExp inputBundle 0).2 = y
    simp [← eval_gbHole_i (fun _ => false) f3 ]
    rw [eval_gb_i]
    apply hideEncodedLabel
