import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.Lemmas

-- In this file we characterizes `adversaryKeys garbledCircuit`. In fact, we are more general: we characterize all fixpoitns of `keyRecovery`.

-- few use of repeat make warnings about tactic making no progress...
set_option linter.unusedTactic false
set_option linter.unusedVariables false

-- Next, we define a function that garbles the given circuit.
-- We need the monad to generate fresh labels

def evalTotal :  {input output : WireBundle} ->  (c : Circuit input output)  -> (inlbl : labelType input) -> (f : (ℕ -> Bool)) -> (i : ℕ) -> ((ℕ -> Bool) × (labelType output) × ℕ)
| .(WireBundle.PairB _ _), .(WireBundle.PairB _ _), Circuit.SwapC _ _, (i1, i2), f, i => (f, (i2, i1), i)
| _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), f, i => (f, ((i1, i2), i3), i)
| _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), f, i => (f, (i1, (i2, i3)), i)
| _, _, Circuit.DupC, x, f, i =>
  let w := (x, x)
  (f, w, i)
| _, _, Circuit.FirstC c _, ⟨b₁, b₂⟩, f, i =>
  let (c', b₁', i1) := evalTotal c b₁ f i
  (c', (b₁', b₂), i1)
| _, _, Circuit.ComposeC c1 c2, b, f, i0 =>
  let (f1, b', i1) := evalTotal c1 b f i0
  let (f2, b'', i2) := evalTotal c2 b' f1 i1
  (f2, b'', i2)
| _, _, Circuit.NandC, (nl, nr), f, i0 =>
  let h := i0
  let f1 (x : ℕ) : Bool :=
    if x = i0 then
      not (and (f nl) (f nr))
    else
      f x
  (f1, h, i0+1)



def eval_i_monotone : forall {input output : WireBundle}  (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (f : ℕ -> Bool),
  (ifi = (evalTotal c inlbl f i).2.2) ->
  i <= ifi
  := by
    intros input out c inlbl i f Hifi
    revert ifi f i inlbl
    induction c <;> try (
      intros ifi inlbl i f Hifi;
      simp at inlbl;
      simp [Hifi, evalTotal])
    case FirstC c b IHc =>
      apply IHc
      rfl
    case ComposeC u v w c1 c2 h1 h2 =>
      generalize Het2 : evalTotal c1 inlbl f i = et2 at *
      have X := @h2 (evalTotal c2 et2.2.1 et2.1 et2.2.2).2.2 _ _ et2.1 (by rfl)
      --have Y := @h1 (evalTotal c1 inlbl f i).2.2 _ _ f (by rfl)
      apply Nat.le_trans (h1 inlbl i f (congrArg Prod.snd (congrArg Prod.snd (id (Eq.symm Het2))))) X

def eval_gb_i : forall {input output : WireBundle}  (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (f : ℕ -> Bool), (evalTotal c inlbl f i).2 = (gb c inlbl i).2 :=  by
  intros input output c
  induction c <;> ((intros inlbl i f); simp at inlbl; try simp [gb, evalTotal])
  case FirstC c b IHc =>
    simp [IHc]
  case ComposeC u v w c1 c2 h1 h2 =>
    simp [h1, h2]

def gb_i_monotone : forall {input output : WireBundle}  (c : Circuit input output) (inlbl : labelType input) (i : ℕ),
  (ifi = (gb c inlbl i).2.2) ->
  i <= ifi := by
    intros w1 w2 c ilbl input Hinput
    have X := eval_gb_i c ilbl input (fun _ => false)
    rw [Hinput, <- X]
    apply eval_i_monotone
    rfl

def eval_gb_f : forall {input output : WireBundle}  (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (f : ℕ -> Bool) (x : ℕ),
  let (f2, _, ifi) := (evalTotal c inlbl f i)
  (f2 x) != (f x) -> (i <= x ∧ x < ifi) := by
  intros input output c
  induction c <;> ((intros inlbl i f x hi);  try simp [gb, evalTotal])
  case NandC =>
    suffices Hi : i = x from (by omega)
    by_contra! H
    simp [H] at hi
    omega
  case FirstC c b IHc =>
    apply IHc
    assumption
  case ComposeC u v w c1 c2 h1 h2 =>
    generalize Het2 : evalTotal c1 inlbl f i = et2 at *
    generalize Hf2 : et2.1 = f2 at *
    if Hf2eq : f2 x = f x then
      rw [← Hf2eq] at hi
      apply h2 at hi
      have ⟨h2₁, h2₂⟩ := hi
      constructor <;> try assumption
      have X := @eval_i_monotone (evalTotal c1 inlbl f i).2.2 _ _ c1 inlbl i f (by rfl)
      rw [Het2] at X
      exact Nat.le_trans X h2₁
    else
      rw [← Hf2, ← Het2] at Hf2eq
      have H1 := h1 inlbl i f x
      simp at H1
      apply H1 at Hf2eq
      constructor <;> try omega
      rw [Het2] at Hf2eq
      have X := @eval_i_monotone (evalTotal c2 et2.2.1 f2 et2.2.2).2.2 _ _ c2 et2.2.1 et2.2.2 f2 (by rfl)
      have Y := Hf2eq.2
      exact Nat.lt_of_lt_of_le Y X



  case AssocC u v w => simp at hi
  case UnAssocC u v w => simp at hi
  case DupC => simp at hi
  case SwapC u v => simp at hi


def eval_gb_fc : forall {input output : WireBundle}  (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (f : ℕ -> Bool) (x : ℕ),
  let (f2, _, ifi) := (evalTotal c inlbl f i)
  (i > x ∨ x >= ifi) -> (f2 x) = (f x)
:= by
  intro input output c inlbl i f x
  simp
  contrapose
  intro H
  have L := eval_gb_f c inlbl i f x
  simp at L
  have L' := L H
  omega



def evalTotalLessThenLemma :
  forall {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (f : ℕ -> Bool),
  (p1 : inputLessThen i inlbl) ->
  let (f2, outlbl, ifi) := (evalTotal c inlbl f i)
  inputLessThen ifi outlbl := by
  intros input output c
  induction c <;> (intros inlbl i f H; simp at inlbl; simp [evalTotal, inputLessThen]; try simp [inputLessThen] at H; try tauto)
  case FirstC c b IHc =>
    have X := IHc inlbl.1 i f H.1
    simp at X
    constructor <;> try assumption
    apply inputLessThenMonotone
    apply eval_i_monotone
    rfl
    apply H.2
  case ComposeC u v w c1 c2 h1 h2 =>
    apply h2
    apply h1
    assumption


-- TODO: prove for evalTotal, then for gb and sim
def outLabelLessThenLemma :
  forall {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ),
  (p1 : inputLessThen i inlbl) ->
  let (_garbled, outlbl, i1) := gb c inlbl i
  inputLessThen i1 outlbl
  := by
    intros input output c inlbl i H
    simp
    have X := (eval_gb_i c inlbl i fun x => false)
    simp [<-X]
    apply evalTotalLessThenLemma
    assumption


def garbleRange :
  forall {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ),
  (p1 : inputLessThen i inlbl) ->
  let (garbled, _outlbl, i1) := gb c inlbl i
  keysInRange (extractKeys garbled) i i1 := by
    intros input output c
    induction c <;> try (simp [gb, extractKeys, getKeyIndex, makeKeyLabel, keysInRange, range] <;> fail)
    case NandC =>
      intros inlbl i _p1;
      simp at inlbl;
      simp [gb, extractKeys, getKeyIndex, makeKeyLabel, keysInRange, range, gb_entry]
      intro x Hx
      simp
      cases Hx
      case inl H1 => simp [H1]
      case inr H2 => rw [H2]; simp; omega
    case FirstC c b IHc =>
      intros inlbl i p1; simp [gb, extractKeys, getKeyIndex, makeKeyLabel]
      apply IHc
      apply p1.1
    case ComposeC u v w c1 c2 h1 h2 =>
      intros inlbl i p1; simp [gb, extractKeys, getKeyIndex, makeKeyLabel]
      apply keyPartsUnionInRange
      · have X := h1 inlbl i p1
        simp at X
        have : (gb c1 inlbl i).2.2 <= (gb c2 (gb c1 inlbl i).2.1 (gb c1 inlbl i).2.2).2.2 := by
          apply gb_i_monotone
          rfl
        simp [keysInRange, range]
        simp [keysInRange, range] at X
        intro x Hx
        have X' := X Hx
        simp at X'
        simp
        constructor; try omega
        have X'₂ := X'.2
        exact Nat.lt_of_lt_of_le X'₂ this
      · have X := h2 (gb c1 inlbl i).2.1 (gb c1 inlbl i).2.2 (by exact outLabelLessThenLemma c1 inlbl i p1)
        simp at X
        have : i <= (gb c1 inlbl i).2.2 := by
          apply gb_i_monotone
          rfl
        simp [keysInRange, range]
        simp [keysInRange, range] at X
        intro x Hx
        have X' := X Hx
        simp at X'
        simp
        constructor; try omega
        apply X'.2
    -- repeat ((intros _inlbl i _p1; simp [gb, extractKeys, getKeyIndex, makeKeyLabel, keysInRange, range]))



def guardedSingleton (b : Bool) (kh : Expression Shape.KeyS) : Finset (Expression Shape.KeyS) :=
  if b then {kh} else ∅

def guardedSingletonSpec (b : Bool) (kh x : Expression Shape.KeyS) :
  x ∈ guardedSingleton b kh <-> (b /\ x = kh) := by
  simp [guardedSingleton]
  constructor
  · intros Hx
    cases b <;> (simp at Hx; try simp [Hx])
  · rintro ⟨H1, H2⟩
    simp [H1, H2]


def keyRecoveryOnGbEntry (b1 b2 : Bool) (nl nr : ℕ) (kh : Expression Shape.KeyS) (eb : BitExpr) (keys : Finset (Expression Shape.KeyS)):
  keyRecovery (gb_entry (makeKey nl b1) (makeKey nr b2) kh eb) keys =
  guardedSingleton (makeKey nl b1 ∈ keys && makeKey nr b2 ∈ keys) kh
  := by
  simp [gb_entry, keyRecovery, keyRecovery, hideEncrypted, extractKeys, extractKeys, guardedSingleton]
  split <;> split
  case isTrue.isTrue Hkl Hkr =>
    cases kh
    simp [ Hkl, Hkr, extractKeys]
  case isTrue.isFalse Hkl Hkr =>
    simp [ Hkl, Hkr, extractKeys]
  case isFalse.isTrue Hkl Hkr =>
    tauto
  case isFalse.isFalse Hkl Hkr =>
    simp [ Hkl, Hkr, extractKeys]




def gb_lemma :
  forall
    {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ)
    (m : ℕ) (keys : Finset (Expression Shape.KeyS)) (f : ℕ -> Bool),
  let (garbled, _, i1) := gb c inlbl i
  let (f2, _, _) := evalTotal c inlbl f i
  forall
    (_p1 : inputLessThen i inlbl) (_p2 : i<=m /\ m < i1) (_p3 : pseudoFix keys garbled i i1) (_p4 : keysAs keys f2 0 m),
    keyAgreement keys m (f2 m) :=
    by
      intro input output c
      induction c <;> (try intro inlbl i  m keys f ilt mRange HpseudoFix asEval; omega)
      case FirstC c b IHc =>
        let X := IHc
        intro inlbl i  m keys f ilt mRange HpseudoFix asEval
        simp at inlbl;
        simp [evalTotal] at X
        have ⟨ilt₁, ilt₂⟩ := ilt
        simp [inputLessThen] at ilt
        apply X <;> try assumption
        repeat omega
      case NandC =>
        intro inlbl i  m keys f ilt mRange HpseudoFix asEval
        simp at inlbl;
        generalize Hgb : (gb Circuit.NandC inlbl i) = gbr at *
        generalize Hev : (evalTotal Circuit.NandC inlbl f i) = evr
        simp [evalTotal] at Hev
        simp [gb] at Hgb
        intro b
        --simp [<-Hgb] at mRange
        have Hm : m=i := by omega
        subst m
        simp [<-Hev]
        have Hfix : forall k, getKeyIndex k = i -> (k ∈ keys <-> k ∈ (keyRecovery gbr.1 keys)) := (by
          intro k Hk
          have : k ∈ range i gbr.2.2 := (by
            simp [range, Hk, <-Hgb]
          )
          apply equalInRangeRw <;> try assumption
          simp [<-Hgb]
          apply HpseudoFix
        )
        clear HpseudoFix
        rw [<-Hgb, recoveryPush, recoveryPush, recoveryPush] at Hfix
        clear Hgb
        repeat rw [keyRecoveryOnGbEntry] at Hfix
        rw [Hfix]
        · clear Hfix
          have HasF : keysAs keys f 0 i := (by
            intro k Hkey Hk2
            have : f k = (evalTotal Circuit.NandC inlbl f i).1 k := (by
              have X := eval_gb_fc Circuit.NandC inlbl i f k
              simp at X
              rw [X]; omega
            )
            simp [this]
            apply asEval <;> omega
            )
          simp [inputLessThen] at ilt
          have A1 : keyAgreement keys inlbl.1 (f inlbl.1) := (by
            apply HasF <;> omega)
          have A2 : keyAgreement keys inlbl.2 (f inlbl.2) := (by
            apply HasF <;> omega)
          rw [keyAgreement] at A1 A2
          have A1P : forall c, decide (makeKey inlbl.1 c ∈ keys) = (f inlbl.1 == c) := by simp [A1]
          repeat rw [A1P]
          have A2P : forall c, decide (makeKey inlbl.2 c ∈ keys) = (f inlbl.2 == c) := by simp [A2]
          repeat rw [A2P]
          repeat rw [<-makeKey]
          generalize f inlbl.1 = w1
          generalize f inlbl.2 = w2
          simp
          repeat rw [guardedSingletonSpec]
          have Z :  (makeKey i true = makeKey i false) = False := by (
            simp [makeKey, makeKeyLabel]
          )
          simp
          cases b
          · simp
            tauto
          · repeat rw [Z]
            simp
            cases w1 <;> simp
        · apply getIndexMakeKey
      case ComposeC u v w c1 c2 h1 h2 =>
        intro inlbl i  m keys f ilt mRange HpseudoFix asEval
        have evalTotalEq : evalTotal (c1>>>c2) inlbl f i = evalTotal (c1>>>c2) inlbl f i := by rfl
        nth_rw 1 [evalTotal] at evalTotalEq
        simp at evalTotalEq
        rw [evalTotalEq]
        let gbc1r := gb c1 inlbl i
        have Hgbc1r : gbc1r = gb c1 inlbl i := by rfl
        let gbc1 := gbc1r.1
        have Hgbc1 : gbc1 = gbc1r.1 := by rfl
        let labeli := gbc1r.2.1
        have Hlabeli : labeli = gbc1r.2.1 := by rfl
        let im := gbc1r.2.2
        have Him : im = gbc1r.2.2 := by rfl
        let gbc2r := gb c2 labeli im
        let gbc2 := gbc2r.1
        let labelf := gbc2r.2.1
        let ifinal := gbc2r.2.2
        have Hileqim: i ≤ im := by
          apply gb_i_monotone c1 inlbl
          rfl
        have Himleqifinal: im ≤ ifinal := by
          apply gb_i_monotone c2 labeli
          rfl
        have T : gb (c1>>>c2) inlbl i = (Expression.Pair gbc1 gbc2, labelf, ifinal) :=
          by rfl

        if iLeq : m < im then
          have R : forall l, 0 <=l -> l < im -> (evalTotal c1 inlbl f i).1 l = ((evalTotal (c1>>>c2) inlbl f i).1 l) := by
            intro l Hl1 Hl2
            simp [evalTotal]
            rw [eval_gb_fc c2]
            apply Or.inl
            simp [im, gbc1r] at Hl2
            have : (gb c1 inlbl i).2 = (evalTotal c1 inlbl f i).2 := by rw [eval_gb_i]
            rw [this] at Hl2
            apply Hl2

          rewrite [<-R] <;> try omega
          apply h1
          · assumption
          · have R2 : (gb c1 inlbl i).2.2 = im := by rfl
            rewrite [R2]
            constructor <;> omega
          · have ⟨T1, _⟩ := splitRange keys gbc1 gbc2 i im ifinal Hileqim Himleqifinal (by exact garbleRange c1 inlbl i ilt) (by exact garbleRange c2 labeli im (outLabelLessThenLemma c1 inlbl i ilt)) HpseudoFix
            apply T1
          · simp [keysAs]
            intro l Hl
            rw [R]
            · simp [keysAs] at asEval
              apply asEval; omega
            · omega
            · omega
        else
          simp [evalTotal]
          have H2 := h2 labeli im m keys  (evalTotal c1 inlbl f i).1
          simp[labeli, gbc1r, im] at H2
          have : (evalTotal c1 inlbl f i).2 = (gb c1 inlbl i).2 := by rw [eval_gb_i c1 inlbl i f]
          simp [this]
          apply H2
          · apply outLabelLessThenLemma
            assumption
          · simp [im, gbc1r] at iLeq
            assumption
          · apply mRange.2
          · have ⟨_, T₂⟩ := splitRange keys gbc1 gbc2 i im ifinal Hileqim Himleqifinal (by exact garbleRange c1 inlbl i ilt) (by exact garbleRange c2 labeli im (outLabelLessThenLemma c1 inlbl i ilt)) HpseudoFix
            apply T₂
          · rw [← this]
            apply asEval

def gb_lemma2
    {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ)
    (keys : Finset (Expression Shape.KeyS)) (f : ℕ -> Bool) garbled:
   (garbled =  (gb c inlbl i).1) ->
   (i1 =  (gb c inlbl i).2.2) ->
   (f2 = (evalTotal c inlbl f i).1) ->
  forall
    (_p1 : inputLessThen i inlbl) (_p3 : pseudoFix keys garbled i i1) (_p4 : keysAs keys f 0 i),
    keysAs keys f2 0 i1
    :=
    by
    intros ILT H1 E1 E2 E3 AsKeys
    have Hii2 : i <=i1 := by (
      apply gb_i_monotone <;> try assumption

    )
    have Hind : forall dm,  (i+dm) <= i1 -> keysAs keys f2 0 (i+dm) :=
    by
      intro m
      induction m with
      | zero =>
        simp
        intro _ l Hl1 Hl2
        have : f2 l = f l :=
        by
          have X := eval_gb_fc c inlbl i f l
          simp at X
          rw [E1]
          apply X
          apply Or.inl
          assumption
        rw [this]
        apply AsKeys <;> omega
      | succ m IHm=>
        intro HRange1 l Hl1 Hl2
        if ML : i+m=l then
          subst ML
          rw [E1]
          apply gb_lemma <;> try assumption
          · have : i1 = (gb c inlbl i).2.2 := by assumption
            rw [<-this]
            omega
          · rw [<-H1, <-ILT]
            apply E3
          · rw [<-E1]
            apply IHm
            omega
        else
          apply IHm <;> try omega
    have Hf : keysAs keys f2 0 (i1) :=
    by
      have : i1 = i+(i1-i) := by omega
      rw [this]
      apply Hind (i1-i)
      omega
    apply Hf

def input2f :  {inputBundle : WireBundle} -> (input : bundleBool inputBundle) -> (f : (ℕ -> Bool)) -> (i : ℕ) -> ((ℕ -> Bool) × ℕ)
| o, b, f, i =>
  let f2 (x : ℕ) : Bool :=
    if x = i then
      b
    else f x
 (f2, (i+1))
| (_, _), (b1, b2), f, i =>
  let (f', i') := input2f b1 f i
  input2f b2 f' i'

def makeLabeExp_i_monotone (inputBundle : WireBundle)  (i : ℕ) :
  i <= (makeLabelExp inputBundle i).2 := by
    revert i
    induction inputBundle
    case PairB b1 b2 Hb1 Hb2 =>
      simp [makeLabelExp]
      simp [makeLabelExp] at Hb1 Hb2
      intros i
      trans
      · apply Hb1
      · apply Hb2
    case SimpleB =>
      intro i
      simp [makeLabelExp]


def makeLabelExpSpec : forall (inputBundle : WireBundle) (i : ℕ),
  let (inlbl, ifi) := makeLabelExp inputBundle i
  inputLessThen ifi inlbl := by
    intros b
    induction b
    case SimpleB => simp [makeLabelExp, inputLessThen]
    case PairB b1 b2 Hb1 Hb2 =>
      intro i
      simp [makeLabelExp, inputLessThen]
      generalize Hbi1 : makeLabelExp b1 i = mleb1 at *
      generalize Hbi2 : makeLabelExp b2 mleb1.2 = mleb2 at *
      have Hb1x := Hb1 i
      simp at Hb1x
      rw [Hbi1] at Hb1x
      have Hb2x := Hb2 mleb1.2
      simp at Hb2x
      rw [Hbi2] at Hb2x
      constructor <;> try assumption
      apply inputLessThenMonotone _ mleb1.2
      rw [← Hbi2]
      apply makeLabeExp_i_monotone
      assumption

def makeLabelLength : forall {inputBundle : WireBundle} (input : bundleBool inputBundle) (i : ℕ) (f : ℕ -> Bool),
  (makeLabelExp inputBundle i).2 = (input2f input f i).2 := by
    intro b input i f
    revert input i f
    induction b
    case SimpleB => simp [makeLabelExp, input2f]
    case PairB b1 b2 Hb1 Hb2 =>
      intros input i f
      simp at input
      simp [makeLabelExp, input2f]
      rw [Hb1, Hb2]

def input2f_i_monotone : forall {inputBundle : WireBundle} (input : bundleBool inputBundle) (i : ℕ) (f : ℕ -> Bool),
  i <= (input2f input f i).2 := by
    intro b input i f
    rw [← makeLabelLength]
    apply makeLabeExp_i_monotone


def inputInRange {inputBundle : WireBundle} (input : bundleBool inputBundle) (i : ℕ) :
  let (inlbl, ifi) := makeLabelExp inputBundle i
  let encodedInput := gEnc inlbl input
  keysInRange (extractKeys (encodedLabelToExpr encodedInput)) i ifi := by
    revert input i
    induction inputBundle
    case SimpleB =>
      intros input i
      simp at input
      simp [makeLabelExp, encodedLabelToExpr, gEnc, extractKeys, getKeyIndex, makeKeyLabel, getKeyIndex]
      -- simp [bundleBool, bundleType] at input
      cases input <;> simp [keysInRange, range, getKeyIndex, makeKey, extractKeys, makeKeyLabel, makeEntryForWire]
      omega
    case PairB bundle₁ bundle₂ Hb₁ Hb₂ =>
      intros input i
      simp [makeLabelExp, encodedLabelToExpr, gEnc, extractKeys, getKeyIndex, makeKeyLabel, getKeyIndex]
      simp [bundleBool, bundleType] at input
      apply keysInRangeUnion
      · apply keysInRangeMonotone
        · rfl
        · apply makeLabeExp_i_monotone
        · apply Hb₁
      · apply keysInRangeMonotone
        · apply makeLabeExp_i_monotone bundle₁ i
        · rfl
        · apply Hb₂


def input2fBounds {inputBundle : WireBundle} (input : bundleBool inputBundle) (i : ℕ) (f : ℕ -> Bool) :
  let (f2, ifi) := input2f input f i
  forall x, f2 x ≠ f x -> x >= i /\ x < ifi := by
    revert i f input
    induction inputBundle
    case SimpleB =>
      intros i f
      simp [input2f]
    case PairB bundle₁ bundle₂ Hb₁ Hb₂ =>
      intros input i f
      simp at input
      simp [input2f]
      intro x Hx
      generalize Hf2 : input2f input.1 f i = f2 at *
      if Hf2x : f2.1 x = f x then
        rw [<-Hf2x] at Hx
        apply Hb₂ at Hx
        have : i ≤ f2.2 := by
          simp [←Hf2]
          apply input2f_i_monotone
        omega
      else
        simp [←Hf2] at Hf2x
        apply Hb₁ at Hf2x
        rw [Hf2] at Hf2x
        have : f2.2 ≤ (input2f input.2 f2.1 f2.2).2 := by apply
          input2f_i_monotone
        omega

def input2fBounds' {inputBundle : WireBundle} (input : bundleBool inputBundle) (i : ℕ) (f : ℕ -> Bool) :
  let (f2, ifi) := input2f input f i
  forall x, (x < i ∨ x >= ifi) -> f2 x = f x
:= by
    simp
    intro x
    contrapose!
    apply input2fBounds

def inputAsFunction {inputBundle : WireBundle} (input : bundleBool inputBundle) (i : ℕ) (f : ℕ -> Bool) :
  let (inlbl, ifi) := makeLabelExp inputBundle i
  let (f2, ifi) := input2f input f i
  let encodedInput := gEnc inlbl input
  keysAs (extractKeys (encodedLabelToExpr encodedInput)) f2 i ifi := by
  revert i f input
  induction inputBundle
  case SimpleB =>
    intros b input f
    simp at b
    simp [makeLabelExp, encodedLabelToExpr, gEnc, extractKeys, getKeyIndex, makeKeyLabel, getKeyIndex, keysAs, input2f, makeKey, makeEntryForWire]
    intro x Hx1 Hx2
    have : x = input := by apply Nat.eq_of_le_of_lt_succ Hx1 Hx2
    subst this
    intro b'
    constructor
    · intro Hx
      simp [input2f]
      simp [makeKey, makeKeyLabel] at Hx
      cases b' <;> cases b <;> simp at Hx ;tauto; try rfl
    · intros Hx
      simp [input2f] at Hx
      subst Hx
      simp [makeKey, makeKeyLabel]
  case PairB bundle₁ bundle₂ Hb₁ Hb₂ =>
    intros input i f
    simp at input
    simp [makeLabelExp, encodedLabelToExpr, gEnc, extractKeys, getKeyIndex, makeKeyLabel, getKeyIndex, input2f]
    apply keysAsUnion
    · apply inputInRange
    · have X := inputInRange input.2 ((makeLabelExp bundle₁ i).2)
      simp at X
      repeat rw [← makeLabelLength]
      apply X
    · have X := Hb₁ input.1 i f
      simp at X
      generalize Tmpeq :  extractKeys (encodedLabelToExpr (gEnc (makeLabelExp bundle₁ i).1 input.1)) = tmp at *
      rw [makeLabelLength]
      apply keysAsMatchingFunction (input2f input.1 f i).1
      · intro y Hy₁ Hy₂
        symm
        apply input2fBounds'
        apply Or.inl
        apply Hy₂
      · subst tmp
        apply X
    · rw [makeLabelLength]
      apply Hb₂


def inputLabelRecovery {inputBundle : WireBundle} (input : bundleBool inputBundle) (i : ℕ) (w : Finset (Expression Shape.KeyS)) :
  let (inlbl, ifi) := makeLabelExp inputBundle i
  let encodedInput := gEnc inlbl input
  keyRecovery (encodedLabelToExpr encodedInput) w = extractKeys (encodedLabelToExpr encodedInput) := by
  revert  i input w
  induction inputBundle
  case SimpleB =>
    intro input i w
    simp [makeLabelExp, encodedLabelToExpr, gEnc, keyRecovery, keyRecovery, hideEncrypted, extractKeys, extractKeys, makeEntryForWire]
  case PairB b₁ b₂ Ib₁ Ib₂ =>
    intro input i w
    simp at input
    simp [ makeLabelExp, encodedLabelToExpr, gEnc, keyRecovery, keyRecovery, hideEncrypted, extractKeys, extractKeys, makeEntryForWire]
    --simp [Ib₁, Ib₂]
    rw [← Ib₁, ← Ib₂]
    simp [ makeLabelExp, encodedLabelToExpr, gEnc, keyRecovery, keyRecovery, hideEncrypted, extractKeys, extractKeys, Ib₁, Ib₂]
    rfl

def inputLemma : forall {inputBundle : WireBundle} (input : bundleBool inputBundle) (i : ℕ) (f : ℕ -> Bool) (w : Finset (Expression Shape.KeyS)),
  let (inlbl, ifi2) := makeLabelExp inputBundle i
  let encodedInput := gEnc inlbl input
  let (f2, ifi) := input2f input f i
  keysAs (keyRecovery (encodedLabelToExpr encodedInput) w) f2 i ifi /\
  keysInRange (keyRecovery (encodedLabelToExpr encodedInput) w) i ifi := by
    intros inputBundle input i f w
    constructor
    · rw [inputLabelRecovery]
      apply inputAsFunction
    · simp [keysInRange]
      trans
      · apply keyRecoveryUpperBound
      · simp [← makeLabelLength]
        apply inputInRange

def maskedLabelToExprSpec {bundle : WireBundle} (masked : maskedLabelType bundle) :
  extractKeys (maskedLabelToExpr masked) = ∅ := by
    revert masked
    induction bundle
    case SimpleB =>
      intros masked
      cases masked
      simp [maskedLabelToExpr, extractKeys]
    case PairB b1 b2 Hb1 Hb2 =>
      intros masked
      simp at masked
      simp [maskedLabelToExpr, extractKeys, Hb1, Hb2]


def finalLemma : forall
    {input output : WireBundle} (c : Circuit input output) (inputVal : bundleBool input)
    (keys : Finset (Expression Shape.KeyS)) (f : ℕ -> Bool),
  let (inlbl, im) := makeLabelExp input 0
  let (f2, _) := input2f inputVal f 0
  let (f3, _, ifi) := evalTotal c inlbl f2 im
  (_p1 : keyRecovery (GarbleNoProjection c inputVal) keys = keys) ->
  keysInRange keys 0 ifi /\
  keysAs keys f3 0 ifi
   := by
  intro input output c inputVal keys f
  split; next inlbl im HmakeLabelExp =>
  split; next f2 im' Hinput2f=>
  split; next f3 outLabel ifi HevalTotal=>
  intro Hkey
  simp [GarbleNoProjection, garbleOutputToExpr, HmakeLabelExp] at Hkey
  simp [keyRecovery, keyRecovery, extractKeys, hideEncrypted, extractKeys] at Hkey
  generalize (gMask output (gb c inlbl im).2.1) = x at Hkey
  have : extractKeys (hideEncrypted keys (maskedLabelToExpr x)) = ∅  := by
    apply Finset.subset_empty.mp
    rw [<- maskedLabelToExprSpec x]
    apply keyRecoveryUpperBound
  simp [this] at Hkey
  have HT := inputLemma inputVal 0 f keys
  simp [HmakeLabelExp, Hinput2f] at HT
  have ⟨HT1, HT2⟩ := HT
  have Hgb := garbleRange c inlbl im (by
    have H := makeLabelExpSpec input 0
    rw [HmakeLabelExp] at H
    exact H)
  simp at Hgb
  have Him : im = im' := by
    have imEq : im = (makeLabelExp input 0).2 := by rw [HmakeLabelExp]
    have im'Eq : im' = (input2f inputVal f 0).2 := by rw [Hinput2f]
    rw [imEq, im'Eq]
    apply makeLabelLength
  have Hifi : ifi = (gb c inlbl im).2.2 := by
    rw [<-eval_gb_i, HevalTotal]
  have GbEncRange : keysInRange (extractKeys (hideEncrypted keys (gb c inlbl im).1)) im ifi := (by
    have GbRange := garbleRange c inlbl im (by
      have Y :=  makeLabelExpSpec input 0
      simp [HmakeLabelExp] at Y
      apply Y)
    simp at GbRange
    rw [Hifi]
    intro key Hkey
    apply GbRange
    apply keyPartsMonotone (hideEncrypted keys (gb c inlbl im).1)
    · apply hideEncryptedSmallerValue
    · assumption
    )
  constructor
  · rw [<-Hkey]
    intro s Hs
    simp at Hs
    cases Hs
    case inr Hs =>
      have X := HT2 Hs
      simp [range] at *
      have T : im <= ifi := (by
        apply gb_i_monotone
        · assumption
      )
      omega
    case inl Hs =>
      have X := GbEncRange Hs
      simp [range] at *
      omega
  · intro l Hl1 Hl2
    rw [<-Hkey]
    rw [Finset.union_comm]
    apply keysAsUnion _ _ 0 im ifi
    · rw [Him]
      assumption
    · assumption
    · intro key Hkey Hkey2
      have Y : (f2 key=f3 key) := (by
        have Z := eval_gb_fc c inlbl im f2 key
        simp [HevalTotal] at Z
        rw [Z]
        omega)
      rw [<-Y]
      rw [<-Him] at HT1
      apply HT1 <;> omega
    · have L2 : equalInRange 0 im keys (extractKeys (hideEncrypted keys (encodedLabelToExpr (gEnc inlbl inputVal)))) := (by
        nth_rw 1 [<-Hkey]
        apply equalInRange_union_empty
        apply (in_other_range_so_empty _ im ifi)
        · assumption
        · omega
      )
      have L : equalInRange im ifi keys (extractKeys (hideEncrypted keys (gb c inlbl im).1))  := (by
        rw [Finset.union_comm] at Hkey
        nth_rw 1 [<-Hkey]
        apply equalInRange_union_empty
        apply (in_other_range_so_empty _ 0 im)
        · rw [Him]
          assumption
        · omega)
      have : keysAs (keys) f3 0 ifi := by
        apply gb_lemma2 c inlbl im keys f2 <;> try assumption
        · rfl
        · rw [HevalTotal]
        · have X := makeLabelExpSpec input 0
          simp [HmakeLabelExp] at X
          assumption
        · apply keysAsSetsEqInRange _ _ (extractKeys (hideEncrypted keys (encodedLabelToExpr (gEnc inlbl inputVal)))) <;> try assumption
          · apply equalInRangeSym
            assumption
          · have X := inputLemma inputVal 0 f keys
            rw [HmakeLabelExp, Hinput2f, <-Him] at X
            simp at X
            apply X.1
      apply keysAsSetsEqInRange _ _ keys <;> try assumption
      intros x _ H2
      apply this <;> try omega
    · omega
    · omega
