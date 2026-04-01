import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleProof
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleHole
import SymbolicGarbledCircuitsInLean.Garbling.Simulate

--This file characterizes `adversaryKeys simulatedCircuit` (in fact: all fixpoints). We characterize `adversaryView simulatedCircuit`, by proving equivalence with `simulateExprHole`. We reuse lemma established when working on garbling.


set_option linter.unusedTactic false

def sim_eval {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (f : ℕ -> Bool) :
  (sim c inlbl i).2 = (evalTotal c inlbl f i).2 := by
  induction c generalizing i f <;> (simp at inlbl; simp [sim, evalTotal])
  case FirstC c b ih =>
    simp [ih inlbl.1 i f]
  case ComposeC c1 c2 ih1 ih2 =>
    generalize (evalTotal c1 inlbl f i).1 = f'
    simp [ih1 inlbl _ f]
    simp [ih2 _ _ f']


def sim_i_monotone {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ) :
  (sim c inlbl i).2.2 >= i := by
  rw [sim_eval _ _ _ (fun _ => false)]
  exact eval_i_monotone c inlbl i (fun _ ↦ false) rfl

-- proof first that sim.2 = eval.2
def simOutLbl {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ) :
  let (_simo, siml, simi) := (sim c inlbl i)
  inputLessThen i inlbl ->
  inputLessThen simi siml := by
  simp at inlbl
  simp [sim_eval _ _ _ (fun _ => false)]
  intro H
  apply evalTotalLessThenLemma
  assumption

def simRange : forall {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ),
  (p1 : inputLessThen i inlbl) ->
  let (simo, _siml, simi) := (sim c inlbl i)
  keysInRange (extractKeys simo) i simi := by
    intros input output c
    induction c <;> try (intros inlbl i _p1; simp at inlbl; simp [sim, extractKeys, getKeyIndex, makeKeyLabel, keysInRange, range] <;> fail)
    case NandC =>
      intros inlbl i _p1; simp at inlbl; simp [sim, extractKeys, getKeyIndex, makeKeyLabel, keysInRange, range, gb_entry]
    case FirstC c b IHc =>
      intros inlbl i p1; simp [sim, extractKeys, getKeyIndex, makeKeyLabel]
      apply IHc
      apply p1.1
    case ComposeC u v w c1 c2 h1 h2 =>
      intros inlbl i p1; simp [sim, extractKeys, getKeyIndex, makeKeyLabel]
      apply keyPartsUnionInRange
      · have X := h1 inlbl i p1
        simp at X
        have : (sim c1 inlbl i).2.2 <= (sim c2 (sim c1 inlbl i).2.1 (sim c1 inlbl i).2.2).2.2 := by
          apply sim_i_monotone
        simp [keysInRange, range]
        simp [keysInRange, range] at X
        intro x Hx
        have X' := X Hx
        simp at X'
        simp
        constructor; try omega
        have X'₂ := X'.2
        exact Nat.lt_of_lt_of_le X'₂ this
      · have X := h2 (sim c1 inlbl i).2.1 (sim c1 inlbl i).2.2 (by
          have Y := simOutLbl c1 inlbl i
          simp at Y
          apply Y p1
        )
        simp at X
        have : i <= (sim c1 inlbl i).2.2 := by
          apply sim_i_monotone
        simp [keysInRange, range]
        simp [keysInRange, range] at X
        intro x Hx
        have X' := X Hx
        simp at X'
        simp
        constructor; try omega
        apply X'.2
    -- repeat ((intros _inlbl i _p1; simp [gb, extractKeys, toExpression, getKeyIndex, makeKeyLabel, keysInRange, range]))


def keysAsMerge (keys : Finset (Expression Shape.KeyS)) (f : ℕ -> Bool) (a b c : ℕ) :
  keysAs keys f a b ->
  keysAs keys f b c ->
  keysAs keys f a c := by
  intro Ha Hb k Hk1 Hk2
  if k < b then
    apply Ha <;> omega
  else
    apply Hb <;> omega

def simulateFixLemma :
  forall
    {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ)
    (keys : Finset (Expression Shape.KeyS)) (f : ℕ -> Bool),
  let (sim, _o, i1) := sim c inlbl i
  forall
    (_p1 : inputLessThen i inlbl) (_p2 : forall x, x >= i -> f x = false) (_p3 : pseudoFix keys sim i i1) (_p4 : keysAs keys f 0 i),
    keysAs keys f i i1
    := by
    intro input output c
    induction c <;> (intro inlbl i keys f; simp at inlbl) <;> (try intro _Hinlbl _Hf _HpseudoFix _HkeysAs x Hn1 Hn2; omega)
    case NandC =>
      simp
      intro Hp1 Hp2 Hp3 Hp4
      intro m Hm1 Hm2
      simp [sim] at Hm2
      have : m = i := by omega
      subst m
      clear Hm1 Hm2
      rw [keyAgreement]
      intro b
      rw [Hp2] <;> try omega
      generalize Hsc :(sim Circuit.NandC inlbl i)= sc at *
      have Hfix : forall k, getKeyIndex k = i -> (k ∈ keys <-> k ∈ (keyRecovery sc.1 keys)) := by (
        intro k Hk
        apply equalInRangeRw
        simp [pseudoFix] at Hp3
        apply Hp3
        simp [range, Hk, <-Hsc, sim]
      )
      simp [<-Hsc, sim] at Hfix
      repeat rw [recoveryPush] at Hfix
      repeat rw [keyRecoveryOnGbEntry] at Hfix
      simp at Hfix
      simp [inputLessThen] at Hp1
      have A1 : keyAgreement keys inlbl.1 (f inlbl.1) := (by
        apply Hp4 <;> omega)
      have A2 : keyAgreement keys inlbl.2 (f inlbl.2) := (by
        apply Hp4 <;> omega)
      rw [keyAgreement] at A1 A2
      simp [A1, A2] at Hfix

      rw [Hfix]
      · clear Hfix
        generalize f inlbl.1 = w1
        generalize f inlbl.2 = w2
        repeat rw [guardedSingletonSpec]
        rw [<-makeKey]
        have : (makeKey i b = makeKey i false <-> b = false) := by (
          simp [makeKey, makeKeyLabel]
          cases b <;> simp
        )
        simp [this]
        clear this A1 A2
        cases b <;> cases w1 <;> simp
      · simp [getIndexMakeKey]
    case FirstC c1 c2 Hi =>
      intro Hinlbl Hf HpseudoFix HkeysAs
      cases inlbl
      next inlbl1 inlbl2 =>
      simp [sim]
      apply Hi inlbl1 i keys f
      · simp [inputLessThen] at Hinlbl
        apply Hinlbl.1
      · assumption
      · apply HpseudoFix
      · assumption
    case ComposeC c1 c2 Hi1 Hi2 =>
      intro Hp1 Hp2 Hp3 Hp4
      have sciR := sim_i_monotone c1 inlbl i
      generalize Hsc1 : (sim c1 inlbl i) = sc1 at *
      have sc2iR := sim_i_monotone c2 sc1.2.1 sc1.2.2
      generalize Hsc2 :(sim c2 sc1.2.1 sc1.2.2)= sc2 at *
      have ⟨Hfix1, Hfix2⟩ := splitRange keys sc1.1 sc2.1 i sc1.2.2 sc2.2.2 sciR sc2iR
        (by simp [<-Hsc1]; apply simRange c1 inlbl i; assumption)
        (by
          simp [<-Hsc2]
          apply simRange c2
          rw [<-Hsc1]
          apply simOutLbl
          assumption
        )
        (by assumption)
      have Has1 : keysAs keys f i sc1.2.2 := (by
        intro m HR1 HR2
        apply Hi1 inlbl i
        · assumption
        · intro x Hx
          apply Hp2; omega
        · simp [Hsc1]
          assumption
        · assumption
        · omega
        · simp [Hsc1]
          assumption
      )
      have Has1 : keysAs keys f sc1.2.2 sc2.2.2 := (by
        intro m HR1 HR2
        apply Hi2 sc1.2.1 sc1.2.2
        · rw [<-Hsc1]
          apply simOutLbl c1 inlbl i
          assumption
        · intro x Hx
          apply Hp2; omega
        · simp [Hsc2]
          assumption
        · apply keysAsMerge keys f 0 i _ <;> assumption
        · omega
        · simp [Hsc2]; assumption
      )
      apply keysAsMerge keys f i sc1.2.2 sc2.2.2 <;> assumption





def simHole_eval {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (f2 : ℕ -> Bool) :
  (simHole c inlbl i).2 = (evalTotal c inlbl f2 i).2 := by
  induction c generalizing i f2 <;> (simp at inlbl; simp [simHole, evalTotal])
  case FirstC c b ih =>
    simp [ih inlbl.1 i f2]
  case ComposeC c1 c2 ih1 ih2 =>
    generalize (evalTotal c1 inlbl f2 i).1 = f'
    simp [ih1 inlbl _ f2]
    simp [ih2 _ _ f']



def simHoleCorrect {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ) (keys : Finset (Expression Shape.KeyS)) :
  let (gbc, _gbL, ifi) := sim c inlbl i
  let (holec, _gbHoleL, _ifi') := simHole c inlbl i
  keysAs keys (fun _ => false) 0 ifi ->
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
    repeat rw [hideEncryptedPush]
    repeat rw [makeHoleEntryCorrect (fun _ => false) (i+1)] <;> (
        (try assumption)
        try (rw [getIndexMakeKey]; omega))
    repeat rw [getTruthMakeKey, getIndexMakeKey]
    congr <;> simp [getKeyTruth, makeKey, makeKeyLabel]
  case AssocC =>
    intro _; simp [hideEncrypted]
  case UnAssocC =>
    intro _; simp [hideEncrypted]
  case SwapC =>
    intro _; simp [hideEncrypted]
  case DupC =>
    intro _; simp [hideEncrypted]
  case ComposeC c1 c2 Ha Hb =>
    intro Hkeys Hinlbl
    simp [hideEncrypted]
    congr
    · apply Ha <;> try assumption
      intro k Hr1 Hr2
      apply Hkeys <;> try omega
      suffices X : (sim c1 inlbl i).2.2 <= (sim c2 (sim c1 inlbl i).2.1 (sim c1 inlbl i).2.2).2.2 from (by
        exact Nat.lt_of_lt_of_le Hr2 X)
      exact sim_i_monotone c2 (sim c1 inlbl i).2.1 (sim c1 inlbl i).2.2
    · have X : (sim c1 inlbl i).2 = (simHole c1 inlbl i).2 := by
        rw [sim_eval  _ _ _ (fun _ => false)]
        rw [simHole_eval _ _ _ _]
      simp [<-X]
      apply Hb (sim c1 inlbl i).2.1 (sim c1 inlbl i).2.2
      · intro k Hr1 Hr2
        apply Hkeys <;> try omega;
      · apply simOutLbl c1 inlbl i
        assumption
  case FirstC c1 Hc =>
    intro a Hinlbl
    apply Hc
    assumption
    simp [inputLessThen] at Hinlbl
    apply Hinlbl.1


-- The main function that simulates garbling of the circuit.
def simulateExprHole {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (output : bundleBool outputBundle) : Expression (garbleOutputShape c) :=
  let (inlbl, i2) := makeLabelExp inputBundle 0
  let (c', outlbl, _) := simHole c inlbl i2
  let encodedInput := sEnc inlbl
  let maskedOutput := sMask outlbl output
  let encodedInputP := encodedLabelToExpr encodedInput
  let maskedOutputP := maskedLabelToExpr maskedOutput
  Expression.Pair (Expression.Pair c' maskedOutputP) encodedInputP

def extend (f : ℕ -> Bool) (n : ℕ) (x : ℕ) :=
  if x < n then f x else false

def input2fOnGenFalse {bundle : WireBundle} (input : labelType bundle) (i n : ℕ):
  (input2f (generateFalseInput input) (fun _ => false) i).1 n  = false
  := by
  revert i n
  induction bundle
  case SimpleB => simp [generateFalseInput, input2f]
  case PairB u v Hu Hv =>
  simp at input
  simp [generateFalseInput, input2f]
  intro i n
  have X1 : (input2f (generateFalseInput input.1) (fun _ ↦ false) i).1 = (fun _ => false) := by
    ext
    apply Hu
  have X2: forall j, (input2f (generateFalseInput input.2) (fun _ ↦ false) j).1 = (fun _ => false) := by
    intro j
    ext
    apply Hv
  rw [X1, X2]

def simFixLemma : forall
    {input output : WireBundle} (c : Circuit input output) (outputVal : bundleBool output)
    (keys : Finset (Expression Shape.KeyS)),
  let (inlbl, im) := makeLabelExp input 0
  let (_, _, ifi) := sim c inlbl im
  (_p1 : keyRecovery (SimulateG c outputVal) keys = keys) ->
  keysInRange keys 0 ifi /\
  keysAs keys (fun _ => false) 0 ifi
   := by
  intro input output c outputVal keys
  split; next inlbl im HmakeLabelExp =>
  simp at inlbl
  split; next f2 ifi Hinput2f=>
  intro Hkey
  have Hifi : ((sim c inlbl im).2.2) = ifi := by simp [Hinput2f]
  simp [SimulateG, garbleOutputToExpr, simulateAux] at Hkey
  simp [keyRecovery, keyRecovery, extractKeys, hideEncrypted, extractKeys, HmakeLabelExp, sEnc] at Hkey
  generalize (sMask (sim c inlbl im).2.1) outputVal = x at Hkey
  have : extractKeys (hideEncrypted keys (maskedLabelToExpr x)) = ∅  := by
    apply Finset.subset_empty.mp
    rw [<- maskedLabelToExprSpec x]
    apply keyRecoveryUpperBound
  simp [this] at Hkey
  generalize HgenFalse : (generateFalseInput inlbl) = genFalse at *
  have HT := inputLemma genFalse 0 (fun _ => false) keys
  simp [HmakeLabelExp, Hinput2f] at HT
  have ⟨HT1, HT2⟩ := HT
  have Hgb := garbleRange c inlbl im (by
    have H := makeLabelExpSpec input 0
    rw [HmakeLabelExp] at H
    exact H)
  simp at Hgb
  have Him : im = (input2f genFalse (fun _ ↦ false) 0).2 := (by
    have : im = (makeLabelExp input 0).2 := by
      rw [HmakeLabelExp]
    rw [this]
    exact makeLabelLength genFalse 0 fun _ ↦ false
  )
  have GbEncRange : keysInRange (extractKeys (hideEncrypted keys (sim c inlbl im).1)) im ifi := (by
    have GbRange := simRange c inlbl im (by
      have Y :=  makeLabelExpSpec input 0
      simp [HmakeLabelExp] at Y
      apply Y)
    simp at GbRange
    rw [<-Hifi]
    intro key Hkey
    apply GbRange
    apply keyPartsMonotone (hideEncrypted keys (sim c inlbl im).1)
    · apply hideEncryptedSmallerValue
    · assumption
    )
  have Henc : keysAs (extractKeys (hideEncrypted keys  (encodedLabelToExpr (gEnc inlbl genFalse)))) (fun _ => false) 0 im := by (
    intro key Hkey Hkey2
    rw [keysAs, keyRecovery] at HT1
    nth_rw 3 [<-HgenFalse] at HT1
    simp [input2fOnGenFalse inlbl] at HT1
    simp
    apply HT1
    rw [<-Him]
    assumption
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
        have X := sim_i_monotone c inlbl im
        rw [Hinput2f] at X
        assumption
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
    · assumption
    · have L2 : equalInRange 0 im keys (extractKeys (hideEncrypted keys (encodedLabelToExpr (gEnc inlbl genFalse)))) := (by
        nth_rw 1 [<-Hkey]
        apply equalInRange_union_empty
        apply (in_other_range_so_empty _ im ifi)
        · assumption
        · omega
      )
      have L : equalInRange im ifi keys (extractKeys (hideEncrypted keys  (sim c inlbl im).1))  := (by
        rw [Finset.union_comm] at Hkey
        nth_rw 1 [<-Hkey]
        apply equalInRange_union_empty
        apply (in_other_range_so_empty _ 0 im)
        · rw [Him]
          assumption
        · omega
        )

      have : keysAs (keys) (fun _ => false) im ifi := by
        simp [<-Hifi]
        apply simulateFixLemma c inlbl im keys (fun _ => false) <;> try assumption
        · have X := makeLabelExpSpec input 0
          simp [HmakeLabelExp] at X
          assumption
        · simp [extend]
        · simp [pseudoFix, Hifi]
          assumption
        · apply keysAsSetsEqInRange _ _ (extractKeys (hideEncrypted keys  (encodedLabelToExpr (gEnc inlbl genFalse)))) <;> try assumption
          · apply equalInRangeSym
            assumption
      apply keysAsSetsEqInRange _ _ keys <;> try assumption
    · omega
    · omega


def simulateExprHoleCorrect {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (outputVal : bundleBool outputBundle) (keys : Finset (Expression Shape.KeyS)) :
  let (_inlbl, _im) := makeLabelExp inputBundle 0
  let gbf := SimulateG c outputVal
  keyRecovery gbf keys = keys ->
  hideEncrypted keys gbf = simulateExprHole c outputVal
  := by
  split
  next inlbl im Hinlbl =>
  simp at inlbl outputVal
  intro gbf Hfix
  simp [gbf, GarbleNoProjection, garbleOutputToExpr, hideEncrypted, hideEncrypted, GarbleExprHole, simulateExprHole, SimulateG, simulateAux]
  congr
  · have Him : (makeLabelExp inputBundle 0).2 = im := by
      simp [Hinlbl]
    have Hhole := simHoleCorrect c (makeLabelExp inputBundle 0).1 im keys
    simp at Hhole
    rw [Him]
    constructor <;> try constructor
    apply Hhole
    · have X := (simFixLemma c outputVal keys Hfix).2
      simp [Hinlbl] at X
      simp [Hinlbl]
      apply X
    · rw [<-Him]
      exact makeLabelExpSpec inputBundle 0
    nth_rw 2 [<-hideMaskedLabel _ keys]
    -- simp [hideEncrypted]
    congr
    generalize (makeLabelExp inputBundle 0).1 = x
    generalize (makeLabelExp inputBundle 0).2 = y
    have X := simHole_eval c x im (fun _ => false)
    -- why `rw [<-X]` not work?! xD
    have Y := sim_eval c x im (fun _ => false)
    rw [<-X] at Y
    assumption
    apply hideEncodedLabel
