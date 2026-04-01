import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleProof
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.GarbleHole
import SymbolicGarbledCircuitsInLean.Expression.Renamings
import SymbolicGarbledCircuitsInLean.Expression.Lemmas.Renaming
import SymbolicGarbledCircuitsInLean.Garbling.Simulate
import SymbolicGarbledCircuitsInLean.Garbling.SymbolicHiding.SimulateProof

-- THis file manages the renaming that maps garbling to simulation. We want to map `GarbleExprHole` to `simulateExprHole` (this is done in lemma `simToGarble`).

--- Below we present the explicit definition of the `gbHole f` function after applying the bit permutation based on `f`.

--- We start by defining the bit permutation function based on the function `f : ℕ → Bool`.

--- Now we define the explicit form, starting with some helper functions.

def keyBitPair (h : ℕ)  (b : Bool) (outBit : Bool) :=
  Prod.mk (makeKey h b) (negatedBit h (xor b outBit))

def anyKey := Expression.VarK 0
def anyBit := (BitExpr.Bit false)

def gbHoleBitSwapped :  {input output : WireBundle} -> (f : ℕ -> Bool) -> (c : Circuit input output)  -> (inlbl : labelType input) -> (i : ℕ)  -> ((Expression (garbledShape c)) × (labelType output) × ℕ)
| .(WireBundle.PairB _ _), .(WireBundle.PairB _ _), _, Circuit.SwapC _ _, (i1, i2), i =>
  (Expression.Eps, (i2, i1), i)
| _, _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), i => (Expression.Eps, ((i1, i2), i3), i)
| _, _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), i => (Expression.Eps, (i1, (i2, i3)), i)
| _, _, _, Circuit.DupC, n, i =>
  let w := (n, n)
  (Expression.Eps, w, i)
| _, _, f, Circuit.FirstC c _, ⟨b₁, b₂⟩, i =>
  let (c', b₁', i2) := gbHoleBitSwapped f c b₁ i
  (c', (b₁', b₂), i2)
| _, _, f, Circuit.ComposeC c1 c2, b, i0 =>
  let (c₁', b', i1) := gbHoleBitSwapped f c1 b i0
  let (c₂', b'', i2) := gbHoleBitSwapped f c2 b' i1
  (Expression.Pair c₁' c₂', b'', i2)
| _, _, f, Circuit.NandC, (nl, nr), i =>
  let h := i
  let x := keyBitPair h (not ((f nl) && (f nr))) (f h)
  let c00 := makeHoleEntry true true   (makeKey nl (f nl))       (makeKey nr (f nr))      x.1 x.2
  let c01 := makeHoleEntry true false  (makeKey nl (f nl))       (makeKey nr (not (f nr))) anyKey anyBit
  let c10 := makeHoleEntry false true  (makeKey nl (not (f nl))) (makeKey nr (f nr))       anyKey anyBit
  let c11 := makeHoleEntry false false (makeKey nl (not (f nl))) (makeKey nr (not (f nr))) anyKey anyBit
  let bl := Expression.BitE (BitExpr.VarB nl)
  let br := Expression.BitE (BitExpr.VarB nr)
  let c := Expression.Perm bl (Expression.Perm br c00 c01) (Expression.Perm br c10 c11)
  (c, h, i+1)

--- Before, we show that it is correct we need to show one auxiliary lemma.
lemma gbHoleBitSwapped2Eq {input output : WireBundle}  (f₁ f₂ : ℕ -> Bool) (c : Circuit input output)  (inlbl : labelType input)  (i : ℕ) :
  (gbHoleBitSwapped f₁ c inlbl i).2 = (evalTotal c inlbl f₂ i).2 := by
  induction c generalizing i f₁ f₂ <;> (simp at inlbl; simp [gbHoleBitSwapped, evalTotal])
  case FirstC c b ih => simp [ih f₁ f₂]
  case ComposeC c1 c2 ih1 ih2 =>
    generalize (evalTotal c1 inlbl f₂ i).1 = f'
    simp [ih2 f₁ f', ih1 f₁ f₂]

lemma gbHoleBitSwapped2EqSameF {input output : WireBundle}  (f: ℕ -> Bool) (c : Circuit input output)  (inlbl : labelType input)  (i : ℕ) :
  (gbHoleBitSwapped f c inlbl i).2 = (evalTotal c inlbl f i).2  := by
  exact gbHoleBitSwapped2Eq f f c inlbl i

--- Here we show that the function `gbHoleBitSwapped` is correct.
lemma gbHoleSwappedCorrect {input output : WireBundle}  (f : ℕ -> Bool) (c : Circuit input output)  (inlbl : labelType input)  (i : ℕ) :
  (gbHoleBitSwapped f c inlbl i).1 = normalizeExpr (applyBitRenaming (bitPerm f) (gbHole f c inlbl i).1) := by
  induction c generalizing i f <;> simp at inlbl
  case NandC =>
    simp [gbHoleBitSwapped, applyBitRenaming]
    generalize Hf1 : f inlbl.1 = f1
    generalize Hf2 : f inlbl.2 = f2
    generalize Hfi : f i = fi
    cases f1 <;> cases f2 <;> cases fi <;> (simp [normalizeExpr, normalizeB, applyBitRenamingB, bitPerm, Hf1, Hf2, Hfi, makeHoleEntry, keyBitPair, makeKey, makeKeyLabel, applyBitRenaming, gbHole]; congr)
  case FirstC c u ih =>
    simp [gbHoleBitSwapped, ih]
    congr
  case ComposeC c1 c2 ih1 ih2 =>
    simp [gbHoleBitSwapped]
    simp [ih2, ih1]
    simp [gbHoleBitSwapped2Eq f f]
    simp [eval_gbHole_i f f]
    congr
  repeat (simp [gbHoleBitSwapped, applyBitRenaming, normalizeExpr, gbHole])

--- Now, we give an explicit form of the function `gbHoleBitSwappedWithEval` where `f` is known to be the `evalOut` function (the only difference is marked with the comment).

def gbHoleBitSwappedWithEval :  {input output : WireBundle} -> (f : ℕ -> Bool) -> (c : Circuit input output)  -> (inlbl : labelType input) -> (i : ℕ)  -> ((Expression (garbledShape c)) × (labelType output) × ℕ)
| .(WireBundle.PairB _ _), .(WireBundle.PairB _ _), _, Circuit.SwapC _ _, (i1, i2), i =>
  (Expression.Eps, (i2, i1), i)
| _, _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), i => (Expression.Eps, ((i1, i2), i3), i)
| _, _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), i => (Expression.Eps, (i1, (i2, i3)), i)
| _, _, _, Circuit.DupC, n, i =>
  let w := (n, n)
  (Expression.Eps, w, i)
| _, _, f, Circuit.FirstC c _, ⟨b₁, b₂⟩, i =>
  let (c', b₁', i2) := gbHoleBitSwappedWithEval f c b₁ i
  (c', (b₁', b₂), i2)
| _, _, f, Circuit.ComposeC c1 c2, b, i0 =>
  let (c₁', b', i1) := gbHoleBitSwappedWithEval f c1 b i0
  let (c₂', b'', i2) := gbHoleBitSwappedWithEval f c2 b' i1
  (Expression.Pair c₁' c₂', b'', i2)
| _, _, f, Circuit.NandC, (nl, nr), i =>
  let h := i
  let x := keyBitPair h (f h) (f h) -- Here we use `f h` instead of `not ((f nl) && (f nr))`
  let c00 := makeHoleEntry true true   (makeKey nl (f nl))       (makeKey nr (f nr))      x.1 x.2
  let c01 := makeHoleEntry true false  (makeKey nl (f nl))       (makeKey nr (not (f nr))) anyKey anyBit
  let c10 := makeHoleEntry false true  (makeKey nl (not (f nl))) (makeKey nr (f nr))       anyKey anyBit
  let c11 := makeHoleEntry false false (makeKey nl (not (f nl))) (makeKey nr (not (f nr))) anyKey anyBit
  let bl := Expression.BitE (BitExpr.VarB nl)
  let br := Expression.BitE (BitExpr.VarB nr)
  let c := Expression.Perm bl (Expression.Perm br c00 c01) (Expression.Perm br c10 c11)
  (c, h, i+1)

def gbHoleBitSwappedWithEval2Eq {input output : WireBundle}  (f₁ f₂ : ℕ -> Bool) (c : Circuit input output)  (inlbl : labelType input)  (i : ℕ) :
  (gbHoleBitSwappedWithEval f₁ c inlbl i).2 = (evalTotal c inlbl f₂ i).2 := by
  induction c generalizing i f₁ f₂ <;> (simp at inlbl; simp [gbHoleBitSwappedWithEval, evalTotal])
  case FirstC c b ih => simp [ih f₁ f₂]
  case ComposeC c1 c2 ih1 ih2 =>
    generalize (evalTotal c1 inlbl f₂ i).1 = f'
    simp [ih2 f₁ f', ih1 f₁ f₂]

--- This is an auxiliary lemma that states that `gbHoleBitSwapped` only deepends on values of `f` from `i` to the returned index.
lemma gbHoleBitSwapped2EqIrrelevantF {input output : WireBundle}  (f₁ f₂ : ℕ → Bool) (c : Circuit input output)  (inlbl : labelType input)  (i : ℕ) :
   let j := (gbHoleBitSwapped f₁ c inlbl i).2.2
   (∀ x, x < j → f₁ x = f₂ x) ->
   inputLessThen i inlbl → (gbHoleBitSwapped f₁ c inlbl i) = (gbHoleBitSwapped f₂ c inlbl i) := by
   revert i inlbl
   induction c <;> (intro inlbl i x Hri Hinput; simp at inlbl; simp [gbHoleBitSwapped])
   case NandC =>
     simp [inputLessThen] at Hinput
     have : i < x := (by
       simp [x]
       rw [gbHoleBitSwapped2Eq _ (fun _ => true)]
       exact Nat.lt_add_one i
     )
     congr <;> try apply Hri; omega
   case ComposeC c1 c2 ih1 ih2 =>
     have : i <= x := by
       simp [x]
       rw [gbHoleBitSwapped2Eq]
       exact eval_i_monotone (c1>>>c2) inlbl i f₁ rfl
     rw [ih1] <;> try assumption
     · rw [ih2] <;> try assumption
       · constructor <;> rfl
       · intro y Hx
         apply Hri
         apply lt_of_le_of_lt' _  Hx
         simp [x]
         simp [gbHoleBitSwapped]
         simp [gbHoleBitSwapped2Eq _ f₂]
       · simp [gbHoleBitSwapped2EqSameF]
         exact evalTotalLessThenLemma c1 inlbl i f₂ Hinput
     · intro y Hy
       apply Hri
       apply lt_of_le_of_lt' _ Hy
       simp [x, gbHoleBitSwapped]
       simp [gbHoleBitSwapped2EqSameF]
       apply eval_i_monotone
       rfl
   case FirstC c u ih =>
     suffices Hx : (gbHoleBitSwapped f₁ c inlbl.1 i) = (gbHoleBitSwapped f₂ c inlbl.1 i) from (by
       simp [gbHoleBitSwapped, Hx]
      )
     apply ih
     apply Hri
     apply Hinput.1


--- And a similar function for `gbHoleBitSwapped`.
lemma gbHoleBitSwappedWithEval2EqIrrelevantF {input output : WireBundle}  (f₁ f₂ : ℕ → Bool) (c : Circuit input output)  (inlbl : labelType input)  (i : ℕ) :
  let j := (gbHoleBitSwappedWithEval f₁ c inlbl i).2.2
  (∀ x, x < j → f₁ x = f₂ x) →
  inputLessThen i inlbl → (gbHoleBitSwappedWithEval f₁ c inlbl i) = (gbHoleBitSwappedWithEval f₂ c inlbl i) := by
   revert i inlbl
   induction c <;> (intro inlbl i x Hri Hinput; simp at inlbl; simp [gbHoleBitSwappedWithEval])
   case NandC =>
     simp [inputLessThen] at Hinput
     have : i < x := (by
       simp [x]
       rw [gbHoleBitSwappedWithEval2Eq _ (fun _ => true)]
       exact Nat.lt_add_one i
     )
     congr <;> try apply Hri; omega
   case ComposeC c1 c2 ih1 ih2 =>
     have : i <= x := by
       simp [x]
       rw [gbHoleBitSwappedWithEval2Eq]
       exact eval_i_monotone (c1>>>c2) inlbl i f₁ rfl
     rw [ih1] <;> try assumption
     · rw [ih2] <;> try assumption
       · constructor <;> rfl
       · intro y Hx
         apply Hri
         apply lt_of_le_of_lt' _  Hx
         simp [x]
         simp [gbHoleBitSwappedWithEval]
         simp [gbHoleBitSwappedWithEval2Eq _ f₂]
       · simp [gbHoleBitSwappedWithEval2Eq _ f₂]
         exact evalTotalLessThenLemma c1 inlbl i f₂ Hinput
     · intro y Hy
       apply Hri
       apply lt_of_le_of_lt' _ Hy
       simp [x, gbHoleBitSwapped]
       simp [gbHoleBitSwappedWithEval2Eq _ f₁]
       apply eval_i_monotone
       rfl
   case FirstC c u ih =>
     suffices Hx : (gbHoleBitSwappedWithEval f₁ c inlbl.1 i) = (gbHoleBitSwappedWithEval f₂ c inlbl.1 i) from (by
       simp [gbHoleBitSwappedWithEval, Hx]
      )
     apply ih
     apply Hri
     apply Hinput.1


def gbHoleSwappedTwoCorrect {input output : WireBundle} (c : Circuit input output) :  (f : ℕ -> Bool) -> (inlbl : labelType input) -> (i : ℕ) ->
  (h : inputLessThen i inlbl) ->
  let f2 := evalTotal c inlbl f i
  (gbHoleBitSwappedWithEval f2.1 c inlbl i) = (gbHoleBitSwapped f2.1 c inlbl i) := by
  induction c <;> (simp [gbHoleBitSwappedWithEval, gbHoleBitSwapped, evalTotal];
    -- simp at inlbl
    )
  case NandC =>
    intro f a1 a2 i Hinlbl
    simp [inputLessThen] at Hinlbl
    have ⟨h1, h2⟩ := Hinlbl
    have Hlbl1neq : a1 ≠ i := by
      generalize a1 = x at *
      intro x2; rw [x2] at h1; omega
    have inlbl2neq: a2 ≠ i := by
      generalize a2 = x at *
      intro x2; rw [x2] at h2; omega
    simp [Hlbl1neq, inlbl2neq]
  case ComposeC c1 c2 ih1 ih2 =>
    intro f inlbl i Hinlbl
    generalize Heval1 : evalTotal c1 inlbl f i = eval1 at *
    generalize Heval2 : evalTotal c2 eval1.2.1 eval1.1 eval1.2.2 = eval2 at *
    generalize HgbP1 : gbHoleBitSwappedWithEval eval2.1 c1 inlbl i = gbP1 at *
    generalize HgbP2 : gbHoleBitSwappedWithEval eval2.1 c2 gbP1.2.1 gbP1.2.2 = gbP2 at *
    generalize Hgb1 : gbHoleBitSwapped eval2.1 c1 inlbl i = gb1 at *
    generalize Hgb2 : gbHoleBitSwapped eval2.1 c2 gb1.2.1 gb1.2.2 = gb2 at *
    have Ha : gbP1.2 = eval1.2 := by
      simp [<-HgbP1, <-Heval1]
      rw [gbHoleBitSwappedWithEval2Eq]
    have Hb : gb1.2 = eval1.2 := by
      simp [<-Hgb1, <-Heval1]
      rw [gbHoleBitSwapped2Eq]
    -- have Hc : gbP2.2 = eval2.2 := by sorry
    -- have Hd : gb2.2 = eval2.2 := by sorry
    have L2 : gbP2 = gb2 := (by
      simp [<-HgbP2, <-Hgb2, <-Heval2]
      have X := ih2 eval1.1 eval1.2.1 eval1.2.2
      simp at X
      rw [Ha, Hb]
      rw [X]
      rw [← Heval1]
      apply evalTotalLessThenLemma
      assumption
    )
    have L1 : gbP1 = gb1 := (by
      simp [<-HgbP1, <-Hgb1]
      simp [<-Heval2]
      rw [gbHoleBitSwappedWithEval2EqIrrelevantF _ eval1.1 c1, gbHoleBitSwapped2EqIrrelevantF _ eval1.1 c1, ← Heval1]
      · have X := ih1 f inlbl i
        simp at X
        rw [X]
        assumption
      · intro x Hx1
        apply eval_gb_fc
        apply Or.inl
        rw [<-Heval1]
        rw [gbHoleBitSwapped2Eq] at Hx1
        assumption
      · assumption
      · intro x Hx2
        rw [<- Heval1]
        apply eval_gb_fc
        apply Or.inl
        rw [gbHoleBitSwappedWithEval2Eq] at Hx2
        assumption
      · assumption
    )
    simp [L1, L2]

  case FirstC c u ih =>
    intro f a1 a2 i Hinlbl
    rw [ih]
    simp [inputLessThen] at Hinlbl
    repeat constructor
    apply Hinlbl.1

-- Now, we are ready to define explicit form after applying both key renaming and bit renaming.
-- Or in other words, an explicit form of applying key renaming to `gbHoleBitSwappedWithEval`.

def gbHoleBitKeyRenamed :  {input output : WireBundle} -> (c : Circuit input output)  -> (inlbl : labelType input) -> (i : ℕ)  -> ((Expression (garbledShape c)) × (labelType output) × ℕ)
| .(WireBundle.PairB _ _), .(WireBundle.PairB _ _), Circuit.SwapC _ _, (i1, i2), i =>
  (Expression.Eps, (i2, i1), i)
| _, _, Circuit.AssocC _ _ _, (i1, (i2, i3)), i => (Expression.Eps, ((i1, i2), i3), i)
| _, _, Circuit.UnAssocC _ _ _, ((i1, i2), i3), i => (Expression.Eps, (i1, (i2, i3)), i)
| _, _, Circuit.DupC, n, i =>
  let w := (n, n)
  (Expression.Eps, w, i)
| _, _, Circuit.FirstC c _, ⟨b₁, b₂⟩, i =>
  let (c', b₁', i2) := gbHoleBitKeyRenamed c b₁ i
  (c', (b₁', b₂), i2)
| _, _, Circuit.ComposeC c1 c2, b, i0 =>
  let (c₁', b', i1) := gbHoleBitKeyRenamed c1 b i0
  let (c₂', b'', i2) := gbHoleBitKeyRenamed c2 b' i1
  (Expression.Pair c₁' c₂', b'', i2)
| _, _, Circuit.NandC, (nl, nr), i =>
  let h := i
  let c00 := makeHoleEntry true true   (makeKey nl false) (makeKey nr false)   (makeKey h false) (BitExpr.VarB h)
  let c01 := makeHoleEntry true false  (makeKey nl false) (makeKey nr true)    anyKey anyBit
  let c10 := makeHoleEntry false true  (makeKey nl true)  (makeKey nr false)   anyKey anyBit
  let c11 := makeHoleEntry false false (makeKey nl true)  (makeKey nr true)    anyKey anyBit
  let bl := Expression.BitE (BitExpr.VarB nl)
  let br := Expression.BitE (BitExpr.VarB nr)
  let c := Expression.Perm bl (Expression.Perm br c00 c01) (Expression.Perm br c10 c11)
  (c, h, i+1)

lemma gbHoleBitKeyRenamed2Eq {input output : WireBundle} (f : ℕ -> Bool) (c : Circuit input output)   (inlbl : labelType input) (i : ℕ):
  (gbHoleBitKeyRenamed c inlbl i).2 =  (evalTotal c inlbl f i).2 := by
  induction c generalizing i f <;> (simp at inlbl; simp [gbHoleBitKeyRenamed, evalTotal]; try simp at inlbl)
  case FirstC c b ih => simp [evalTotal, gbHoleBitKeyRenamed, ih f]
  case ComposeC c1 c2 ih1 ih2 =>
    generalize (evalTotal c1 inlbl f i).1 = f'
    simp [ih2 f', ih1 f]


lemma swapKeysRenamingMakeKeyF (x : ℕ) (f : ℕ → Bool) : Expression.VarK (makeKeySwap f (makeKeyLabel x (f x))) = makeKey x false := by
  simp [applyKeyRenamingP, makeKeySwap, makeKeyLabel, condNotNat, notNat, yesNat]
  generalize Hfx : f x = fx
  cases fx <;> (simp [Hfx]; try rfl)
  have : (2 * x + 1) / 2 = x := by omega
  simp [this, Hfx]
  have : (2 * x + 1) % 2 = 1 := by omega
  simp [makeKeyLabel, makeKey, this]

lemma swapKeysRenamingMakeKeyF2 (x : ℕ) (f : ℕ → Bool) : applyKeyRenamingP (makeKeySwap f) (makeKey x (f x)) = makeKey x false := by
  simp [applyKeyRenamingP, swapKeysRenamingMakeKeyF, makeKey]

lemma swapKeysRenamingMakeKeyT (x : ℕ) (f : ℕ → Bool) : Expression.VarK (makeKeySwap f (makeKeyLabel x !(f x))) = makeKey x true := by
  simp [applyKeyRenamingP, makeKeySwap, makeKeyLabel, condNotNat, notNat]
  generalize Hfx : f x = fx
  cases fx <;> (simp [yesNat, Hfx]; try rfl)
  have : (2 * x + 1) % 2 = 1 := by omega
  -- simp [this]
  have : ((2 * x + 1) / 2) = x := by omega
  simp [this, Hfx]
  rfl

lemma swapKeysRenamingMakeKeyT2 (x : ℕ) (f : ℕ → Bool) : applyKeyRenamingP (makeKeySwap f) (makeKey x !(f x)) = makeKey x true := by
  simp [applyKeyRenamingP, swapKeysRenamingMakeKeyT, makeKey]

lemma gbHoleBitKeyRenamedCorrect {input output : WireBundle} (c : Circuit input output) (f : ℕ -> Bool)  (inlbl : labelType input) (i : ℕ):
  (gbHoleBitKeyRenamed c inlbl i).1 = applyKeyRenamingP (makeKeySwap f) (gbHoleBitSwappedWithEval f c inlbl i).1 := by
  induction c generalizing i f <;> (simp at inlbl; simp [applyKeyRenamingP, gbHoleBitKeyRenamed, gbHoleBitSwappedWithEval])
  case ComposeC c1 c2 ih1 ih2 =>
    simp [← ih1, ← ih2]
    simp [gbHoleBitKeyRenamed2Eq f c1 inlbl i]
    simp [gbHoleBitSwappedWithEval2Eq f f]
  case FirstC c1 u ih =>
    simp [← ih, ← gbHoleBitKeyRenamed2Eq]
  case NandC =>
    simp [applyKeyRenamingP, swapKeysRenamingMakeKeyF, swapKeysRenamingMakeKeyT, makeHoleEntry, keyBitPair, makeKey]
    congr



-- todo: remove
lemma gbHoleBitKeyRenamedCorrect2 {input output : WireBundle} (c : Circuit input output) (f : ℕ -> Bool)  (inlbl : labelType input) (i : ℕ):
  (h : inputLessThen i inlbl) ->
  let (f2, _, _) := evalTotal c inlbl f i
  (gbHoleBitKeyRenamed c inlbl i).1 =
  normalizeExpr (
  applyKeyRenamingP (makeKeySwap f2) (
  applyBitRenaming (bitPerm f2) (gbHole f2 c inlbl i).1)
   ) := by
  intro Hinlbl
  simp
  rw [normalize_renameK_commute]
  rw [<-gbHoleSwappedCorrect]
  rw [<-gbHoleSwappedTwoCorrect]
  rw [<-gbHoleBitKeyRenamedCorrect]
  assumption



lemma simHoleAsGb {input output : WireBundle} (c : Circuit input output) (inlbl : labelType input) (i : ℕ) :
  (gbHoleBitKeyRenamed c inlbl i) = (simHole c inlbl i) := by
  revert i
  induction c
  <;> (intro i; simp at inlbl; simp [gbHoleBitKeyRenamed, simHole])
  case NandC =>
    rfl
  case ComposeC u v w c1 c2 Hc1 Hc2=>
    simp [Hc1]
    simp [Hc2]
  case FirstC c u H =>
    simp [H]



-- section about renamings

lemma applyVarRenamingPairPush {s₁ s₂ : Shape} (f : ℕ → Bool) (p : Expression s₁) (q : Expression s₂) :
  applyVarRenaming (makeVarRenaming f) (Expression.Pair p q) = Expression.Pair (applyVarRenaming (makeVarRenaming f) p) (applyVarRenaming (makeVarRenaming f) q) := by
    simp [applyVarRenaming, makeVarRenaming, applyKeyRenamingP, bitPerm, makeKeySwap, applyBitRenaming]

lemma applyVarRenamingFEqInRange {inputBundle : WireBundle} (input : bundleBool inputBundle) (f₁ f₂ : ℕ → Bool) (i : ℕ) :
  let ⟨l, j⟩ := makeLabelExp inputBundle i
  let p := (encodedLabelToExpr (gEnc l input))
  (∀ x, i <= x -> x < j -> f₁ x = f₂ x) →
  applyVarRenaming (makeVarRenaming f₁) p = applyVarRenaming (makeVarRenaming f₂) p := by
  induction inputBundle generalizing f₁ f₂ i <;> simp at input
  case SimpleB =>
    simp [encodedLabelToExpr]
    intro hx
    simp [applyVarRenaming, applyBitRenaming, applyKeyRenamingP, negatedBit, makeLabelExp, makeVarRenaming, makeKeySwap, bitPerm]
    simp [makeLabelExp] at hx
    have hx : f₁ i = f₂ i := by
      apply hx <;> omega
    cases input <;> try simp
    · simp [applyKeyRenamingP, applyBitRenaming, applyBitRenamingB, bitPerm, bitPerm, gEnc, encodedLabelToExpr, makeKey, negatedBit, varOrNegVarToExpr, hx, makeKeySwap, makeEntryForWire]
      congr
      simp [makeKeyLabel]
      assumption
    · simp [gEnc, encodedLabelToExpr, applyBitRenaming, applyBitRenamingB, bitPerm, applyBitRenamingB, bitPerm, negatedBit, hx, makeKeySwap, applyKeyRenamingP, varOrNegVarToExpr, makeKey, makeEntryForWire]
      congr
      simp [makeKeyLabel]
      have : (2 * i + 1) / 2 = i := by omega
      simp [this]
      assumption
  case PairB b1 b2 ih1 ih2 =>
    simp[encodedLabelToExpr]
    intro hfeq
    simp [makeLabelExp] at hfeq ih1 ih2
    simp [makeLabelExp, gEnc, encodedLabelToExpr]
    rw [applyVarRenamingPairPush]
    rw [ih1, ih2]
    · rfl
    · intro x hx₁ hx₂
      apply hfeq <;> try assumption
      trans (makeLabelExp b1 i).2
      apply makeLabeExp_i_monotone
      assumption
    · intro x hx₁ hx₂
      apply hfeq <;> try assumption
      apply lt_of_lt_of_le
      apply hx₂
      apply makeLabeExp_i_monotone




lemma applyKeyRenamingToMakeLabelExp {inputBundle : WireBundle} (input : bundleBool inputBundle) (f : ℕ → Bool) (i : ℕ) :
  let inputLabel := makeLabelExp inputBundle i
  let f2 := (input2f input f i).1
  let rename := makeVarRenaming f2
  normalizeExpr ( applyVarRenaming rename (encodedLabelToExpr (gEnc inputLabel.1 input)))
  =
   encodedLabelToExpr (sEnc inputLabel.1) :=
  by
    induction inputBundle generalizing f i
    case SimpleB =>
      simp [sEnc, generateFalseInput, gEnc, makeLabelExp,
            applyVarRenaming, applyVarRenaming, normalizeExpr, normalizeB,
            encodedLabelToExpr, makeKeySwap, bitPerm, makeLabelExp, input2f,
            normalizeExpr, makeVarRenaming, applyKeyRenamingP, applyBitRenaming, applyBitRenamingB]
      simp [normalizeB, negatedBit, applyBitRenaming, applyBitRenamingB, normalizeExpr, bitPerm, condNotNat, varOrNegVarToExpr, makeEntryForWire, applyKeyRenamingP]
      congr
      · cases input <;>
        simp [applyBitRenamingB, varOrNegVarToExpr, bitPerm, normalizeB]
      · simp[applyKeyRenamingP, makeKeySwap, condNotNat, makeKeyLabel, makeKey, makeEntryForWire]
        cases input
        · simp[yesNat]
        · simp[notNat, yesNat]
          have x : (2 * i + 1) / 2 = i  := by omega
          simp [x]
    case PairB b1 b2 ih1 ih2 =>
      simp only [makeLabelExp, encodedLabelToExpr, sEnc, gEnc, generateFalseInput]
      simp at input
      simp [normalizeExpr, normalizeB, applyKeyRenamingP, applyBitRenamingB, makeKeySwap, encodedLabelToExpr, gEnc,  makeLabelExp, input2f, sEnc]
      simp [applyVarRenamingPairPush]
      simp [normalizeExpr]
      congr
      · generalize Hf₂ :  (input2f input.2 (input2f input.1 f i).1 (input2f input.1 f i).2).1 = f₂
        generalize Hf₁ : (input2f input.1 f i).1 = f₁
        have Y := applyVarRenamingFEqInRange input.1 f₂ f₁ i
        simp at Y
        rw [Y]
        ·
          have X := ih1 input.1 f i
          simp [Hf₁, Hf₂] at X
          rw [X]
          rfl
        · intro x _ hx₂
          simp [←Hf₁, ← Hf₂]
          rw [makeLabelLength] at hx₂
          rw [input2fBounds']
          apply Or.inl
          apply hx₂
      · generalize Hm : (input2f input.1 f i) = im at *
        have X := ih2 input.2 im.1 im.2
        simp at X
        have : im.2 = (makeLabelExp b1 i).2 := by
          rw [makeLabelLength, Hm]
        rw [<- this]
        rw [X]
        rfl


lemma generateLabelFSwap (f1 f2 : ℕ -> Bool) {bundle : WireBundle} (inlbl : labelType bundle)  (i : ℕ) :
  inputLessThen i inlbl ->
  (forall x, x < i -> f1 x = f2 x) ->
  generateLabel f1 inlbl = generateLabel f2 inlbl
  := by
  induction bundle <;> simp at inlbl
  case SimpleB =>
    intro Hinlbl Hf
    simp [inputLessThen] at Hinlbl
    simp [generateLabel]
    apply Hf
    assumption
  case PairB u v H1 H2=>
    intro Hinlbl Hf
    simp [inputLessThen] at Hinlbl
    simp [generateLabel]
    rw [H1, H2] <;> tauto

lemma renamingLemma {bundle : WireBundle} (label : labelType bundle) (f1 : ℕ -> Bool) :
  normalizeExpr
    (applyKeyRenamingP (makeKeySwap f1)
      (applyBitRenaming (bitPerm f1) (maskedLabelToExpr (gMask bundle label)))) =
   maskedLabelToExpr (sMask label (generateLabel f1 label))
 := by
induction bundle <;> simp at label
next =>
  simp [gMask, maskedLabelToExpr, generateLabel, sMask, applyBitRenaming, applyBitRenamingB]
  have : Expression.BitE (varOrNegVarToExpr (bitPerm f1 label)) = Expression.BitE (negatedBit label (f1 label)) := by
    simp [normalizeB, negatedBit, bitPerm, varOrNegVarToExpr]
    cases (f1 label) <;> simp
  simp [<-this, applyKeyRenamingP, normalizeExpr]
  congr
  simp [varOrNegVarToExpr, bitPerm]
  cases (f1 label) <;> simp [normalizeB]
next u v Hu Hv =>
  simp [gMask, maskedLabelToExpr, applyBitRenaming, applyKeyRenamingP, normalizeExpr]
  rw [Hu label.1]
  rw [Hv label.2]
  cases label
  simp [generateLabel, sMask, maskedLabelToExpr]

lemma evalCircuitSpec {inputBundle outputBundle: WireBundle} (c : Circuit inputBundle outputBundle) (inlbl : labelType inputBundle) (i : ℕ) (f : ℕ -> Bool):
  (inputLessThen i inlbl) ->
  let inputBool := generateLabel f inlbl
  let ev := evalTotal c inlbl f i
  generateLabel ev.1 ev.2.1 = evalCircuit c inputBool := by
  revert f i
  induction c <;>
    (intro i f Hinlbl; simp at inlbl; simp [evalCircuit, evalTotal, generateLabel])
  case ComposeC inputBundle v w c1 c2 Hu Hv =>
    generalize Hev : evalTotal (c1>>>c2) inlbl f i = ev
    simp [evalTotal] at Hev
    generalize Hev1 : evalTotal c1 inlbl f i = ev1 at *
    simp [<-Hu _ i f (by assumption)]
    simp [Hev1]
    simp [<-Hv ev1.2.1 ev1.2.2 ev1.1 (by
      simp [<-Hev1]
      apply evalTotalLessThenLemma
      assumption
      )]
  case FirstC c1 u H =>
    generalize Hev1 : evalTotal c1 inlbl.1 f i = ev1
    rw [<-H _ i]
    have : generateLabel ev1.1 inlbl.2 = generateLabel f inlbl.2 := by
      apply generateLabelFSwap
      simp [inputLessThen] at Hinlbl
      apply Hinlbl.2
      simp [<-Hev1]
      intro x Hx
      apply eval_gb_fc
      left
      omega
    simp [this, Hev1]
    simp [inputLessThen] at Hinlbl
    apply Hinlbl.1

lemma generateLabelRound {inputBundle : WireBundle} (inlbl : bundleBool inputBundle) (i : ℕ) (f : ℕ -> Bool):
  let inputf := input2f inlbl f i
  let label := makeLabelExp inputBundle i
  generateLabel inputf.1 label.1 = inlbl := by
  revert i f
  induction inputBundle
  simp [generateLabel, input2f, makeLabelExp]
  case PairB u v Hu Hv =>
    simp [generateLabel, input2f, makeLabelExp]
    intro i f
    simp at inlbl
    have X2 := Hv inlbl.2
    have X1 := Hu inlbl.1
    simp at X1 X2
    have : (input2f inlbl.1 f i).2 = (makeLabelExp u i).2 := by
      exact Eq.symm (makeLabelLength inlbl.1 i f)
    simp [input2f]
    rw [this, X2]
    congr
    nth_rw 2 [<-X1 i f]
    apply generateLabelFSwap _ _ _ (makeLabelExp u i).2
    exact makeLabelExpSpec u i
    intro x Hx
    generalize (input2f inlbl.1 f i).1 = f'
    apply input2fBounds'
    left
    assumption

lemma evalCircuitSpecOld {inputBundle outputBundle: WireBundle} (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle) (i : ℕ):
  let inputf := input2f input (fun _x ↦ false) i
  let label := makeLabelExp inputBundle i
  let ev := evalTotal c (label).1 inputf.1 (label).2
  generateLabel ev.1 ev.2.1 = evalCircuit c input := by
  simp
  generalize Hinputf : input2f input (fun _x ↦ false) i = inputf
  generalize Hlabel : makeLabelExp inputBundle i = label
  generalize Heval : evalTotal c (label).1 inputf.1 (label).2 = ev
  have X := evalCircuitSpec c label.1 label.2 inputf.1
  simp [Hinputf, Hlabel, Heval] at X
  rw [X]
  · congr
    simp [<-Hinputf, <-Hlabel]
    apply generateLabelRound
  · simp [<-Hlabel]
    exact makeLabelExpSpec inputBundle i


lemma simToGarble {inputBundle outputBundle : WireBundle} (c : Circuit inputBundle outputBundle) (input : bundleBool inputBundle) :
  let inputLabel := makeLabelExp inputBundle 0
  let e0 := input2f input (fun _x ↦ false) 0
  let f1 := (evalTotal c inputLabel.1 e0.1 inputLabel.2).1
  normalizeExpr (applyVarRenaming (bitPerm f1, makeKeySwap f1) (GarbleExprHole f1 c input)) =
    simulateExprHole c (evalCircuit c input) := by
      intro inputLabel e0 f1
      simp [GarbleExprHole, applyVarRenaming, simulateExprHole]
      simp [applyKeyRenamingP, applyBitRenaming]
      simp [normalizeExpr]
      constructor <;> try constructor
      · have X := gbHoleBitKeyRenamedCorrect2 c e0.1 inputLabel.1 inputLabel.2 (by
          apply makeLabelExpSpec)
        rw [<-X]
        rw [simHoleAsGb]
      · have Hinputlabel : inputLabel = makeLabelExp inputBundle 0 := by rfl
        rw [<-Hinputlabel]
        simp [<-eval_gbHole_i e0.1 f1 c inputLabel.1 inputLabel.2]
        simp [simHole_eval c inputLabel.1 inputLabel.2 e0.1]
        let e1 := evalTotal c inputLabel.1 e0.1 inputLabel.2
        have : (generateLabel f1 e1.2.1) = (evalCircuit c input) := by
          rw [<-evalCircuitSpecOld _ _ 0]
        rw [<-this]
        apply renamingLemma
      · have Y := applyVarRenamingFEqInRange input f1 e0.1 0
        simp [applyVarRenaming, applyVarRenaming, makeVarRenaming] at Y
        rw [Y]
        · have X := applyKeyRenamingToMakeLabelExp input (fun _ => false) 0
          simp [applyVarRenaming, applyVarRenaming, makeVarRenaming] at X
          simp [e0]
          simp [X]
        · intro x hx
          apply eval_gb_fc
          apply Or.inl
          assumption
