import SymbolicGarbledCircuitsInLean.Garbling.Circuits
import SymbolicGarbledCircuitsInLean.Expression.Defs
import SymbolicGarbledCircuitsInLean.Expression.Lemmas.HideEncrypted
import SymbolicGarbledCircuitsInLean.Garbling.GarblingDef

def getIndexMakeKey (n : ℕ) (b : Bool) : getKeyIndex (makeKey n b) = n := by
  simp [getKeyIndex, makeKey, makeKeyLabel]
  cases b <;> (simp; try omega)

def getTruthMakeKey (n : ℕ) (b : Bool) : getKeyTruth (makeKey n b) = b := by
  simp [getKeyTruth, makeKey, makeKeyLabel]
  cases b <;> (simp; try omega)

def getToMakeKey (k : Expression Shape.KeyS) : k = (makeKey (getKeyIndex k) (getKeyTruth k)) := by
  simp [getKeyIndex, getKeyTruth, makeKey, makeKeyLabel]
  cases k
  case VarK x =>
  generalize Hmod : x % 2 = mod
  cases mod
  case zero =>
    simp [Hmod]
    omega
  case succ x' =>
    have : x' = 0 := by omega
    subst x'
    simp [Hmod]
    omega

def keyAgreement (keys : Finset (Expression Shape.KeyS)) (x : ℕ) (b: Bool) : Prop := forall c,
  (makeKey x c) ∈ keys <-> b = c

def keysAs (keys : Finset (Expression Shape.KeyS)) (f : ℕ -> Bool) (i j : ℕ):=
  forall x : ℕ, i <= x -> x < j -> (
    keyAgreement keys x (f x)
  )

def inputLessThen (n : ℕ) : {input : WireBundle} -> (inlbl : labelType input) -> Prop
| o, l =>
  let l1 : ℕ := l
  l1 < n
| (_o1, _o2), (l1, l2) => inputLessThen n l1 /\ inputLessThen n l2

def inputLessThenMonotone {b : WireBundle} (l : labelType b) (i j : ℕ) :
  i <= j -> inputLessThen i l -> inputLessThen j l := by
    intro H1 H2
    induction b
    case PairB b1 b2 =>
      -- simp [inputLessThen] at H2
      constructor
      · simp [labelType] at l
        apply b1
        apply H2.1
      · simp [labelType] at l
        apply b2
        apply H2.2
    case SimpleB =>
      simp [inputLessThen]
      simp [inputLessThen] at H2
      omega

def range (i j : ℕ) : Set (Expression Shape.KeyS) :=
  {k | i <= getKeyIndex k /\ getKeyIndex k < j}

def equalInRange (i j : ℕ) (K₁ K₂ : Finset (Expression Shape.KeyS)) : Prop :=
  (K₁.toSet ∩ range i j) = (K₂.toSet ∩ range i j)

def equalInRangeSym (i j : ℕ) (K₁ K₂ : Finset (Expression Shape.KeyS)) :
   equalInRange i j K₁ K₂ ->
   equalInRange i j K₂ K₁ :=
  by
    simp [equalInRange]
    intro H
    apply Eq.symm
    assumption

def pseudoFix (keys : Finset (Expression Shape.KeyS)) {shape : Shape} (exp : Expression shape) (i j : ℕ) : Prop :=
  equalInRange i j keys (keyRecovery exp keys)

def keysInRange (keys : Finset (Expression Shape.KeyS)) (i j : ℕ) :=
  keys.toSet ⊆ range i j

def keyPartsUnionInRange (K₁ K₂ : Finset (Expression Shape.KeyS)) (i j : ℕ) :
  keysInRange K₁ i j -> keysInRange K₂ i j -> keysInRange (K₁ ∪ K₂) i j := by
  intro H1 H2
  intro x Hx
  simp at Hx
  cases Hx
  case inl h =>
    apply H1
    assumption
  case inr h =>
    apply H2
    assumption

def smallerRangeEq (a₁ a₂ b₁ b₂ : ℕ) (ha : a₁ ≤ a₂) (hb : b₁ ≥ b₂) : range a₂ b₂ ⊆ range a₁ b₁ :=
  by
    simp [range]
    intro x Hx₁ Hx₂
    omega

def rangesDisjoint (a b c : ℕ ) : range a b ∩ range b c = ∅ := by
  ext x
  simp[range]
  omega

def unionInterDisjointEq {Q : Type} (X₁ X₂ A B C D : Set Q)
  (Hdisjoint : X₁ ∩ X₂ = ∅ )
  (hEq : (A ∩ X₁) ∪ (B ∩ X₂) = (C ∩ X₁) ∪ (D ∩ X₂)) :
  (A ∩ X₁ = C ∩ X₁ ) ∧ (B ∩ X₂ = D ∩ X₂) := by
    constructor
    · have : ((A ∩ X₁) ∪ (B ∩ X₂)) ∩ X₁ = ((C ∩ X₁) ∪ (D ∩ X₂)) ∩ X₁ := by congr
      simp [Set.union_inter_distrib_right] at this
      repeat rw [Set.inter_assoc] at this
      simp [Set.inter_comm, Hdisjoint] at this
      simp [Set.inter_comm]
      assumption
    · have : ((A ∩ X₁) ∪ (B ∩ X₂)) ∩ X₂ = ((C ∩ X₁) ∪ (D ∩ X₂)) ∩ X₂ := by congr
      simp [Set.union_inter_distrib_right] at this
      repeat rw [Set.inter_assoc] at this
      simp [Hdisjoint] at this
      assumption

def rangeEmpty {a b : ℕ} (H : a ≥ b) : range a b = ∅ := by
  simp [range]
  ext
  simp
  omega


def subsetDisjointSoDisjoint  {Q : Type} (A B C : Set Q) :
  Set.Subset A B -> B ∩ C = ∅ -> A ∩ C = ∅ := by
    intros H1 H2
    have : A = A ∩ B := by exact Set.left_eq_inter.mpr H1
    rw [this, Set.inter_assoc, H2]
    simp

def splitRange :
  forall (keys : Finset (Expression Shape.KeyS)) {shape1 shape2} (exp1 : Expression shape1) (exp2 : Expression shape2) (a b c : ℕ),
  a ≤ b -> b ≤ c ->
  keysInRange (extractKeys exp1) a b ->
  keysInRange (extractKeys exp2) b c ->
  pseudoFix keys (Expression.Pair exp1 exp2) a c ->
  (pseudoFix keys (exp1) a b /\ pseudoFix keys (exp2) b c) := by
    intros keys shape1 shape2 exp1 exp2 a b c hab hbc Hrange1 Hrange2 HpseudoFix
    simp [pseudoFix] at HpseudoFix
    rw [keyRecoveryOnPair, equalInRange] at HpseudoFix
    simp [Set.union_inter_distrib_right] at HpseudoFix
    have hraneunion : range a b ∪ range b c = range a c := by
      simp [range]
      ext
      simp
      omega
    rw [← hraneunion] at HpseudoFix
    simp [Set.inter_union_distrib_left] at HpseudoFix
    have HrangesDisjoint := rangesDisjoint a b c
    have HExp1bc: ↑(keyRecovery exp1 keys) ∩ (range b c) = ∅  := by
      apply subsetDisjointSoDisjoint _ (range a b) <;> try assumption
      apply Set.Subset.trans (keyRecoveryUpperBound exp1 keys) Hrange1
    have HExp2ab: ↑(keyRecovery exp2 keys) ∩ (range a b) = ∅  := by
      apply subsetDisjointSoDisjoint _ (range b c)
      · apply Set.Subset.trans (keyRecoveryUpperBound exp2 keys) Hrange2
      · rw [Set.inter_comm]; assumption
    simp [HExp1bc, HExp2ab] at HpseudoFix
    apply unionInterDisjointEq <;> try assumption

def equalInRangeRw (k1 k2 : Finset (Expression Shape.KeyS)) (i j : ℕ) (k : Expression Shape.KeyS) :
  equalInRange i j k1 k2 ->
  k ∈ (range i j) ->
  (k ∈ k1 ↔ k ∈ k2) := by
  intro Heq Hrange
  have S : forall Q : Finset _, k ∈ Q <-> k ∈ Q.toSet ∩ (range i j) := (by
    simp [Set.mem_inter_iff, Hrange]
  )
  rw [equalInRange] at Heq
  rw [S, S]
  rw [Heq]


def keysInRangeUnion (i j : ℕ) (k1 k2 : Finset (Expression Shape.KeyS)) :
  keysInRange k1 i j -> keysInRange k2 i j -> keysInRange (k1 ∪ k2) i j := by
    intro H1 H2
    intro x Hx
    simp [keysInRange] at H1 H2
    simp at Hx
    cases Hx
    case inl Hx1 =>
      apply H1
      assumption
    case inr Hx2 =>
      apply H2
      assumption

def keysInRangeMonotone (i j k l : ℕ) (keys : Finset (Expression Shape.KeyS)) :
  i <= k -> j >= l -> keysInRange keys k l -> keysInRange keys i j := by
    intro H1 H2 H3
    intro x Hx
    simp [keysInRange, range] at H3
    simp [keysInRange, range]
    apply H3 at Hx
    simp at Hx
    omega


def keyNotPresent (keys : Finset (Expression Shape.KeyS)) (x : ℕ) : Prop :=
  (¬ Expression.VarK (makeKeyLabel x false) ∈ keys)
    /\ (¬ Expression.VarK (makeKeyLabel x true) ∈ keys)


def helper_lemma2 (k1 k2 : Finset (Expression Shape.KeyS)) (a b l : ℕ) (x : Bool) :
  (keysInRange k2 a b) ->
  keyAgreement k1 l x ->
  (¬  (a <= l ∧ l < b)) ->
  keyAgreement (k1 ∪ k2) l x := by
    intro Range keyAgrr notRange
    have H : keyNotPresent k2 l := by
      simp [keysInRange] at Range
      simp [keyNotPresent]
      have Hget : forall b, getKeyIndex (Expression.VarK (makeKeyLabel l b)) = l := by
        simp [getKeyIndex, makeKeyLabel, getKeyIndex]
        omega
      constructor <;>
      · by_contra a
        have X := Range a
        simp [range, Hget] at X
        omega
    simp [keyNotPresent] at H
    simp [keyAgreement]
    simp [keyAgreement] at keyAgrr
    tauto


def keysAsUnion (k1 k2 : Finset (Expression Shape.KeyS)) (a b c : ℕ) (f : ℕ -> Bool) :
  (keysInRange k1 a b) ->
  (keysInRange k2 b c) ->
  (keysAs k1 f a b) ->
  (keysAs k2 f b c) ->
  (keysAs (k1 ∪ k2) f a c) := by
    intro R1 R2 K1 K2 l Hl1 Hl2
    if Rl : l < b then
      apply helper_lemma2 k1 k2 b c l (f l) R2 (K1 l Hl1 Rl) (by omega)
    else
      have : k1 ∪ k2 = k2 ∪ k1 := by exact Finset.union_comm k1 k2
      rw [this]
      apply helper_lemma2 k2 k1 a b l (f l) R1 (K2 l (by omega) (by omega)) (by omega)


def keysAsMonotone (i j k l : ℕ)  (keys : Finset (Expression Shape.KeyS)) (f : ℕ -> Bool) :
  i <= k -> j >= l -> keysAs keys f i j -> keysAs keys f k l := by
  intros H1 H2 H3
  intro x Hx₁ Hx₂
  apply H3 <;> omega

def keysAsMatchingFunction (f₁ f₂ : ℕ -> Bool) (i j : ℕ) (keys : Finset (Expression Shape.KeyS))  :
  (forall x, x >= i -> x < j -> f₁ x = f₂ x) -> keysAs keys f₁ i j -> keysAs keys f₂ i j := by
    intros H1 H2
    intro x Hx₁ Hx₂
    rw [← H1] <;> try assumption
    apply H2 <;> assumption


def memberInterRange : forall {A : Type} [DecidableEq A] (a : A) (X : Finset A) (Y : Set A) (_Hay : a ∈ Y), a ∈ X <-> a ∈ ↑X ∩ Y  := by
  intros A _ a X Y HaY
  constructor
  · intros member
    simp
    tauto
  · intro ⟨H₁, _⟩
    apply H₁


def keysAsSetsEqInRange (i j : ℕ) (k1 k2 : Finset (Expression Shape.KeyS)) (f : ℕ -> Bool) :
  equalInRange i j k1 k2 ->
  keysAs k1 f i j ->
  keysAs k2 f i j := by
    intros Heq Hk1 x Hx1 Hx2
    simp [keyAgreement]
    simp [equalInRange] at Heq
    have : forall b, makeKey x b ∈ k1 <-> makeKey x b ∈ k2 := by
      intro b
      rw [memberInterRange (makeKey x b) k1 (range i j),
          memberInterRange (makeKey x b) k2 (range i j),
          Heq]
      · simp [makeKey, makeKeyLabel, getKeyIndex, range]
        have : (2 * x + 1) / 2 = x := by omega
        cases b <;> simp[this]; omega
        constructor <;> assumption
      · simp [makeKey, makeKeyLabel, getKeyIndex, range]
        have : (2 * x + 1) / 2 = x := by omega
        cases b <;> simp[this]; omega
        constructor <;> assumption
    rw [←this, ←this]
    simp [keysAs, keyAgreement] at Hk1
    apply Hk1 <;> assumption

def equalInRange_union (X X' Y : Finset (Expression Shape.KeyS)) (i j : ℕ):
  equalInRange i j X X' ->
  equalInRange i j (X ∪ Y) (X' ∪ Y) :=
  by
    simp [equalInRange]
    intro Hkey
    rw [Set.union_inter_distrib_right]
    rw [Set.union_inter_distrib_right]
    exact congrFun (congrArg Union.union Hkey) (↑Y ∩ range i j)

def equalInRange_union_empty (X Y : Finset (Expression Shape.KeyS)) (i j : ℕ):
  equalInRange i j X ∅ ->
  equalInRange i j (X ∪ Y) (Y) :=
  by
    intro H
    nth_rw 2 [<-Finset.empty_union Y]
    apply equalInRange_union
    assumption

def in_other_range_so_empty (X : Finset (Expression Shape.KeyS)) (i j : ℕ) (a b : ℕ) :
  keysInRange X i j ->
  (j <= a ∨ b <= i) ->
  equalInRange a b X ∅ :=
  by
    intro H Hdisjoint
    ext key
    simp
    intro Hk
    have S := H Hk
    simp [range] at S
    simp [range]
    omega
