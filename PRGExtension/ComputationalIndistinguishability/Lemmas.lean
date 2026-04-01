import SymbolicGarbledCircuitsInLean.ComputationalIndistinguishability.Def

-- This file proves basic properties of indistinguishability, such as transitivity and symmetry. It also includes the lemma `IndistinguishabilityByReduction`, which shows how to use reductions to prove indistinguishability.

lemma distSymm (x y : NNReal) : distance x y = distance y x := by
  simp [distance]
  simp [dist_comm]

lemma distTriangle (x y z : NNReal) : distance x z ≤ distance x y + distance y z := by
  simp [distance]
  apply dist_triangle


lemma distSelf (x : NNReal) : distance x x = 0 := by
  simp [distance]

lemma neglSum (f1 f2 : (κ : ℕ) -> NNReal) : negl f1 -> negl f2 -> negl (fun κ => f1 κ + f2 κ) := by
  intro H1 H2
  simp [negl]
  intro k
  have ⟨w1, H1'⟩ := H1 k
  have ⟨w2, H2'⟩ := H2 k
  exists (w1 + w2)
  intro i
  rw [add_mul]
  apply add_le_add (H1' i) (H2' i)

lemma neglMonotone (f1 f2 : (κ : ℕ) -> NNReal) (H : forall i, f1 i <= f2 i) : negl f2 -> negl f1 := by
  intro Hn
  simp [negl]
  intro k
  have ⟨w, Hn2⟩ := Hn k
  exists w
  intro i
  have Hn3 := Hn2 i
  trans (↑(f2 i) * ↑i ^ k)
  · have Z := H i
    exact mul_le_mul_right' (H i) (↑i ^ k)
  · apply Hn3

lemma neglTriangle (f1 f2 f3 : (κ : ℕ) -> NNReal) (H : forall i, f1 i <= f2 i + f3 i) : negl f2 -> negl f3 -> negl f1 :=
  by
   intro H1 H2
   apply (neglMonotone f1 (fun i => f2 i + f3 i))
   exact fun i ↦ H i
   apply neglSum <;> assumption

lemma neglTriangle2 (f1 f2 f3: ℕ -> NNReal)
  (H1 : negl (fun i => distance (f1 i) (f2 i)))
  (H2 : negl (fun i => distance (f2 i) (f3 i)))
  : negl (fun i => distance (f1 i) (f3 i)) :=
  by
    apply neglTriangle _ (fun i => distance (f1 i) (f2 i)) (fun i => distance (f2 i) (f3 i)) <;> try assumption
    exact fun i ↦ distTriangle (f1 i) (f2 i) (f3 i)


noncomputable
def CompIndistinguishabilityF
  {Domain : ℕ -> Type}
  (distr1 : famDistr Domain)
  (distinguisher : famComp Domain (fun _ => Bool))
  (κ : ℕ) : NNReal :=
    let x : PMF (Option Bool) := compToDistrSimple distr1 distinguisher κ
    (getPMF x (some True))

def CompIndistinguishabilityDistrDef2
  (IsPolyTime : PolyFamOracleCompPred)
  {Domain : ℕ -> Type}
  (distr1 distr2 : famDistr Domain) : Prop :=
  forall distinguisher : famComp Domain (fun _ => Bool),
  (polyTimeFamComp IsPolyTime distinguisher) ->
  negl (fun κ => distance (CompIndistinguishabilityF distr1 distinguisher κ) (CompIndistinguishabilityF distr2 distinguisher κ))

lemma CompIndistinguishabilityDistrDefEq
  (IsPolyTime : PolyFamOracleCompPred)
  {Domain : ℕ -> Type}
  (distr1 distr2 : famDistr Domain)
  : CompIndistinguishabilityDistr IsPolyTime distr1 distr2 = CompIndistinguishabilityDistrDef2 IsPolyTime distr1 distr2 :=
  by
    simp [CompIndistinguishabilityDistrDef2, CompIndistinguishabilityDistr, CompIndistinguishabilityF]
    unfold advantage
    rfl

lemma indRfl (IsPolyTime : PolyFamOracleCompPred)
  {Domain : ℕ -> Type}
  {distr1 : famDistr Domain}
  :  CompIndistinguishabilityDistr IsPolyTime distr1 distr1 :=
  by
    simp [CompIndistinguishabilityDistrDefEq]
    simp [CompIndistinguishabilityDistrDef2]
    conv =>
      intro
      arg 2
      arg 1
      intro
      rw [distSelf]
    intro d p
    simp [negl]
    exists 0

lemma indTrans
  (IsPolyTime : PolyFamOracleCompPred)
  {Domain : ℕ -> Type}
  {distr1 distr2 distr3 : famDistr Domain}
  (H1 : CompIndistinguishabilityDistr IsPolyTime distr1 distr2)
  (H2 : CompIndistinguishabilityDistr IsPolyTime distr2 distr3)
  : CompIndistinguishabilityDistr IsPolyTime distr1 distr3 :=
by
  simp [CompIndistinguishabilityDistrDefEq] at *
  simp [CompIndistinguishabilityDistrDef2]
  intro disti
  intro HpolyDstri
  apply neglTriangle2
  apply H1; assumption
  apply H2; assumption


lemma indSym
  {IsPolyTime : PolyFamOracleCompPred}
  {Domain : ℕ -> Type}
  {distr1 distr2 : famDistr Domain}
  (H1 : CompIndistinguishabilityDistr IsPolyTime distr1 distr2)
  : CompIndistinguishabilityDistr IsPolyTime distr2 distr1 :=
  by
    rw [CompIndistinguishabilityDistrDefEq] at *
    simp [CompIndistinguishabilityDistrDef2] at *
    conv =>
      intro
      arg 2
      arg 1
      intro
      rw [distSymm]
    assumption

lemma indTransRev
  (IsPolyTime : PolyFamOracleCompPred)
  {Domain : ℕ -> Type}
  {distr1 distr2 distr3 : famDistr Domain}
  (H2 : CompIndistinguishabilityDistr IsPolyTime distr3 distr2)
  (H1 : CompIndistinguishabilityDistr IsPolyTime distr1 distr2)
: CompIndistinguishabilityDistr IsPolyTime distr1 distr3 :=
by
  apply indTrans _ H1 (indSym H2)


lemma IndistinguishabilityByReduction {X : ℕ -> Type} {I : Type} {Spec : ℕ -> OracleSpec I}
  (IsPolyTime : PolyFamOracleCompPred)
  (HisPoly : PolyTimeClosedUnderComposition IsPolyTime)
  (seededOracleImpl1 seededOracleImpl2 : famSeededOracle Spec)
  (Hind : CompIndistinguishabilitySeededOracle IsPolyTime seededOracleImpl1 seededOracleImpl2)
  (reduction : famOracleComp Spec X)
  (Hreduction : IsPolyTime reduction)
  : CompIndistinguishabilityDistr IsPolyTime
    (compToDistrGen seededOracleImpl1 reduction)
    (compToDistrGen seededOracleImpl2 reduction)
    :=
  by
    simp [CompIndistinguishabilityDistr]
    intro disti
    intro HpolyDistri
    conv =>
      congr
      intro κ
      simp [advantage]
      rw [compositionSemantics]
      rw [compositionSemantics]
    apply Hind
    apply HisPoly <;> assumption
