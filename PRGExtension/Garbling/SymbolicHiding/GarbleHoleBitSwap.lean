import PRGExtension.Garbling.SymbolicHiding.SimulateProof
import PRGExtension.Expression.Renamings

/-!
# The renaming that maps garbling to simulation

LM18 Theorem 5: `Pattern(Garble(C,x)) ≈ Pattern(Simulate(C,C(x)))`.

The witness is `makeVarRenaming f`, where `f i` is the value carried by the wire whose label
has bit index `i`.  It does two things at once:

* the **key** half `makeKeySwap f` exchanges `K_{2i}` and `K_{2i+1}` exactly when wire `i`
  carries `1`, sending each label's *active* key — the one the garbling reveals — to that
  label's key `0`, which is the one the simulation reveals.  Because a label's two keys carry
  the same `G`-prefix (`SwapCompatible`), this works under any number of `Dup`s;
* the **bit** half `bitPerm f` negates `B_i` on the same indices, which via `normalizeExpr`'s
  rule `π[¬b](p₀,p₁) ↝ π[b](p₁,p₀)` moves each garbled table's decryptable row to position
  `(0,0)`, where the simulator's is.

At a `NAnd` gate the two effects cancel exactly.  Row `(v_i,v_j)` carries `(¬B_h, K_h¹)`
unless `(v_i,v_j) = (1,1)`, where it carries `(B_h, K_h⁰)`.  In the first case the gate's
output is `1`, so `f` flips index `h`: `¬B_h ↦ ¬¬B_h ↝ B_h` and `K_h¹ ↦ K_h⁰`.  In the second
the output is `0` and `f` fixes `h`.  Either way the row becomes `(B_h, K_h⁰)` — exactly what
`Sim` writes in all four rows.
-/

namespace PRG

/-! ## The key counter, independently of the labels -/
def gbCtr : {s t : WireBundle} -> Circuit s t -> ℕ -> ℕ
  | _, _, Circuit.NandC, ctr => ctr + 1
  | _, _, Circuit.FirstC c _, ctr => gbCtr c ctr
  | _, _, Circuit.ComposeC c1 c2, ctr => gbCtr c2 (gbCtr c1 ctr)
  | _, _, Circuit.SwapC _ _, ctr => ctr
  | _, _, Circuit.AssocC _ _ _, ctr => ctr
  | _, _, Circuit.UnAssocC _ _ _, ctr => ctr
  | _, _, Circuit.DupC, ctr => ctr
theorem gb_ctr_eq : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    (gb c u ctr).2.2 = gbCtr c ctr := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨i1, i2⟩ ctr; rfl
  | AssocC a b d => rintro ⟨i1, i2, i3⟩ ctr; rfl
  | UnAssocC a b d => rintro ⟨⟨i1, i2⟩, i3⟩ ctr; rfl
  | DupC => intro l ctr; rfl
  | NandC => rintro ⟨li, lj⟩ ctr; rfl
  | FirstC c1 wb ih => rintro ⟨b1, b2⟩ ctr; exact ih b1 ctr
  | ComposeC c1 c2 ih1 ih2 =>
      intro b ctr
      show (gb c2 (gb c1 b ctr).2.1 (gb c1 b ctr).2.2).2.2 = gbCtr c2 (gbCtr c1 ctr)
      rw [ih2 _ _, ih1 b ctr]
lemma gbCtr_mono : ∀ {s t : WireBundle} (c : Circuit s t) (ctr : ℕ), ctr ≤ gbCtr c ctr := by
  intro s t c
  induction c with
  | SwapC a b => intro ctr; exact le_refl _
  | AssocC a b d => intro ctr; exact le_refl _
  | UnAssocC a b d => intro ctr; exact le_refl _
  | DupC => intro ctr; exact le_refl _
  | NandC => intro ctr; show ctr ≤ ctr + 1; omega
  | FirstC c1 wb ih => intro ctr; exact ih ctr
  | ComposeC c1 c2 ih1 ih2 => intro ctr; exact le_trans (ih1 ctr) (ih2 _)
/-! ## Labels are swap-compatible

Every label's two keys are `G^w(K_{2b})` and `G^w(K_{2b+1})` for the *same* `w` and for
`b = l.bit`.  Rather than name `w`, we record the consequence Theorem 5 uses: the key
renaming `makeKeySwap f` exchanges a label's two keys exactly when `f` flips the label's
own bit index. -/
def SwapCompatible (l : WireLabel) : Prop :=
  ∀ f : ℕ → Bool,
    applyKeyRenamingP (makeKeySwap f) l.key0 = cond (f l.bit) l.key1 l.key0 ∧
    applyKeyRenamingP (makeKeySwap f) l.key1 = cond (f l.bit) l.key0 l.key1
def SwapCompatibleB : {b : WireBundle} -> labelType b -> Prop
  | WireBundle.SimpleB, l => SwapCompatible l
  | WireBundle.PairB _ _, (l1, l2) => SwapCompatibleB l1 ∧ SwapCompatibleB l2
lemma makeKeySwap_even (f : ℕ → Bool) (i : ℕ) :
    makeKeySwap f (2*i) = if f i then 2*i+1 else 2*i := by
  simp only [makeKeySwap, condNotNat, notNat, yesNat]
  have h1 : 2*i/2 = i := by omega
  have h2 : 2*i%2 = 0 := by omega
  rw [h1, h2]
  cases f i <;> simp
lemma makeKeySwap_odd (f : ℕ → Bool) (i : ℕ) :
    makeKeySwap f (2*i+1) = if f i then 2*i else 2*i+1 := by
  simp only [makeKeySwap, condNotNat, notNat, yesNat]
  have h1 : (2*i+1)/2 = i := by omega
  have h2 : (2*i+1)%2 = 1 := by omega
  rw [h1, h2]
  cases f i <;> simp
lemma swapCompatible_varK (i : ℕ) :
    SwapCompatible ⟨i, Expression.VarK (2*i), Expression.VarK (2*i+1)⟩ := by
  intro f
  constructor <;>
    · simp only [applyKeyRenamingP, makeKeySwap_even, makeKeySwap_odd]
      cases f i <;> simp
lemma swapCompatible_G0 {l : WireLabel} (h : SwapCompatible l) :
    SwapCompatible ⟨l.bit, Expression.G0 l.key0, Expression.G0 l.key1⟩ := by
  intro f
  obtain ⟨h0, h1⟩ := h f
  constructor <;>
    · simp only [applyKeyRenamingP]
      first | rw [h0] | rw [h1]
      cases f l.bit <;> simp
lemma swapCompatible_G1 {l : WireLabel} (h : SwapCompatible l) :
    SwapCompatible ⟨l.bit, Expression.G1 l.key0, Expression.G1 l.key1⟩ := by
  intro f
  obtain ⟨h0, h1⟩ := h f
  constructor <;>
    · simp only [applyKeyRenamingP]
      first | rw [h0] | rw [h1]
      cases f l.bit <;> simp
theorem gb_swapCompatible : ∀ {s t : WireBundle} (c : Circuit s t) (u : labelType s) (ctr : ℕ),
    SwapCompatibleB u → SwapCompatibleB (gb c u ctr).2.1 := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨i1, i2⟩ ctr ⟨h1, h2⟩; exact ⟨h2, h1⟩
  | AssocC a b d => rintro ⟨i1, i2, i3⟩ ctr ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  | UnAssocC a b d => rintro ⟨⟨i1, i2⟩, i3⟩ ctr ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  | DupC => intro l ctr h; exact ⟨swapCompatible_G0 h, swapCompatible_G1 h⟩
  | NandC => rintro ⟨li, lj⟩ ctr _; exact swapCompatible_varK ctr
  | FirstC c1 wb ih => rintro ⟨u1, u2⟩ ctr ⟨h1, h2⟩; exact ⟨ih u1 ctr h1, h2⟩
  | ComposeC c1 c2 ih1 ih2 => intro u ctr h; exact ih2 _ _ (ih1 u ctr h)
lemma makeLabels_swapCompatible : ∀ (b : WireBundle) (i : ℕ),
    SwapCompatibleB (makeLabels b i).1
  | WireBundle.SimpleB, i => swapCompatible_varK i
  | WireBundle.PairB o1 o2, i =>
      ⟨makeLabels_swapCompatible o1 i, makeLabels_swapCompatible o2 (makeLabels o1 i).2⟩
/-! ## The wire-value assignment

`f : ℕ → Bool` records, for each key-variable index, the value the corresponding wire
carries.  Theorem 5's renaming is `makeVarRenaming f`.  Rather than reason about `f`
globally, the main induction takes `AgreesOn f c v ctr` as a *structural* hypothesis, which
`Compose` splits along the circuit — no freshness argument needed there.  Freshness enters
only once, in `agreesOn_valueMap`, to see that the canonical `f` really does agree. -/
def LabelValues (f : ℕ → Bool) : {b : WireBundle} -> labelType b -> bundleBool b -> Prop
  | WireBundle.SimpleB, l, v => f l.bit = v
  | WireBundle.PairB _ _, (l1, l2), (v1, v2) => LabelValues f l1 v1 ∧ LabelValues f l2 v2
def AgreesOn (f : ℕ → Bool) : {s t : WireBundle} -> (c : Circuit s t) ->
    bundleBool s -> ℕ -> Prop
  | _, _, Circuit.NandC, (vi, vj), ctr => f ctr = !(vi && vj)
  | _, _, Circuit.FirstC c _, (v1, _), ctr => AgreesOn f c v1 ctr
  | _, _, Circuit.ComposeC c1 c2, v, ctr =>
      AgreesOn f c1 v ctr ∧ AgreesOn f c2 (evalCircuit c1 v) (gbCtr c1 ctr)
  | _, _, Circuit.SwapC _ _, _, _ => True
  | _, _, Circuit.AssocC _ _ _, _, _ => True
  | _, _, Circuit.UnAssocC _ _ _, _, _ => True
  | _, _, Circuit.DupC, _, _ => True
def valueMap : {s t : WireBundle} -> (c : Circuit s t) -> bundleBool s -> ℕ ->
    (ℕ → Bool) -> (ℕ → Bool)
  | _, _, Circuit.NandC, (vi, vj), ctr, f => Function.update f ctr (!(vi && vj))
  | _, _, Circuit.FirstC c _, (v1, _), ctr, f => valueMap c v1 ctr f
  | _, _, Circuit.ComposeC c1 c2, v, ctr, f =>
      valueMap c2 (evalCircuit c1 v) (gbCtr c1 ctr) (valueMap c1 v ctr f)
  | _, _, Circuit.SwapC _ _, _, _, f => f
  | _, _, Circuit.AssocC _ _ _, _, _, f => f
  | _, _, Circuit.UnAssocC _ _ _, _, _, f => f
  | _, _, Circuit.DupC, _, _, f => f
theorem valueMap_lt : ∀ {s t : WireBundle} (c : Circuit s t) (v : bundleBool s) (ctr : ℕ)
    (f : ℕ → Bool) (m : ℕ), m < ctr → valueMap c v ctr f m = f m := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨v1, v2⟩ ctr f m _; rfl
  | AssocC a b d => rintro ⟨v1, v2, v3⟩ ctr f m _; rfl
  | UnAssocC a b d => rintro ⟨⟨v1, v2⟩, v3⟩ ctr f m _; rfl
  | DupC => intro v ctr f m _; rfl
  | NandC =>
      rintro ⟨vi, vj⟩ ctr f m hm
      show Function.update f ctr _ m = f m
      exact Function.update_of_ne (by omega) _ _
  | FirstC c1 wb ih => rintro ⟨v1, v2⟩ ctr f m hm; exact ih v1 ctr f m hm
  | ComposeC c1 c2 ih1 ih2 =>
      intro v ctr f m hm
      show valueMap c2 _ (gbCtr c1 ctr) (valueMap c1 v ctr f) m = f m
      rw [ih2 _ _ _ m (lt_of_lt_of_le hm (gbCtr_mono c1 ctr)), ih1 v ctr f m hm]
theorem valueMap_ge : ∀ {s t : WireBundle} (c : Circuit s t) (v : bundleBool s) (ctr : ℕ)
    (f : ℕ → Bool) (m : ℕ), gbCtr c ctr ≤ m → valueMap c v ctr f m = f m := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨v1, v2⟩ ctr f m _; rfl
  | AssocC a b d => rintro ⟨v1, v2, v3⟩ ctr f m _; rfl
  | UnAssocC a b d => rintro ⟨⟨v1, v2⟩, v3⟩ ctr f m _; rfl
  | DupC => intro v ctr f m _; rfl
  | NandC =>
      rintro ⟨vi, vj⟩ ctr f m hm
      have : ctr + 1 ≤ m := hm
      show Function.update f ctr _ m = f m
      exact Function.update_of_ne (by omega) _ _
  | FirstC c1 wb ih => rintro ⟨v1, v2⟩ ctr f m hm; exact ih v1 ctr f m hm
  | ComposeC c1 c2 ih1 ih2 =>
      intro v ctr f m hm
      have hm' : gbCtr c2 (gbCtr c1 ctr) ≤ m := hm
      show valueMap c2 _ (gbCtr c1 ctr) (valueMap c1 v ctr f) m = f m
      rw [ih2 _ _ _ m hm',
        ih1 v ctr f m (le_trans (gbCtr_mono c2 (gbCtr c1 ctr)) hm')]
/-- `AgreesOn` only looks at `f` inside the sub-circuit's own counter range. -/
theorem agreesOn_congr : ∀ {s t : WireBundle} (c : Circuit s t) (v : bundleBool s) (ctr : ℕ)
    (f g : ℕ → Bool), (∀ m, ctr ≤ m → m < gbCtr c ctr → f m = g m) →
    AgreesOn f c v ctr → AgreesOn g c v ctr := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨v1, v2⟩ ctr f g _ _; trivial
  | AssocC a b d => rintro ⟨v1, v2, v3⟩ ctr f g _ _; trivial
  | UnAssocC a b d => rintro ⟨⟨v1, v2⟩, v3⟩ ctr f g _ _; trivial
  | DupC => intro v ctr f g _ _; trivial
  | NandC =>
      rintro ⟨vi, vj⟩ ctr f g h ha
      show g ctr = _
      rw [← h ctr (le_refl _) (by show ctr < ctr + 1; omega)]
      exact ha
  | FirstC c1 wb ih => rintro ⟨v1, v2⟩ ctr f g h ha; exact ih v1 ctr f g h ha
  | ComposeC c1 c2 ih1 ih2 =>
      intro v ctr f g h ⟨ha1, ha2⟩
      have hb1 := gbCtr_mono c1 ctr
      have hb2 := gbCtr_mono c2 (gbCtr c1 ctr)
      have h' : ∀ m, ctr ≤ m → m < gbCtr c2 (gbCtr c1 ctr) → f m = g m := h
      exact ⟨ih1 v ctr f g (fun m h1 h2 => h' m h1 (by omega)) ha1,
        ih2 _ _ f g (fun m h1 h2 => h' m (by omega) h2) ha2⟩
/-- The canonical assignment agrees with the circuit it was built from. -/
theorem agreesOn_valueMap : ∀ {s t : WireBundle} (c : Circuit s t) (v : bundleBool s)
    (ctr : ℕ) (f : ℕ → Bool), AgreesOn (valueMap c v ctr f) c v ctr := by
  intro s t c
  induction c with
  | SwapC a b => rintro ⟨v1, v2⟩ ctr f; trivial
  | AssocC a b d => rintro ⟨v1, v2, v3⟩ ctr f; trivial
  | UnAssocC a b d => rintro ⟨⟨v1, v2⟩, v3⟩ ctr f; trivial
  | DupC => intro v ctr f; trivial
  | NandC =>
      rintro ⟨vi, vj⟩ ctr f
      show Function.update f ctr _ ctr = _
      simp
  | FirstC c1 wb ih => rintro ⟨v1, v2⟩ ctr f; exact ih v1 ctr f
  | ComposeC c1 c2 ih1 ih2 =>
      intro v ctr f
      refine ⟨?_, ih2 _ _ _⟩
      refine agreesOn_congr c1 v ctr (valueMap c1 v ctr f) _ ?_ (ih1 v ctr f)
      intro m _ h2
      exact (valueMap_lt c2 _ (gbCtr c1 ctr) (valueMap c1 v ctr f) m h2).symm

/-! ## Theorem 5 -/

/-- The shape both sides normalise to at a `NAnd` gate: the decryptable row is at position
    `(0,0)` and carries `(B_h, K_h⁰)`; the sibling row is an `Enc`/`Hidden`; the two rows
    under the wrong outer key are indistinguishable holes. -/
def nandPattern (li lj : WireLabel) (n : ℕ) :
    Expression (Shape.PairS (Shape.PairS (Shape.EncS (Shape.EncS (Shape.PairS Shape.BitS Shape.KeyS)))
      (Shape.EncS (Shape.EncS (Shape.PairS Shape.BitS Shape.KeyS))))
      (Shape.PairS (Shape.EncS (Shape.EncS (Shape.PairS Shape.BitS Shape.KeyS)))
      (Shape.EncS (Shape.EncS (Shape.PairS Shape.BitS Shape.KeyS))))) :=
  Expression.Perm (Expression.BitE li.bitE)
    (Expression.Perm (Expression.BitE lj.bitE)
      (Expression.Enc li.key0 (Expression.Enc lj.key0
        (Expression.Pair (Expression.BitE (BitExpr.VarB n)) (Expression.VarK (2*n)))))
      (Expression.Enc li.key0 (Expression.Hidden lj.key1)))
    (Expression.Perm (Expression.BitE lj.bitE)
      (Expression.Hidden li.key1) (Expression.Hidden li.key1))
lemma nand_pattern_sim (T : Finset (Expression Shape.KeyS)) (li lj : WireLabel) (n : ℕ)
    (hi1 : li.key0 ∈ T) (hi0 : li.key1 ∉ T)
    (hj1 : lj.key0 ∈ T) (hj0 : lj.key1 ∉ T) :
    normalizeExpr (hideEncrypted T (sim Circuit.NandC (li, lj) n).1)
      = nandPattern li lj n := by
  simp only [sim, gbEntry, hideEncrypted, hideEncrypted_key, normalizeExpr, normalizeB,
    nandPattern, WireLabel.bitE, hi1, hi0, hj1, hj0, if_true, if_false, reduceIte]
lemma nand_pattern_gb (S : Finset (Expression Shape.KeyS)) (li lj : WireLabel) (n : ℕ)
    (f : ℕ → Bool) (vi vj : Bool)
    (hfi : f li.bit = vi) (hfj : f lj.bit = vj) (hfn : f n = !(vi && vj))
    (hsci : SwapCompatible li) (hscj : SwapCompatible lj)
    (hi1 : cond vi li.key1 li.key0 ∈ S) (hi0 : cond vi li.key0 li.key1 ∉ S)
    (hj1 : cond vj lj.key1 lj.key0 ∈ S) (hj0 : cond vj lj.key0 lj.key1 ∉ S) :
    normalizeExpr (applyVarRenaming (makeVarRenaming f)
        (hideEncrypted S (gb Circuit.NandC (li, lj) n).1))
      = nandPattern li lj n := by
  obtain ⟨hri0, hri1⟩ := hsci f
  obtain ⟨hrj0, hrj1⟩ := hscj f
  rw [hfi] at hri0 hri1
  rw [hfj] at hrj0 hrj1
  cases vi <;> cases vj <;>
    simp_all only [cond_true, cond_false, Bool.and_self, Bool.and_true, Bool.and_false,
      Bool.false_and, Bool.true_and, Bool.not_true, Bool.not_false] <;>
    simp [gb, gbEntry, hideEncrypted, hideEncrypted_key, applyVarRenaming,
      applyBitRenaming, applyBitRenamingB, applyKeyRenamingP, makeVarRenaming, bitPerm,
      varOrNegVarToExpr, normalizeExpr, normalizeB, nandPattern, WireLabel.bitE,
      hi1, hi0, hj1, hj0, hri0, hri1, hrj0, hrj1, hfi, hfj, hfn,
      makeKeySwap_even, makeKeySwap_odd]
theorem theorem5_core {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) (f : ℕ → Bool) :
    ∀ {s' t' : WireBundle} (c' : Circuit s' t') (u' : labelType s') (ctr' : ℕ)
      (v : bundleBool s'),
      GbStage c (makeLabels s 0).1 (makeLabels s 0).2 c' u' ctr' →
      LabelValues f u' v → SwapCompatibleB u' →
      LabelValueIn (keySubterms (Garble c x)) (adversaryKeys (Garble c x)) u' v →
      LabelZeroIn (keySubterms (Simulate c (evalCircuit c x)))
        (adversaryKeys (Simulate c (evalCircuit c x))) u' →
      AgreesOn f c' v ctr' →
      (normalizeExpr (applyVarRenaming (makeVarRenaming f)
          (hideEncrypted (adversaryKeys (Garble c x)) (gb c' u' ctr').1))
        = normalizeExpr (hideEncrypted (adversaryKeys (Simulate c (evalCircuit c x)))
            (sim c' u' ctr').1))
      ∧ LabelValues f (gb c' u' ctr').2.1 (evalCircuit c' v) := by
  intro s' t' c'
  set y := evalCircuit c x with hy
  set S := adversaryKeys (Garble c x) with hS
  set T := adversaryKeys (Simulate c y) with hT
  have hsubS : keySubterms (gb c (makeLabels s 0).1 (makeLabels s 0).2).1
      ⊆ keySubterms (Garble c x) := keySubterms_garble_gb c x
  have hsubT : keySubterms (sim c (makeLabels s 0).1 (makeLabels s 0).2).1
      ⊆ keySubterms (Simulate c y) := keySubterms_simulate_sim c y
  induction c' with
  | SwapC a b => rintro ⟨i1, i2⟩ ctr ⟨v1, v2⟩ _ ⟨h1, h2⟩ _ _ _ _; exact ⟨rfl, h2, h1⟩
  | AssocC a b d =>
      rintro ⟨i1, i2, i3⟩ ctr ⟨v1, v2, v3⟩ _ ⟨h1, h2, h3⟩ _ _ _ _; exact ⟨rfl, ⟨h1, h2⟩, h3⟩
  | UnAssocC a b d =>
      rintro ⟨⟨i1, i2⟩, i3⟩ ctr ⟨⟨v1, v2⟩, v3⟩ _ ⟨⟨h1, h2⟩, h3⟩ _ _ _ _; exact ⟨rfl, h1, h2, h3⟩
  | DupC => intro l ctr v _ hlv _ _ _ _; exact ⟨rfl, hlv, hlv⟩
  | NandC =>
      rintro ⟨li, lj⟩ n ⟨vi, vj⟩ hstage ⟨hfi, hfj⟩ ⟨hsci, hscj⟩ ⟨invi, invj⟩ ⟨invi', invj'⟩ hag
      obtain ⟨m1, m2, m3, m4⟩ := nand_keySubterms li lj n
      obtain ⟨p1, p2, p3, p4⟩ := nand_keySubterms_sim li lj n
      have hks := hstage.keySubterms_subset
      have hkt := hstage.keySubterms_subset_sim
      have hi := invi ⟨hsubS (hks m1), hsubS (hks m2)⟩
      have hj := invj ⟨hsubS (hks m3), hsubS (hks m4)⟩
      have hti := invi' ⟨hsubT (hkt p1), hsubT (hkt p2)⟩
      have htj := invj' ⟨hsubT (hkt p3), hsubT (hkt p4)⟩
      have hfn : f n = !(vi && vj) := hag
      refine ⟨?_, hfn⟩
      rw [nand_pattern_gb S li lj n f vi vj hfi hfj hfn hsci hscj hi.1 hi.2 hj.1 hj.2,
        nand_pattern_sim T li lj n hti.1 hti.2 htj.1 htj.2]
  | FirstC c1 wb ih =>
      rintro ⟨u1, u2⟩ ctr ⟨v1, v2⟩ hstage ⟨hlv1, hlv2⟩ ⟨hsc1, hsc2⟩ ⟨hi1, hi2⟩ ⟨hz1, hz2⟩ hag
      obtain ⟨heq, hout⟩ :=
        ih u1 ctr v1 (hstage.trans (GbStage.first (GbStage.refl c1 u1 ctr)))
          hlv1 hsc1 hi1 hz1 hag
      exact ⟨heq, hout, hlv2⟩
  | ComposeC c1 c2 ih1 ih2 =>
      intro u' ctr' v hstage hlv hsc hinvS hinvT hag
      have st1 := hstage.trans (GbStage.composeL (GbStage.refl c1 u' ctr'))
      obtain ⟨heq1, hout1⟩ := ih1 u' ctr' v st1 hlv hsc hinvS hinvT hag.1
      have st2 := hstage.trans (GbStage.composeR
        (GbStage.refl c2 (gb c1 u' ctr').2.1 (gb c1 u' ctr').2.2))
      have hag2 : AgreesOn f c2 (evalCircuit c1 v) (gb c1 u' ctr').2.2 := by
        rw [gb_ctr_eq]; exact hag.2
      obtain ⟨heq2, hout2⟩ := ih2 (gb c1 u' ctr').2.1 (gb c1 u' ctr').2.2 (evalCircuit c1 v)
        st2 hout1 (gb_swapCompatible c1 u' ctr' hsc)
        (lemma7_value c x c1 u' ctr' v st1 hinvS)
        (lemma8_zero c y c1 u' ctr' st1 hinvT) hag2
      refine ⟨?_, hout2⟩
      show normalizeExpr (applyVarRenaming (makeVarRenaming f)
          (Expression.Pair (hideEncrypted S (gb c1 u' ctr').1)
            (hideEncrypted S (gb c2 (gb c1 u' ctr').2.1 (gb c1 u' ctr').2.2).1)))
        = normalizeExpr (Expression.Pair (hideEncrypted T (sim c1 u' ctr').1)
            (hideEncrypted T (sim c2 (sim c1 u' ctr').2.1 (sim c1 u' ctr').2.2).1))
      simp only [applyVarRenaming, applyBitRenaming, applyKeyRenamingP, normalizeExpr,
        sim_snd_fst, sim_snd_snd]
      simp only [applyVarRenaming] at heq1 heq2
      rw [heq1, heq2]
/-- The keys the input encoding reveals, and the ones it withholds. -/
def selKeys : {b : WireBundle} -> labelType b -> bundleBool b -> Finset (Expression Shape.KeyS)
  | WireBundle.SimpleB, l, v => {cond v l.key1 l.key0}
  | WireBundle.PairB _ _, (l1, l2), (v1, v2) => selKeys l1 v1 ∪ selKeys l2 v2
def unselKeys : {b : WireBundle} -> labelType b -> bundleBool b -> Finset (Expression Shape.KeyS)
  | WireBundle.SimpleB, l, v => {cond v l.key0 l.key1}
  | WireBundle.PairB _ _, (l1, l2), (v1, v2) => unselKeys l1 v1 ∪ unselKeys l2 v2
lemma selKeys_subset : ∀ {b : WireBundle} (u : labelType b) (v : bundleBool b),
    selKeys u v ⊆ labelKeys u
  | WireBundle.SimpleB, l, v => by
      cases v <;> simp [selKeys, labelKeys]
  | WireBundle.PairB o1 o2, (l1, l2), (v1, v2) => by
      simp only [selKeys, labelKeys]
      exact Finset.union_subset_union (selKeys_subset l1 v1) (selKeys_subset l2 v2)
lemma unselKeys_subset : ∀ {b : WireBundle} (u : labelType b) (v : bundleBool b),
    unselKeys u v ⊆ labelKeys u
  | WireBundle.SimpleB, l, v => by
      cases v <;> simp [unselKeys, labelKeys]
  | WireBundle.PairB o1 o2, (l1, l2), (v1, v2) => by
      simp only [unselKeys, labelKeys]
      exact Finset.union_subset_union (unselKeys_subset l1 v1) (unselKeys_subset l2 v2)
/-- Distinct labels never hide a key they also reveal. -/
lemma unsel_notMem_sel : ∀ {b : WireBundle} (u : labelType b) (v : bundleBool b),
    DistinctLabels u → ∀ k ∈ unselKeys u v, k ∉ selKeys u v
  | WireBundle.SimpleB, l, v, hd, k, hk => by
      cases v <;>
        · simp only [unselKeys, selKeys, cond_true, cond_false, Finset.mem_singleton] at hk ⊢
          subst hk
          simpa using fun h => hd (by first | exact h.symm | exact h)
  | WireBundle.PairB o1 o2, (l1, l2), (v1, v2), hd, k, hk => by
      obtain ⟨d1, d2, hdisj⟩ := hd
      simp only [unselKeys, Finset.mem_union] at hk
      simp only [selKeys, Finset.mem_union, not_or]
      rcases hk with hk | hk
      · refine ⟨unsel_notMem_sel l1 v1 d1 k hk, fun hc => ?_⟩
        exact mem_of_inter_empty hdisj (unselKeys_subset l1 v1 hk) (selKeys_subset l2 v2 hc)
      · refine ⟨fun hc => ?_, unsel_notMem_sel l2 v2 d2 k hk⟩
        exact mem_of_inter_empty hdisj (selKeys_subset l1 v1 hc) (unselKeys_subset l2 v2 hk)
/-- The encoded input reveals exactly the selected keys. -/
lemma extractKeys_view_gEnc_eq (S : Finset (Expression Shape.KeyS)) :
    ∀ {b : WireBundle} (u : labelType b) (x : bundleBool b),
      extractKeys (hideEncrypted S (encodedLabelToExpr (gEnc u x))) = selKeys u x
  | WireBundle.SimpleB, l, x => by
      cases x <;>
        · simp only [gEnc, encodedLabelToExpr, hideEncrypted, hideEncrypted_key, cond_true,
            cond_false, extractKeys, extractKeys_key, selKeys]
          simp
  | WireBundle.PairB o1 o2, (l1, l2), (x1, x2) => by
      simp only [gEnc, encodedLabelToExpr, hideEncrypted, extractKeys, selKeys,
        extractKeys_view_gEnc_eq S l1 x1, extractKeys_view_gEnc_eq S l2 x2]
/-- Assemble `LabelValueIn` from the two global facts about the whole label bundle. -/
lemma labelValueIn_of (U S : Finset (Expression Shape.KeyS)) :
    ∀ {b : WireBundle} (u : labelType b) (x : bundleBool b),
      (∀ k ∈ selKeys u x, k ∈ S) → (∀ k ∈ unselKeys u x, k ∉ S) → LabelValueIn U S u x
  | WireBundle.SimpleB, l, x, hs, hu => by
      intro _
      refine ⟨hs _ (by simp [selKeys]), hu _ (by simp [unselKeys])⟩
  | WireBundle.PairB o1 o2, (l1, l2), (x1, x2), hs, hu => by
      simp only [selKeys, unselKeys] at hs hu
      refine ⟨labelValueIn_of U S l1 x1 (fun k hk => hs k (Finset.mem_union_left _ hk))
          (fun k hk => hu k (Finset.mem_union_left _ hk)),
        labelValueIn_of U S l2 x2 (fun k hk => hs k (Finset.mem_union_right _ hk))
          (fun k hk => hu k (Finset.mem_union_right _ hk))⟩
def zeroBundle : (b : WireBundle) -> bundleBool b
  | WireBundle.SimpleB => false
  | WireBundle.PairB b1 b2 => (zeroBundle b1, zeroBundle b2)
lemma sEnc_eq_gEnc : ∀ {b : WireBundle} (u : labelType b),
    sEnc u = gEnc u (zeroBundle b)
  | WireBundle.SimpleB, l => rfl
  | WireBundle.PairB o1 o2, (l1, l2) => by
      simp only [sEnc, gEnc, zeroBundle, sEnc_eq_gEnc l1, sEnc_eq_gEnc l2]
lemma labelZeroIn_of (U T : Finset (Expression Shape.KeyS)) :
    ∀ {b : WireBundle} (u : labelType b),
      (∀ k ∈ selKeys u (zeroBundle b), k ∈ T) →
      (∀ k ∈ unselKeys u (zeroBundle b), k ∉ T) → LabelZeroIn U T u
  | WireBundle.SimpleB, l, hs, hu => by
      intro _
      refine ⟨hs _ (by simp [selKeys, zeroBundle]), hu _ (by simp [unselKeys, zeroBundle])⟩
  | WireBundle.PairB o1 o2, (l1, l2), hs, hu => by
      simp only [selKeys, unselKeys, zeroBundle] at hs hu
      refine ⟨labelZeroIn_of U T l1 (fun k hk => hs k (Finset.mem_union_left _ hk))
          (fun k hk => hu k (Finset.mem_union_left _ hk)),
        labelZeroIn_of U T l2 (fun k hk => hs k (Finset.mem_union_right _ hk))
          (fun k hk => hu k (Finset.mem_union_right _ hk))⟩
/-- The input encoding really does reveal one key of each input wire … -/
theorem input_sel_mem {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    ∀ k ∈ selKeys (makeLabels s 0).1 x, k ∈ adversaryKeys (Garble c x) := by
  intro k hk
  apply extractKeys_adversaryView_subset
  rw [extractKeys_adversaryView_garble, Finset.mem_union]
  right
  rw [extractKeys_view_gEnc_eq]
  exact hk
/-- … and withholds the other. -/
theorem input_unsel_notMem {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    ∀ k ∈ unselKeys (makeLabels s 0).1 x, k ∉ adversaryKeys (Garble c x) := by
  intro k hk hcon
  have hlk : k ∈ labelKeys (makeLabels s 0).1 := unselKeys_subset _ x hk
  have h1 := atomic_recovered_garble c x (makeLabels_atomic s 0 k hlk) hcon
  rw [extractKeys_adversaryView_garble, Finset.mem_union] at h1
  rcases h1 with h1 | h1
  · obtain ⟨j, hj1, _, hj3⟩ :=
      extractKeys_view_range (adversaryKeys (Garble c x)) c (makeLabels s 0).1
        (makeLabels s 0).2 k h1
    have h2 := labelKeys_below (makeLabels s 0).1 (makeLabels_below s 0).2 k hlk
    have h3 := h2 j (by rw [hj3]; simp [keySubterms])
    omega
  · rw [extractKeys_view_gEnc_eq] at h1
    exact unsel_notMem_sel _ x (makeLabels_stronglyIndependent s 0).2 k hk h1
theorem input_sel_mem_sim {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    ∀ k ∈ selKeys (makeLabels s 0).1 (zeroBundle s), k ∈ adversaryKeys (Simulate c y) := by
  intro k hk
  apply extractKeys_adversaryView_subset
  rw [extractKeys_adversaryView_simulate, Finset.mem_union]
  right
  rw [sEnc_eq_gEnc, extractKeys_view_gEnc_eq]
  exact hk
theorem input_unsel_notMem_sim {s t : WireBundle} (c : Circuit s t) (y : bundleBool t) :
    ∀ k ∈ unselKeys (makeLabels s 0).1 (zeroBundle s), k ∉ adversaryKeys (Simulate c y) := by
  intro k hk hcon
  have hlk : k ∈ labelKeys (makeLabels s 0).1 := unselKeys_subset _ _ hk
  have h1 := atomic_recovered_simulate c y (makeLabels_atomic s 0 k hlk) hcon
  rw [extractKeys_adversaryView_simulate, Finset.mem_union] at h1
  rcases h1 with h1 | h1
  · obtain ⟨j, hj1, _, hj3⟩ :=
      extractKeys_view_range_sim (adversaryKeys (Simulate c y)) c (makeLabels s 0).1
        (makeLabels s 0).2 k h1
    have h2 := labelKeys_below (makeLabels s 0).1 (makeLabels_below s 0).2 k hlk
    have h3 := h2 j (by rw [hj3]; simp [keySubterms])
    omega
  · rw [sEnc_eq_gEnc, extractKeys_view_gEnc_eq] at h1
    exact unsel_notMem_sel _ _ (makeLabels_stronglyIndependent s 0).2 k hk h1
def inputValues : {b : WireBundle} -> labelType b -> bundleBool b ->
    (ℕ → Bool) -> (ℕ → Bool)
  | WireBundle.SimpleB, l, v, g => Function.update g l.bit v
  | WireBundle.PairB _ _, (l1, l2), (v1, v2), g => inputValues l2 v2 (inputValues l1 v1 g)
lemma inputValues_lt : ∀ (b : WireBundle) (i : ℕ) (x : bundleBool b) (g : ℕ → Bool) (m : ℕ),
    m < i → inputValues (makeLabels b i).1 x g m = g m
  | WireBundle.SimpleB, i, x, g, m, hm => by
      show Function.update g i x m = g m
      exact Function.update_of_ne (by omega) _ _
  | WireBundle.PairB o1 o2, i, (x1, x2), g, m, hm => by
      have h1 := (makeLabels_below o1 i).1
      show inputValues (makeLabels o2 (makeLabels o1 i).2).1 x2
        (inputValues (makeLabels o1 i).1 x1 g) m = g m
      rw [inputValues_lt o2 _ x2 _ m (by omega), inputValues_lt o1 i x1 g m hm]
lemma inputValues_ge : ∀ (b : WireBundle) (i : ℕ) (x : bundleBool b) (g : ℕ → Bool) (m : ℕ),
    (makeLabels b i).2 ≤ m → inputValues (makeLabels b i).1 x g m = g m
  | WireBundle.SimpleB, i, x, g, m, hm => by
      have hm' : i + 1 ≤ m := hm
      show Function.update g i x m = g m
      exact Function.update_of_ne (by omega) _ _
  | WireBundle.PairB o1 o2, i, (x1, x2), g, m, hm => by
      have h2 := (makeLabels_below o2 (makeLabels o1 i).2).1
      have hm' : (makeLabels o2 (makeLabels o1 i).2).2 ≤ m := hm
      show inputValues (makeLabels o2 (makeLabels o1 i).2).1 x2
        (inputValues (makeLabels o1 i).1 x1 g) m = g m
      rw [inputValues_ge o2 _ x2 _ m hm', inputValues_ge o1 i x1 g m (by omega)]
lemma labelValues_congr : ∀ (b : WireBundle) (i : ℕ) (x : bundleBool b) (f g : ℕ → Bool),
    (∀ m, i ≤ m → m < (makeLabels b i).2 → f m = g m) →
    LabelValues f (makeLabels b i).1 x → LabelValues g (makeLabels b i).1 x
  | WireBundle.SimpleB, i, x, f, g, h, hl => by
      show g i = x
      rw [← h i (le_refl _) (by show i < i + 1; omega)]; exact hl
  | WireBundle.PairB o1 o2, i, (x1, x2), f, g, h, ⟨hl1, hl2⟩ => by
      have h1 := (makeLabels_below o1 i).1
      have h2 := (makeLabels_below o2 (makeLabels o1 i).2).1
      have h' : ∀ m, i ≤ m → m < (makeLabels o2 (makeLabels o1 i).2).2 → f m = g m := h
      exact ⟨labelValues_congr o1 i x1 f g (fun m ha hb => h' m ha (by omega)) hl1,
        labelValues_congr o2 _ x2 f g (fun m ha hb => h' m (by omega) hb) hl2⟩
lemma labelValues_inputValues : ∀ (b : WireBundle) (i : ℕ) (x : bundleBool b) (g : ℕ → Bool),
    LabelValues (inputValues (makeLabels b i).1 x g) (makeLabels b i).1 x
  | WireBundle.SimpleB, i, x, g => by show Function.update g i x i = x; simp
  | WireBundle.PairB o1 o2, i, (x1, x2), g => by
      refine ⟨?_, labelValues_inputValues o2 _ x2 _⟩
      refine labelValues_congr o1 i x1 (inputValues (makeLabels o1 i).1 x1 g) _ ?_
        (labelValues_inputValues o1 i x1 g)
      intro m _ hb
      exact (inputValues_lt o2 (makeLabels o1 i).2 x2 _ m hb).symm
/-! ## The encoded input and the output masks -/
lemma view_gEnc_eq (S T : Finset (Expression Shape.KeyS)) (f : ℕ → Bool) :
    ∀ {b : WireBundle} (u : labelType b) (x : bundleBool b),
      LabelValues f u x → SwapCompatibleB u →
      normalizeExpr (applyVarRenaming (makeVarRenaming f)
          (hideEncrypted S (encodedLabelToExpr (gEnc u x))))
        = normalizeExpr (hideEncrypted T (encodedLabelToExpr (sEnc u)))
  | WireBundle.SimpleB, l, x, hlv, hsc => by
      obtain ⟨hr0, hr1⟩ := hsc f
      have hf : f l.bit = x := hlv
      rw [hf] at hr0 hr1
      cases x <;>
        simp [gEnc, sEnc, encodedLabelToExpr, hideEncrypted, hideEncrypted_key,
          applyVarRenaming, applyBitRenaming, applyBitRenamingB, applyKeyRenamingP,
          makeVarRenaming, bitPerm, varOrNegVarToExpr, normalizeExpr, normalizeB,
          WireLabel.bitE, hf, hr0, hr1]
  | WireBundle.PairB o1 o2, (l1, l2), (x1, x2), ⟨hv1, hv2⟩, ⟨hs1, hs2⟩ => by
      simp only [gEnc, sEnc, encodedLabelToExpr, hideEncrypted, applyVarRenaming,
        applyBitRenaming, applyKeyRenamingP, normalizeExpr]
      have e1 := view_gEnc_eq S T f l1 x1 hv1 hs1
      have e2 := view_gEnc_eq S T f l2 x2 hv2 hs2
      simp only [applyVarRenaming] at e1 e2
      rw [e1, e2]
lemma view_mask_eq (S T : Finset (Expression Shape.KeyS)) (f : ℕ → Bool) :
    ∀ {b : WireBundle} (w : labelType b) (y : bundleBool b), LabelValues f w y →
      normalizeExpr (applyVarRenaming (makeVarRenaming f)
          (hideEncrypted S (maskedLabelToExpr (gMask w))))
        = normalizeExpr (hideEncrypted T (maskedLabelToExpr (sMask w y)))
  | WireBundle.SimpleB, l, y, hlv => by
      have hf : f l.bit = y := hlv
      cases y <;>
        simp [gMask, sMask, maskedLabelToExpr, hideEncrypted, applyVarRenaming,
          applyBitRenaming, applyBitRenamingB, applyKeyRenamingP, makeVarRenaming, bitPerm,
          varOrNegVarToExpr, normalizeExpr, normalizeB, WireLabel.bitE, hf]
  | WireBundle.PairB o1 o2, (l1, l2), (y1, y2), ⟨hv1, hv2⟩ => by
      simp only [gMask, sMask, maskedLabelToExpr, hideEncrypted, applyVarRenaming,
        applyBitRenaming, applyKeyRenamingP, normalizeExpr]
      have e1 := view_mask_eq S T f l1 y1 hv1
      have e2 := view_mask_eq S T f l2 y2 hv2
      simp only [applyVarRenaming] at e1 e2
      rw [e1, e2]
/-! ## Theorem 5 -/
theorem theorem5 : Theorem5 := by
  intro s t c x
  refine ⟨makeVarRenaming (valueMap c x (makeLabels s 0).2
      (inputValues (makeLabels s 0).1 x (fun _ => false))),
    makeTotalRenamingCorrect _, ?_⟩
  set g₀ := inputValues (makeLabels s 0).1 x (fun _ => false) with hg₀
  set f := valueMap c x (makeLabels s 0).2 g₀ with hf
  set y := evalCircuit c x with hy
  set S := adversaryKeys (Garble c x) with hS
  set T := adversaryKeys (Simulate c y) with hT
  -- the input labels record `x`, and `f` records every gate's output value
  have hlv0 : LabelValues f (makeLabels s 0).1 x := by
    refine labelValues_congr s 0 x g₀ f ?_ (labelValues_inputValues s 0 x _)
    intro m _ hb
    exact (valueMap_lt c x (makeLabels s 0).2 g₀ m hb).symm
  have hag : AgreesOn f c x (makeLabels s 0).2 := agreesOn_valueMap c x _ g₀
  have hsc0 : SwapCompatibleB (makeLabels s 0).1 := makeLabels_swapCompatible s 0
  have hinvS : LabelValueIn (keySubterms (Garble c x)) S (makeLabels s 0).1 x :=
    labelValueIn_of _ _ _ x (input_sel_mem c x) (input_unsel_notMem c x)
  have hinvT : LabelZeroIn (keySubterms (Simulate c y)) T (makeLabels s 0).1 :=
    labelZeroIn_of _ _ _ (input_sel_mem_sim c y) (input_unsel_notMem_sim c y)
  obtain ⟨heq, hout⟩ := theorem5_core c x f c (makeLabels s 0).1 (makeLabels s 0).2 x
    (GbStage.refl c (makeLabels s 0).1 (makeLabels s 0).2) hlv0 hsc0 hinvS hinvT hag
  -- the encoded input and the output masks
  have hgenc := view_gEnc_eq S T f (makeLabels s 0).1 x hlv0 hsc0
  have hmask := view_mask_eq S T f (gb c (makeLabels s 0).1 (makeLabels s 0).2).2.1 y hout
  show normalizeExpr (applyVarRenaming (makeVarRenaming f) (hideEncrypted S
      (Expression.Pair (gb c (makeLabels s 0).1 (makeLabels s 0).2).1
        (Expression.Pair (encodedLabelToExpr (gEnc (makeLabels s 0).1 x))
          (maskedLabelToExpr (gMask (gb c (makeLabels s 0).1 (makeLabels s 0).2).2.1))))))
    = normalizeExpr (hideEncrypted T
      (Expression.Pair (sim c (makeLabels s 0).1 (makeLabels s 0).2).1
        (Expression.Pair (encodedLabelToExpr (sEnc (makeLabels s 0).1))
          (maskedLabelToExpr (sMask (sim c (makeLabels s 0).1 (makeLabels s 0).2).2.1 y)))))
  rw [sim_snd_fst]
  simp only [hideEncrypted, applyVarRenaming, applyBitRenaming, applyKeyRenamingP,
    normalizeExpr]
  simp only [applyVarRenaming] at heq hgenc hmask
  rw [heq, hgenc, hmask]

end PRG
