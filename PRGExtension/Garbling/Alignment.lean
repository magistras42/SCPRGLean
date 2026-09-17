import PRGExtension.Garbling.ValueInvariant
import PRGExtension.Expression.Renamings

/-!
# Aligning the garbled and simulated views

Theorem 5's renaming is `makeVarRenaming f`, where `f i` is the value carried by the wire
whose label has bit index `i`.  It has to do two things at once: send each label's *active*
key (the one the garbling reveals) to the label's key `0` (the one the simulation reveals),
and flip the corresponding permutation bit so the decryptable row moves to position `(0,0)`.

This file supplies what the main induction needs.

* `gbCtr` — the key counter, as a function of the circuit alone, with `gb_ctr_eq`.
* `SwapCompatible` — every label's keys are `G^w(K_{2b})` and `G^w(K_{2b+1})` for the same
  `w` and `b = l.bit`.  Rather than name `w`, we record the consequence: `makeKeySwap f`
  exchanges a label's two keys exactly when `f` flips the label's own bit index.  Preserved
  by `gb` and satisfied by `makeLabels`.
* `LabelValues`, `AgreesOn`, `valueMap` — `AgreesOn f c v ctr` is a *structural* statement
  that `f` records the right value at each `NAnd` gate of `c`, so `Compose` splits it along
  the circuit and the main induction needs no freshness reasoning.  Freshness enters exactly
  once, in `agreesOn_valueMap`.
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

end PRG
