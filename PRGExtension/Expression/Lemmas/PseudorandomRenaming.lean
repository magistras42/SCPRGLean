import PRGExtension.Expression.ComputationalSemantics.Soundness
import PRGExtension.Expression.Lemmas.ReplacePRG
import PRGExtension.Expression.Renamings
import Mathlib.Data.Finset.Image

/-!
# [Mic09, Lemma 2]: the structure of a pseudorandom key renaming

`PrgRenameRel` *defines* a pseudorandom key renaming by LM18's two generators — a bijection
of the atomic keys, and re-rooting one PRG node — because that is what the soundness proof
consumes.  [Mic09, Lemma 2] is the symbolic result behind that definition: every
`𝖦`-preserving map `α_K : S → 𝐊*` is the unique extension of a bijection between `Roots(S)`
and `Roots(α_K S)`, so the two generators are exhaustive.

This file formalises the factorisation and the correspondence with the generators:

* `gPreserving_eq_substKeys` / `gPreserving_ext` — a `𝖦`-preserving map is the unique
  extension of its restriction to the atomic keys, that extension being `substKeys`;
* `rootsOf_keySubterms` — the roots of a chain-closed key set are exactly its atomic
  members, which is what makes "determined on `Roots`" the same as "determined on the
  atomic keys";
* `prgRenameRel_substKeys_atomic` and `prgRenameRel_substKeys_growOne` — each generator is
  such an extension, the second via `growOne`, the leaf substitution that is the inverse of
  one `idealize` hop (`rp_substKeys_growOne` proves the round trip);
* `substKeys_atomic_compInd`, `substKeys_growOne_compInd` — the computational consequences,
  through `prgRename`.

The converse direction — that a `𝖦`-preserving extension is reachable from the two
generators — is proved for every renaming that moves the occurring keys onto **fresh**
variables (`prgRenameRel_of_freshRenaming`), and hence, composing with an arbitrary
bijection of the roots, for the rename-then-grow form LM18 uses
(`prgRenameRel_rename_then_grow`).  Its base case needed `exists_perm_extending`: extending
a finite injection to a permutation of `ℕ`, which Mathlib's `Equiv.extendSubtype` does not
give because it assumes a `Fintype`.  A renaming that *mixes* permutation and growth over
keys that stay put is still not covered; see the note at the end of the file.

Nothing in the development depends on the converse: the soundness proof only ever *builds*
renamings from the generators, never analyses an arbitrary one.
-/

namespace PRG

/-- Substituting a key expression for every atomic key variable. -/
def substKeys (ρ : ℕ → Expression Shape.KeyS) : {s : Shape} → Expression s → Expression s
  | _, Expression.VarK n => ρ n
  | _, Expression.G0 k => Expression.G0 (substKeys ρ k)
  | _, Expression.G1 k => Expression.G1 (substKeys ρ k)
  | _, Expression.Pair a b => Expression.Pair (substKeys ρ a) (substKeys ρ b)
  | _, Expression.Perm b a c => Expression.Perm b (substKeys ρ a) (substKeys ρ c)
  | _, Expression.Enc k m => Expression.Enc (substKeys ρ k) (substKeys ρ m)
  | _, Expression.Hidden k => Expression.Hidden (substKeys ρ k)
  | _, Expression.BitE b => Expression.BitE b
  | _, Expression.Eps => Expression.Eps

/-- `𝖦`-preservation: `α ∘ G_b = G_b ∘ α`.  LM18/[Mic09] require exactly this of a
    pseudorandom key renaming. -/
def GPreserving (α : Expression Shape.KeyS → Expression Shape.KeyS) : Prop :=
  (∀ k, α (Expression.G0 k) = Expression.G0 (α k))
  ∧ (∀ k, α (Expression.G1 k) = Expression.G1 (α k))

/--
  **[Mic09, Lemma 2], first half: a `𝖦`-preserving map is the unique extension of its
  restriction to the roots.**

  For the key algebra the roots are the atomic variables (`rootsOf_keySubterms` below), so
  "determined on `Roots`" means "determined by `fun n ↦ α (K n)`", and the extension is
  `substKeys`.
-/
theorem gPreserving_eq_substKeys {α : Expression Shape.KeyS → Expression Shape.KeyS}
    (h : GPreserving α) :
    ∀ k : Expression Shape.KeyS, α k = substKeys (fun n => α (Expression.VarK n)) k
  | Expression.VarK n => by simp [substKeys]
  | Expression.G0 k => by
      rw [h.1 k, substKeys, gPreserving_eq_substKeys h k]
  | Expression.G1 k => by
      rw [h.2 k, substKeys, gPreserving_eq_substKeys h k]

/-- Uniqueness, stated directly: two `𝖦`-preserving maps agreeing on the atomic keys agree. -/
theorem gPreserving_ext {α β : Expression Shape.KeyS → Expression Shape.KeyS}
    (hα : GPreserving α) (hβ : GPreserving β)
    (h : ∀ n, α (Expression.VarK n) = β (Expression.VarK n)) : ∀ k, α k = β k := by
  intro k
  rw [gPreserving_eq_substKeys hα k, gPreserving_eq_substKeys hβ k]
  congr 1
  funext n; exact h n

/-- `substKeys` is itself `𝖦`-preserving, so the extension exists as well as being unique. -/
theorem gPreserving_substKeys (ρ : ℕ → Expression Shape.KeyS) :
    GPreserving (fun k => substKeys ρ k) := ⟨fun _ => rfl, fun _ => rfl⟩

/--
  **The roots of a chain-closed key set are its atomic members.**

  `keySubterms e` is chain-closed (it contains every suffix of every chain it contains), so
  this identifies LM18's `Roots(·)` with the atomic keys — which is what makes the
  factorisation above the same statement as [Mic09, Lemma 2].
-/
theorem rootsOf_keySubterms {s : Shape} (e : Expression s) :
    rootsOf (keySubterms e) = (keySubterms e).filter (fun k => isAtomicKey k = true) := by
  ext k
  simp only [mem_rootsOf, Finset.mem_filter]
  constructor
  · rintro ⟨hk, hroot⟩
    refine ⟨hk, ?_⟩
    cases k with
    | VarK n => rfl
    | G0 c =>
        exfalso
        have := hroot c (keySubterms_of_G0 hk)
        simp [strictYields] at this
    | G1 c =>
        exfalso
        have := hroot c (keySubterms_of_G1 hk)
        simp [strictYields] at this
  · rintro ⟨hk, hat⟩
    refine ⟨hk, fun k' _ => ?_⟩
    cases k with
    | VarK n => simp [strictYields]
    | G0 _ => simp [isAtomicKey] at hat
    | G1 _ => simp [isAtomicKey] at hat

/-! ## Generator 1: a bijection of the atomic keys -/

lemma applyBitRenamingB_id : ∀ b : BitExpr,
    applyBitRenamingB (fun n => VarOrNegVar.Var n) b = b
  | BitExpr.VarB n => rfl
  | BitExpr.Not b => by rw [applyBitRenamingB, applyBitRenamingB_id b]
  | BitExpr.Bit b => rfl

lemma applyBitRenaming_id : ∀ {s : Shape} (e : Expression s),
    applyBitRenaming (fun n => VarOrNegVar.Var n) e = e := by
  intro s e
  induction e with
  | BitE b => rw [applyBitRenaming, applyBitRenamingB_id]
  | Pair a b ih1 ih2 => rw [applyBitRenaming, ih1, ih2]
  | Perm b a c _ ih1 ih2 =>
      cases b with
      | BitE b' => simp only [applyBitRenaming, applyBitRenamingB_id, ih1, ih2]
  | Enc k m _ ihm => rw [applyBitRenaming, ihm]
  | _ => rfl

lemma substKeys_varK (r : KeyRenaming) : ∀ {s : Shape} (e : Expression s),
    substKeys (fun n => Expression.VarK (r n)) e = applyKeyRenamingP r e := by
  intro s e
  induction e with
  | VarK n => rfl
  | G0 k ih => rw [substKeys, applyKeyRenamingP, ih]
  | G1 k ih => rw [substKeys, applyKeyRenamingP, ih]
  | Pair a b ih1 ih2 => rw [substKeys, applyKeyRenamingP, ih1, ih2]
  | Perm b a c _ ih1 ih2 => rw [substKeys, applyKeyRenamingP, ih1, ih2]
  | Enc k m ihk ihm => rw [substKeys, applyKeyRenamingP, ihk, ihm]
  | Hidden k ih => rw [substKeys, applyKeyRenamingP, ih]
  | BitE b => rfl
  | Eps => rfl

/-- A `𝖦`-preserving map whose value on every atomic key is again atomic, and which is a
    bijection there, is the `atomic` generator. -/
theorem prgRenameRel_substKeys_atomic {s : Shape} (e : Expression s)
    (r : KeyRenaming) (hr : validKeyRenaming r) :
    PrgRenameRel e (substKeys (fun n => Expression.VarK (r n)) e) := by
  have hb : validVarRenaming ((fun n => VarOrNegVar.Var n), r) := by
    refine ⟨?_, hr⟩
    show Function.Bijective (castVarOrNegVar ∘ (fun n => VarOrNegVar.Var n))
    have : (castVarOrNegVar ∘ (fun n => VarOrNegVar.Var n)) = id := by
      funext n; simp [castVarOrNegVar]
    rw [this]; exact Function.bijective_id
  have h2 : applyVarRenaming ((fun n => VarOrNegVar.Var n), r) e
      = substKeys (fun n => Expression.VarK (r n)) e := by
    show applyKeyRenamingP r (applyBitRenaming (fun n => VarOrNegVar.Var n) e) = _
    rw [applyBitRenaming_id, substKeys_varK]
  rw [← h2]
  exact PrgRenameRel.atomic ((fun n => VarOrNegVar.Var n), r) hb e

/-! ## Generator 2: growing one PRG node -/

/-- The leaf substitution that grows `K_i` and `K_j` into `G0(K_t)` and `G1(K_t)` — the
    inverse of one `idealize` step, expressed as a map on the roots. -/
def growOne (t i j : ℕ) : ℕ → Expression Shape.KeyS := fun n =>
  if n = i then Expression.G0 (Expression.VarK t)
  else if n = j then Expression.G1 (Expression.VarK t)
  else Expression.VarK n

lemma keySubterms_substKeys_growOne (t i j : ℕ) (hit : i ≠ t) (hjt : j ≠ t) :
    ∀ {s : Shape} (e : Expression s),
      Expression.VarK i ∉ keySubterms (substKeys (growOne t i j) e)
      ∧ Expression.VarK j ∉ keySubterms (substKeys (growOne t i j) e) := by
  intro s e
  induction e with
  | VarK n =>
      simp only [substKeys, growOne]
      split_ifs <;> simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] <;>
        constructor <;> simp_all <;> omega
  | G0 k ih =>
      simp only [substKeys, keySubterms, Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨⟨by simp, ih.1⟩, ⟨by simp, ih.2⟩⟩
  | G1 k ih =>
      simp only [substKeys, keySubterms, Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨⟨by simp, ih.1⟩, ⟨by simp, ih.2⟩⟩
  | Pair a b ih1 ih2 =>
      simp only [substKeys, keySubterms, Finset.mem_union, not_or]
      exact ⟨⟨ih1.1, ih2.1⟩, ⟨ih1.2, ih2.2⟩⟩
  | Perm b a c _ ih1 ih2 =>
      simp only [substKeys, keySubterms, Finset.mem_union, not_or]
      exact ⟨⟨ih1.1, ih2.1⟩, ⟨ih1.2, ih2.2⟩⟩
  | Enc k m ihk ihm =>
      simp only [substKeys, keySubterms, Finset.mem_union, not_or]
      exact ⟨⟨ihk.1, ihm.1⟩, ⟨ihk.2, ihm.2⟩⟩
  | Hidden k ih => simp only [substKeys, keySubterms]; exact ih
  | BitE b => simp [substKeys, keySubterms]
  | Eps => simp [substKeys, keySubterms]

lemma exprKeys_substKeys_growOne_no_t (t i j : ℕ) (hit : i ≠ t) (hjt : j ≠ t) :
    ∀ {s : Shape} (e : Expression s), Expression.VarK t ∉ keySubterms e →
      Expression.VarK t ∉ exprKeys (substKeys (growOne t i j) e) := by
  intro s e
  induction e with
  | VarK n =>
      intro hn
      simp only [keySubterms, Finset.mem_singleton] at hn
      simp only [substKeys, growOne]
      split_ifs with h1 h2
      · simp [exprKeys]
      · simp [exprKeys]
      · simp only [exprKeys, Finset.mem_singleton]
        intro hc; exact hn (by rw [← hc])
  | G0 k _ => intro _; simp [substKeys, exprKeys]
  | G1 k _ => intro _; simp [substKeys, exprKeys]
  | Pair a b ih1 ih2 =>
      intro h
      simp only [keySubterms, Finset.mem_union, not_or] at h
      simp only [substKeys, exprKeys, Finset.mem_union, not_or]
      exact ⟨ih1 h.1, ih2 h.2⟩
  | Perm b a c _ ih1 ih2 =>
      intro h
      simp only [keySubterms, Finset.mem_union, not_or] at h
      simp only [substKeys, exprKeys, Finset.mem_union, not_or]
      exact ⟨ih1 h.1, ih2 h.2⟩
  | Enc k m ihk ihm =>
      intro h
      simp only [keySubterms, Finset.mem_union, not_or] at h
      simp only [substKeys, exprKeys, Finset.mem_union, not_or]
      exact ⟨ihk h.1, ihm h.2⟩
  | Hidden k ih =>
      intro h; simp only [keySubterms] at h; simp only [substKeys, exprKeys]; exact ih h
  | BitE b => intro _; simp [substKeys, exprKeys]
  | Eps => intro _; simp [substKeys, exprKeys]

/-- Growing and then idealising is the identity: `growOne` really is the inverse of one hop. -/
lemma rp_substKeys_growOne (t i j : ℕ) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t) :
    ∀ {s : Shape} (e : Expression s), Expression.VarK t ∉ keySubterms e →
      rp t i j (substKeys (growOne t i j) e) = e := by
  intro s e
  induction e with
  | VarK n =>
      intro hn
      simp only [keySubterms, Finset.mem_singleton] at hn
      have hnt : n ≠ t := fun h => hn (by rw [h])
      simp only [substKeys, growOne]
      split_ifs with h1 h2
      · rw [h1, rp_G0]; simp
      · rw [h2, rp_G1]; simp
      · rfl
  | G0 k ih =>
      intro h
      simp only [keySubterms, Finset.mem_union, not_or] at h
      simp only [substKeys]
      rw [rp_G0, if_neg ?_, ih h.2]
      intro hc
      rw [hc] at ih
      have := exprKeys_substKeys_growOne_no_t t i j hit hjt k h.2
      rw [hc] at this
      simp [exprKeys] at this
  | G1 k ih =>
      intro h
      simp only [keySubterms, Finset.mem_union, not_or] at h
      simp only [substKeys]
      rw [rp_G1, if_neg ?_, ih h.2]
      intro hc
      have := exprKeys_substKeys_growOne_no_t t i j hit hjt k h.2
      rw [hc] at this
      simp [exprKeys] at this
  | Pair a b ih1 ih2 =>
      intro h
      simp only [keySubterms, Finset.mem_union, not_or] at h
      simp only [substKeys]; rw [rp_pair, ih1 h.1, ih2 h.2]
  | Perm b a c _ ih1 ih2 =>
      intro h
      simp only [keySubterms, Finset.mem_union, not_or] at h
      simp only [substKeys]; rw [rp_perm, ih1 h.1, ih2 h.2]
  | Enc k m ihk ihm =>
      intro h
      simp only [keySubterms, Finset.mem_union, not_or] at h
      simp only [substKeys]; rw [rp_enc, ihk h.1, ihm h.2]
  | Hidden k ih =>
      intro h; simp only [keySubterms] at h
      simp only [substKeys]; rw [rp_hidden, ih h]
  | BitE b => intro _; rfl
  | Eps => intro _; rfl

/-- **Generator 2 is an instance of `substKeys`.** -/
theorem prgRenameRel_substKeys_growOne {s : Shape} (e : Expression s) (t i j : ℕ)
    (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t) (ht : Expression.VarK t ∉ keySubterms e) :
    PrgRenameRel e (substKeys (growOne t i j) e) := by
  refine PrgRenameRel.symm (?_ : PrgRenameRel (substKeys (growOne t i j) e) e)
  have hgrow := rp_substKeys_growOne t i j hij hit hjt e ht
  have hkey := keySubterms_substKeys_growOne t i j hit hjt e
  have := PrgRenameRel.idealize (substKeys (growOne t i j) e) t i j
    (exprKeys_substKeys_growOne_no_t t i j hit hjt e ht) hij hkey.1 hkey.2
  rwa [show replacePRG (Expression.VarK t) i j (substKeys (growOne t i j) e) = e from hgrow]
    at this

/-! ## Computational consequences -/

/--
  **[Mic09, Lemma 2] composed with LM18 Lemma 2**, for the atomic generator: renaming the
  roots by a bijection is computationally invisible.
-/
theorem substKeys_atomic_compInd
    (IsPolyTime : PolyFamOracleCompPred)
    (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
    (enc : encryptionScheme) (prg : prgScheme)
    (HreductionPrg : PrgReductionPolyTime IsPolyTime enc prg)
    (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
    {s : Shape} (e : Expression s) (r : KeyRenaming) (hr : validKeyRenaming r) :
    CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (exprToFamDistr enc prg e))
      (famDistrLift (exprToFamDistr enc prg (substKeys (fun n => Expression.VarK (r n)) e))) :=
  prgRename IsPolyTime HPolyTime enc prg HreductionPrg HPrgSecure
    (prgRenameRel_substKeys_atomic e r hr)

/-- The same for the growth generator: replacing `K_i, K_j` by `G0(K_t), G1(K_t)` for a fresh
    `K_t` is computationally invisible.  This is the direction LM18 needs — it turns two
    independent atomic keys into a PRG-derived pair. -/
theorem substKeys_growOne_compInd
    (IsPolyTime : PolyFamOracleCompPred)
    (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
    (enc : encryptionScheme) (prg : prgScheme)
    (HreductionPrg : PrgReductionPolyTime IsPolyTime enc prg)
    (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg)
    {s : Shape} (e : Expression s) (t i j : ℕ)
    (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (ht : Expression.VarK t ∉ keySubterms e) :
    CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (exprToFamDistr enc prg e))
      (famDistrLift (exprToFamDistr enc prg (substKeys (growOne t i j) e))) :=
  prgRename IsPolyTime HPolyTime enc prg HreductionPrg HPrgSecure
    (prgRenameRel_substKeys_growOne e t i j hij hit hjt ht)

/-! ## [Mic09, Lemma 2], the generation direction -/

/--
  **Extending a finite injection to a permutation of `ℕ`.**

  `Equiv.extendSubtype` needs a `Fintype`, so it does not apply to `ℕ`.  When the injection
  moves its domain entirely off itself — which is the situation in the base case of
  [Mic09, Lemma 2], where every image is a *fresh* variable — the extension is a product of
  transpositions with pairwise disjoint supports, built here by induction on the domain.

  The `outside` clause is the invariant that makes the induction go through: each stage fixes
  everything it has not been told to move.
-/
theorem exists_perm_extending (f : ℕ → ℕ) :
    ∀ (F : Finset ℕ),
      (∀ m ∈ F, ∀ n ∈ F, f m = f n → m = n) →
      (∀ n ∈ F, f n ∉ F) →
      ∃ r : Equiv.Perm ℕ, (∀ n ∈ F, r n = f n)
        ∧ (∀ x, x ∉ F → x ∉ F.image f → r x = x) := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty => intro _ _; exact ⟨Equiv.refl ℕ, by simp, by simp⟩
  | @insert a F' ha ih =>
      intro hinj hout
      have hinj' : ∀ m ∈ F', ∀ n ∈ F', f m = f n → m = n := fun m hm n hn =>
        hinj m (Finset.mem_insert_of_mem hm) n (Finset.mem_insert_of_mem hn)
      have hout' : ∀ n ∈ F', f n ∉ F' :=
        fun n hn hc => hout n (Finset.mem_insert_of_mem hn) (Finset.mem_insert_of_mem hc)
      obtain ⟨r', hr'F, hr'out⟩ := ih hinj' hout'
      -- `f a` is outside `F'` and outside `f '' F'`, so `r'` fixes it
      have hfa_notF' : f a ∉ F' := fun hc =>
        hout a (Finset.mem_insert_self a F') (Finset.mem_insert_of_mem hc)
      have hfa_notim : f a ∉ F'.image f := by
        intro hc
        obtain ⟨n, hn, hfn⟩ := Finset.mem_image.mp hc
        have hna : n = a :=
          hinj n (Finset.mem_insert_of_mem hn) a (Finset.mem_insert_self a F') hfn
        exact ha (hna ▸ hn)
      have hr'fa : r' (f a) = f a := hr'out _ hfa_notF' hfa_notim
      refine ⟨(Equiv.swap a (f a)).trans r', ?_, ?_⟩
      · intro n hn
        rcases Finset.mem_insert.mp hn with rfl | hn'
        · simp only [Equiv.trans_apply, Equiv.swap_apply_left]; exact hr'fa
        · have h1 : n ≠ a := fun h => ha (h ▸ hn')
          have h2 : n ≠ f a := fun h => hfa_notF' (h ▸ hn')
          simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
          exact hr'F n hn'
      · intro x hx hxim
        have h1 : x ≠ a := fun h => hx (h ▸ Finset.mem_insert_self a F')
        have h2 : x ≠ f a := fun h =>
          hxim (h ▸ Finset.mem_image.mpr ⟨a, Finset.mem_insert_self a F', rfl⟩)
        simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
        refine hr'out x (fun hc => hx (Finset.mem_insert_of_mem hc)) (fun hc => hxim ?_)
        obtain ⟨n, hn, hfn⟩ := Finset.mem_image.mp hc
        exact Finset.mem_image.mpr ⟨n, Finset.mem_insert_of_mem hn, hfn⟩

lemma atomic_eq_varK : ∀ {k : Expression Shape.KeyS}, isAtomicKey k = true → k = Expression.VarK (baseVar k)
  | Expression.VarK n, _ => by simp
  | Expression.G0 _, h => by simp [isAtomicKey] at h
  | Expression.G1 _, h => by simp [isAtomicKey] at h

lemma keySubterms_baseVar : ∀ k : Expression Shape.KeyS,
    Expression.VarK (baseVar k) ∈ keySubterms k
  | Expression.VarK n => by simp [keySubterms]
  | Expression.G0 c => by
      simp only [baseVar_G0, keySubterms, Finset.mem_union]
      exact Or.inr (keySubterms_baseVar c)
  | Expression.G1 c => by
      simp only [baseVar_G1, keySubterms, Finset.mem_union]
      exact Or.inr (keySubterms_baseVar c)

/-- The atomic key indices occurring in an expression. -/
def occIdx {s : Shape} (e : Expression s) : Finset ℕ :=
  ((keySubterms e).filter (fun k => isAtomicKey k = true)).image baseVar

lemma mem_occIdx {s : Shape} {e : Expression s} {n : ℕ} :
    n ∈ occIdx e ↔ Expression.VarK n ∈ keySubterms e := by
  simp only [occIdx, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨k, ⟨hk, hat⟩, hb⟩
    rw [atomic_eq_varK hat, hb] at hk; exact hk
  · intro h; exact ⟨Expression.VarK n, ⟨h, rfl⟩, by simp⟩

lemma substKeys_congr {ρ σ : ℕ → Expression Shape.KeyS} :
    ∀ {s : Shape} (e : Expression s), (∀ n ∈ occIdx e, ρ n = σ n) →
      substKeys ρ e = substKeys σ e := by
  intro s e
  induction e with
  | VarK n => intro h; exact h n (mem_occIdx.mpr (by simp [keySubterms]))
  | G0 k ih => intro h; rw [substKeys, substKeys, ih (fun n hn => h n (by
      rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn]))]
  | G1 k ih => intro h; rw [substKeys, substKeys, ih (fun n hn => h n (by
      rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn]))]
  | Pair a b ih1 ih2 =>
      intro h
      rw [substKeys, substKeys,
        ih1 (fun n hn => h n (by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn])),
        ih2 (fun n hn => h n (by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn]))]
  | Perm b a c _ ih1 ih2 =>
      intro h
      rw [substKeys, substKeys,
        ih1 (fun n hn => h n (by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn])),
        ih2 (fun n hn => h n (by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn]))]
  | Enc k m ihk ihm =>
      intro h
      rw [substKeys, substKeys,
        ihk (fun n hn => h n (by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn])),
        ihm (fun n hn => h n (by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn]))]
  | Hidden k ih => intro h; rw [substKeys, substKeys, ih (fun n hn => h n (by
      rw [mem_occIdx] at hn ⊢; simpa [keySubterms] using hn))]
  | BitE b => intro _; rfl
  | Eps => intro _; rfl

lemma substKeys_id : ∀ {s : Shape} (e : Expression s),
    substKeys (fun n => Expression.VarK n) e = e := by
  intro s e
  induction e with
  | VarK n => rfl
  | G0 k ih => rw [substKeys, ih]
  | G1 k ih => rw [substKeys, ih]
  | Pair a b ih1 ih2 => rw [substKeys, ih1, ih2]
  | Perm b a c _ ih1 ih2 => rw [substKeys, ih1, ih2]
  | Enc k m ihk ihm => rw [substKeys, ihk, ihm]
  | Hidden k ih => rw [substKeys, ih]
  | BitE b => rfl
  | Eps => rfl

/-- `Keys` of a substituted expression is the image of `Keys`. -/
lemma exprKeys_substKeys (ρ : ℕ → Expression Shape.KeyS) :
    ∀ {s : Shape} (e : Expression s),
      exprKeys (substKeys ρ e) = (exprKeys e).image (fun k => substKeys ρ k) := by
  intro s e
  induction e with
  | VarK n => simp [substKeys, exprKeys, exprKeys_key]
  | G0 k _ => simp [substKeys, exprKeys]
  | G1 k _ => simp [substKeys, exprKeys]
  | Pair a b ih1 ih2 => simp [substKeys, exprKeys, ih1, ih2, Finset.image_union]
  | Perm b a c _ ih1 ih2 => simp [substKeys, exprKeys, ih1, ih2, Finset.image_union]
  | Enc k m ihk ihm => simp [substKeys, exprKeys, ihk, ihm, Finset.image_union]
  | Hidden k ih => simp [substKeys, exprKeys, ih]
  | BitE b => simp [substKeys, exprKeys]
  | Eps => simp [substKeys, exprKeys]

/-- Substitution does not invent key subterms beyond those of the images. -/
lemma keySubterms_substKeys (ρ : ℕ → Expression Shape.KeyS) :
    ∀ {s : Shape} (e : Expression s), ∀ k ∈ keySubterms (substKeys ρ e),
      (∃ n ∈ occIdx e, k ∈ keySubterms (ρ n)) ∨ isAtomicKey k = false := by
  intro s e
  induction e with
  | VarK n =>
      intro k hk
      exact Or.inl ⟨n, mem_occIdx.mpr (by simp [keySubterms]), hk⟩
  | G0 c ih =>
      intro k hk
      simp only [substKeys, keySubterms, Finset.mem_union, Finset.mem_singleton] at hk
      rcases hk with rfl | hk
      · exact Or.inr rfl
      · rcases ih k hk with ⟨n, hn, h⟩ | h
        · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn], h⟩
        · exact Or.inr h
  | G1 c ih =>
      intro k hk
      simp only [substKeys, keySubterms, Finset.mem_union, Finset.mem_singleton] at hk
      rcases hk with rfl | hk
      · exact Or.inr rfl
      · rcases ih k hk with ⟨n, hn, h⟩ | h
        · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn], h⟩
        · exact Or.inr h
  | Pair a b ih1 ih2 =>
      intro k hk
      simp only [substKeys, keySubterms, Finset.mem_union] at hk
      rcases hk with hk | hk
      · rcases ih1 k hk with ⟨n, hn, h⟩ | h
        · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn], h⟩
        · exact Or.inr h
      · rcases ih2 k hk with ⟨n, hn, h⟩ | h
        · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn], h⟩
        · exact Or.inr h
  | Perm b a c _ ih1 ih2 =>
      intro k hk
      simp only [substKeys, keySubterms, Finset.mem_union] at hk
      rcases hk with hk | hk
      · rcases ih1 k hk with ⟨n, hn, h⟩ | h
        · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn], h⟩
        · exact Or.inr h
      · rcases ih2 k hk with ⟨n, hn, h⟩ | h
        · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn], h⟩
        · exact Or.inr h
  | Enc kk m ihk ihm =>
      intro k hk
      simp only [substKeys, keySubterms, Finset.mem_union] at hk
      rcases hk with hk | hk
      · rcases ihk k hk with ⟨n, hn, h⟩ | h
        · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn], h⟩
        · exact Or.inr h
      · rcases ihm k hk with ⟨n, hn, h⟩ | h
        · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simp [keySubterms, hn], h⟩
        · exact Or.inr h
  | Hidden kk ih =>
      intro k hk
      simp only [substKeys, keySubterms] at hk
      rcases ih k hk with ⟨n, hn, h⟩ | h
      · exact Or.inl ⟨n, by rw [mem_occIdx] at hn ⊢; simpa [keySubterms] using hn, h⟩
      · exact Or.inr h
  | BitE b => intro k hk; simp [substKeys, keySubterms] at hk
  | Eps => intro k hk; simp [substKeys, keySubterms] at hk

lemma keySize_rp_le (t i j : ℕ) : ∀ k : Expression Shape.KeyS,
    keySize (rp t i j k) ≤ keySize k
  | Expression.VarK _ => by simp [rp, replacePRG, keySize]
  | Expression.G0 c => by
      rw [rp_G0]; split_ifs with h
      · simp [keySize]
      · simp only [keySize]; have := keySize_rp_le t i j c; omega
  | Expression.G1 c => by
      rw [rp_G1]; split_ifs with h
      · simp [keySize]
      · simp only [keySize]; have := keySize_rp_le t i j c; omega

end PRG

namespace PRG

lemma substKeys_key_ne_varK {ρ : ℕ → Expression Shape.KeyS} {t : ℕ}
    (h : ∀ n, ρ n ≠ Expression.VarK t) :
    ∀ c : Expression Shape.KeyS, substKeys ρ c ≠ Expression.VarK t
  | Expression.VarK n => h n
  | Expression.G0 _ => by simp [substKeys]
  | Expression.G1 _ => by simp [substKeys]

lemma substKeys_rp_comm (t i j : ℕ) (ρ : ℕ → Expression Shape.KeyS)
    (h : ∀ n, ρ n ≠ Expression.VarK t) :
    ∀ {s : Shape} (e : Expression s),
      rp t i j (substKeys ρ e) = substKeys (fun n => rp t i j (ρ n)) e := by
  intro s e
  induction e with
  | VarK n => rfl
  | G0 c ih =>
      simp only [substKeys]
      rw [rp_G0, if_neg (substKeys_key_ne_varK h c), ih]
  | G1 c ih =>
      simp only [substKeys]
      rw [rp_G1, if_neg (substKeys_key_ne_varK h c), ih]
  | Pair a b ih1 ih2 => simp only [substKeys]; rw [rp_pair, ih1, ih2]
  | Perm b a c _ ih1 ih2 => simp only [substKeys]; rw [rp_perm, ih1, ih2]
  | Enc k m ihk ihm => simp only [substKeys]; rw [rp_enc, ihk, ihm]
  | Hidden k ih => simp only [substKeys]; rw [rp_hidden, ih]
  | BitE b => rfl
  | Eps => rfl

lemma keySubterms_substKeys_sub (ρ : ℕ → Expression Shape.KeyS) :
    ∀ {s : Shape} (e : Expression s), ∀ n ∈ occIdx e,
      keySubterms (ρ n) ⊆ keySubterms (substKeys ρ e) := by
  intro s e
  induction e with
  | VarK m =>
      intro n hn
      rw [mem_occIdx] at hn
      simp only [keySubterms, Finset.mem_singleton] at hn
      injection hn with hn; subst hn
      exact Finset.Subset.refl _
  | G0 c ih =>
      intro n hn
      rw [mem_occIdx] at hn
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hn
      rcases hn with hn | hn
      · exact absurd hn (by simp)
      · refine Finset.Subset.trans (ih n (mem_occIdx.mpr hn)) ?_
        intro x hx; simp only [substKeys, keySubterms, Finset.mem_union]; exact Or.inr hx
  | G1 c ih =>
      intro n hn
      rw [mem_occIdx] at hn
      simp only [keySubterms, Finset.mem_union, Finset.mem_singleton] at hn
      rcases hn with hn | hn
      · exact absurd hn (by simp)
      · refine Finset.Subset.trans (ih n (mem_occIdx.mpr hn)) ?_
        intro x hx; simp only [substKeys, keySubterms, Finset.mem_union]; exact Or.inr hx
  | Pair a b ih1 ih2 =>
      intro n hn
      rw [mem_occIdx] at hn
      simp only [keySubterms, Finset.mem_union] at hn
      simp only [substKeys, keySubterms]
      rcases hn with hn | hn
      · exact Finset.Subset.trans (ih1 n (mem_occIdx.mpr hn)) Finset.subset_union_left
      · exact Finset.Subset.trans (ih2 n (mem_occIdx.mpr hn)) Finset.subset_union_right
  | Perm b a c _ ih1 ih2 =>
      intro n hn
      rw [mem_occIdx] at hn
      simp only [keySubterms, Finset.mem_union] at hn
      simp only [substKeys, keySubterms]
      rcases hn with hn | hn
      · exact Finset.Subset.trans (ih1 n (mem_occIdx.mpr hn)) Finset.subset_union_left
      · exact Finset.Subset.trans (ih2 n (mem_occIdx.mpr hn)) Finset.subset_union_right
  | Enc k m ihk ihm =>
      intro n hn
      rw [mem_occIdx] at hn
      simp only [keySubterms, Finset.mem_union] at hn
      simp only [substKeys, keySubterms]
      rcases hn with hn | hn
      · exact Finset.Subset.trans (ihk n (mem_occIdx.mpr hn)) Finset.subset_union_left
      · exact Finset.Subset.trans (ihm n (mem_occIdx.mpr hn)) Finset.subset_union_right
  | Hidden k ih =>
      intro n hn
      rw [mem_occIdx] at hn
      simp only [keySubterms] at hn
      simp only [substKeys, keySubterms]
      exact ih n (mem_occIdx.mpr hn)
  | BitE b => intro n hn; rw [mem_occIdx] at hn; simp [keySubterms] at hn
  | Eps => intro n hn; rw [mem_occIdx] at hn; simp [keySubterms] at hn

lemma rp_eq_varK (t i j : ℕ) : ∀ {y : Expression Shape.KeyS} {k : ℕ},
    rp t i j y = Expression.VarK k → y = Expression.VarK k ∨ k = i ∨ k = j
  | Expression.VarK m, k, h => Or.inl h
  | Expression.G0 c, k, h => by
      rw [rp_G0] at h
      by_cases hc : c = Expression.VarK t
      · rw [if_pos hc] at h; injection h with h; exact Or.inr (Or.inl h.symm)
      · rw [if_neg hc] at h; exact absurd h (by simp)
  | Expression.G1 c, k, h => by
      rw [rp_G1] at h
      by_cases hc : c = Expression.VarK t
      · rw [if_pos hc] at h; injection h with h; exact Or.inr (Or.inr h.symm)
      · rw [if_neg hc] at h; exact absurd h (by simp)

end PRG

namespace PRG

/--
  **A fresh independent renaming.**  `ρ` moves each atomic key occurring in `e` to a key
  expression built entirely over *new* variables (`fresh`), injectively (`inj`), and the
  images are pairwise independent — none yields another (`indep`).

  This is the reading of [Mic09, Lemma 2]'s "`α_K` restricts to a bijection between
  `Roots(S)` and `Roots(α_K S)`" that the hop side conditions actually need.  `fresh` is
  what makes each `idealize` seed absent from the expression, and `indep` is what stops a
  seed from being revealed alongside a key derived from it.
-/
structure FreshRenaming {s : Shape} (e : Expression s) (ρ : ℕ → Expression Shape.KeyS) : Prop where
  fresh : ∀ n ∈ occIdx e, ∀ k : ℕ, Expression.VarK k ∈ keySubterms (ρ n) → k ∉ occIdx e
  inj   : ∀ m ∈ occIdx e, ∀ n ∈ occIdx e, ρ m = ρ n → m = n
  indep : ∀ m ∈ occIdx e, ∀ n ∈ occIdx e, strictYields (ρ m) (ρ n) = false

/--
  **[Mic09, Lemma 2], the generation direction.**

  Every fresh independent renaming is a pseudorandom key renaming — i.e. is reachable from
  LM18's two generators.  By induction on `∑ keySize (ρ n)`: if every image is atomic the
  renaming *is* the atomic generator (extended to a permutation of `ℕ` by
  `exists_perm_extending`); otherwise idealising at the bottom of one image's chain shortens
  that image by exactly one and preserves the three conditions, so one `symm idealize` hop
  plus the induction hypothesis finishes it.
-/
theorem prgRenameRel_of_freshRenaming :
    ∀ (M : ℕ) {s : Shape} (e : Expression s) (ρ : ℕ → Expression Shape.KeyS),
      (∑ n ∈ occIdx e, keySize (ρ n)) ≤ M → FreshRenaming e ρ →
      PrgRenameRel e (substKeys ρ e) := by
  intro M
  induction M with
  | zero =>
      intro s e ρ hM _
      have hempty : occIdx e = ∅ := by
        by_contra hc
        obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hc
        have h1 : keySize (ρ n) ≤ ∑ m ∈ occIdx e, keySize (ρ m) :=
          Finset.single_le_sum (f := fun m => keySize (ρ m)) (fun _ _ => Nat.zero_le _) hn
        have := keySize_pos (ρ n)
        omega
      have hid : substKeys ρ e = e := by
        rw [substKeys_congr e (fun n hn => absurd hn (by rw [hempty]; simp)), substKeys_id]
      rw [hid]
      have h2 := prgRenameRel_substKeys_atomic e (fun n => n) Function.bijective_id
      simpa [substKeys_id] using h2
  | succ M ih =>
      intro s e ρ hM hρ
      -- normalise `ρ` outside `occIdx e`: harmless, and it makes the seed genuinely absent
      classical
      by_cases hall : ∀ n ∈ occIdx e, isAtomicKey (ρ n) = true
      · have hinj : ∀ m ∈ occIdx e, ∀ n ∈ occIdx e,
            baseVar (ρ m) = baseVar (ρ n) → m = n := by
          intro m hm n hn hb
          refine hρ.inj m hm n hn ?_
          rw [atomic_eq_varK (hall m hm), atomic_eq_varK (hall n hn), hb]
        have hout : ∀ n ∈ occIdx e, baseVar (ρ n) ∉ occIdx e := fun n hn =>
          hρ.fresh n hn _ (keySubterms_baseVar (ρ n))
        obtain ⟨r, hr, _⟩ := exists_perm_extending (fun n => baseVar (ρ n)) (occIdx e) hinj hout
        rw [substKeys_congr e (σ := fun n => Expression.VarK (r n))
          (fun n hn => (atomic_eq_varK (hall n hn)).trans
            (congrArg Expression.VarK (hr n hn).symm))]
        exact prgRenameRel_substKeys_atomic e (r : ℕ → ℕ) r.bijective
      · push_neg at hall
        obtain ⟨n₀, hn₀, hna'⟩ := hall
        have hna : isAtomicKey (ρ n₀) = false := by
          cases h : isAtomicKey (ρ n₀); · rfl
          · exact absurd h hna'
        set t := baseVar (ρ n₀) with ht
        have ht_occ : t ∉ occIdx e := hρ.fresh n₀ hn₀ t (keySubterms_baseVar (ρ n₀))
        -- replace `ρ` by a copy that maps the non-occurring indices above `t`
        set σ : ℕ → Expression Shape.KeyS :=
          fun n => if n ∈ occIdx e then ρ n else Expression.VarK (t + 1 + n) with hσ
        have hσocc : ∀ n ∈ occIdx e, σ n = ρ n := fun n hn => by simp only [hσ, if_pos hn]
        have hsum : (∑ n ∈ occIdx e, keySize (σ n)) = ∑ n ∈ occIdx e, keySize (ρ n) :=
          Finset.sum_congr rfl (fun n hn => by rw [hσocc n hn])
        have hsub : substKeys σ e = substKeys ρ e := substKeys_congr e hσocc
        have hFσ : FreshRenaming e σ := by
          refine ⟨?_, ?_, ?_⟩
          · intro n hn k hk; rw [hσocc n hn] at hk; exact hρ.fresh n hn k hk
          · intro m hm n hn h; rw [hσocc m hm, hσocc n hn] at h; exact hρ.inj m hm n hn h
          · intro m hm n hn; rw [hσocc m hm, hσocc n hn]; exact hρ.indep m hm n hn
        rw [← hsub]
        -- the seed is not the image of anything
        have hnoT : ∀ n, σ n ≠ Expression.VarK t := by
          intro n hc
          by_cases hn : n ∈ occIdx e
          · rw [hσocc n hn] at hc
            have h1 := hρ.indep n hn n₀ hn₀
            rw [hc, ht] at h1
            rw [strictYields_baseVar (ρ n₀) hna] at h1
            exact Bool.noConfusion h1
          · rw [hσ] at hc; simp only [if_neg hn] at hc
            injection hc with hc; omega
        -- fresh target indices, avoiding `e`, the substituted expression, and `t`
        obtain ⟨N, hN⟩ := exists_fresh_index (keySubterms e ∪ keySubterms (substKeys σ e))
        set i := max N (t + 1) with hidef
        set j := i + 1 with hjdef
        have hij : i ≠ j := by omega
        have hit : i ≠ t := by have := le_max_right N (t + 1); omega
        have hjt : j ≠ t := by have := le_max_right N (t + 1); omega
        have hmi := hN i (le_max_left _ _)
        have hmj := hN j (by have := le_max_left N (t + 1); omega)
        rw [Finset.mem_union, not_or] at hmi hmj
        -- the key expressions in play avoid `i` and `j`
        have havoid : ∀ n ∈ occIdx e,
            Expression.VarK i ∉ keySubterms (σ n) ∧ Expression.VarK j ∉ keySubterms (σ n) := by
          intro n hn
          have hs := keySubterms_substKeys_sub σ e n hn
          exact ⟨fun hc => hmi.2 (hs hc), fun hc => hmj.2 (hs hc)⟩
        -- the hop's own side condition
        have hseed : Expression.VarK t ∉ exprKeys (substKeys σ e) := by
          rw [exprKeys_substKeys]
          intro hc
          obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hc
          cases k with
          | VarK m => exact hnoT m (by simpa [substKeys] using hke)
          | G0 c => exact absurd hke (by simp [substKeys])
          | G1 c => exact absurd hke (by simp [substKeys])
        -- one idealisation hop
        have hop := PrgRenameRel.idealize (substKeys σ e) t i j hseed hij hmi.2 hmj.2
        have hcomm : replacePRG (Expression.VarK t) i j (substKeys σ e)
            = substKeys (fun n => rp t i j (σ n)) e := substKeys_rp_comm t i j σ hnoT e
        rw [hcomm] at hop
        -- the shortened renaming still satisfies the three conditions
        have hF' : FreshRenaming e (fun n => rp t i j (σ n)) := by
          refine ⟨?_, ?_, ?_⟩
          · intro n hn k hk
            obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp (keySubterms_rp t i j (σ n) hk)
            rcases rp_eq_varK t i j hyk with h | h | h
            · rw [h] at hy; exact hρ.fresh n hn k (by rw [← hσocc n hn]; exact hy)
            · rw [h]; exact fun hc => hmi.1 (mem_occIdx.mp hc)
            · rw [h]; exact fun hc => hmj.1 (mem_occIdx.mp hc)
          · intro m hm n hn h
            exact hρ.inj m hm n hn (by
              rw [← hσocc m hm, ← hσocc n hn]
              exact rp_inj t i j hij hit hjt (havoid m hm).1 (havoid m hm).2
                (havoid n hn).1 (havoid n hn).2 h)
          · intro m hm n hn
            cases hy : strictYields (rp t i j (σ m)) (rp t i j (σ n))
            · rfl
            · exfalso
              have := strictYields_rp_reflect t i j hij hit hjt (σ m) (havoid m hm).1
                (havoid m hm).2 (σ n) (havoid n hn).1 (havoid n hn).2 hy
              rw [hσocc m hm, hσocc n hn, hρ.indep m hm n hn] at this
              exact Bool.noConfusion this
        -- the measure strictly decreases
        have hlt : (∑ n ∈ occIdx e, keySize (rp t i j (σ n)))
            < ∑ n ∈ occIdx e, keySize (σ n) := by
          refine Finset.sum_lt_sum (fun n _ => keySize_rp_le t i j (σ n)) ⟨n₀, hn₀, ?_⟩
          rw [hσocc n₀ hn₀, ht]
          have := keySize_rp i j (ρ n₀) hna
          omega
        exact PrgRenameRel.trans (ih e _ (by omega) hF') (PrgRenameRel.symm hop)

/-- **Rename the roots, then grow the PRG structure** — the composite form LM18 uses. -/
theorem prgRenameRel_rename_then_grow {s : Shape} (e : Expression s)
    (r : KeyRenaming) (hr : validKeyRenaming r) (ρ : ℕ → Expression Shape.KeyS)
    (hF : FreshRenaming (substKeys (fun n => Expression.VarK (r n)) e) ρ) :
    PrgRenameRel e (substKeys ρ (substKeys (fun n => Expression.VarK (r n)) e)) :=
  PrgRenameRel.trans (prgRenameRel_substKeys_atomic e r hr)
    (prgRenameRel_of_freshRenaming _ _ ρ (le_refl _) hF)

/-!
  ## What [Mic09, Lemma 2] still lacks here

  `prgRenameRel_of_freshRenaming` covers every renaming that moves the occurring keys onto
  *fresh* variables.  Composed with `prgRenameRel_substKeys_atomic` (an arbitrary bijection
  of the roots, needing no freshness) via `PrgRenameRel.trans`, that is how LM18 uses
  Lemma 2: rename the roots, then grow the PRG structure.

  What is not covered is a renaming that mixes the two — one that both permutes occurring
  keys and grows structure over keys that stay put.  Such a `ρ` should factor as
  (bijection) ∘ (fresh growth), but the factorisation is not formalised.

  An earlier version of this file stated a single "general" form with the hypothesis
  "distinct occurring keys receive images with distinct atomic bases".  That hypothesis is
  **wrong**: `growOne t i j` sends `i` and `j` to `G0(K_t)` and `G1(K_t)`, whose bases are
  both `t`, so it excluded the very generator it was meant to subsume.  `FreshRenaming`'s
  `indep` clause — the images are pairwise non-yielding — is the correct reading.
-/

end PRG
