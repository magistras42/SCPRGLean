import PRGExtension.Expression.ComputationalSemantics.Soundness
import PRGExtension.Expression.Lemmas.ReplacePRG
import PRGExtension.Expression.Renamings

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

What is **not** proved is the converse direction — that every `𝖦`-preserving extension is
reachable from the two generators.  It is stated as `Mic09Lemma2General`; see the discussion
there.  Nothing in the development depends on it: the soundness proof only ever *builds*
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

/-!
  ## What remains of [Mic09, Lemma 2]

  Proved above: a `𝖦`-preserving map is the unique extension of its restriction to the roots
  (`gPreserving_eq_substKeys`, `gPreserving_ext`), the roots of a chain-closed key set are its
  atomic members (`rootsOf_keySubterms`), and each of `PrgRenameRel`'s two generators is an
  instance of such an extension (`prgRenameRel_substKeys_atomic`,
  `prgRenameRel_substKeys_growOne`).

  Not proved: that *every* such extension is reachable from the two generators.  The
  conjectured statement is below.  The intended argument iterates `growOne`, each step
  shortening `∑ n, keySize (ρ n)` over the finitely many indices occurring in `e`; the
  measure is routine, the freshness bookkeeping — choosing each index pair `(i, j)` so that
  every `idealize` side condition holds at every intermediate stage — is not.

  The hypothesis below is this formalisation's reading of [Mic09]'s "`α_K` is the unique
  extension of a bijection between `Roots(S)` and `Roots(α_K S)`": distinct occurring keys
  must receive images with distinct atomic bases.  It permits an arbitrary bijection of the
  roots (all bases distinct) and permits growth onto fresh variables, which is what the two
  generators do.  It has *not* been checked to be exactly the right condition, and may need
  adjusting when the proof is attempted — the same thing happened twice to the statements of
  LM18 Lemmas 7 and 8.
-/
def Mic09Lemma2General : Prop :=
  ∀ {s : Shape} (e : Expression s) (ρ : ℕ → Expression Shape.KeyS),
    (∀ m n, Expression.VarK m ∈ keySubterms e → Expression.VarK n ∈ keySubterms e →
      m ≠ n → baseVar (ρ m) ≠ baseVar (ρ n)) →
    PrgRenameRel e (substKeys ρ e)

end PRG
