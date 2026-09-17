import PRGExtension.Expression.Lemmas.ReplacePRG
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOneKey
import PRGExtension.Expression.ComputationalSemantics.SoundnessProof.HidingOnePrgSeed

/-!
# Hiding one key, without the atomicity restriction

LM18 Lemma 3's general case.  See `hideOneKeyGen`.
-/

open PRG
namespace PRG

lemma keySize_pos : ∀ k : Expression Shape.KeyS, 1 ≤ keySize k
  | Expression.VarK _ => by simp [keySize]
  | Expression.G0 _ => by simp [keySize]
  | Expression.G1 _ => by simp [keySize]

/--
  **Hiding one key, with no atomicity restriction.**

  `symbolicToSemanticIndistinguishabilityHidingOneKey` can only target a key *variable*:
  the IND-CPA reduction has to identify the oracle's uniform key with it.  LM18's Lemma 3
  removes that restriction by a pseudorandom key renaming, and this is that argument.

  The two hypotheses are LM18's, read off `Keys(expr)`:

  * `Hroot` — nothing occurring in `expr` is a strict *ancestor* of `k`, i.e. `k` is a root
    of `Keys(expr)`.  For a non-atomic `k` this is exactly what licenses the hop: the atomic
    variable `K_t` at the bottom of `k`'s chain does not occur in `expr`, which is
    `PrgRenameRel.idealize`'s side condition.
  * `Hdesc` — nothing occurring in `expr` is a strict *descendant* of `k`.  For atomic `k`
    this is `seedFree`, which the IND-CPA reduction needs (it never learns `k`, so it could
    not compute `prg0 k`).

  The proof is by induction on `keySize k`.  Atomic `k` is the existing IND-CPA step.  For
  non-atomic `k` we idealise at `K_t`, which shortens `k`'s chain by one (`keySize_rp`),
  hide the shorter key by induction, and undo the hop — the middle step lines up because
  idealisation commutes with hiding (`rp_hideSelected`).
-/
theorem hideOneKeyGen
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition (fun {_ _ _} => IsPolyTime))
  (Hreduction : ∀ enc prg shape (expr : Expression shape) key₀,
    IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (HreductionPrg : ∀ (enc_ : encryptionScheme) (prg_ : prgScheme) (s_ : Shape)
    (expr_ : Expression s_) (targetSeed_ : Expression Shape.KeyS) (idx0_ idx1_ : ℕ),
    IsPolyTime (fun κ => reductionToPrgOracle enc_ prg_ expr_ targetSeed_ idx0_ idx1_ κ))
  (enc : encryptionScheme) (prg : prgScheme)
  (HEncIndCpa : encryptionSchemeIndCpa (fun {_ _ _} => IsPolyTime) enc)
  (HPrgSecure : prgSchemeSecure (fun {_ _ _} => IsPolyTime) prg) :
  ∀ (n : ℕ) {shape : Shape} (expr : Expression shape) (k : Expression Shape.KeyS),
    keySize k ≤ n →
    k ∉ extractKeys expr →
    (∀ k' ∈ exprKeys expr, strictYields k' k = false) →
    (∀ k' ∈ exprKeys expr, strictYields k k' = false) →
    CompIndistinguishabilityDistr (fun {_ _ _} => IsPolyTime)
      (famDistrLift (exprToFamDistr enc prg expr))
      (famDistrLift (exprToFamDistr enc prg (removeOneKey k expr))) := by
  intro n
  induction n with
  | zero => intro shape expr k hn _ _ _; exact absurd hn (by have := keySize_pos k; omega)
  | succ n ih =>
      intro shape expr k hn Hk Hroot Hdesc
      cases hat : isAtomicKey k with
      | true =>
          -- atomic: the existing IND-CPA step
          cases k with
          | VarK m =>
              exact symbolicToSemanticIndistinguishabilityHidingOneKey IsPolyTime HPolyTime
                Hreduction enc HEncIndCpa expr m Hk Hdesc
          | G0 _ => simp [isAtomicKey] at hat
          | G1 _ => simp [isAtomicKey] at hat
      | false =>
          -- non-atomic: idealise the bottom of `k`'s chain, hide, undo
          set t := baseVar k with ht
          have hty : strictYields (Expression.VarK t) k = true := strictYields_baseVar k hat
          have Hseed : Expression.VarK t ∉ exprKeys expr := by
            intro hc; rw [Hroot _ hc] at hty; exact Bool.noConfusion hty
          obtain ⟨N, hN⟩ := exists_fresh_index (keySubterms expr ∪ keySubterms k)
          set i := max N (t + 1) with hi_def
          set j := i + 1 with hj_def
          have hij : i ≠ j := by omega
          have hit : i ≠ t := by have := le_max_right N (t+1); omega
          have hjt : j ≠ t := by have := le_max_right N (t+1); omega
          have hmi := hN i (le_max_left _ _)
          have hmj := hN j (by have := le_max_left N (t+1); omega)
          rw [Finset.mem_union, not_or] at hmi hmj
          obtain ⟨hmiE, hmiK⟩ := hmi
          obtain ⟨hmjE, hmjK⟩ := hmj
          -- hop 1
          have hop1 := symbolicToSemanticIndistinguishabilityPrgIdealization IsPolyTime
            HPolyTime HreductionPrg enc prg HPrgSecure expr t i j Hseed hij hmiE hmjE
          -- the shortened key and the idealised expression
          have hsize : keySize (rp t i j k) + 1 = keySize k := keySize_rp i j k hat
          have havoid : ∀ a ∈ exprKeys expr, Expression.VarK i ∉ keySubterms a
              ∧ Expression.VarK j ∉ keySubterms a := by
            intro a ha
            have hsub := keySubterms_subset_of_mem_exprKeys expr a ha
            exact ⟨fun hc => hmiE (hsub hc), fun hc => hmjE (hsub hc)⟩
          have Hk2 : rp t i j k ∉ extractKeys (rp t i j expr) := by
            rw [extractKeys_rp]
            intro hc
            obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hc
            have haE : a ∈ exprKeys expr := by
              rw [exprKeys_eq_extractKeys_union_encKeys]; exact Finset.mem_union_left _ ha
            obtain ⟨hai, haj⟩ := havoid a haE
            exact Hk (by rwa [rp_inj t i j hij hit hjt hai haj hmiK hmjK hae] at ha)
          have Hroot2 : ∀ k' ∈ exprKeys (rp t i j expr),
              strictYields k' (rp t i j k) = false := by
            intro k' hk'
            rw [exprKeys_rp] at hk'
            obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hk'
            obtain ⟨hai, haj⟩ := havoid a ha
            cases hy : strictYields k' (rp t i j k)
            · rfl
            · exfalso
              rw [← hae] at hy
              have hb := strictYields_rp_reflect t i j hij hit hjt a hai haj k hmiK hmjK hy
              rw [Hroot a ha] at hb
              exact Bool.noConfusion hb
          have Hdesc2 : ∀ k' ∈ exprKeys (rp t i j expr),
              strictYields (rp t i j k) k' = false := by
            intro k' hk'
            rw [exprKeys_rp] at hk'
            obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hk'
            obtain ⟨hai, haj⟩ := havoid a ha
            cases hy : strictYields (rp t i j k) k'
            · rfl
            · exfalso
              rw [← hae] at hy
              have hb := strictYields_rp_reflect t i j hij hit hjt k hmiK hmjK a hai haj hy
              rw [Hdesc a ha] at hb
              exact Bool.noConfusion hb
          have hmid := ih (rp t i j expr) (rp t i j k) (by omega) Hk2 Hroot2 Hdesc2
          -- commutation, then hop 2 backwards
          have hcomm : removeOneKey (rp t i j k) (rp t i j expr)
              = rp t i j (removeOneKey k expr) := by
            simp only [removeOneKey]
            exact (rp_hideSelected t i j hij hit hjt k hmiK hmjK expr hmiE hmjE).symm
          have hshrink : keySubterms (removeOneKey k expr) ⊆ keySubterms expr :=
            keySubtermsMonotone _ _ (hideEncryptedSSmallerValue _ _)
          have hop2 := symbolicToSemanticIndistinguishabilityPrgIdealization IsPolyTime
            HPolyTime HreductionPrg enc prg HPrgSecure (removeOneKey k expr) t i j
            (by
              intro hc
              have : Expression.VarK t ∈ exprKeys expr :=
                exprKeysMonotone _ _ (hideEncryptedSSmallerValue _ _) hc
              exact Hseed this)
            hij (fun hc => hmiE (hshrink hc)) (fun hc => hmjE (hshrink hc))
          apply indTrans (fun {I Spec Output} ↦ IsPolyTime) hop1
          rw [hcomm] at hmid
          exact indTrans (fun {I Spec Output} ↦ IsPolyTime) hmid (indSym hop2)

end PRG
