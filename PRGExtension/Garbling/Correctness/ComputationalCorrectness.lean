import PRGExtension.Garbling.Correctness.Correctness
import PRGExtension.Expression.ComputationalSemantics.Def
import PRGExtension.Expression.ComputationalSemantics.NormalizePreserves

/-!
# Computational correctness of the garbling scheme

`garbleCorrect` (`Garbling/Correctness/Correctness.lean`) is LM18 Theorem 4 *symbolically*: the symbolic
evaluator, which decrypts by pattern-matching `Enc k e ↦ e`, returns `C(x)`.  That says nothing
about real bit strings.  This file supplies the computational statement — the base paper's
correctness definition, `Evaluate(Garble(C,x)) = C(x)` — as `garbleCorrectComp`.

Soundness does **not** give this, and is not meant to.  Its shape is
`symIndistinguishable e₁ e₂ → …`: a relation between two *expressions* mapped to a relation
between two *distributions*.  Correctness says a function applied to *one* distribution yields
a value, which is not an instance of that.  The missing ingredient was
`encryptionFunctions.decrypt_encrypt` (`CHECKPOINT.md` §3.2, F9): without it the symbolic
`decrypt` had no computational counterpart to agree with.

Three replacements turn `gEv` into `gEvComp`:

* `extractPair` ↦ `vecTake`/`vecDrop`;
* `extractPerm` ↦ selection by the encoded bit.  This is point-and-permute: `Perm` stores
  `c_B` first and the encoded bit is `B xor x`, so the row for the true input bit sits at
  index `β`.  `perm_select` is that fact; `xorVarB_eq_xor_val` is why the symbolic
  name-and-parity comparison agrees with XOR of the actual values, which is what lets the
  evaluator choose a row without knowing the environment;
* `decrypt` ↦ `enc.decrypt`, justified by `evalExpr_decrypt`.

`gEvComp_sim` is the simulation lemma, by induction on the circuit, mirroring `gEvCorrect`
case for case.  `garbleCorrectComp` assembles it with `decodeComp_correct`.

Note that `gEvComp` is *total* where `gEv` returns `Option`: the symbolic partiality comes
only from pattern-match failure on expressions that cannot arise.  One source of that
partiality is `decrypt`'s hole arm, and it is the one place where the two evaluators disagree
rather than merely differ in totality — `evalExpr_hidden_decrypt` says a hole's bits decrypt to
`ones`, a wrong wire label rather than a failure.  `garble_holeFree` (`Garbling/HoleFree.lean`)
is why that is unreachable: no garbled circuit contains a hole.  `gEvComp_sim`'s
`gEv c g i = some ov` hypothesis still carries the rest of the structural invariant, so it
stays.
-/
namespace PRG

/-- One garbled-table entry's shape. -/
abbrev nandOne : Shape := Shape.EncS (Shape.EncS (Shape.PairS Shape.BitS Shape.KeyS))

/-- The computational reading of an encoded bundle: a real bit and a real key per wire. -/
abbrev encodedValType (κ : ℕ) : WireBundle → Type := bundleType (Bool × BitVector κ)
/-- Likewise for masks. -/
abbrev maskValType : WireBundle → Type := bundleType Bool

/-- The value a symbolic encoded label takes.  Total: `Expression (PairS 𝔹 𝕂)` can only be a
`Pair`, and its first component can only be a `BitE`. -/
def encLabelVal {κ : ℕ} (prg : prgFunctions κ) (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool) :
    Expression (Shape.PairS Shape.BitS Shape.KeyS) → Bool × BitVector κ
  | Expression.Pair (Expression.BitE b) k => (evalBitExpr bVars b, keyVal prg kVars k)

def encodedLabelVal {κ : ℕ} (prg : prgFunctions κ) (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool) :
    {b : WireBundle} → encodedLabelType b → encodedValType κ b
  | WireBundle.SimpleB, e => encLabelVal prg kVars bVars e
  | WireBundle.PairB _ _, (l1, l2) =>
      (encodedLabelVal prg kVars bVars l1, encodedLabelVal prg kVars bVars l2)

def maskedLabelVal (bVars : ℕ → Bool) :
    {b : WireBundle} → maskedLabelType b → maskValType b
  | WireBundle.SimpleB, Expression.BitE m => evalBitExpr bVars m
  | WireBundle.PairB _ _, (m1, m2) =>
      (maskedLabelVal bVars m1, maskedLabelVal bVars m2)

end PRG

namespace PRG

/-- **The computational garbled-circuit evaluator**, mirroring `gEv` (`GarblingDef.lean`) on
real values.  Three replacements: `extractPair` becomes `vecTake`/`vecDrop`, `extractPerm`
becomes selection by the encoded bit (point-and-permute — the row for the true input bit sits
at index `β`, because `Perm` puts `c_{B}` first and the encoded bit is `B xor x`), and
`decrypt` becomes `enc.decrypt`.  Unlike `gEv` it is total: the partiality of the symbolic
version comes only from pattern-match failure. -/
def gEvCompOn {κ : ℕ} (encLen : ℕ → ℕ)
    (dec : {n : ℕ} → BitVector κ → BitVector (encLen n) → BitVector n)
    (prg : prgFunctions κ) :
    {inp out : WireBundle} → (c : Circuit inp out) →
    BitVector (shapeLengthOn κ encLen (garbledShape c)) →
    encodedValType κ inp → encodedValType κ out
  | _, _, Circuit.SwapC _ _, _, (i1, i2) => (i2, i1)
  | _, _, Circuit.AssocC _ _ _, _, (w1, (w2, w3)) => ((w1, w2), w3)
  | _, _, Circuit.UnAssocC _ _ _, _, ((w1, w2), w3) => (w1, (w2, w3))
  | _, _, Circuit.DupC, _, (b, k) => ((b, prg.prg0 k), (b, prg.prg1 k))
  | _, _, Circuit.FirstC c _, gv, (i1, i2) => (gEvCompOn encLen dec prg c gv i1, i2)
  | _, _, Circuit.ComposeC c1 c2, gv, i =>
      gEvCompOn encLen dec prg c2 (vecDrop gv) (gEvCompOn encLen dec prg c1 (vecTake gv) i)
  | _, _, Circuit.NandC, gv, ((b0, k0), (b1, k1)) =>
      let row2 : BitVector (shapeLengthOn κ encLen (Shape.PairS nandOne nandOne)) :=
        if b0 then vecDrop gv else vecTake gv
      let row1 : BitVector (shapeLengthOn κ encLen nandOne) :=
        if b1 then vecDrop row2 else vecTake row2
      let c3 := dec (n := encLen (1 + κ)) k0 row1
      let c4 := dec (n := 1 + κ) k1 c3
      ((vecTake (n := 1) (m := κ) c4).get 0, vecDrop (n := 1) (m := κ) c4)

/-- The evaluator at a specification scheme.  *Delta*-equal to `gEvCompOn` at that scheme's
`encryptLength` and `decrypt`, which is what lets an executable implementation reuse this
file's theorems verbatim. -/
def gEvComp {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) :
    {inp out : WireBundle} → (c : Circuit inp out) →
    BitVector (shapeLength κ enc (garbledShape c)) →
    encodedValType κ inp → encodedValType κ out :=
  gEvCompOn enc.encryptLength enc.decrypt prg

end PRG

namespace PRG
variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}
  {kVars : ℕ → BitVector κ} {bVars : ℕ → Bool}

lemma mem_support_pair_iff {s₁ s₂ : Shape} (e₁ : Expression s₁) (e₂ : Expression s₂) (v) :
    v ∈ (evalExpr enc prg kVars bVars (Expression.Pair e₁ e₂)).support ↔
      ∃ v₁ ∈ (evalExpr enc prg kVars bVars e₁).support,
      ∃ v₂ ∈ (evalExpr enc prg kVars bVars e₂).support, v = List.Vector.append v₁ v₂ := by
  rw [evalExpr]
  simp only [Bind.bind, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Pure.pure]

/-- **Point-and-permute, computationally.**  `Perm` stores `c_B` first, so selecting index `β`
lands in the branch indexed by `B xor β`. -/
lemma perm_select {s : Shape} (b : BitExpr) (e₁ e₂ : Expression s) (β : Bool) (gv)
    (hgv : gv ∈ (evalExpr enc prg kVars bVars
        (Expression.Perm (Expression.BitE b) e₁ e₂)).support) :
    (if β then vecDrop gv else vecTake gv) ∈
      (evalExpr enc prg kVars bVars
        (if xor (evalBitExpr bVars b) β then e₂ else e₁)).support := by
  rw [evalExpr] at hgv
  simp only [Bind.bind, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Pure.pure] at hgv
  obtain ⟨v₁, h₁, v₂, h₂, hv⟩ := hgv
  cases hb : evalBitExpr bVars b <;> cases hbeta : β <;>
      rw [hb] at hv <;>
      simp only [Bool.false_eq_true, if_false, if_true, PMF.mem_support_pure_iff] at hv <;>
      subst hv
  · simpa [hb, hbeta] using h₁
  · simpa [hb, hbeta] using h₂
  · simpa [hb, hbeta] using h₂
  · simpa [hb, hbeta] using h₁

end PRG

namespace PRG
variable {bVars : ℕ → Bool}

/-- The value of a `𝔹`-shaped expression. -/
def bitExprVal (bVars : ℕ → Bool) : Expression Shape.BitS → Bool
  | Expression.BitE b => evalBitExpr bVars b

/-- A bit expression's value, read off the `VarOrNegVar` its normal form reduces to. -/
lemma exprToVarOrNegVar2_val (b : BitExpr) (v : VarOrNegVar)
    (h : exprToVarOrNegVar2 b = some v) :
    evalBitExpr bVars b =
      (if castVarOrNegVar2Bool v then bVars (castVarOrNegVar v)
       else !(bVars (castVarOrNegVar v))) := by
  rw [normalizeEvalBitExpr bVars b]
  unfold exprToVarOrNegVar2 at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    simp_all [castVarOrNegVar, castVarOrNegVar2Bool, evalBitExpr]
  · simp only [Option.some.injEq] at h; subst h
    simp_all [castVarOrNegVar, castVarOrNegVar2Bool, evalBitExpr]
  · simp at h

/-- **`xorVarB` computes the XOR of the two bits' actual values.**  Symbolically it compares
variable *names* and negation parity; that is the same thing as XORing the values, which is
what lets the computational evaluator select a row without knowing the environment. -/
lemma xorVarB_eq_xor_val (v₁ v₂ : Expression Shape.BitS) (r : Bool)
    (h : xorVarB v₁ v₂ = some r) :
    r = xor (bitExprVal bVars v₁) (bitExprVal bVars v₂) := by
  cases v₁ with | BitE b₁ =>
  cases v₂ with | BitE b₂ =>
  simp only [xorVarB, exprToVarOrNegVar, Option.bind] at h
  rcases h₁ : exprToVarOrNegVar2 b₁ with _ | u₁ <;> rw [h₁] at h <;> simp at h
  rcases h₂ : exprToVarOrNegVar2 b₂ with _ | u₂ <;> rw [h₂] at h <;> simp at h
  obtain ⟨hcast, hr⟩ := h
  rw [bitExprVal, bitExprVal, exprToVarOrNegVar2_val b₁ u₁ h₁,
      exprToVarOrNegVar2_val b₂ u₂ h₂, hcast, ← hr]
  cases u₁ <;> cases u₂ <;>
    simp [castVarOrNegVar2Bool, castVarOrNegVar] at hcast ⊢

end PRG

namespace PRG
variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}
  {kVars : ℕ → BitVector κ} {bVars : ℕ → Bool}

/-- A `(bit, key)` payload is deterministic, so its semantics is a point mass. -/
lemma evalExpr_pairBitKey (b : BitExpr) (k : Expression Shape.KeyS) :
    evalExpr enc prg kVars bVars (Expression.Pair (Expression.BitE b) k)
      = PMF.pure (List.Vector.append
          (List.Vector.cons (evalBitExpr bVars b) List.Vector.nil) (keyVal prg kVars k)) := by
  rw [evalExpr, evalExpr, evalExpr_key enc prg kVars bVars k]
  simp [Bind.bind, Pure.pure]

/-- Reading a `(bit, key)` payload back out of its value. -/
lemma encLabelVal_of_support (b : BitExpr) (k : Expression Shape.KeyS) (v)
    (hv : v ∈ (evalExpr enc prg kVars bVars
        (Expression.Pair (Expression.BitE b) k)).support) :
    ((vecTake (n := 1) (m := κ) v).get 0, vecDrop (n := 1) (m := κ) v)
      = encLabelVal prg kVars bVars (Expression.Pair (Expression.BitE b) k) := by
  rw [evalExpr_pairBitKey] at hv
  simp only [PMF.mem_support_pure_iff] at hv
  subst hv
  simp [encLabelVal, vecTake_append, vecDrop_append, List.Vector.get]

end PRG

namespace PRG
variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}
  {kVars : ℕ → BitVector κ} {bVars : ℕ → Bool}

/-- `extractPair` succeeds only on a `Pair`.  Stated with explicit match arms: `cases` on an
`Expression (PairS s₁ s₂)` cannot eliminate the `Perm` constructor, which would need
`s₁ = s₂`. -/
lemma extractPair_eq {s₁ s₂ : Shape} : ∀ (e : Expression (Shape.PairS s₁ s₂)) (g1 g2),
    extractPair e = some (Prod.mk g1 g2) → e = Expression.Pair g1 g2
  | Expression.Pair _ _, _, _, h => by
      simp only [extractPair, Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1, h.2]
  | Expression.Perm _ _ _, _, _, h => by simp [extractPair] at h

/-- `decrypt` succeeds only on an `Enc` under the matching key. -/
lemma decrypt_eq {s : Shape} (key : Expression Shape.KeyS) :
    ∀ (e : Expression (Shape.EncS s)) (r), decrypt key e = some r → e = Expression.Enc key r
  | Expression.Enc k p, r, h => by
      simp only [decrypt] at h
      by_cases hk : k = key
      · subst hk; simp at h; rw [h]
      · simp [hk] at h
  | Expression.Hidden _, _, h => by simp [decrypt] at h

/-- `extractPerm` succeeds only on a `Perm`, and the half it selects is the one indexed by the
XOR of the two bits' *values* — which is what `gEvComp` selects with `vecTake`/`vecDrop`. -/
lemma extractPerm_fst {s : Shape} (var : Expression Shape.BitS) :
    ∀ (e : Expression (Shape.PairS s s)) (r1 r2), extractPerm var e = some (Prod.mk r1 r2) →
    ∃ bb e1 e2, e = Expression.Perm (Expression.BitE bb) e1 e2 ∧
      r1 = (if xor (evalBitExpr bVars bb) (bitExprVal bVars var) then e2 else e1)
  | Expression.Pair _ _, _, _, h => by simp [extractPerm] at h
  | Expression.Perm (Expression.BitE bb) e1 e2, r1, r2, h => by
      cases var with | BitE vb =>
      refine ⟨bb, e1, e2, rfl, ?_⟩
      simp only [extractPerm] at h
      rcases hs : xorVarB (Expression.BitE bb) (Expression.BitE vb) with _ | sw <;>
        rw [hs] at h <;> simp at h
      have hval := xorVarB_eq_xor_val (bVars := bVars) _ _ _ hs
      simp only [bitExprVal] at hval ⊢
      subst hval
      simp only [condSwap] at h
      by_cases hc : (evalBitExpr bVars bb ^^ evalBitExpr bVars vb) = true
      · rw [if_pos hc]; rw [if_pos hc] at h; exact (congrArg Prod.fst h).symm
      · rw [if_neg hc]; rw [if_neg hc] at h; exact (congrArg Prod.fst h).symm

theorem gEvComp_sim : ∀ {inp out : WireBundle} (c : Circuit inp out)
    (g : Expression (garbledShape c)) (i : encodedLabelType inp) (ov : encodedLabelType out),
    gEv c g i = some ov →
    ∀ gv ∈ (evalExpr enc prg kVars bVars g).support,
      gEvComp enc prg c gv (encodedLabelVal prg kVars bVars i)
        = encodedLabelVal prg kVars bVars ov := by
  intro inp out c
  induction c with
  | SwapC x y =>
      intro g i ov h gv _
      cases g; obtain ⟨i1, i2⟩ := i
      simp [gEv] at h; subst h
      rfl
  | AssocC x y z =>
      intro g i ov h gv _
      cases g; obtain ⟨i1, i2, i3⟩ := i
      simp [gEv] at h; subst h
      rfl
  | UnAssocC x y z =>
      intro g i ov h gv _
      cases g; obtain ⟨⟨i1, i2⟩, i3⟩ := i
      simp [gEv] at h; subst h
      rfl
  | DupC =>
      intro g i ov h gv _
      cases g
      cases i with | Pair b k =>
      cases b with | BitE b' =>
      simp [gEv] at h; subst h
      simp [gEvComp, gEvCompOn, encodedLabelVal, encLabelVal, keyVal]
  | FirstC c u ih =>
      intro g i ov h gv hgv
      obtain ⟨i1, i2⟩ := i
      simp only [gEv] at h
      rcases hx : gEv c g i1 with _ | ov1 <;> rw [hx] at h <;> simp at h
      subst h
      have ihx := ih g i1 ov1 hx gv hgv
      simp only [gEvComp] at ihx
      simp only [gEvComp, gEvCompOn, encodedLabelVal, ihx]
  | ComposeC c1 c2 ih1 ih2 =>
      intro g i ov h gv hgv
      simp only [gEv] at h
      rcases hp : extractPair g with _ | ⟨g1, g2⟩ <;> rw [hp] at h <;> simp at h
      obtain rfl := extractPair_eq g g1 g2 hp
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := (mem_support_pair_iff g1 g2 gv).mp hgv
      rcases hx : gEv c1 g1 i with _ | m <;> rw [hx] at h <;> simp at h
      have ihx1 := ih1 g1 i m hx v1 hv1
      have ihx2 := ih2 g2 m ov h v2 hv2
      simp only [gEvComp] at ihx1 ihx2
      simp only [gEvComp, gEvCompOn, vecTake_append, vecDrop_append, ihx1, ihx2]
  | NandC =>
      intro g i ov h gv hgv
      obtain ⟨i0, i1⟩ := i
      cases i0 with | Pair bb0 k0 => cases bb0 with | BitE b0 =>
      cases i1 with | Pair bb1 k1 => cases bb1 with | BitE b1 =>
      simp only [gEv] at h
      rcases hp0 : extractPerm (Expression.BitE b0) g with _ | ⟨c1, d1⟩ <;>
        rw [hp0] at h <;> simp at h
      rcases hp1 : extractPerm (Expression.BitE b1) c1 with _ | ⟨c2, d2⟩ <;>
        rw [hp1] at h <;> simp at h
      rcases hd0 : decrypt k0 c2 with _ | c3 <;> rw [hd0] at h <;> simp at h
      rcases hd1 : decrypt k1 c3 with _ | c4 <;> rw [hd1] at h <;> simp at h
      subst h
      -- unfold the two permutation layers
      obtain ⟨bA, A1, A2, rfl, hc1⟩ := extractPerm_fst (bVars := bVars) _ g c1 d1 hp0
      obtain ⟨bB, B1, B2, hcc, hc2⟩ := extractPerm_fst (bVars := bVars) _ c1 c2 d2 hp1
      simp only [bitExprVal] at hc1 hc2
      -- the computational row selection lands in the same branch
      have hrow2 := perm_select (enc := enc) (prg := prg) (kVars := kVars) (bVars := bVars)
        bA A1 A2 (evalBitExpr bVars b0) gv hgv
      rw [← hc1] at hrow2
      rw [hcc] at hrow2
      have hrow1 := perm_select (enc := enc) (prg := prg) (kVars := kVars) (bVars := bVars)
        bB B1 B2 (evalBitExpr bVars b1) _ hrow2
      rw [← hc2] at hrow1
      -- decrypt twice
      obtain rfl := decrypt_eq k0 c2 c3 hd0
      obtain rfl := decrypt_eq k1 c3 c4 hd1
      cases c4 with | Pair cb ck => cases cb with | BitE cb' =>
      have h3 := evalExpr_decrypt enc prg kVars bVars k0 _ _ hrow1
      have h4 := evalExpr_decrypt enc prg kVars bVars k1 _ _ h3
      simp only [gEvComp, gEvCompOn, encodedLabelVal, encLabelVal]
      exact encLabelVal_of_support cb' ck _ h4

end PRG

namespace PRG
variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}
  {kVars : ℕ → BitVector κ} {bVars : ℕ → Bool}

/-- Computational `decode`: XOR each wire's bit against its mask. -/
def decodeComp : {b : WireBundle} → encodedValType κ b → maskValType b → bundleBool b
  | WireBundle.SimpleB, l, m => xor l.1 m
  | WireBundle.PairB _ _, l, m => (decodeComp l.1 m.1, decodeComp l.2 m.2)

lemma decodeComp_correct : ∀ (b : WireBundle) (lbl : labelType b) (outv : bundleBool b),
    decodeComp (κ := κ) (encodedLabelVal prg kVars bVars (gEnc lbl outv))
      (maskedLabelVal bVars (gMask lbl)) = outv
  | WireBundle.SimpleB, lbl, outv => by
      cases outv <;>
        simp [gEnc, gMask, decodeComp, encodedLabelVal, encLabelVal, maskedLabelVal,
          WireLabel.bitE, evalBitExpr]
  | WireBundle.PairB u w, lbl, outv => by
      obtain ⟨l1, l2⟩ := lbl; obtain ⟨o1, o2⟩ := outv
      simp only [gEnc, gMask, decodeComp, encodedLabelVal, maskedLabelVal]
      rw [decodeComp_correct u l1 o1, decodeComp_correct w l2 o2]

/-- Parse an encoded bundle out of its bit vector. -/
def parseEncodedValOn (encLen : ℕ → ℕ) :
    (b : WireBundle) → BitVector (shapeLengthOn κ encLen (encodedShape b)) → encodedValType κ b
  | WireBundle.SimpleB, v => ((vecTake (n := 1) (m := κ) v).get 0, vecDrop (n := 1) (m := κ) v)
  | WireBundle.PairB u w, v =>
      (parseEncodedValOn encLen u (vecTake v), parseEncodedValOn encLen w (vecDrop v))

def parseEncodedVal (enc : encryptionFunctions κ) :
    (b : WireBundle) → BitVector (shapeLength κ enc (encodedShape b)) → encodedValType κ b :=
  parseEncodedValOn enc.encryptLength

lemma parseEncodedVal_of_support : ∀ (b : WireBundle) (i : encodedLabelType b) (v),
    v ∈ (evalExpr enc prg kVars bVars (encodedLabelToExpr i)).support →
    parseEncodedVal enc b v = encodedLabelVal prg kVars bVars i
  | WireBundle.SimpleB, i, v, hv => by
      cases i with | Pair bb k => cases bb with | BitE b' =>
      exact encLabelVal_of_support b' k v hv
  | WireBundle.PairB u w, i, v, hv => by
      obtain ⟨i1, i2⟩ := i
      simp only [encodedLabelToExpr] at hv
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := (mem_support_pair_iff _ _ v).mp hv
      have h1 := parseEncodedVal_of_support u i1 v1 hv1
      have h2 := parseEncodedVal_of_support w i2 v2 hv2
      simp only [parseEncodedVal] at h1 h2
      simp only [parseEncodedVal, parseEncodedValOn, encodedLabelVal, vecTake_append,
        vecDrop_append, h1, h2]

end PRG

namespace PRG
variable {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}
  {kVars : ℕ → BitVector κ} {bVars : ℕ → Bool}

def parseMaskValOn (encLen : ℕ → ℕ) :
    (b : WireBundle) → BitVector (shapeLengthOn κ encLen (maskShape b)) → maskValType b
  | WireBundle.SimpleB, v => (show BitVector 1 from v).get 0
  | WireBundle.PairB u w, v =>
      (parseMaskValOn encLen u (vecTake v), parseMaskValOn encLen w (vecDrop v))

def parseMaskVal (enc : encryptionFunctions κ) :
    (b : WireBundle) → BitVector (shapeLength κ enc (maskShape b)) → maskValType b :=
  parseMaskValOn enc.encryptLength

lemma parseMaskVal_of_support : ∀ (b : WireBundle) (m : maskedLabelType b) (v),
    v ∈ (evalExpr enc prg kVars bVars (maskedLabelToExpr m)).support →
    parseMaskVal enc b v = maskedLabelVal bVars m
  | WireBundle.SimpleB, m, v, hv => by
      cases m with | BitE mb =>
      simp only [maskedLabelToExpr, evalExpr, PMF.mem_support_pure_iff, Pure.pure] at hv
      subst hv
      simp [parseMaskVal, parseMaskValOn, maskedLabelVal, List.Vector.get]
  | WireBundle.PairB u w, m, v, hv => by
      obtain ⟨m1, m2⟩ := m
      simp only [maskedLabelToExpr] at hv
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := (mem_support_pair_iff _ _ v).mp hv
      have h1 := parseMaskVal_of_support u m1 v1 hv1
      have h2 := parseMaskVal_of_support w m2 v2 hv2
      simp only [parseMaskVal] at h1 h2
      simp only [parseMaskVal, parseMaskValOn, maskedLabelVal, vecTake_append,
        vecDrop_append, h1, h2]

/-- **`Evaluate`** (LM18/the base paper's correctness definition): parse the garbled output,
run the computational evaluator, decode. -/
def EvaluateCompOn (encLen : ℕ → ℕ)
    (dec : {n : ℕ} → BitVector κ → BitVector (encLen n) → BitVector n)
    (prg : prgFunctions κ) {s t : WireBundle}
    (c : Circuit s t) (v : BitVector (shapeLengthOn κ encLen (garbleShapeFull c))) : bundleBool t :=
  decodeComp (gEvCompOn encLen dec prg c (vecTake v)
      (parseEncodedValOn encLen s (vecTake (vecDrop v))))
    (parseMaskValOn encLen t (vecDrop (vecDrop v)))

/-- **`Evaluate`** at a specification scheme; *delta*-equal to `EvaluateCompOn`. -/
def EvaluateComp (enc : encryptionFunctions κ) (prg : prgFunctions κ) {s t : WireBundle}
    (c : Circuit s t) (v : BitVector (shapeLength κ enc (garbleShapeFull c))) : bundleBool t :=
  EvaluateCompOn enc.encryptLength enc.decrypt prg c v

/-- **Computational correctness of the garbling scheme.**  The computational counterpart of
`garbleCorrect`: every bit vector the garbled circuit can actually take evaluates to `C(x)`. -/
theorem garbleCorrectComp {s t : WireBundle} (c : Circuit s t) (x : bundleBool s) :
    ∀ v ∈ (evalExpr enc prg kVars bVars (Garble c x)).support,
      EvaluateComp enc prg c v = evalCircuit c x := by
  intro v hv
  simp only [Garble] at hv
  obtain ⟨gv, hgv, rest, hrest, rfl⟩ := (mem_support_pair_iff _ _ v).mp hv
  obtain ⟨iv, hiv, mv, hmv, rfl⟩ := (mem_support_pair_iff _ _ rest).mp hrest
  have hi := parseEncodedVal_of_support _ _ iv hiv
  have hm := parseMaskVal_of_support _ _ mv hmv
  have hg := gEvComp_sim c _ _ _ (gEvCorrect c (makeLabels s 0).1 (makeLabels s 0).2 x) gv hgv
  simp only [parseEncodedVal] at hi
  simp only [parseMaskVal] at hm
  simp only [gEvComp] at hg
  simp only [EvaluateComp, EvaluateCompOn, vecTake_append, vecDrop_append, hi, hm, hg]
  exact decodeComp_correct _ _ _

end PRG
