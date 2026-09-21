import PRGExtension.Expression.Defs
import PRGExtension.Expression.SymbolicIndistinguishability
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Vector.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs

import PRGExtension.Core.CardinalityLemmas

/-!
# Computational semantics of expressions

Where the symbolic algebra meets actual bit strings.  An `Expression` is interpreted as a
distribution over bit vectors, given an encryption scheme, a PRG, and an environment
assigning values to the key and bit variables.

* `encryptionFunctions` / `encryptionScheme`, `prgFunctions` / `prgScheme` — the primitives.
  Note that `encryptionFunctions` relates `encrypt` and `decrypt` by **nothing**: there is no
  correctness field, so a scheme whose ciphertext ignores the message is legal.  That is not
  hypothetical — `scratch/DegenerateEnc.lean` uses one to show that IND-CPA alone places no
  constraint on the adversary class.
* `shapeLength` — the length of the bit vector a shape produces.
* `PolyLength`, `LengthPoly`, `shapeLength_poly` — LM18 Definition 1's *length* half.  Without
  `LengthPoly`, `encryptLength n = 2 ^ n` is a legal scheme, the value of a nested `Enc` is
  exponentially long in the expression depth, and every cost argument downstream fails.
* `PolySized` — poly-sized type families, carrying the width as **data** so that a cost model's
  obligations are arithmetic in the widths.  The side condition every clause about moving data
  has to carry.
* `evalExpr` — the semantics itself.  `exprToDistr` / `exprToFamDistr` close it over a
  uniformly sampled environment.
-/

namespace PRG

-- This file defines computational semantics (`exprToFamDistr`), a function that maps an expression (and an encryption scheme) to a distribution over bitstrings.

abbrev BitVector (n: ℕ) := List.Vector Bool n

open Classical
open PMF

-- We consider an encryption scheme
structure encryptionFunctions (κ : ℕ) where
  encryptLength : ℕ -> ℕ
  encrypt : {n : ℕ} -> (key : BitVector κ) -> (msg : BitVector n) -> PMF (BitVector (encryptLength n))
  decrypt : {n : ℕ} -> (key : BitVector κ) -> (msg : BitVector (encryptLength n)) -> BitVector n
  /-- **Decryption inverts encryption** (`CHECKPOINT.md` §3.2, F9).  Without this the two
  fields are unrelated, and then: a scheme whose ciphertext ignores the message is legal (so
  IND-CPA constrains nothing — `scratch/DegenerateEnc.lean`), and no *computational*
  correctness statement is reachable, because the symbolic evaluator's `decrypt` has no
  computational counterpart to agree with. -/
  decrypt_encrypt : ∀ {n : ℕ} (key : BitVector κ) (msg : BitVector n),
    ∀ c ∈ (encrypt key msg).support, decrypt key c = msg

def encryptionScheme : Type := (κ : ℕ) -> encryptionFunctions κ

structure prgFunctions (κ : ℕ) where
  -- A PRG deterministically maps a κ-bit seed to two independent κ-bit pseudo-random strings
  prg0 : BitVector κ → BitVector κ
  prg1 : BitVector κ → BitVector κ

def prgScheme : Type := (κ : ℕ) -> prgFunctions κ

def shapeLength (κ : ℕ) (scheme : encryptionFunctions κ) (s : Shape) : ℕ :=
  match s with
  | Shape.BitS => 1
  | Shape.KeyS => κ
  | Shape.EmptyS => 0
  | Shape.PairS s₁ s₂ => (shapeLength κ scheme s₁) + (shapeLength κ scheme s₂)
  | Shape.EncS s => scheme.encryptLength (shapeLength κ scheme s)

/-!
### Ciphertext growth: the length half of LM18 Definition 1

`encryptionFunctions.encryptLength` above is an arbitrary `ℕ → ℕ`, and nothing in the types
rules out `encryptLength n = 2 ^ n`.  For such a scheme the ciphertext of a nested `Enc` is
*exponential* in the expression depth, so `shapeLength` is not polynomially bounded in `κ`
and no cost analysis of the reductions can succeed — the pen-and-paper argument at the end
of `SoundnessProof/HidingOneKey.lean` silently assumes this away when it says "since
`encrypt (k, n)` runs in time `p (n + κ)`, its output length is also bounded by `p (n + κ)`".

LM18 Definition 1 rules it out implicitly, by demanding polynomial-*time* encryption.
`LengthPoly` states the length consequence explicitly, and `shapeLength_poly` is the form
every later cost argument actually consumes.

`prgFunctions` needs no analogue: `prg0`/`prg1` have type `BitVector κ → BitVector κ`, so
their output lengths are pinned by the type.
-/

/-- A length family that is polynomially bounded in the security parameter.  This is the
side condition every cost clause about bit vectors carries: an operation on bit vectors is
only cheap if the vectors are not themselves huge. -/
def PolyLength (d : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ κ, d κ ≤ p.eval κ

lemma PolyLength.const (n : ℕ) : PolyLength (fun _ => n) :=
  ⟨Polynomial.C n, fun _ => by simp⟩

lemma PolyLength.id : PolyLength (fun κ => κ) := ⟨Polynomial.X, fun _ => by simp⟩

lemma PolyLength.add {d₁ d₂ : ℕ → ℕ} (h₁ : PolyLength d₁) (h₂ : PolyLength d₂) :
    PolyLength (fun κ => d₁ κ + d₂ κ) := by
  obtain ⟨p₁, hp₁⟩ := h₁
  obtain ⟨p₂, hp₂⟩ := h₂
  exact ⟨p₁ + p₂, fun κ => by simpa using Nat.add_le_add (hp₁ κ) (hp₂ κ)⟩

/-!
### Poly-sized type families

A cost model that charges for anything at all has to bound the width of the values it moves
around: a family of poly-size circuits has I/O width bounded by its size, so a type family
whose values need `2 ^ κ` bits to write down cannot be the domain or codomain of one.

`PolySized` records that bound, and records it **as data** — the width itself, not an
existential.  That is deliberate.  Every primitive's cost will be a function of exactly this
width, so when a concrete cost semantics arrives (`CHECKPOINT.md` §3.1) each closure clause's
proof obligation is arithmetic in `width` rather than a re-derivation of the statement.  It
is the `calf`-style "carry the bound" formulation, in the only form statable before `cost`
exists.
-/

/-- Evidence that a type family's values fit in polynomially many bits. -/
structure PolySized (D : ℕ → Type) where
  /-- The number of bits needed to write down a `D κ`. -/
  width : ℕ → ℕ
  widthPoly : PolyLength width
  finite : ∀ κ, Finite (D κ)
  card_le : ∀ κ, Nat.card (D κ) ≤ 2 ^ width κ

namespace PolySized

/-- Bit vectors of polynomially bounded length. -/
def bitVector (d : ℕ → ℕ) (h : PolyLength d) : PolySized (fun κ => BitVector (d κ)) where
  width := d
  widthPoly := h
  finite _ := inferInstance
  card_le κ := by simp [Nat.card_eq_fintype_card, card_vector]

def bool : PolySized (fun _ => Bool) where
  width _ := 1
  widthPoly := PolyLength.const 1
  finite _ := inferInstance
  card_le κ := by simp [Nat.card_eq_fintype_card]

def unit : PolySized (fun _ => Unit) where
  width _ := 0
  widthPoly := PolyLength.const 0
  finite _ := inferInstance
  card_le κ := by simp [Nat.card_eq_fintype_card]

/-- The sampled bit environment: `l` bits. -/
def bitEnv (l : ℕ) : PolySized (fun _ => Fin l → Bool) where
  width _ := l
  widthPoly := PolyLength.const l
  finite _ := inferInstance
  card_le κ := by simp [Nat.card_eq_fintype_card]

/-- The sampled key environment: `l` keys of `κ` bits each. -/
def keyEnv (l : ℕ) : PolySized (fun κ => Fin l → BitVector κ) where
  width κ := l * κ
  widthPoly := by
    obtain ⟨p, hp⟩ := PolyLength.id
    exact ⟨Polynomial.C l * Polynomial.X, fun κ => by simp⟩
  finite _ := inferInstance
  card_le κ := by
    simp [Nat.card_eq_fintype_card, card_vector, ← pow_mul, Nat.mul_comm]

/-- Positions into a poly-length bit vector: `d κ` of them, so `d κ` bits over-counts but
bounds. -/
def fin (d : ℕ → ℕ) (h : PolyLength d) : PolySized (fun κ => Fin (d κ)) where
  width := d
  widthPoly := h
  finite _ := inferInstance
  card_le κ := by
    simpa [Nat.card_eq_fintype_card] using Nat.le_of_lt (Nat.lt_two_pow_self (n := d κ))

/-- Widths add. -/
def prod {D E : ℕ → Type} (hD : PolySized D) (hE : PolySized E) :
    PolySized (fun κ => D κ × E κ) where
  width κ := hD.width κ + hE.width κ
  widthPoly := PolyLength.add hD.widthPoly hE.widthPoly
  finite κ := @Finite.instProd _ _ (hD.finite κ) (hE.finite κ)
  card_le κ := by
    haveI := hD.finite κ
    haveI := hE.finite κ
    rw [Nat.card_prod, pow_add]
    exact Nat.mul_le_mul (hD.card_le κ) (hE.card_le κ)

end PolySized

/-- **LM18 Definition 1, length half**: ciphertexts grow polynomially in the message length
and the security parameter.  Required of any scheme for which the efficiency analysis of the
reductions is meaningful. -/
def LengthPoly (enc : encryptionScheme) : Prop :=
  ∃ p : Polynomial ℕ, ∀ κ n, (enc κ).encryptLength n ≤ p.eval (n + κ)

/-- Evaluation of a polynomial with natural-number coefficients is monotone.  (Mathlib has
this for ordered semirings via `Polynomial.eval` only in specialised forms; the two-line
induction is cheaper than hunting for the right instance.) -/
lemma polyEvalMono {p : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
      simpa [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

/-- **The output-length induction of the prose cost analysis, formalised.**

For a *fixed* shape, the length of the bit vector produced by the computational semantics is
bounded by a polynomial in `κ`.  The `EncS` case is the only one that needs anything: it is
exactly where `LengthPoly` is consumed, and exactly where an unconstrained `encryptLength`
would break the induction. -/
theorem shapeLength_poly (enc : encryptionScheme) (H : LengthPoly enc) (s : Shape) :
    PolyLength (fun κ => shapeLength κ (enc κ) s) := by
  unfold PolyLength
  obtain ⟨p, hp⟩ := H
  induction s with
  | BitS => exact ⟨1, by simp [shapeLength]⟩
  | KeyS => exact ⟨Polynomial.X, by simp [shapeLength]⟩
  | EmptyS => exact ⟨0, by simp [shapeLength]⟩
  | PairS s₁ s₂ ih₁ ih₂ =>
      obtain ⟨q₁, h₁⟩ := ih₁
      obtain ⟨q₂, h₂⟩ := ih₂
      exact ⟨q₁ + q₂, fun κ => by
        simpa [shapeLength] using Nat.add_le_add (h₁ κ) (h₂ κ)⟩
  | EncS s ih =>
      obtain ⟨q, h⟩ := ih
      -- `p (q κ + κ)`: the prose's `p (q (κ) + κ)`.
      refine ⟨p.comp (q + Polynomial.X), fun κ => ?_⟩
      simp only [shapeLength, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
      exact le_trans (hp κ _) (polyEvalMono (Nat.add_le_add_right (h κ) κ))

def allVarsSmallerThanBExpr (e : BitExpr) (n : ℕ ) : Prop :=
  match e with
  | BitExpr.VarB k => k < n
  | BitExpr.Bit _ => true
  | BitExpr.Not e' => allVarsSmallerThanBExpr e' n

def allVarsSmallerThan {s : Shape} (e : Expression s) (n : ℕ) : Prop :=
match e with
| Expression.BitE b => allVarsSmallerThanBExpr b n
| Expression.VarK k => k < n
| Expression.Pair e₁ e₂ => allVarsSmallerThan e₁ n ∧ allVarsSmallerThan e₂ n
| Expression.Enc e₁ e₂ => allVarsSmallerThan e₁ n ∧ allVarsSmallerThan e₂ n
| Expression.Perm e₁ e₂ e₃ => allVarsSmallerThan e₁ n ∧ allVarsSmallerThan e₂ n ∧ allVarsSmallerThan e₃ n
| Expression.Hidden k => allVarsSmallerThan k n
| Expression.Eps => True
| Expression.G0 e => allVarsSmallerThan e n
| Expression.G1 e => allVarsSmallerThan e n

def allVarsSmallerThanBExprMonotone {e : BitExpr} {n₁ : ℕ} {n₂ : ℕ} (h : n₁ ≤ n₂) (h' : allVarsSmallerThanBExpr e n₁) : allVarsSmallerThanBExpr e n₂ := by
  induction e
  case VarB k =>
    simp [allVarsSmallerThanBExpr] at h'
    exact Nat.lt_of_lt_of_le h' h
  case Bit b =>
    simp [allVarsSmallerThanBExpr]
  case Not e ihe =>
    simp [allVarsSmallerThanBExpr] at h'
    apply ihe
    assumption

def allVarsSmallerThanMonotone {s : Shape} (e : Expression s) (n₁ : ℕ ) (n₂ : ℕ) (h₁ : n₁ ≤ n₂) (h₂ : allVarsSmallerThan e n₁) : allVarsSmallerThan e n₂ := by
  induction e
  case BitE b =>
    simp [allVarsSmallerThan] at h₂ ⊢
    apply allVarsSmallerThanBExprMonotone h₁ h₂
  case VarK k =>
    simp [allVarsSmallerThan] at h₂ ⊢
    omega
  case Pair e₁ e₂ ih₁ ih₂ =>
    simp [allVarsSmallerThan] at h₂ ⊢
    exact ⟨ih₁ h₂.1, ih₂ h₂.2⟩
  case Enc e₁ e₂ ih₁ ih₂ =>
    simp [allVarsSmallerThan] at h₂ ⊢
    exact ⟨ih₁ h₂.1, ih₂ h₂.2⟩
  case Perm e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
    simp [allVarsSmallerThan] at h₂ ⊢
    exact ⟨ih₁ h₂.1, ih₂ h₂.2.1, ih₃ h₂.2.2⟩
  case Eps =>
    simp [allVarsSmallerThan]
  -- All wrapper/key cases seamlessly rely on the induction hypothesis!
  case Hidden k ih =>
    simp [allVarsSmallerThan] at h₂ ⊢
    exact ih h₂
  case G0 e ih =>
    simp [allVarsSmallerThan] at h₂ ⊢
    exact ih h₂
  case G1 e ih =>
    simp [allVarsSmallerThan] at h₂ ⊢
    exact ih h₂

def getMaxVarBExpr : BitExpr -> ℕ
  | BitExpr.VarB k => k
  | BitExpr.Bit _ => 0
  | BitExpr.Not e => getMaxVarBExpr e

def getMaxVar {s : Shape} : Expression s -> ℕ
  | Expression.BitE b => getMaxVarBExpr b
  | Expression.VarK k => k
  | Expression.Pair e₁ e₂ => max (getMaxVar e₁) (getMaxVar e₂)
  | Expression.Enc e₁ e₂ => max (getMaxVar e₁) (getMaxVar e₂)
  | Expression.Perm e₁ e₂ e₃ => max (max (getMaxVar e₁) (getMaxVar e₂)) (getMaxVar e₃)
  | Expression.Hidden k => getMaxVar k
  | Expression.Eps => 0
  | Expression.G0 e => getMaxVar e
  | Expression.G1 e => getMaxVar e

lemma allVarsSmallerThanMaxBexpr (e : BitExpr) : allVarsSmallerThanBExpr e (getMaxVarBExpr e + 1) := by
  induction e
  case VarB k =>
    simp [getMaxVarBExpr]
    apply Nat.lt_succ_self
  case Bit b =>
    simp [getMaxVarBExpr, allVarsSmallerThanBExpr]
  case Not e' ih =>
    simp [getMaxVarBExpr, allVarsSmallerThanBExpr]
    assumption

lemma allVarsSmallerThanMax {s : Shape} (e : Expression s) : allVarsSmallerThan e (getMaxVar e + 1) := by
  induction e <;> try simp [getMaxVar, allVarsSmallerThan]
  case BitE b =>
    apply allVarsSmallerThanMaxBexpr
  case Pair e₁ e₂ ih₁ ih₂ =>
    constructor
    · apply allVarsSmallerThanMonotone e₁ (getMaxVar e₁ + 1)
      · omega
      · assumption
    · apply allVarsSmallerThanMonotone e₂ (getMaxVar e₂ + 1)
      · omega
      · assumption
  case Enc e₁ e₂ ih₁ ih₂ =>
    constructor
    · apply allVarsSmallerThanMonotone e₁ (getMaxVar e₁ + 1)
      · omega
      · assumption
    · apply allVarsSmallerThanMonotone e₂ (getMaxVar e₂ + 1)
      · omega
      · assumption
  case Perm e₁ e₂ e₃ ih₁ ih₂ ih₃ =>
    constructor <;> try constructor
    · apply allVarsSmallerThanMonotone e₁ (getMaxVar e₁ + 1)
      · omega
      · assumption
    · apply allVarsSmallerThanMonotone e₂ (getMaxVar e₂ + 1)
      · omega
      · assumption
    · apply allVarsSmallerThanMonotone e₃ (getMaxVar e₃ + 1)
      · omega
      · assumption
  case Hidden k ih =>
    exact ih
  case G0 e ih =>
    exact ih
  case G1 e ih =>
    exact ih

lemma getMaxVarMonotone {s : Shape} (e1 e2 : Expression s) (H : e1 ⊆ e2) : getMaxVar e1 <= getMaxVar e2 :=
  by
  induction e2 <;> cases e1 <;> simp [ExpressionInclusion, getMaxVar] at *
  case BitE.BitE H =>
    rw [H]
  case VarK.VarK =>
    rw [H]
  case Pair.Pair s1 s2 e1 e2 H1 H2 f1 f2  =>
    have L : getMaxVar f1 ≤ getMaxVar e1 := by apply H1; apply H.1
    have R : getMaxVar f2 ≤ getMaxVar e2 := by apply H2; apply H.2
    omega
  case Perm.Perm s0 s1 s2 e1 H1 H2 e0 f1 f2 =>
    have L : getMaxVar f1 ≤ getMaxVar s1 := by apply H1; apply H.1
    have R : getMaxVar f2 ≤ getMaxVar s2 := by apply H2; apply H.2.1
    have Z : getMaxVar e0 ≤ getMaxVar s0 := by apply e1; apply H.2.2
    omega
  case Enc.Enc e1 e2 H1 H2 f1 f2 =>
    have R : getMaxVar f2 ≤ getMaxVar e2 := by apply H2; apply H.2
    rw [H.1]
    omega
  case Enc.Hidden e1 e2 e3 H2 f1 f2 =>
    rw [H]
    cases e2 <;> simp [getMaxVar]
  case Hidden.Hidden =>
    rw [H]
  case G0.G0 ih_e e_inner =>
    apply ih_e
    exact H
  case G1.G1 ih_e e_inner =>
    apply ih_e
    exact H

def evalBitExpr (bVars : ℕ -> Bool) (e : BitExpr) : Bool :=
  match e with
  | BitExpr.VarB v =>
    bVars v
  | BitExpr.Not e' =>
    not (evalBitExpr bVars e')
  | BitExpr.Bit b => b

def ones {k : ℕ} := List.Vector.replicate k true

noncomputable
def evalExpr (enc : encryptionFunctions κ) (prg : prgFunctions κ) (kVars : ℕ -> BitVector κ) (bVars : ℕ -> Bool) (e : Expression s) : PMF (BitVector (shapeLength κ enc s)) :=
  match e with
  | Expression.Enc k e => do
    let e' ← evalExpr enc prg kVars bVars e
    let key ← evalExpr enc prg kVars bVars k
    enc.encrypt key e'
  | Expression.Pair e₁ e₂ => do
    let e₁' ← evalExpr enc prg kVars bVars e₁
    let e₂' ← evalExpr enc prg kVars bVars e₂
    PMF.pure $ List.Vector.append e₁' e₂'
  | Expression.BitE b => do
    let b' := evalBitExpr bVars b
    PMF.pure $ List.Vector.cons b' List.Vector.nil
  | Expression.VarK k => do
    PMF.pure (kVars k)
  | Expression.Perm (Expression.BitE b) e₁ e₂ => do
    let b' := evalBitExpr bVars b
    let e₁' ← evalExpr enc prg kVars bVars e₁
    let e₂' ← evalExpr enc prg kVars bVars e₂
    if b' then PMF.pure $ List.Vector.append e₂' e₁'
    else PMF.pure $ List.Vector.append e₁' e₂'
  | Expression.Eps =>
    PMF.pure List.Vector.nil
  | Expression.Hidden k => do
    let key ← evalExpr enc prg kVars bVars k
    enc.encrypt key ones
  -- NEW PRG COMPUTATIONAL SEMANTICS:
  | Expression.G0 e => do
    let e' ← evalExpr enc prg kVars bVars e
    PMF.pure (prg.prg0 e')
  | Expression.G1 e => do
    let e' ← evalExpr enc prg kVars bVars e
    PMF.pure (prg.prg1 e')

-- Evaluating a *key* expression is deterministic: `VarK` is a lookup and `G0`/`G1` are
-- function applications, so the resulting `PMF` is a Dirac measure.  Recording this
-- explicitly saves every downstream proof from pushing a monadic bind through a
-- computation that has no randomness in it.
def keyVal {κ : ℕ} (prg : prgFunctions κ) (kVars : ℕ -> BitVector κ) :
    Expression Shape.KeyS → BitVector κ
  | Expression.VarK n => kVars n
  | Expression.G0 k => prg.prg0 (keyVal prg kVars k)
  | Expression.G1 k => prg.prg1 (keyVal prg kVars k)

-- (structural recursion rather than `induction`: the `Shape` index is fixed at `𝕂`)
lemma evalExpr_key {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ)
    (kVars : ℕ -> BitVector κ) (bVars : ℕ -> Bool) :
    (k : Expression Shape.KeyS) → evalExpr enc prg kVars bVars k = PMF.pure (keyVal prg kVars k)
  | Expression.VarK n => by simp [evalExpr, keyVal]
  | Expression.G0 k => by
      simp [evalExpr, keyVal, evalExpr_key enc prg kVars bVars k, PMF.pure_bind, Bind.bind]
  | Expression.G1 k => by
      simp [evalExpr, keyVal, evalExpr_key enc prg kVars bVars k, PMF.pure_bind, Bind.bind]

/-!
### Decryption commutes with the semantics

The computational content of F9 (`CHECKPOINT.md` §3.2).  The symbolic evaluator decrypts by
pattern-matching `Enc k e ↦ e`; a computational evaluator must call `enc.decrypt` and land in
the same place.  `encryptionFunctions.decrypt_encrypt` is exactly what makes that true, and
these two lemmas are where it is consumed.
-/

/-- Computational decryption of an `Enc` node recovers a value the plaintext could have had. -/
lemma evalExpr_decrypt {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (k : Expression Shape.KeyS) {s : Shape} (e : Expression s) :
    ∀ c ∈ (evalExpr enc prg kVars bVars (Expression.Enc k e)).support,
      enc.decrypt (keyVal prg kVars k) c ∈ (evalExpr enc prg kVars bVars e).support := by
  intro c hc
  rw [evalExpr] at hc
  rw [evalExpr_key enc prg kVars bVars k] at hc
  simp only [Bind.bind, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hc
  obtain ⟨m, hm, hc⟩ := hc
  obtain ⟨_, rfl, hc⟩ := hc
  rw [enc.decrypt_encrypt _ _ _ hc]
  exact hm

/-- A hole decrypts to the fixed public constant, carrying no information — which is the point
of `Hidden`. -/
lemma evalExpr_hidden_decrypt {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (k : Expression Shape.KeyS) {s : Shape} :
    ∀ c ∈ (evalExpr (s := Shape.EncS s) enc prg kVars bVars (Expression.Hidden k)).support,
      enc.decrypt (keyVal prg kVars k) c = ones := by
  intro c hc
  rw [evalExpr] at hc
  rw [evalExpr_key enc prg kVars bVars k] at hc
  simp only [Bind.bind, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hc
  obtain ⟨_, rfl, hc⟩ := hc
  exact enc.decrypt_encrypt _ _ _ hc

/-!
### Splitting a bit vector by shape

`List.Vector.append` is how `Pair` and `Perm` build their values; a computational evaluator has
to undo it.  Mathlib has the `cons` cases of `get_append` but not the general ones, so they are
proved here.
-/

lemma get_append_left : ∀ {n m : ℕ} (a : BitVector n) (b : BitVector m)
    (i : Fin n) (h : (i.val : ℕ) < n + m),
    (a.append b).get ⟨i.val, h⟩ = a.get i := by
  intro n
  induction n with
  | zero => intro m a b i h; exact absurd i.isLt (by omega)
  | succ n ih =>
      intro m a b i h
      obtain ⟨x, a', rfl⟩ := a.exists_eq_cons
      rcases i with ⟨iv, hiv⟩
      cases iv with
      | zero => simp [List.Vector.get_append_cons_zero]
      | succ j =>
          have := ih a' b ⟨j, by omega⟩ (by omega)
          simpa [List.Vector.get_append_cons_succ] using this

lemma get_append_right : ∀ {n m : ℕ} (a : BitVector n) (b : BitVector m)
    (i : Fin m) (h : n + (i.val : ℕ) < n + m),
    (a.append b).get ⟨n + i.val, h⟩ = b.get i := by
  intro n
  induction n with
  | zero =>
      intro m a b i h
      obtain rfl := a.eq_nil
      obtain ⟨l, hl⟩ := b
      simp [List.Vector.append, List.Vector.get]
  | succ n ih =>
      intro m a b i h
      obtain ⟨x, a', rfl⟩ := a.exists_eq_cons
      have := ih a' b i (by omega)
      simpa [List.Vector.get_append_cons_succ, Nat.succ_add] using this

/-- The first `n` bits. -/
def vecTake {n m : ℕ} (v : BitVector (n + m)) : BitVector n :=
  List.Vector.ofFn (fun i : Fin n => v.get ⟨i.val, by omega⟩)
/-- The last `m` bits. -/
def vecDrop {n m : ℕ} (v : BitVector (n + m)) : BitVector m :=
  List.Vector.ofFn (fun i : Fin m => v.get ⟨n + i.val, by omega⟩)

@[simp] lemma vecTake_append {n m : ℕ} (a : BitVector n) (b : BitVector m) :
    vecTake (a.append b) = a := by simp [vecTake, get_append_left]
@[simp] lemma vecDrop_append {n m : ℕ} (a : BitVector n) (b : BitVector m) :
    vecDrop (a.append b) = b := by simp [vecDrop, get_append_right]

def extendFin {k : ℕ} (default : X) (x : Fin k -> X) :  (ℕ -> X) :=
  fun i =>
    if H : i<k then
      x ⟨i, H⟩
    else
      default

-- Update the wrappers to pass the PRG down:
noncomputable
def evalExprVarsL {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (vars_length : ℕ) (e : Expression s)  : PMF (BitVector (shapeLength κ enc s)) := do
  let bvars <- uniformOfFintype (Fin vars_length -> Bool)
  let kvars <- uniformOfFintype (Fin vars_length -> BitVector κ)
  evalExpr enc prg (extendFin ones kvars) (extendFin false bvars) e

def restrict {k l : ℕ} (H : l<=k) (f : Fin k -> S) : (Fin l -> S) :=
  fun i =>
    f ⟨i, by omega⟩

noncomputable
def exprToDistr {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (e : Expression s)  : PMF (BitVector (shapeLength κ enc s)) :=
  evalExprVarsL enc prg (getMaxVar e + 1) e

noncomputable
def exprToFamDistr (enc : encryptionScheme) (prg : prgScheme) (e : Expression s) : (κ : ℕ) → PMF (BitVector (shapeLength κ (enc κ) s)) :=
  fun κ => exprToDistr (enc κ) (prg κ) e

----- LEMMAS -----

def agreeOnPrefix (l : ℕ) (f1 f2 : ℕ -> S) := forall i, i < l -> f1 i = f2 i

lemma evalNoMatterBit (l : ℕ) (bVars1 bVars2 : ℕ -> Bool) (e : BitExpr) :
  agreeOnPrefix (l) bVars1 bVars2 ->
  l >= 1 + getMaxVarBExpr e ->
  evalBitExpr bVars1 e = evalBitExpr bVars2 e := by
  intro Hb Hl
  induction e <;> try simp [evalBitExpr]
  case VarB a =>
    simp [agreeOnPrefix] at Hb
    apply Hb

    simp [getMaxVarBExpr] at Hl
    omega
  case Not a Ha =>
    apply Ha
    assumption


lemma evalNoMatter {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (l : ℕ) (kVars1 kVars2: (ℕ -> BitVector κ)) (bVars1 bVars2 : ℕ -> Bool) (e : Expression s) :
  agreeOnPrefix l kVars1 kVars2 ->
  agreeOnPrefix l bVars1 bVars2 ->
  l >= getMaxVar e + 1 ->
  evalExpr enc prg kVars1 bVars1 e = evalExpr enc prg kVars2 bVars2 e := by
  intro Hk Hb Hl
  induction e <;> try (simp [evalExpr, evalBitExpr]; try simp [getMaxVar] at Hl)
  case BitE a =>
    rw [evalNoMatterBit l]
    assumption
    omega
  case VarK a =>
    rw [Hk]
    assumption
  case Pair e1 e2 He1 He2 =>
    rw [He1, He2] <;> omega
  case Perm s e1 e2 Hs He1 He2 =>
    cases s
    simp [getMaxVar] at Hl
    simp [evalExpr]
    rw [He1] <;> try omega
    rw [He2] <;> try omega
    rw [evalNoMatterBit l] <;> omega
  case Enc k e Hk_ih He_ih =>
    --simp [getMaxVar] at Hl
    --simp [evalExpr]
    rw [He_ih] <;> try omega
    rw [Hk_ih]; omega
  case Hidden k Hk_ih =>
    -- simp [getMaxVar] at Hl
    -- simp [evalExpr]
    rw [Hk_ih]; omega
  case G0 k Hk_ih =>
    -- simp [getMaxVar] at Hl
    -- simp [evalExpr]
    rw [Hk_ih] ; omega
  case G1 k Hk_ih =>
    -- simp [getMaxVar] at Hl
    -- simp [evalExpr]
    rw [Hk_ih] ; omega

lemma restrictAndExtend (l1 l2 : ℕ) (H : l1 <= l2) (f : Fin l2 -> S) (zero : S) :
  agreeOnPrefix l1 (extendFin zero f) (extendFin zero (restrict H f)) := by
  intro i Hi
  have H2 : i < l2 := by omega
  have Ha : extendFin zero f i = f ⟨i, H2⟩ := by
    simp [extendFin]
    exact dif_pos H2
  have Hb : extendFin zero (restrict H f) i = f ⟨i, H2⟩ := by
    simp [extendFin]
    exact dif_pos Hi
  rw [Ha, Hb]

lemma boring {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (l : ℕ) (l2 : ℕ) (kVars: (Fin l -> BitVector κ)) (bVars : Fin l -> Bool) (e : Expression s) :
  (H : l >= l2) ->
  (l2 >= getMaxVar e+1) ->
  evalExpr enc prg (extendFin ones kVars) (extendFin false bVars) e =
  evalExpr enc prg (extendFin ones (restrict H kVars)) (extendFin false (restrict H bVars)) e := by
  intro H Hl
  apply evalNoMatter _ prg (l2)
  apply restrictAndExtend
  apply restrictAndExtend
  assumption

noncomputable
def rnd1 (κ : ℕ) (vars_length : ℕ)  : PMF ((Fin vars_length -> Bool) × (Fin vars_length -> BitVector κ)) := do
  let bvars <- uniformOfFintype (Fin vars_length -> Bool)
  let kvars <- uniformOfFintype (Fin vars_length -> BitVector κ)
  return (bvars, kvars)

noncomputable
def rnd2 (κ : ℕ) (vars_length1 vars_length2 : ℕ) (H : vars_length2 <= vars_length1) : PMF ((Fin vars_length2 -> Bool) × (Fin vars_length2 -> BitVector κ)) := do
  let bvars <- uniformOfFintype (Fin vars_length1 -> Bool)
  let kvars <- uniformOfFintype (Fin vars_length1 -> BitVector κ)
  return (restrict H bvars, restrict H kvars)

lemma rndsEq {κ : ℕ} (vars_length1 vars_length2 : ℕ) (H : vars_length2 <= vars_length1) : rnd1 κ vars_length2 = rnd2 κ vars_length1 vars_length2 H := by
  simp [rnd1, rnd2]
  ext x
  -- cases x with | mk kv bv =>
  simp [Functor.map, PMF.bind, uniformOfFintype, uniformOfFinset, ofFinset, Bind.bind]
  simp [Subtype.mk, Functor.map, DFunLike.coe]
  rw [tsum_eq_single x.1]
  swap
  · intro a
    intro h
    rw [ENNReal.tsum_eq_zero.mpr] <;> try simp
    intro i hi
    apply h
    rw [hi]
  rw [tsum_eq_single x.2]
  swap
  · intro b hb
    simp
    intro hcontra
    apply hb
    rw [hcontra]
  simp
  conv =>
    rhs
    arg 1
    intro a
    arg 2
    arg 1
    intro b
    rw [← mul_one ((2 ^ κ) ^ vars_length1)⁻¹]
    rw [← mul_zero (((2 : ENNReal) ^ κ) ^ vars_length1)⁻¹]
    rw [←mul_ite]
    -- change
    --   ((2 ^ κ) ^ vars_length2)⁻¹ * ((fun x => if x = (a, b) then 1 else 0) x)
    rfl
  simp only [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  simp [tsum_fintype, ← Finset.card_subtype]
  -- have hfin : Fintype {p : (Fin vars_length1 → Bool) × (Fin vars_length1 → BitVector κ) // x.1 = restrict H p.1 /\ x.2 = restrict H p.2} := by
  --   infer_instance
  rw [@Fintype.card_congr _ {p : (Fin vars_length1 → Bool) × (Fin vars_length1 → BitVector κ) // (fun p1 => x.1 = restrict H p1) p.1 /\ (fun p2 => x.2 = restrict H p2) p.2}]
  swap
  · apply Equiv.subtypeEquivProp
    ext p
    constructor
    · intro hx
      simp [hx]
    · intro ⟨hx₁, hx₂⟩
      simp [<- hx₁, <- hx₂]
  rw [@Fintype.card_congr _ ({p // (fun p1 => x.1 = restrict H p1) p} × {p // (fun p2 => x.2 = restrict H p2) p})]
  swap
  · apply (@Equiv.subtypeProdEquivProd _ _ (fun p1 => x.1 = restrict H p1) (fun p2 => x.2 = restrict H p2))
  simp
  let S : Finset (Fin vars_length1) := { x : Fin vars_length1 | x < vars_length2}
  let x1' : Fin vars_length1 → Bool := fun i =>
    if H : i < vars_length2 then x.1 ⟨i.1, H⟩
    else false
  rw [@Fintype.card_congr _ { p : (Fin vars_length1 → Bool) // forall i : S, p i = x1' i }]
  swap
  · apply Equiv.subtypeEquivProp
    ext p
    constructor
    · intro hx ⟨i, hi⟩
      simp [hx, restrict, x1']
      simp [S] at hi
      intro
      assumption
    · intro h
      ext ⟨vi, hi⟩
      simp [restrict]
      let i' : S := ⟨⟨vi, by omega⟩ , by simp [S]; assumption⟩
      have hi' := h i'
      simp [i'] at hi'
      simp [hi', x1']
      rw [dite_cond_eq_true]
      simp
      assumption
  rw [cardinalityCount]
  simp [S]
  simp [← Finset.card_subtype]
  rw [@Fintype.card_congr _ (Fin vars_length2)]
  swap
  · exact {
      toFun := fun i => ⟨i, by omega⟩
      invFun := fun i => ⟨⟨i, by omega⟩, by simp⟩
      left_inv := by intro i; simp
      right_inv := by intro i; simp
    }
  simp
  let x2' : Fin vars_length1 → BitVector κ := fun i =>
    if H : i < vars_length2 then x.2 ⟨i.1, H⟩
    else ones
  rw [@Fintype.card_congr _ { p : (Fin vars_length1 → BitVector κ) // forall i : S, p i = x2' i }]
  swap
  · apply Equiv.subtypeEquivProp
    ext p
    constructor
    · intro hx ⟨i, hi⟩
      simp [hx, restrict, x2']
      simp [S] at hi
      rw [ite_cond_eq_true] ; (try (simp; assumption))
    · intro h
      ext ⟨vi, hi⟩
      simp [restrict]
      let i' : S := ⟨⟨vi, by omega⟩ , by simp [S]; assumption⟩
      have hi' := h i'
      simp [i'] at hi'
      simp [hi', x2']
      rw [dite_cond_eq_true]
      simp
      assumption
  rw [cardinalityCount x2' S]
  simp [S]
  simp [← Finset.card_subtype]
  rw [@Fintype.card_congr _ (Fin vars_length2)]
  swap
  · exact {
      toFun := fun i => ⟨i, by omega⟩
      invFun := fun i => ⟨⟨i, by omega⟩, by simp⟩
      left_inv := by intro i; simp
      right_inv := by intro i; simp
    }
  ring_nf
  simp [← ENNReal.rpow_natCast, ← ENNReal.rpow_neg, ←ENNReal.rpow_add]
  congr 1
  ring_nf
  repeat rw [Nat.cast_sub]
  simp [← neg_mul, mul_sub, add_sub]
  simp [neg_mul]
  simp [sub_eq_add_neg, add_comm]
  ring
  all_goals (try assumption)

noncomputable
def evalExprVarsL2 {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (vars_length : ℕ) (e : Expression s)  : PMF (BitVector (shapeLength κ enc s)) := do
  let rand <- rnd1 κ vars_length
  let (bvars, kvars) := rand
  evalExpr enc prg (extendFin ones kvars) (extendFin false bvars) e

lemma evalExprVarsL2Eq {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (vars_length : ℕ) (e : Expression s) : evalExprVarsL2 enc prg vars_length e = evalExprVarsL enc prg vars_length e := by
  simp [evalExprVarsL2, evalExprVarsL]
  simp [rnd1]


lemma evalExprVarsNoMatter {s : Shape} {κ : ℕ} (enc : encryptionFunctions κ) (prg : prgFunctions κ) (vars_length1 vars_length2: ℕ) (e : Expression s) :
  vars_length1 >= vars_length2 ->
  vars_length2 >= (getMaxVar e + 1) ->
  evalExprVarsL enc prg vars_length1 e = evalExprVarsL enc prg vars_length2 e := by
  intro Hv1 Hv2
  nth_rw 2 [<-evalExprVarsL2Eq]
  simp [evalExprVarsL]
  simp [evalExprVarsL2]
  rw [rndsEq vars_length1] <;> try assumption
  simp [rnd2]
  conv =>
    lhs
    congr
    · skip
    · intro x
      congr
      · skip
      · intro y
        rw [boring enc prg vars_length1 vars_length2 _ _ _ (by assumption) (by assumption)]
        skip

def subst {X n} (i : ℕ) (x : X) (f : Fin n -> X) : Fin n -> X :=
  fun j =>
    if i=j then
      x
    else f j

noncomputable
def resample {X: Type} [Fintype X] [Nonempty X] (n : ℕ) (i : ℕ) : PMF (Fin n → X) :=
  do
  let x <- uniformOfFintype (Fin n -> X)
  let y <- uniformOfFintype X
  return subst i y x

lemma subst_eq {X n} (i : ℕ) (hi : i < n) (f : Fin n -> X) :
  subst i (f ⟨i, hi⟩) f = f := by
    ext x
    simp [subst]
    intro hi
    simp [hi]

lemma subst_eq_le {X n} (i : ℕ) (hi : n ≤ i) (x : X) (f : Fin n -> X) :
  subst i x f = f := by
    ext j
    simp [subst]
    intro hj
    omega

lemma sym_eq (a : A) (b : A) : (a = b) = (b = a) := by
    apply (@iff_iff_eq (a = b) (b = a)).mp
    constructor <;> (intro; symm; assumption)


lemma resampleIsTrivial {X: Type} [Fintype X] [Nonempty X] : resample n i = uniformOfFintype (Fin n -> X) := by
  ext1 b
  simp [resample, Bind.bind, PMF.bind, DFunLike.coe, uniformOfFintype, uniformOfFinset, ofFinset, Functor.map, Pure.pure, PMF.pure]
  simp [ENNReal.tsum_mul_left]
  if H : i < n then
    conv =>
      lhs; arg 2; arg 1; intro v
      rw [tsum_eq_single (b ⟨i, H⟩)]
      rw [← @mul_one ENNReal _ (↑(Fintype.card X))⁻¹]
      rw [← mul_ite_zero]
      rfl
      tactic =>
        intro x' hx'
        rw [ite_cond_eq_false]
        simp
        intro hcontra
        apply hx'
        rw [hcontra]
        simp [subst]
    rw [ENNReal.tsum_mul_left]
    simp [tsum_fintype, ← Finset.card_subtype]
    let Si : Finset (Fin n) := {s : Fin n | s = ⟨i, H⟩}
    let S : Finset (Fin n) := Finset.univ \ Si

    conv =>
      lhs; arg 2; arg 2
      rw [@Fintype.card_congr _ {f : Fin n → X // ∀ (x : S), f x = b x}]
      rw [cardinalityCount]
      rfl
      tactic =>
        apply Equiv.subtypeEquivProp
        ext f
        constructor
        · intro hf x
          rw [hf]
          simp [subst]
          rw [ite_cond_eq_false]
          simp
          have ⟨vx, hx⟩ := x
          simp [S, Si] at hx
          simp
          intro hcontra
          apply hx
          symm
          ext
          simp
          assumption
        · simp [S, Si]
          intro ha
          ext j
          simp [subst]
          split
          next hij =>
            simp [hij]
          next hij =>
            rw [ha]
            intro hcontra
            apply hij
            symm
            rw [hcontra]
    simp[S, Si, Finset.card_sdiff, ←Finset.card_subtype]
    conv =>
      rhs; rw [← @mul_one ENNReal _ (↑(Fintype.card X) ^ n)⁻¹]
      rfl
    congr 1
    have : n - (n - 1) = 1 := by
      omega
    simp [this]
    rw [ENNReal.inv_mul_cancel]
    all_goals simp
  else
    conv =>
      lhs; arg 2; arg 1; intro v; arg 1; intro y
      rw [subst_eq_le]
      rfl
      tactic => omega
    simp [tsum_fintype]
    rw [ENNReal.mul_inv_cancel, mul_one]
    all_goals simp

def subst2 (i : ℕ) (val : X) (kVars : (ℕ -> X)) :=
  fun x =>
    if x = i then val else kVars x


-- Two-index substitution: the PRG reduction has to bind BOTH halves of the oracle's
-- answer at once.
def subst3 {X : Type} (i j : ℕ) (vi vj : X) (f : ℕ -> X) : ℕ -> X :=
  fun x => if x = i then vi else if x = j then vj else f x

lemma subst3_eq_subst2 {X : Type} (i j : ℕ) (vi vj : X) (f : ℕ -> X) :
  subst3 i j vi vj f = subst2 i vi (subst2 j vj f) := by
  funext x
  simp only [subst3, subst2]

def restrictInfToFin  (l : ℕ)  (f : ℕ -> S) : (Fin l -> S) :=
  fun i =>
    f i

noncomputable
def resampling2 {X: Type} [Fintype X] [Nonempty X] (n : ℕ) (key₀ : ℕ) (ones : X) : PMF (Fin n -> X) :=
  do
    let b <- uniformOfFintype (Fin n -> X)
    let y <- uniformOfFintype X
    return restrictInfToFin n (subst2 key₀ y (extendFin ones b))

lemma resampling2EqResample {X: Type} [Fintype X] [Nonempty X] (n : ℕ) (key₀ : ℕ) (ones : X) :
  resampling2 n key₀ ones = resample n key₀ := by
  ext1 b
  simp [resampling2, resample]
  congr
  ext x₁ x₂
  congr
  ext a₁ k
  simp [restrictInfToFin, extendFin, subst, subst2]
  congr 1
  simp [eq_comm]

lemma resampleIsTrivial2 {X: Type} [Fintype X] [Nonempty X] (ones : X):
  uniformOfFintype (Fin n -> X) =
  resampling2 n key₀ ones
   := by
    rw[resampling2EqResample, resampleIsTrivial]

-- ---------------------------------------------------------------------------------
-- Two-index resampling, mirroring `resample`/`resampling2`/`resampleIsTrivial2`.
-- The PRG reduction binds both halves of the oracle answer, so it needs the
-- two-variable version of "overwriting two coordinates with fresh uniform values
-- leaves the uniform distribution alone".
-- ---------------------------------------------------------------------------------

noncomputable
def resample3 {X: Type} [Fintype X] [Nonempty X] (n : ℕ) (i j : ℕ) : PMF (Fin n → X) :=
  do
  let x <- uniformOfFintype (Fin n -> X)
  let y0 <- uniformOfFintype X
  let y1 <- uniformOfFintype X
  return subst i y0 (subst j y1 x)

noncomputable
def resampling3 {X: Type} [Fintype X] [Nonempty X] (n : ℕ) (i j : ℕ) (ones : X) : PMF (Fin n -> X) :=
  do
    let b <- uniformOfFintype (Fin n -> X)
    let y0 <- uniformOfFintype X
    let y1 <- uniformOfFintype X
    return restrictInfToFin n (subst3 i j y0 y1 (extendFin ones b))

lemma restrict_subst3 {X : Type} (n i j : ℕ) (y0 y1 ones : X) (b : Fin n -> X) :
  restrictInfToFin n (subst3 i j y0 y1 (extendFin ones b)) = subst i y0 (subst j y1 b) := by
  funext k
  simp only [restrictInfToFin, subst3, subst, extendFin]
  by_cases h0 : (k : ℕ) = i
  · simp [h0, eq_comm]
  · by_cases h1 : (k : ℕ) = j
    · simp [h0, h1, eq_comm, Ne.symm h0]
    · have hk : (k : ℕ) < n := k.isLt
      simp [h0, h1, hk, Ne.symm h0, Ne.symm h1]

lemma resampling3EqResample3 {X: Type} [Fintype X] [Nonempty X] {n i j : ℕ} (ones : X) :
  resampling3 (X := X) n i j ones = resample3 (X := X) n i j := by
  simp only [resampling3, resample3, restrict_subst3]

lemma resample3IsTrivial {X: Type} [Fintype X] [Nonempty X] {n i j : ℕ} :
  resample3 (X := X) n i j = uniformOfFintype (Fin n -> X) := by
  -- swap the two fresh draws, fold the inner pair into `resample n j`, then `resample n i`
  have h2 : resample3 (X := X) n i j
      = (resample (X := X) n j) >>=
        (fun z => uniformOfFintype X >>= fun y0 => PMF.pure (subst i y0 z)) := by
    simp only [resample3, resample, Bind.bind, PMF.bind_bind, PMF.pure_bind]
    congr 1
    funext x
    simp [PMF.pure_bind, Bind.bind, Pure.pure]
    rw [PMF.bind_comm]
  rw [h2, resampleIsTrivial]
  exact resampleIsTrivial

lemma resampleIsTrivial3 {X: Type} [Fintype X] [Nonempty X] {n i j : ℕ} (ones : X):
  uniformOfFintype (Fin n -> X) = resampling3 n i j ones := by
  rw [resampling3EqResample3, resample3IsTrivial]

lemma cutAndExtend [Fintype X] [Nonempty X] (ones : X) (Seq : ℕ -> X) :
  agreeOnPrefix n Seq (extendFin ones (@restrictInfToFin X n Seq)) :=
by
  intro i Hi
  simp [extendFin, Hi, restrictInfToFin]

lemma evalCutAndExtend {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ} {s : Shape} {e : Expression s} {key₀ : ℕ} {seed : BitVector κ} {a : Fin n → Bool} {b : Fin n → BitVector κ} (n : ℕ) (H : n > getMaxVar e):
  evalExpr enc prg (subst2 key₀ seed (extendFin ones b)) (extendFin false a) e =
  evalExpr enc prg (extendFin ones (@restrictInfToFin _ n (subst2 key₀ seed (extendFin ones b)))) (extendFin false a) e :=
by
  apply evalNoMatter enc prg n
  apply cutAndExtend
  simp [agreeOnPrefix]
  assumption

lemma veryBoring {κ l : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ} {s : Shape} {e : Expression s} {key₀ : ℕ}:
  (do
    let a ← PMF.uniformOfFintype (BitVector κ)
    let b ←  (PMF.uniformOfFintype (Fin l → Bool))
    let c ←  (PMF.uniformOfFintype (Fin l → BitVector κ))
    evalExpr enc prg (extendFin ones (restrictInfToFin l (subst2 key₀ a (extendFin ones c)))) (extendFin false b) e
  ) =
  (do
    let b ←  (PMF.uniformOfFintype (Fin l → Bool))
    let c <- resampling2 l key₀ ones
    evalExpr enc prg (extendFin ones c) (extendFin false b) e
  ) := by
  simp [resampling2]
  simp [Bind.bind]
  conv =>
    lhs
    rw [PMF.bind_comm]
    arg 2
    intro x
    rw [PMF.bind_comm]

lemma resamplingLemma2 {κ l : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ} {s : Shape} {e : Expression s} (key₀ : ℕ) : (l > getMaxVar e) ->
  (do
    let seed ← PMF.uniformOfFintype (BitVector κ)
    let a ←  (PMF.uniformOfFintype (Fin l → Bool))
    let b ←  (PMF.uniformOfFintype (Fin l → BitVector κ))
    evalExpr enc prg (subst2 key₀ seed (extendFin ones b)) (extendFin false a) e) =
   (exprToDistr enc prg e)
  := by
  intro Hi
  conv =>
    lhs
    arg 2; intro a
    arg 2; intro b
    arg 2; intro c
    rw [evalCutAndExtend l Hi]
  rw [veryBoring]
  rw [<-resampleIsTrivial2 ones]
  simp [exprToDistr]
  rw [<-evalExprVarsNoMatter enc prg l (getMaxVar e + 1)]
  · simp [evalExprVarsL]
  · exact Hi
  · apply Nat.le_refl


lemma lifting (x : PMF X) (f : X -> PMF Y) :
  let lhs : OptionT PMF Y := liftM (
    do
      let a : X <- x
      f a
  )
  let rhs : OptionT PMF Y :=
  (do
    let a : X <- liftM x
    liftM (f a)
  )
  lhs = rhs :=
  by
    simp [liftM, monadLift, MonadLift.monadLift, OptionT.lift, OptionT.mk]
    conv =>
      rhs
      rw [@Bind.bind, Monad.toBind, OptionT.instMonad]
      simp [OptionT.bind, OptionT.mk]

-- Two-index analogues of `evalCutAndExtend` / `veryBoring` / `resamplingLemma2`.
lemma evalCutAndExtend3 {κ : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ} {s : Shape}
    {e : Expression s} {i j : ℕ} {y0 y1 : BitVector κ} {a : Fin n → Bool} {b : Fin n → BitVector κ}
    (n : ℕ) (H : n > getMaxVar e):
  evalExpr enc prg (subst3 i j y0 y1 (extendFin ones b)) (extendFin false a) e =
  evalExpr enc prg (extendFin ones (@restrictInfToFin _ n (subst3 i j y0 y1 (extendFin ones b)))) (extendFin false a) e :=
by
  apply evalNoMatter enc prg n
  apply cutAndExtend
  simp [agreeOnPrefix]
  assumption

lemma veryBoring3 {κ l : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ} {s : Shape}
    {e : Expression s} {i j : ℕ}:
  (do
    let y0 ← PMF.uniformOfFintype (BitVector κ)
    let y1 ← PMF.uniformOfFintype (BitVector κ)
    let b ←  (PMF.uniformOfFintype (Fin l → Bool))
    let c ←  (PMF.uniformOfFintype (Fin l → BitVector κ))
    evalExpr enc prg (extendFin ones (restrictInfToFin l (subst3 i j y0 y1 (extendFin ones c)))) (extendFin false b) e
  ) =
  (do
    let b ←  (PMF.uniformOfFintype (Fin l → Bool))
    let c <- resampling3 l i j ones
    evalExpr enc prg (extendFin ones c) (extendFin false b) e
  ) := by
  simp [resampling3]
  simp [Bind.bind]
  conv =>
    lhs
    arg 2
    intro y0
    rw [PMF.bind_comm]
  conv =>
    lhs
    rw [PMF.bind_comm]
  conv =>
    lhs
    arg 2
    intro b
    arg 2
    intro y0
    rw [PMF.bind_comm]
  conv =>
    lhs
    arg 2
    intro b
    rw [PMF.bind_comm]

lemma resamplingLemma3Prg {κ l : ℕ} {enc : encryptionFunctions κ} {prg : prgFunctions κ}
    {s : Shape} {e : Expression s} (i j : ℕ) : (l > getMaxVar e) ->
  (do
    let y0 ← PMF.uniformOfFintype (BitVector κ)
    let y1 ← PMF.uniformOfFintype (BitVector κ)
    let a ←  (PMF.uniformOfFintype (Fin l → Bool))
    let b ←  (PMF.uniformOfFintype (Fin l → BitVector κ))
    evalExpr enc prg (subst3 i j y0 y1 (extendFin ones b)) (extendFin false a) e) =
   (exprToDistr enc prg e)
  := by
  intro Hi
  conv =>
    lhs
    arg 2
    intro y0
    arg 2
    intro y1
    arg 2
    intro a
    arg 2
    intro b
    rw [evalCutAndExtend3 l Hi]
  rw [veryBoring3]
  rw [<-resampleIsTrivial3 ones]
  simp [exprToDistr]
  rw [<-evalExprVarsNoMatter enc prg l (getMaxVar e + 1)]
  · simp [evalExprVarsL]
  · exact Hi
  · apply Nat.le_refl

lemma resamplingLemma {κ l : ℕ} {enc : encryptionScheme} {prg : prgScheme} {s : Shape} {e : Expression s} {key₀ : ℕ} : (l > getMaxVar e) ->
  (do
    let z : OptionT PMF _ := PMF.uniformOfFintype (BitVector κ)
    let seed ← z
    let a ← liftM (PMF.uniformOfFintype (Fin l → Bool))
    let b ← liftM (PMF.uniformOfFintype (Fin l → BitVector κ))
    liftM (evalExpr (enc κ) (prg κ) (subst2 key₀ seed (extendFin ones b)) (extendFin false a) e)) =
  liftM (exprToFamDistr enc prg e κ)
  :=
  by
    intro H
    rw [exprToFamDistr]
    rw [<-resamplingLemma2 key₀ H]
    simp [lifting]
lemma resamplingLemmaPrg {κ l : ℕ} {enc : encryptionScheme} {prg : prgScheme} {s : Shape}
    {e : Expression s} {i j : ℕ} : (l > getMaxVar e) ->
  (do
    let y0 ← (liftM (PMF.uniformOfFintype (BitVector κ)) : OptionT PMF _)
    let y1 ← (liftM (PMF.uniformOfFintype (BitVector κ)) : OptionT PMF _)
    let a ← liftM (PMF.uniformOfFintype (Fin l → Bool))
    let b ← liftM (PMF.uniformOfFintype (Fin l → BitVector κ))
    liftM (evalExpr (enc κ) (prg κ) (subst3 i j y0 y1 (extendFin ones b)) (extendFin false a) e)) =
  liftM (exprToFamDistr enc prg e κ)
  :=
  by
    intro H
    rw [exprToFamDistr]
    rw [<-resamplingLemma3Prg i j H]
    rw [lifting]
    congr
    ext1 y0
    rw [lifting]
    congr
    ext1 y1
    rw [lifting]
    congr
    ext1 a
    rw [lifting]


end PRG
