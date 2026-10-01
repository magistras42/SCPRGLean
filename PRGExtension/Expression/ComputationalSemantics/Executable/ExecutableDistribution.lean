import PRGExtension.Expression.ComputationalSemantics.Executable.Executable
import PRGExtension.Core.UniformProduct

/-!
# The distributional refinement

`evalExprExecOn_mem_support` says every value the implementation produces is one the
specification could have produced.  That is enough to transport *correctness*, which is a
statement about individual outputs.  It is not enough to transport *security*, which is a
statement about distributions: a scheme that always returns the same ciphertext satisfies the
support law and is insecure.

This file closes that gap.  Drawing the coin supply uniformly and running the code yields
**exactly** the distribution the specification assigns:

```
(uniform coins).map (fun c => evalExprExecOn … c e i) = evalExpr ex.spec …
```

so anything proved about `exprToFamDistr` — `garblingSecureRelative` in particular — is a
statement about the code.

The ingredients, in the order `FUTURE-WORK.md` predicted them:

* **A coin-count measure on expressions** — `encCount`, with `evalExprExecOn_counter` showing
  the evaluator's counter advances by exactly that, and `evalExprExecOn_coins_congr` showing the
  result depends only on the coins in the window `[i, i + encCount e)`.  Together these say the
  coin consumption is *structural*: it depends on the expression, never on the values.
* **A change-of-variables induction** — `execDistr_eq` below.
* **A strictly stronger law than `ExecScheme.mem_support`** — `(uniform coins).map (run k m)`
  must *equal* `encrypt k m`.  For an `ExecEnc` this is free: `ExecEnc.spec` defines `encrypt`
  that way, so the law holds by `rfl`.
* **The uniform-on-a-product lemma** — `uniformFinArrow_bind_split` (`Core/UniformProduct.lean`),
  which was the part not in Mathlib.
-/

namespace PRG

open PMF
open scoped ENNReal

/-! ## Coin consumption is structural -/

/-- How many coins evaluating an expression consumes: one per encryption node.  Note the order —
`evalExprExecOn` evaluates an `Enc`'s *message* before its *key*, and draws its coin last. -/
def encCount : {s : Shape} → Expression s → ℕ
  | _, Expression.Eps => 0
  | _, Expression.BitE _ => 0
  | _, Expression.VarK _ => 0
  | _, Expression.G0 k => encCount k
  | _, Expression.G1 k => encCount k
  | _, Expression.Pair e₁ e₂ => encCount e₁ + encCount e₂
  | _, Expression.Perm _ e₁ e₂ => encCount e₁ + encCount e₂
  | _, Expression.Enc k e => encCount e + encCount k + 1
  | _, Expression.Hidden k => encCount k + 1

variable {κ : ℕ} {encLen : ℕ → ℕ} {randLen : ℕ}

/-- **The counter advances by exactly `encCount`.**  It depends on the expression alone — not on
the environment, not on the coins, not on any value computed along the way. -/
theorem evalExprExecOn_counter
    (run : {n : ℕ} → BitVector κ → BitVector n → BitVector randLen → BitVector (encLen n))
    (prg : prgFunctions κ) (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool)
    (coins : ℕ → BitVector randLen) :
    ∀ {s : Shape} (e : Expression s) (i : ℕ),
      (evalExprExecOn encLen randLen run prg kVars bVars coins e i).2 = i + encCount e
  | _, Expression.Eps, i => by simp [evalExprExecOn, encCount]
  | _, Expression.BitE _, i => by simp [evalExprExecOn, encCount]
  | _, Expression.VarK _, i => by simp [evalExprExecOn, encCount]
  | _, Expression.G0 k, i => by
      simpa [evalExprExecOn, encCount] using
        evalExprExecOn_counter run prg kVars bVars coins k i
  | _, Expression.G1 k, i => by
      simpa [evalExprExecOn, encCount] using
        evalExprExecOn_counter run prg kVars bVars coins k i
  | _, Expression.Pair e₁ e₂, i => by
      have h₁ := evalExprExecOn_counter run prg kVars bVars coins e₁ i
      have h₂ := evalExprExecOn_counter run prg kVars bVars coins e₂
        (evalExprExecOn encLen randLen run prg kVars bVars coins e₁ i).2
      simp only [evalExprExecOn, encCount]
      rw [h₂, h₁, Nat.add_assoc]
  | _, Expression.Perm (Expression.BitE b) e₁ e₂, i => by
      have h₁ := evalExprExecOn_counter run prg kVars bVars coins e₁ i
      have h₂ := evalExprExecOn_counter run prg kVars bVars coins e₂
        (evalExprExecOn encLen randLen run prg kVars bVars coins e₁ i).2
      simp only [evalExprExecOn, encCount]
      rw [h₂, h₁, Nat.add_assoc]
  | _, Expression.Enc k e, i => by
      have he := evalExprExecOn_counter run prg kVars bVars coins e i
      have hk := evalExprExecOn_counter run prg kVars bVars coins k
        (evalExprExecOn encLen randLen run prg kVars bVars coins e i).2
      simp only [evalExprExecOn, encCount]
      rw [hk, he]
      omega
  | _, Expression.Hidden k, i => by
      have hk := evalExprExecOn_counter run prg kVars bVars coins k i
      simp only [evalExprExecOn, encCount]
      rw [hk]
      omega

/-- **The result depends only on the coins actually consumed**, namely those in the window
`[i, i + encCount e)`.  This is what makes the coin supply splittable between subexpressions. -/
theorem evalExprExecOn_coins_congr
    (run : {n : ℕ} → BitVector κ → BitVector n → BitVector randLen → BitVector (encLen n))
    (prg : prgFunctions κ) (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool) :
    ∀ {s : Shape} (e : Expression s) (i : ℕ) (coins coins' : ℕ → BitVector randLen),
      (∀ j, i ≤ j → j < i + encCount e → coins j = coins' j) →
      evalExprExecOn encLen randLen run prg kVars bVars coins e i
        = evalExprExecOn encLen randLen run prg kVars bVars coins' e i
  | _, Expression.Eps, i, _, _, _ => rfl
  | _, Expression.BitE _, i, _, _, _ => rfl
  | _, Expression.VarK _, i, _, _, _ => rfl
  | _, Expression.G0 k, i, c, c', h => by
      simp only [evalExprExecOn]
      rw [evalExprExecOn_coins_congr run prg kVars bVars k i c c' h]
  | _, Expression.G1 k, i, c, c', h => by
      simp only [evalExprExecOn]
      rw [evalExprExecOn_coins_congr run prg kVars bVars k i c c' h]
  | _, Expression.Pair e₁ e₂, i, c, c', h => by
      have h₁ := evalExprExecOn_coins_congr run prg kVars bVars e₁ i c c'
        (fun j hj hj' => h j hj (by simp only [encCount]; omega))
      have hc₁ := evalExprExecOn_counter (encLen := encLen) run prg kVars bVars c' e₁ i
      have h₂ := evalExprExecOn_coins_congr run prg kVars bVars e₂ (i + encCount e₁) c c'
        (fun j hj hj' => h j (by omega) (by simp only [encCount]; omega))
      simp only [evalExprExecOn]
      rw [h₁, hc₁, h₂]
  | _, Expression.Perm (Expression.BitE b) e₁ e₂, i, c, c', h => by
      have h₁ := evalExprExecOn_coins_congr run prg kVars bVars e₁ i c c'
        (fun j hj hj' => h j hj (by simp only [encCount]; omega))
      have hc₁ := evalExprExecOn_counter (encLen := encLen) run prg kVars bVars c' e₁ i
      have h₂ := evalExprExecOn_coins_congr run prg kVars bVars e₂ (i + encCount e₁) c c'
        (fun j hj hj' => h j (by omega) (by simp only [encCount]; omega))
      simp only [evalExprExecOn]
      rw [h₁, hc₁, h₂]
  | _, Expression.Enc k e, i, c, c', h => by
      have he := evalExprExecOn_coins_congr run prg kVars bVars e i c c'
        (fun j hj hj' => h j hj (by simp only [encCount]; omega))
      have hce := evalExprExecOn_counter (encLen := encLen) run prg kVars bVars c' e i
      have hk := evalExprExecOn_coins_congr run prg kVars bVars k (i + encCount e) c c'
        (fun j hj hj' => h j (by omega) (by simp only [encCount]; omega))
      have hck := evalExprExecOn_counter (encLen := encLen) run prg kVars bVars c' k
        (i + encCount e)
      have hlast : c (i + encCount e + encCount k) = c' (i + encCount e + encCount k) :=
        h _ (by omega) (by simp only [encCount]; omega)
      simp only [evalExprExecOn]
      rw [he, hce, hk, hck, hlast]
  | _, Expression.Hidden k, i, c, c', h => by
      have hk := evalExprExecOn_coins_congr run prg kVars bVars k i c c'
        (fun j hj hj' => h j hj (by simp only [encCount]; omega))
      have hck := evalExprExecOn_counter (encLen := encLen) run prg kVars bVars c' k i
      have hlast : c (i + encCount k) = c' (i + encCount k) :=
        h _ (by omega) (by simp only [encCount]; omega)
      simp only [evalExprExecOn]
      rw [hk, hck, hlast]

/-! ## Placing a finite block of coins

The evaluator takes a supply indexed by `ℕ`; a *distribution* needs a finite one.  `coinsAt`
bridges them: `encCount e` coins placed at offset `i`, which by `evalExprExecOn_coins_congr` is
all the evaluator can see.
-/

/-- A finite block of coins, placed at offset `i`.  Outside the block the value is arbitrary and
never read. -/
def coinsAt {R : ℕ} (i : ℕ) {N : ℕ} (c : Fin N → BitVector R) : ℕ → BitVector R :=
  fun j => if h : j - i < N then c ⟨j - i, h⟩ else List.Vector.replicate R false

/-- On the first block, placing `m + n` coins agrees with placing the first `m`. -/
theorem coinsAt_castAdd {R m n : ℕ} (i : ℕ) (c : Fin (m + n) → BitVector R) (j : ℕ)
    (hj : i ≤ j) (hj' : j < i + m) :
    coinsAt i c j = coinsAt i (fun t : Fin m => c (Fin.castAdd n t)) j := by
  simp only [coinsAt]
  rw [dif_pos (show j - i < m + n by omega), dif_pos (show j - i < m by omega)]
  exact congrArg c (Fin.ext rfl)

/-- On the second block, placing `m + n` coins at `i` agrees with placing the last `n` at
`i + m`. -/
theorem coinsAt_natAdd {R m n : ℕ} (i : ℕ) (c : Fin (m + n) → BitVector R) (j : ℕ)
    (hj : i + m ≤ j) (hj' : j < i + m + n) :
    coinsAt i c j = coinsAt (i + m) (fun t : Fin n => c (Fin.natAdd m t)) j := by
  simp only [coinsAt]
  rw [dif_pos (show j - i < m + n by omega), dif_pos (show j - (i + m) < n by omega)]
  exact congrArg c (Fin.ext (by simp; omega))

/-! ## The refinement -/

/-- **The distributional refinement.**  Drawing the coins uniformly and running the code gives
*exactly* the distribution the specification assigns — not merely something in its support.

The induction is a change of variables: at each node with two subexpressions the block of coins
splits in two (`uniformFinArrow_map_split`), the two halves are independent, and the induction
hypotheses apply to each.  `evalExprExecOn_coins_congr` is what lets the halves be substituted
for the whole, and `evalExprExecOn_counter` is what says where the split falls.  At `Enc` and
`Hidden` the last coin of the block is the encryption's own randomness, and
`ExecEnc.spec`'s `encrypt` — the push-forward of the uniform distribution on coins — is exactly
what it feeds. -/
theorem execDistr_eq (ex : ExecEnc κ) (prg : prgFunctions κ)
    (kVars : ℕ → BitVector κ) (bVars : ℕ → Bool) :
    ∀ {s : Shape} (e : Expression s) (i : ℕ),
      ((uniformOfFintype (Fin (encCount e) → BitVector ex.randLen)).map
          (fun c => (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                       (coinsAt i c) e i).1))
        = evalExpr ex.spec prg kVars bVars e
  | _, Expression.Eps, i => by
      simp only [evalExprExecOn, evalExpr]
      exact PMF.map_const _ _
  | _, Expression.BitE b, i => by
      simp only [evalExprExecOn, evalExpr]
      exact PMF.map_const _ _
  | _, Expression.VarK k, i => by
      simp only [evalExprExecOn, evalExpr]
      exact PMF.map_const _ _
  | _, Expression.G0 k, i => by
      have ih := execDistr_eq ex prg kVars bVars k i
      simp only [evalExprExecOn, evalExpr, encCount, Bind.bind, Pure.pure]
      rw [← ih, PMF.bind_map]
      rfl
  | _, Expression.G1 k, i => by
      have ih := execDistr_eq ex prg kVars bVars k i
      simp only [evalExprExecOn, evalExpr, encCount, Bind.bind, Pure.pure]
      rw [← ih, PMF.bind_map]
      rfl
  | _, Expression.Pair e₁ e₂, i => by
      have ih₁ := execDistr_eq ex prg kVars bVars e₁ i
      have ih₂ := execDistr_eq ex prg kVars bVars e₂ (i + encCount e₁)
      have key : ∀ c : Fin (encCount e₁ + encCount e₂) → BitVector ex.randLen,
          (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars (coinsAt i c)
              (Expression.Pair e₁ e₂) i).1
            = List.Vector.append
                (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                  (coinsAt i (fun t : Fin (encCount e₁) => c (Fin.castAdd _ t))) e₁ i).1
                (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                  (coinsAt (i + encCount e₁)
                    (fun t : Fin (encCount e₂) => c (Fin.natAdd _ t))) e₂ (i + encCount e₁)).1 := by
        intro c
        have hcnt := evalExprExecOn_counter (encLen := ex.encryptLength) ex.run prg kVars bVars
          (coinsAt i c) e₁ i
        have h₁ := evalExprExecOn_coins_congr (encLen := ex.encryptLength) ex.run prg kVars bVars
          e₁ i (coinsAt i c) (coinsAt i (fun t : Fin (encCount e₁) => c (Fin.castAdd _ t)))
          (fun j hj hj' => coinsAt_castAdd i c j hj hj')
        have h₂ := evalExprExecOn_coins_congr (encLen := ex.encryptLength) ex.run prg kVars bVars
          e₂ (i + encCount e₁) (coinsAt i c)
          (coinsAt (i + encCount e₁) (fun t : Fin (encCount e₂) => c (Fin.natAdd _ t)))
          (fun j hj hj' => coinsAt_natAdd i c j hj (by omega))
        simp only [evalExprExecOn]
        rw [hcnt, h₁, h₂]
      simp only [key, encCount]
      rw [uniformFinArrow_map_split (encCount e₁) (encCount e₂)
        (fun a b => List.Vector.append
          (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
            (coinsAt i a) e₁ i).1
          (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
            (coinsAt (i + encCount e₁) b) e₂ (i + encCount e₁)).1)]
      simp only [evalExpr, Bind.bind, Pure.pure]
      rw [← ih₁, PMF.bind_map]
      simp only [← ih₂, PMF.bind_map, Function.comp_def]
      rfl
  | _, Expression.Perm (Expression.BitE b) e₁ e₂, i => by
      have ih₁ := execDistr_eq ex prg kVars bVars e₁ i
      have ih₂ := execDistr_eq ex prg kVars bVars e₂ (i + encCount e₁)
      have key : ∀ c : Fin (encCount e₁ + encCount e₂) → BitVector ex.randLen,
          (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars (coinsAt i c)
              (Expression.Perm (Expression.BitE b) e₁ e₂) i).1
            = (if evalBitExpr bVars b then
                  List.Vector.append
                    (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                      (coinsAt (i + encCount e₁)
                        (fun t : Fin (encCount e₂) => c (Fin.natAdd _ t))) e₂
                      (i + encCount e₁)).1
                    (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                      (coinsAt i (fun t : Fin (encCount e₁) => c (Fin.castAdd _ t))) e₁ i).1
                else
                  List.Vector.append
                    (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                      (coinsAt i (fun t : Fin (encCount e₁) => c (Fin.castAdd _ t))) e₁ i).1
                    (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                      (coinsAt (i + encCount e₁)
                        (fun t : Fin (encCount e₂) => c (Fin.natAdd _ t))) e₂
                      (i + encCount e₁)).1) := by
        intro c
        have hcnt := evalExprExecOn_counter (encLen := ex.encryptLength) ex.run prg kVars bVars
          (coinsAt i c) e₁ i
        have h₁ := evalExprExecOn_coins_congr (encLen := ex.encryptLength) ex.run prg kVars bVars
          e₁ i (coinsAt i c) (coinsAt i (fun t : Fin (encCount e₁) => c (Fin.castAdd _ t)))
          (fun j hj hj' => coinsAt_castAdd i c j hj hj')
        have h₂ := evalExprExecOn_coins_congr (encLen := ex.encryptLength) ex.run prg kVars bVars
          e₂ (i + encCount e₁) (coinsAt i c)
          (coinsAt (i + encCount e₁) (fun t : Fin (encCount e₂) => c (Fin.natAdd _ t)))
          (fun j hj hj' => coinsAt_natAdd i c j hj (by omega))
        simp only [evalExprExecOn]
        rw [hcnt, h₁, h₂]
      simp only [key, encCount]
      rw [uniformFinArrow_map_split (encCount e₁) (encCount e₂)
        (fun a b₂ => if evalBitExpr bVars b then
            List.Vector.append
              (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                (coinsAt (i + encCount e₁) b₂) e₂ (i + encCount e₁)).1
              (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                (coinsAt i a) e₁ i).1
          else
            List.Vector.append
              (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                (coinsAt i a) e₁ i).1
              (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                (coinsAt (i + encCount e₁) b₂) e₂ (i + encCount e₁)).1)]
      simp only [evalExpr, Bind.bind, Pure.pure]
      rw [← ih₁, PMF.bind_map]
      simp only [← ih₂, PMF.bind_map, Function.comp_def, ← apply_ite PMF.pure]
      rfl
  | _, Expression.Enc k e, i => by
      have ihe := execDistr_eq ex prg kVars bVars e i
      have ihk := execDistr_eq ex prg kVars bVars k (i + encCount e)
      have key : ∀ c : Fin (encCount e + encCount k + 1) → BitVector ex.randLen,
          (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars (coinsAt i c)
              (Expression.Enc k e) i).1
            = ex.run
                (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                  (coinsAt (i + encCount e)
                    (fun t : Fin (encCount k) =>
                      c (Fin.castAdd 1 (Fin.natAdd (encCount e) t)))) k (i + encCount e)).1
                (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                  (coinsAt i
                    (fun t : Fin (encCount e) =>
                      c (Fin.castAdd 1 (Fin.castAdd (encCount k) t)))) e i).1
                (c (Fin.natAdd (encCount e + encCount k) 0)) := by
        intro c
        have hce : ∀ j, i ≤ j → j < i + encCount e →
            coinsAt i c j = coinsAt i (fun t : Fin (encCount e) =>
              c (Fin.castAdd 1 (Fin.castAdd (encCount k) t))) j := by
          intro j hj hj'
          simp only [coinsAt]
          rw [dif_pos (show j - i < encCount e + encCount k + 1 by omega),
            dif_pos (show j - i < encCount e by omega)]
          exact congrArg c (Fin.ext rfl)
        have hck : ∀ j, i + encCount e ≤ j → j < i + encCount e + encCount k →
            coinsAt i c j = coinsAt (i + encCount e) (fun t : Fin (encCount k) =>
              c (Fin.castAdd 1 (Fin.natAdd (encCount e) t))) j := by
          intro j hj hj'
          simp only [coinsAt]
          rw [dif_pos (show j - i < encCount e + encCount k + 1 by omega),
            dif_pos (show j - (i + encCount e) < encCount k by omega)]
          exact congrArg c (Fin.ext (by simp; omega))
        have hlast : coinsAt i c (i + encCount e + encCount k)
            = c (Fin.natAdd (encCount e + encCount k) 0) := by
          simp only [coinsAt]
          rw [dif_pos (show i + encCount e + encCount k - i < encCount e + encCount k + 1 by omega)]
          exact congrArg c (Fin.ext (by simp; omega))
        have hcnte := evalExprExecOn_counter (encLen := ex.encryptLength) ex.run prg kVars bVars
          (coinsAt i c) e i
        have hcntk := evalExprExecOn_counter (encLen := ex.encryptLength) ex.run prg kVars bVars
          (coinsAt i c) k (i + encCount e)
        have h1 := evalExprExecOn_coins_congr (encLen := ex.encryptLength) ex.run prg kVars bVars
          e i (coinsAt i c)
          (coinsAt i (fun t : Fin (encCount e) => c (Fin.castAdd 1 (Fin.castAdd (encCount k) t))))
          (fun j hj hj' => hce j hj hj')
        have h2 := evalExprExecOn_coins_congr (encLen := ex.encryptLength) ex.run prg kVars bVars
          k (i + encCount e) (coinsAt i c)
          (coinsAt (i + encCount e)
            (fun t : Fin (encCount k) => c (Fin.castAdd 1 (Fin.natAdd (encCount e) t))))
          (fun j hj hj' => hck j hj (by omega))
        simp only [evalExprExecOn]
        rw [hcnte, hcntk, h1, h2, hlast]
      simp only [key, encCount]
      rw [uniformFinArrow_map_split (encCount e + encCount k) 1
        (fun a b₂ => ex.run
          (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
            (coinsAt (i + encCount e)
              (fun t : Fin (encCount k) => a (Fin.natAdd (encCount e) t))) k (i + encCount e)).1
          (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
            (coinsAt i (fun t : Fin (encCount e) => a (Fin.castAdd (encCount k) t))) e i).1
          (b₂ 0))]
      simp only [uniformFinOne_map]
      rw [uniformFinArrow_bind_split (encCount e) (encCount k)
        (fun a₁ a₂ => (uniformOfFintype (BitVector ex.randLen)).map
          (ex.run
            (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
              (coinsAt (i + encCount e) a₂) k (i + encCount e)).1
            (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
              (coinsAt i a₁) e i).1))]
      simp only [evalExpr, Bind.bind, Pure.pure, ExecEnc.spec_encrypt]
      rw [← ihe, PMF.bind_map]
      simp only [← ihk, PMF.bind_map, Function.comp_def]
  | _, @Expression.Hidden sp kk, i => by
      have ih := execDistr_eq ex prg kVars bVars kk i
      have key : ∀ c : Fin (encCount kk + 1) → BitVector ex.randLen,
          (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars (coinsAt i c)
              (Expression.Hidden kk) i).1
            = ex.run
                (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
                  (coinsAt i (fun t : Fin (encCount kk) => c (Fin.castAdd 1 t))) kk i).1
                (ones (k := shapeLengthOn κ ex.encryptLength sp))
                ((fun t : Fin 1 => c (Fin.natAdd (encCount kk) t)) 0) := by
        intro c
        have hcnt := evalExprExecOn_counter (encLen := ex.encryptLength) ex.run prg kVars bVars
          (coinsAt i c) kk i
        have hk := evalExprExecOn_coins_congr (encLen := ex.encryptLength) ex.run prg kVars bVars
          kk i (coinsAt i c) (coinsAt i (fun t : Fin (encCount kk) => c (Fin.castAdd 1 t)))
          (fun j hj hj' => coinsAt_castAdd i c j hj hj')
        have hlast : coinsAt i c (i + encCount kk)
            = (fun t : Fin 1 => c (Fin.natAdd (encCount kk) t)) 0 := by
          rw [coinsAt_natAdd i c (i + encCount kk) (by omega) (by omega)]
          simp [coinsAt]
        simp only [evalExprExecOn]
        rw [hcnt, hk, hlast]
      simp only [key, encCount]
      rw [uniformFinArrow_map_split (encCount kk) 1
        (fun a b₂ => ex.run (evalExprExecOn ex.encryptLength ex.randLen ex.run prg kVars bVars
            (coinsAt i a) kk i).1 (ones (k := shapeLengthOn κ ex.encryptLength sp)) (b₂ 0))]
      simp only [uniformFinOne_map]
      simp only [evalExpr, Bind.bind, Pure.pure, ExecEnc.spec_encrypt]
      rw [← ih, PMF.bind_map]
      rfl

/-! ## Over the sampled environment

`exprToDistr` closes `evalExpr` over a uniformly sampled environment; an implementation samples
one too.  Since the coins and the environment are drawn independently, the refinement lifts
without any further product reasoning.
-/

/-- **The distribution an implementation actually produces**: draw the environment, draw the
coins, run the code.  Everything here is something an implementation really does. -/
noncomputable def execToDistr (ex : ExecEnc κ) (prg : prgFunctions κ) {s : Shape}
    (e : Expression s) : PMF (BitVector (shapeLengthOn κ ex.encryptLength s)) :=
  (uniformOfFintype (Fin (getMaxVar e + 1) → Bool)).bind fun bvars =>
    (uniformOfFintype (Fin (getMaxVar e + 1) → BitVector κ)).bind fun kvars =>
      (uniformOfFintype (Fin (encCount e) → BitVector ex.randLen)).map fun c =>
        (evalExprExecOn ex.encryptLength ex.randLen ex.run prg
          (extendFin ones kvars) (extendFin false bvars) (coinsAt 0 c) e 0).1

/-- **The refinement, at the top of the expression layer.**  What the implementation produces is
`exprToDistr` of the specification it denotes — the same distribution, not merely a value in its
support. -/
theorem execToDistr_eq (ex : ExecEnc κ) (prg : prgFunctions κ) {s : Shape} (e : Expression s) :
    execToDistr ex prg e = exprToDistr ex.spec prg e := by
  simp only [execToDistr, exprToDistr, evalExprVarsL, Bind.bind]
  exact congrArg _ (funext fun bvars => congrArg _ (funext fun kvars =>
    execDistr_eq ex prg _ _ e 0))

/-! ## Families

Security is stated at every security parameter at once, so the implementation has to be a
family too.
-/

/-- A family of implementations, one per security parameter. -/
def ExecEncScheme : Type := (κ : ℕ) → ExecEnc κ

namespace ExecEncScheme

/-- The scheme family an implementation family denotes. -/
noncomputable def spec (E : ExecEncScheme) : encryptionScheme := fun κ => (E κ).spec

/-- The distributions the implementation family actually produces. -/
noncomputable def toFamDistr (E : ExecEncScheme) (prg : prgScheme) {s : Shape}
    (e : Expression s) : (κ : ℕ) → PMF (BitVector (shapeLength κ (E.spec κ) s)) :=
  fun κ => execToDistr (E κ) (prg κ) e

/-- **The refinement, as a family.**  This is the form every security statement in the
development consumes: `exprToFamDistr` *is* what the implementation produces. -/
theorem toFamDistr_eq (E : ExecEncScheme) (prg : prgScheme) {s : Shape} (e : Expression s) :
    E.toFamDistr prg e = exprToFamDistr E.spec prg e :=
  funext fun κ => execToDistr_eq (E κ) (prg κ) e

end ExecEncScheme

end PRG
