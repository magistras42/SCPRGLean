import PRGExtension.Expression.SymbolicIndistinguishability
open PRG

-- ===================================================================
-- A two-gate garbled circuit: NAnd  >>>  Dup  >>>  NAnd
-- following LM18 Section 4 (Gb for NAnd and Dup).
--
-- wire i : B_i = VarB 0,  K_i^0 = VarK 0, K_i^1 = VarK 1
-- wire j : B_j = VarB 1,  K_j^0 = VarK 2, K_j^1 = VarK 3
-- wire h : B_h = VarB 2,  K_h^0 = VarK 4, K_h^1 = VarK 5   (output of gate 1)
-- wire m : B_m = VarB 3,  K_m^0 = VarK 6, K_m^1 = VarK 7   (output of gate 2)
--
-- Dup on wire h yields the two label pairs
--    ( B_h, (G0 K_h^0, G0 K_h^1) )   and   ( B_h, (G1 K_h^0, G1 K_h^1) )
-- which are the input keys of gate 2.  Dup itself contributes epsilon.
-- ===================================================================

abbrev Ki0 : Expression 𝕂 := .VarK 0
abbrev Ki1 : Expression 𝕂 := .VarK 1
abbrev Kj0 : Expression 𝕂 := .VarK 2
abbrev Kj1 : Expression 𝕂 := .VarK 3
abbrev Kh0 : Expression 𝕂 := .VarK 4
abbrev Kh1 : Expression 𝕂 := .VarK 5
abbrev Km0 : Expression 𝕂 := .VarK 6
abbrev Km1 : Expression 𝕂 := .VarK 7

abbrev Bi : BitExpr := .VarB 0
abbrev Bj : BitExpr := .VarB 1
abbrev Bh : BitExpr := .VarB 2
abbrev Bm : BitExpr := .VarB 3

/-- one garbled table entry  ⦃⦃(b, k)⦄_{kin}⦄_{kout} -/
def ent (kout kin : Expression 𝕂) (b : BitExpr) (k : Expression 𝕂) :=
  Expression.Enc kout (Expression.Enc kin (Expression.Pair (Expression.BitE b) k))

/-- gate 1 : NAnd on wires i, j -> wire h.  NAND(1,1)=0, all others 1. -/
def C1 :=
  Expression.Perm (Expression.BitE Bi)
    (Expression.Perm (Expression.BitE Bj)
      (ent Ki0 Kj0 (.Not Bh) Kh1) (ent Ki0 Kj1 (.Not Bh) Kh1))
    (Expression.Perm (Expression.BitE Bj)
      (ent Ki1 Kj0 (.Not Bh) Kh1) (ent Ki1 Kj1 Bh Kh0))

/-- gate 2 : NAnd on the two Dup copies of wire h -> wire m. -/
def C2 :=
  Expression.Perm (Expression.BitE Bh)
    (Expression.Perm (Expression.BitE Bh)
      (ent (.G0 Kh0) (.G1 Kh0) (.Not Bm) Km1) (ent (.G0 Kh0) (.G1 Kh1) (.Not Bm) Km1))
    (Expression.Perm (Expression.BitE Bh)
      (ent (.G0 Kh1) (.G1 Kh0) (.Not Bm) Km1) (ent (.G0 Kh1) (.G1 Kh1) Bm Km0))

/-- garbled input for x = (0,0):  GEnc gives (B_i,K_i^0),(B_j,K_j^0); GMask gives B_m. -/
def xt :=
  Expression.Pair
    (Expression.Pair (Expression.Pair (Expression.BitE Bi) Ki0)
                     (Expression.Pair (Expression.BitE Bj) Kj0))
    (Expression.BitE Bm)

/-- Garble(C, (0,0)) = ((C1,C2), x~) -/
def e := Expression.Pair (Expression.Pair C1 C2) xt

-- ===================================================================
-- LM18 vocabulary, defined locally (absent from the library - see 4.7 item 6)
-- ===================================================================

-- `exprKeys`, `strictYields`, `isAtomicKey` and the corrected `keyRecovery` (with LM18's
-- ancestor clause) now live in PRGExtension/Expression/SymbolicIndistinguishability.lean,
-- so this file doubles as a regression check on them.

/-- every key expression occurring anywhere in `e` (= keySubterms e, as a list) -/
def cands : List (Expression 𝕂) :=
  [Ki0, Ki1, Kj0, Kj1, Kh0, Kh1, Km0, Km1,
   .G0 Kh0, .G1 Kh0, .G0 Kh1, .G1 Kh1]

def nameOf : Expression 𝕂 -> String
  | .VarK 0 => "K_i^0" | .VarK 1 => "K_i^1"
  | .VarK 2 => "K_j^0" | .VarK 3 => "K_j^1"
  | .VarK 4 => "K_h^0" | .VarK 5 => "K_h^1"
  | .VarK 6 => "K_m^0" | .VarK 7 => "K_m^1"
  | .VarK n => s!"K{n}"
  | .G0 k   => s!"G0({nameOf k})"
  | .G1 k   => s!"G1({nameOf k})"

def lst (S : Finset (Expression 𝕂)) : List String :=
  (cands.filter (fun k => decide (k ∈ S))).map nameOf

-- `rootsOf` (LM18 `Roots`) and `isAtomicKey` now live in the library, so we use those.

-- ===================================================================
-- greatest-fixpoint iteration, unrolled by hand.  `greatestFixpoint` starts at
-- `keySubterms e` and iterates `keyRecovery e` until the set stops changing,
-- so this reproduces `adversaryKeys e` exactly.
-- ===================================================================

def S0 := keySubterms e
def S1 := keyRecovery e S0
def S2 := keyRecovery e S1
def S3 := keyRecovery e S2
def S4 := keyRecovery e S3

#eval ("cards S0..S4", S0.card, S1.card, S2.card, S3.card, S4.card)
#eval ("S3 = S2?", decide (S3 = S2), " |  S4 = S3? (fixpoint)", decide (S4 = S3))

#eval ("S0 = keySubterms e", lst S0)
#eval ("S1", lst S1)
#eval ("S2", lst S2)
#eval ("S3 = adversaryKeys e", lst S3)

def view := hideEncrypted S3 e   -- = adversaryView e

#eval ("Keys(adversaryView e)", lst (exprKeys view))
#eval ("Roots(Keys(view))",     lst (rootsOf (exprKeys view)))
#eval ("NON-ATOMIC ROOTS",      lst ((rootsOf (exprKeys view)).filter (fun k => !isAtomicKey k)))
-- by `ancestorKeys_eq_empty_iff` this decides LM18 independence of Keys(view)
#eval ("Keys(view) independent (LM18)?", decide (ancestorKeys (exprKeys view) = ∅))

#eval ("K_h^0     in Keys(view)?", decide (Kh0 ∈ exprKeys view))
#eval ("G0(K_h^0) in Keys(view)?", decide ((Expression.G0 Kh0) ∈ exprKeys view))
#eval ("ancestor clause can fire on K_h^0?  (needs K_h^0 in Keys(view))",
        decide (Kh0 ∈ exprKeys view))
