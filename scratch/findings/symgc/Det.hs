{-# LANGUAGE GADTs, DataKinds, TypeOperators, FlexibleInstances, ScopedTypeVariables, ExistentialQuantification #-}
module Main where

import qualified Data.HashSet as HashSet
import Data.HashSet (HashSet)
import Control.Monad (forM_)
import Expr
import Circuit
import Garble
import Proof

gstarIn :: HashSet (Exp KeyS) -> HashSet (Exp KeyS) -> HashSet (Exp KeyS)
gstarIn univ s = HashSet.union s (HashSet.filter inG univ)
  where inG k = any (\a -> a == k || yields a k) (HashSet.toList s)

patternLM18 :: Patternable a => a -> a
patternLM18 e = pp e (go (keys e) (30 :: Int))
  where univ = keys e
        go s 0 = s
        go s n = let s' = gstarIn univ (pr (pp e s))
                 in if s' == s then s else go s' (n-1)

tally :: PGC -> (Int,Int)
tally PEmptyGC = (0,0)
tally (a :&: b) = let (x,y) = tally a; (u,v) = tally b in (x+u, y+v)
tally (PTable t) = go t
  where go :: Pat s -> (Int,Int)
        go (PPair p q)   = add (go p) (go q)
        go (PPerm _ p q) = add (go p) (go q)
        go (PEnc _ p)    = add (1,0) (go p)
        go (PHide _ _)   = (0,1)
        go _             = (0,0)
        add (a',b') (c,d) = (a'+c, b'+d)

anyLiteralPerm :: PGC -> Bool
anyLiteralPerm PEmptyGC = False
anyLiteralPerm (a :&: b) = anyLiteralPerm a || anyLiteralPerm b
anyLiteralPerm (PTable t) = go t
  where go :: Pat s -> Bool
        go (PPair p q)   = go p || go q
        go (PPerm b p q) = isLit b || go p || go q
        go (PEnc _ p)    = go p
        go _             = False
        isLit (Bit _) = True
        isLit _       = False

data Case = forall s t. Case String (Circuit s t) (Wires Bool s)

cases :: [Case]
cases =
  [ Case "notC = CAT DUP NAND  [generator base case, x=F]" (CAT DUP NAND) (W False)
  , Case "notC                 [x=T]"                     (CAT DUP NAND) (W True)
  , Case "CAT NAND DUP         [2-wire base, FF]" (CAT NAND DUP) (W False :+: W False)
  , Case "CAT NAND DUP         [2-wire base, TT]" (CAT NAND DUP) (W True  :+: W True)
  , Case "andCircuit           [paper's example, TT]" andCircuit (W True :+: W True)
  , Case "andCircuit           [FT]"                  andCircuit (W False :+: W True)
  , Case "c_example            [Garble.hs example, TT]" c_example (W True :+: W True)
  , Case "CAT (CAT DUP NAND) (CAT DUP NAND)  [FF chain]" (CAT (CAT DUP NAND) (CAT DUP NAND)) (W False)
  ]

main :: IO ()
main = do
  putStrLn "circuit                                          SymGC(open/hole)  Def3(open/hole)  prop SymGC  prop Def3  norm-bug hit"
  putStrLn (replicate 118 '-')
  forM_ cases $ \(Case nm c w) -> do
    let g   = garble c w
        pg0 = garbledToPGarbled g
        (bm,km,v) = gbRenamings c w
        psg0 = garbledToPGarbled (simulate c v w)
        sym = pattern pg0
        lm  = patternLM18 pg0
        (o1,h1) = tally (pgb_c sym)
        (o2,h2) = tally (pgb_c lm)
        p1 = norm (renameKey (renameBit sym bm) km) == norm (pattern psg0)
        p2 = norm (renameKey (renameBit lm bm) km)  == norm (patternLM18 psg0)
        lit = anyLiteralPerm (pgb_c (norm sym))
    putStrLn $ pad 48 nm ++ pad 18 (show o1 ++ "/" ++ show h1)
             ++ pad 17 (show o2 ++ "/" ++ show h2)
             ++ pad 12 (show p1) ++ pad 11 (show p2) ++ show lit
  where pad n s = s ++ replicate (max 1 (n - length s)) ' '
