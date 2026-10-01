{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, DeriveGeneric, FlexibleInstances #-}
module Proof where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Expr
import Circuit
import Garble

type PGTable = Pat ((GTEntryS :*: GTEntryS) :*: (GTEntryS :*: GTEntryS))
type PWLabel = Pat (BitS :*: (KeyS :*: KeyS))

data PGC = PEmptyGC | PTable PGTable | PGC :&: PGC
  deriving (Eq,Show)

gcToPGC :: GC -> PGC
gcToPGC EmptyGC = PEmptyGC
gcToPGC (Table t) = PTable (expToPat t)
gcToPGC (gc0 :/: gc1) = (gcToPGC gc0) :&: (gcToPGC gc1)

wireExpToPat :: Wires (Exp s) w -> Wires (Pat s) w
wireExpToPat (W e) = W (expToPat e)
wireExpToPat (u :+: v) = (wireExpToPat u) :+: (wireExpToPat v)

instance Patternable PGC where
  keys PEmptyGC   = HashSet.empty
  keys (PTable t) = keys t
  keys (pgc0 :&: pgc1) = HashSet.union (keys pgc0) (keys pgc1)
  keysInParts PEmptyGC   = HashSet.empty
  keysInParts (PTable t) = keysInParts t
  keysInParts (pgc0 :&: pgc1) = HashSet.union (keysInParts pgc0) (keysInParts pgc1)
  pp PEmptyGC _ = PEmptyGC
  pp (PTable t) ks = PTable (pp t ks)
  pp (pgc0 :&: pgc1) ks = (pp pgc0 ks) :&: (pp pgc1 ks)
  norm PEmptyGC = PEmptyGC
  norm (PTable t) = PTable (norm t)
  norm (pgc0 :&: pgc1) = (norm pgc0) :&: (norm pgc1)
  renameBit PEmptyGC _ = PEmptyGC
  renameBit (PTable t) hm = PTable (renameBit t hm)
  renameBit (pgc0 :&: pgc1) hm = (renameBit pgc0 hm) :&: (renameBit pgc1 hm)
  renameKey PEmptyGC _ = PEmptyGC
  renameKey (PTable t) hm = PTable (renameKey t hm)
  renameKey (pgc0 :&: pgc1) hm = (renameKey pgc0 hm) :&: (renameKey pgc1 hm)

instance Patternable p => Patternable (Wires p w) where
  keys (W e) = keys e
  keys (u :+: v) = HashSet.union (keys u) (keys v)
  keysInParts (W e) = keysInParts e
  keysInParts (u :+: v) = HashSet.union (keysInParts u) (keysInParts v)
  pp (W e) ks     = W (pp e ks)
  pp (u :+: v) ks = (pp u ks) :+: (pp v ks)
  norm (W e)     = W (norm e)
  norm (u :+: v) = (norm u) :+: (norm v)
  renameBit (W e) hm     = W (renameBit e hm)
  renameBit (u :+: v) hm = (renameBit u hm) :+: (renameBit v hm)
  renameKey (W e) hm     = W (renameKey e hm)
  renameKey (u :+: v) hm = (renameKey u hm) :+: (renameKey v hm)

data PGarbled s t = PGarbled {
  pgb_c :: PGC,
  pgb_x :: Wires (Pat (BitS :*: KeyS)) s,
  pgb_m :: Wires (Pat BitS) t
  } deriving (Show,Eq)

instance Patternable (PGarbled s t) where
  keys pg = HashSet.union (keys (pgb_c pg))
                          (HashSet.union (keys (pgb_x pg)) (keys (pgb_m pg)))
  keysInParts pg = HashSet.union (keysInParts (pgb_c pg))
                                 (HashSet.union (keysInParts (pgb_x pg))
                                                (keysInParts (pgb_m pg)))
  pp pg ks = PGarbled (pp (pgb_c pg) ks) (pp (pgb_x pg) ks) (pp (pgb_m pg) ks)
  norm pg  = PGarbled (norm (pgb_c pg)) (norm (pgb_x pg)) (norm (pgb_m pg))
  renameBit pg hm = PGarbled (renameBit (pgb_c pg) hm) (renameBit (pgb_x pg) hm) (renameBit (pgb_m pg) hm)
  renameKey pg hm = PGarbled (renameKey (pgb_c pg) hm) (renameKey (pgb_x pg) hm) (renameKey (pgb_m pg) hm)

garbledToPGarbled :: Garbled s t -> PGarbled s t
garbledToPGarbled (Garbled gc gx m) = PGarbled (gcToPGC gc) (wireExpToPat gx) (wireExpToPat m)

bitRenamingFor :: Bool -> Exp BitS -> BitRenaming
bitRenamingFor False _ = HashMap.empty
bitRenamingFor True  b = HashMap.singleton b (Not b)

keyRenamingFor :: Bool -> (Exp KeyS, Exp KeyS) -> KeyRenaming
keyRenamingFor False _       = HashMap.empty
keyRenamingFor True  (k0,k1) = HashMap.insert k1 k0 (HashMap.singleton k0 k1)

getInputRenamings :: Wires Bool s -> WireM (BitRenaming,KeyRenaming)
getInputRenamings (W z) = do
  Pair b (Pair k0 k1) <- getWireLabel
  return (bitRenamingFor z b, keyRenamingFor z (k0,k1))
getInputRenamings (u :+: v) = do
  (bmu,kmu) <- getInputRenamings u
  (bmv,kmv) <- getInputRenamings v
  return (HashMap.union bmu bmv, HashMap.union kmu kmv)

getOutputRenamings :: Circuit s t -> BitRenaming -> KeyRenaming -> Wires Bool s
                   -> WireM (BitRenaming,KeyRenaming,Wires Bool t)
getOutputRenamings SWAP  bm km (u :+: v)           = pure (bm,km,(v :+: u))
getOutputRenamings ASSOC bm km (u :+: (v :+: w))   = pure (bm,km,((u :+: v) :+: w))
getOutputRenamings UNASSOC bm km ((u :+: v) :+: w) = pure (bm,km,(u :+: (v :+: w)))
getOutputRenamings (CAT c0 c1) bm km w = do
  (bm',km',u)   <- getOutputRenamings c0 bm km w
  (bm'',km'',v) <- getOutputRenamings c1 bm' km' u
  return (bm'',km'',v)
getOutputRenamings (FIRST c) bm km (u :+: w) = do
  (bm',km',v)   <- getOutputRenamings c bm km u
  return (bm',km',(v :+: w))
getOutputRenamings DUP bm km w = pure (bm,km,(w :+: w))
getOutputRenamings NAND bm km (W x :+: W y) = do
  Pair b (Pair k0 k1) <- getWireLabel
  let z   = not (x && y)
      bm' = bitRenamingFor z b
      km' = keyRenamingFor z (k0,k1)
  return (HashMap.union bm' bm, HashMap.union km' km, W z)

gbRenamings :: Circuit s t -> Wires Bool s -> (BitRenaming,KeyRenaming,Wires Bool t)
gbRenamings c u = evalWireM genRenamings where
  genRenamings = do
    (ibm,ikm)   <- getInputRenamings u
    (obm,okm,v) <- getOutputRenamings c ibm ikm u
    return (obm,okm,v)
