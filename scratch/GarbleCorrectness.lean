import PRGExtension.Garbling.Evaluation
open PRG

-- LM18 Theorem 4 checked by evaluation on small circuits.  `notC`, `andC` and `orC` all
-- contain `Dup`, so the PRG path in both `Gb` and `GEv` is exercised.
-- Run with:  lake env lean scratch/GarbleCorrectness.lean
--
-- NB: `Circuits.lean` declares `notation "(" o1 "," o2 ")"` for `WireBundle.PairB`, which
-- shadows ordinary tuple syntax in this file; hence the explicit `WireBundle.PairB`
-- and the string-based reporting below.

def one1 (c : Circuit o o) (x : Bool) : String :=
  let r : Option Bool := testGarbleEval c x
  let y : Bool := evalCircuit c x
  s!"  {x} -> {reprStr r}  ok={decide (r = some y)}"

def report1 (name : String) (c : Circuit o o) : List String :=
  name :: ([false, true].map (one1 c))

def one2 (c : Circuit (WireBundle.PairB o o) o) (a b : Bool) : String :=
  let x : bundleBool (WireBundle.PairB o o) := Prod.mk a b
  let r : Option Bool := testGarbleEval c x
  let y : Bool := evalCircuit c x
  s!"  {a},{b} -> {reprStr r}  ok={decide (r = some y)}"

def report2 (name : String) (c : Circuit (WireBundle.PairB o o) o) : List String :=
  name :: [one2 c false false, one2 c false true, one2 c true false, one2 c true true]

#eval report1 "notC = Dup >>> NAnd" notC
#eval report2 "NAnd" Circuit.NandC
#eval report2 "andC = NAnd >>> notC" andC
#eval report2 "orC  = (notC x notC) >>> NAnd" orC
