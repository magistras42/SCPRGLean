-- imports

-- THIS WILL REPLACE SOUNDNESS.LEAN

theorem symbolicEquivalenceImpliesComputationalIndistinguishability
  (IsPolyTime : PolyFamOracleCompPred)
  (HPolyTime : PolyTimeClosedUnderComposition IsPolyTime)
  (enc : encryptionScheme) (HEncIndCpa : encryptionSchemeIndCpa IsPolyTime enc)
  (prg : prgScheme) (HPrgSecure : prgSchemeSecure IsPolyTime prg)
  -- Include polynomial time reduction assumptions for BOTH IND-CPA and PRG
  (HreductionCpa : forall enc prg shape expr key₀, IsPolyTime (reductionHidingOneKey enc prg expr key₀))
  (HreductionPrg : forall enc prg shape expr seed, IsPolyTime (reductionToPrgOracle enc prg expr seed))
  {shape : Shape} (e1 e2 : Expression shape)
  -- The symbolic game hop assumption:
  (H_equiv : symbolicEquivalence e1 e2) :
  -- The semantic guarantee:
  CompIndistinguishabilityDistr IsPolyTime
    (famDistrLift (exprToFamDistr enc prg e1))
    (famDistrLift (exprToFamDistr enc prg e2)) := by

  -- We prove this by induction on the structure of the symbolic game hops!
  induction H_equiv with

  | structural expr1 expr2 H_sym_ind =>
      -- 1. Use `symbolicToSemanticIndistinguishabilityAdversaryView` (from IND-CPA proof)
      -- 2. Use normalization/renaming lemmas to show structural equality implies distribution equality
      sorry

  | idealize_PRG expr targetSeed idx0 idx1 H_no_seed H_diff H_fresh0 H_fresh1 =>
      -- This matches the PRG theorem we just defined!
      apply symbolicToSemanticIndistinguishabilityPrgIdealization
      exact IsPolyTime
      -- ... pass assumptions

  | trans expr1 expr2 expr3 H1 H2 IH1 IH2 =>
      -- Use the transitivity of computational indistinguishability (`indTrans`)
      apply indTrans
      exact IH1
      exact IH2

  | symm expr1 expr2 H1 IH1 =>
      -- Use the symmetry of computational indistinguishability (`indSymm`)
      apply indSymm
      exact IH1
