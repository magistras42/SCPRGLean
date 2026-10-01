import PRGExtension
#print axioms PRG.garblingSecureFromEfficiency
#print axioms PRG.garblingSecure
#print axioms symbolicToSemanticSoundness
#print axioms PRG.fixpointStepSound
#print axioms PRG.theorem5
#print axioms PRG.lemma7
#print axioms PRG.lemma8
#print axioms PRG.prgRenameRel_substKeys_general
#print axioms PRG.adversaryView_eq_gStar
#print axioms PRG.theorem4_holds
#print axioms PRG.garbleCorrect
-- new
#print axioms PRG.garblingSecureFromCostModel
#print axioms PRG.encReduction_polyTime
#print axioms PRG.evalEfficiencyFromPrimitives_holds
#print axioms PRG.prgEnvSampler_polyTime
#print axioms PRG.shapeLength_poly
#print axioms PRG.redFn_polyTime
#print axioms PRG.evalExpr_polyTime
-- generated class (2026-09-21)
#print axioms PRG.genPolyTimeModel
#print axioms PRG.genBitOpsEfficient
#print axioms PRG.gen_encReduction_polyTime
#print axioms PRG.gen_efficientEvalPrg
#print axioms PRG.gen_prgEnvSampler_polyTime
#print axioms PRG.garblingSecureGenerated
#print axioms PRG.garblingSecureRelative
-- computational correctness (F9, 2026-09-21h)
#print axioms PRG.garbleCorrectComp
#print axioms PRG.gEvComp_sim
#print axioms PRG.decodeComp_correct
-- projectivity (2026-09-21i)
#print axioms PRG.Garble_projective
#print axioms PRG.gEncCorrect
-- executable implementation (FUTURE-WORK Half 1, 2026-09-28)
#print axioms PRG.evalExprExec_mem_support
#print axioms PRG.evalExprRun_mem_support_exprToDistr
#print axioms PRG.evalExprRun_mem_support_exprToFamDistr
#print axioms PRG.garbleExecCorrect
#print axioms PRG.garbleExec_mem_support
#print axioms PRG.garbleExec_projective
-- hole-freeness (FUTURE-WORK cost C2, 2026-09-28)
#print axioms PRG.holeFree_key
#print axioms PRG.holeFree_enc_exists
#print axioms PRG.gb_holeFree
#print axioms PRG.sim_holeFree
#print axioms PRG.garble_holeFree
#print axioms PRG.simulate_holeFree
-- the #eval-able implementation (FUTURE-WORK item 1, 2026-09-28)
#print axioms PRG.evalExprExecOn_mem_support
#print axioms PRG.ExecEnc.evalExprRun_mem_support
#print axioms PRG.ExecEnc.evalExprRun_mem_support_exprToDistr
#print axioms PRG.ExecEnc.garbleExecCorrect
#print axioms PRG.ExecEnc.garbleExec_mem_support
#print axioms PRG.ChaCha20.xorStream_xorStream
#print axioms PRG.chacha20Enc
-- the distributional refinement (FUTURE-WORK Half 2, 2026-09-28)
#print axioms PRG.map_equiv_uniformOfFintype
#print axioms PRG.uniformOfFintype_prod
#print axioms PRG.uniformFinArrow_bind_split
#print axioms PRG.evalExprExecOn_counter
#print axioms PRG.evalExprExecOn_coins_congr
#print axioms PRG.execDistr_eq
#print axioms PRG.execToDistr_eq
#print axioms PRG.ExecEncScheme.toFamDistr_eq
#print axioms PRG.garblingSecureExec
-- evaluator totality (FUTURE-WORK C2 follow-up, 2026-09-28)
#print axioms PRG.gEv_isSome_of_gb
#print axioms PRG.gEvComp_of_gb
#print axioms PRG.GEvalExpr_eq_EvaluateComp
-- variable-stretch expansion (the PRF hybrid, started 2026-09-29)
#print axioms PRG.uniformFinArrow_cons
#print axioms PRG.idealExpand_eq_uniform
#print axioms PRG.hybridExpand_zero
#print axioms PRG.hybridExpand_full
#print axioms PRG.hybridSeeded_succ
#print axioms PRG.expandRedRealEq
#print axioms PRG.expandRedIdealEq
#print axioms PRG.hybridStep
#print axioms PRG.expandKeys_indist_uniform
#print axioms PRG.expandKeys_indist_uniform_post
#print axioms PRG.ExecEnc.execToDistr_eq_bind
#print axioms PRG.garblingSecureExecSeeded

/-! ## Domain separation (`Crypto/DomainSeparation.lean`, added 2026-10-01 for FUTURE-WORK R2)

The separation facts need only `propext` — they are statements about the reserved nonce bit, with
no choice and no quotients anywhere. -/
#print axioms PRG.dsNonce_ne_of_tag
#print axioms PRG.dsNonceDisjoint
#print axioms PRG.dsPrgNonce_not_mem_range
#print axioms PRG.chacha20_ds_nonce_disjoint
#print axioms PRG.dsExecEnc_dec_run
#print axioms PRG.chacha20EncDS_dec_run
#print axioms PRG.oldNonceSpacesOverlap
