(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory arithmeticTheory;
open pred_setTheory;

val _ = new_theory "setLemmas";

val set_l1 = store_thm ("set_l1",
``!s. FINITE s ==> !f. 0 < SIGMA f s ==> ?e. e IN s /\ 0 < f e``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [SUM_IMAGE_THM] THEN
`0 < f e + SIGMA f s` by METIS_TAC [DELETE_NON_ELEMENT] THEN
Cases_on `f e = 0` THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
`0 < f e` by FULL_SIMP_TAC arith_ss [] THEN METIS_TAC []
])


val set_l2 = store_thm ("set_l2",
``!s. FINITE s ==> !f.((?e. e IN s /\ 0 < f e) ==> 0 < SIGMA f s)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
SRW_TAC [] [SUM_IMAGE_THM,FINITE_SING] THEN DECIDE_TAC,
SRW_TAC [] [SUM_IMAGE_THM,FINITE_SING] THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
FULL_SIMP_TAC (srw_ss()) [Once DECOMPOSITION] THEN
`FINITE t` by METIS_TAC [INSERT_SING_UNION,FINITE_UNION] THEN
SRW_TAC [] [SUM_IMAGE_THM,FINITE_UNION] THEN DECIDE_TAC
])

val set_l3 = store_thm ("set_l3",
``!s. FINITE s ==> !f.((?e. e IN s /\ n <= f e) ==> n <= SIGMA f s)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
SRW_TAC [] [SUM_IMAGE_THM,FINITE_SING] THEN DECIDE_TAC,
SRW_TAC [] [SUM_IMAGE_THM,FINITE_SING] THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
FULL_SIMP_TAC (srw_ss()) [Once DECOMPOSITION] THEN
`FINITE t` by METIS_TAC [INSERT_SING_UNION,FINITE_UNION] THEN
SRW_TAC [] [SUM_IMAGE_THM,FINITE_UNION] THEN DECIDE_TAC
])

val inter_l1 = store_thm ("inter_l1",
``!s e.e IN s ==> (s INTER {e} = {e})``,
SRW_TAC [] [EXTENSION,EQ_IMP_THM]
)

val inter_l2 = store_thm ("inter_l2",
``!s e.~(e IN s) ==> (s INTER {e} = {})``,
SRW_TAC [] [EXTENSION,EQ_IMP_THM]
)
 

val set_l4 = store_thm ("set_l4",
``!s.FINITE s ==> !f.(SIGMA f s = 0) ==> (!e. e IN s ==> (f e = 0))``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THEN
(FULL_SIMP_TAC (srw_ss()) [Once INSERT_SING_UNION] THEN
`SIGMA f {e} + SIGMA f s - SIGMA f ({e} INTER s) = 0` by METIS_TAC [FINITE_SING,SUM_IMAGE_UNION] THEN
`{e} INTER s = {}` by METIS_TAC [inter_l2,INTER_COMM] THEN
FULL_SIMP_TAC (srw_ss()) [SUM_IMAGE_THM])
)

val f_diff1 = store_thm ("f_diff1",
``!s1.FINITE s1 ==> !f s2.SIGMA f (s1 INTER s2) <= SIGMA f s1``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [SUM_IMAGE_THM] THEN
FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
Cases_on `e IN s2` THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [SUM_IMAGE_THM] THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
`(s1 INTER s2 DELETE e)=(s1 DELETE e) INTER s2` by SRW_TAC [] [DELETE_INTER] THEN
ASM_REWRITE_TAC [],
Cases_on `f e` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT],
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [DELETE_NON_ELEMENT] THEN
`0 <= SUC n` by FULL_SIMP_TAC arith_ss [] THEN
`0 + SIGMA f (s1 INTER s2) <=  SUC n +SIGMA f s1` by FULL_SIMP_TAC (srw_ss()) [LESS_EQ_LESS_EQ_MONO] THEN
DECIDE_TAC]]
)

val f_diff = store_thm("f_diff",
``!s1.FINITE s1 ==> !f s2.(SIGMA f (s1 DIFF s2)) = SIGMA f s1 - SIGMA f (s1 INTER s2)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [SUM_IMAGE_THM] THENL[
Cases_on `e IN s2` THEN
FULL_SIMP_TAC (srw_ss()) [SUM_IMAGE_THM,INSERT_INTER,SUM_IMAGE_DELETE] THENL[
DECIDE_TAC, 

FULL_SIMP_TAC (srw_ss()) [SUM_IMAGE_THM,INSERT_INTER,INSERT_DIFF,SUM_IMAGE_DELETE,FINITE_DIFF] THEN
`SIGMA f (s1 INTER s2) <= SIGMA f s1`  by METIS_TAC [f_diff1] THEN
DECIDE_TAC]])


val set_neq = store_thm("set_neq", 
``!s2.FINITE s2 ==> !s1.FINITE s1 ==>
(CARD s1 > CARD s2) ==> ?e.(~(e IN s2) /\ (e IN s1))``,
SRW_TAC [] [] THEN
Q_TAC SUFF_TAC `~(s1 SUBSET s2)` THENL[
METIS_TAC [SUBSET_DEF],
METIS_TAC [CARD_SUBSET, DECIDE ``~(x<y /\ y<=x)``, GREATER_DEF]])

val insert_absorption = store_thm ("insert_absorption", 
``!s.FINITE s ==> (e IN s) ==> ((e INSERT s) = s)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [] [] THEN
METIS_TAC [INSERT_INSERT, INSERT_COMM])



val inter_card_less = store_thm ("inter_card_less", 
``!s1.FINITE s1 ==> e IN s1 ==> ~(e IN s2) ==> CARD s1 - (CARD (s1 INTER s2)) > 0``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
`CARD (s1 INTER s2) <= CARD s1` by METIS_TAC [CARD_INTER_LESS_EQ] THEN
FULL_SIMP_TAC (arith_ss) [],
FULL_SIMP_TAC (srw_ss()) [INSERT_INTER] THEN
`CARD (s1 INTER s2) <= CARD s1` by METIS_TAC [CARD_INTER_LESS_EQ] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
Cases_on `e' IN s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (arith_ss) []])

val subset_inter = store_thm ("subset_inter", 
``!s2.FINITE s2 ==> !s1.s1 SUBSET s2 ==> !t.(s1 INTER t) SUBSET  (s2 INTER t)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [] [] THEN
`!e.e IN s1 ==> e IN (e INSERT s2)` by FULL_SIMP_TAC (srw_ss()) [] THEN
`!e.e IN (s1 INTER t) ==> e IN (e INSERT s2)` by FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF])


val card_same_inter = store_thm ("card_same_inter", 
``!s2.FINITE s2 ==> s1 PSUBSET s2 ==> 
~(e IN s1) ==> (e IN s2) ==> (e IN t) ==>
CARD (s1 INTER t) < CARD (s2 INTER t)``,
SRW_TAC [] [] THEN
`CARD s1 < CARD s2` by METIS_TAC [CARD_PSUBSET] THEN
`s1 SUBSET s2 /\ ~(s1=s2)` by METIS_TAC [PSUBSET_DEF] THEN
`!e.e IN s1 ==> e IN s2` by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
`CARD (s1 INTER t) <= CARD s1` by METIS_TAC [CARD_INTER_LESS_EQ, PSUBSET_FINITE] THEN
`CARD (s2 INTER t) <= CARD s2` by METIS_TAC [CARD_INTER_LESS_EQ] THEN
`(s1 INTER t) SUBSET (s2 INTER t)` by METIS_TAC [subset_inter] THEN
`e IN (s2 INTER t)` by FULL_SIMP_TAC (srw_ss()) [] THEN
`~(e IN (s1 INTER t))` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [PSUBSET_DEF, PSUBSET_FINITE, CARD_PSUBSET, INTER_FINITE])

val insert_union = store_thm ("insert_union", 
``(s1 UNION (x INSERT s2)) = x INSERT (s1 UNION s2)``,
SRW_TAC [] [EXTENSION,EQ_IMP_THM] THEN
METIS_TAC [])

val setc_mem_in = store_thm ("setc_mem_in",
``{e | e IN LIST_TO_SET l} = {e | MEM e l}``,
SRW_TAC [] [EXTENSION])


val not_in_inter = store_thm ("not_in_inter", 
``!s1.FINITE s1 ==> e IN s1 ==> ~(e IN s2) ==> ~(e IN (s1 INTER s2))``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [] [])




val _ = export_theory ();
