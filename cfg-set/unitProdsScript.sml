(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory relationTheory listTheory
open pred_setTheory regexpTheory grammarDefTheory listLemmaTheory
eProdsTheory

(* Rules of the form A->B, where A and B are in nonTerminals g *)
val unitProds = Define `unitProds g = {rule l r | ?nt.(r=[NTS nt]) /\ rule l r IN rules g}`;

(* A->*B where A and B are in nonTerminals g *)
val allDeps = Define `allDeps g = {(a,b) |  RTC (derives g) [a] [b]}`

val nonUnitProds = Define `nonUnitProds g = ((rules g) DIFF (unitProds g))`;

val newProds = Define `newProds g p' = {rule a r | ?b.(rule b r IN p' /\ (NTS a,NTS b) IN allDeps (G (unitProds g) (startSym g)))}`;

val upgr_rules = Define `(upgr_rules g =  (nonUnitProds g) UNION (newProds g (nonUnitProds g)))`;

val upgr = Define `upgr g = G (upgr_rules g) (startSym g)`;

val upgr_runs = prove (
``rules (upgr g) = (nonUnitProds g) UNION (newProds g (nonUnitProds g))``,
Cases_on `g` THEN SRW_TAC [] [upgr_rules,rules_def,upgr]
);

val eq_supgr = prove(
``startSym g = startSym (upgr g)``,
Cases_on `g` THEN METIS_TAC [startSym_def,upgr]
);


val eq_sneup = prove(
``startSym (negr g) = startSym (upgr g)``,
Cases_on `g` THEN METIS_TAC [startSym_def,upgr,negr_def]
);

(*
Theorem 4.4
Every CFL without e is defined by a grammar with no useless symbols,e-productions, or unit productions.
*)

val upgr_r1 = prove (
``derives (G (unitProds (negr g)) (startSym (negr g))) v v' ==> derives (G (rules (negr g)) (startSym (negr g))) v v'``,
FULL_SIMP_TAC (srw_ss()) [unitProds,rules_def,derives_def,eq_sneup] THEN
METIS_TAC []
);


val upgr_r2 = prove(
``!u v.RTC (derives (G (unitProds (negr g)) (startSym (negr g)))) u v ==> RTC (derives (G (rules (negr g)) (startSym (negr g)))) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
METIS_TAC [RTC_RULES,upgr_r1, RTC_SUBSET,RTC_RULES_RIGHT1]
);


val upgr_r3 = prove(
``!v v'.derives (upgr (negr g)) v v' ==> RTC (derives (negr g)) v v'``,
SRW_TAC [] [derives_def, upgr_runs, nonUnitProds,newProds,allDeps] 
THENL[
 METIS_TAC [res1,derives_same_append_left,derives_same_append_right,RTC_SUBSET],
Cases_on `g` THEN
`RTC (derives (G (rules (negr (G f s))) (startSym (negr (G f s))))) [NTS lhs] [NTS b]` by METIS_TAC [upgr_r2] THEN
`derives (negr (G f s)) [NTS b] rhs` by METIS_TAC [res1] THEN
FULL_SIMP_TAC (srw_ss()) [eq_sneup,startSym_def,rules_def] THEN
`RTC (derives (negr (G f s))) [NTS lhs] rhs` by METIS_TAC [RTC_RULES_RIGHT1,eq_sneup,eq_snegr,negr_runs,negr_def,rules_def] THEN
METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left]
]);


val upgr_r4 = prove(
``!u v.RTC (derives (upgr (negr g))) u v ==> RTC (derives (negr g)) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [upgr_r3,RTC_RTC]
);

val upgr_r5 = prove(
``derives (negr g) v v' ==> EVERY isTmnlSym v' ==> derives (upgr (negr g)) v v'``,
SRW_TAC [] [derives_def,upgr_runs,nonUnitProds,newProds,allDeps] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN
SRW_TAC [] [] THEN
DISJ1_TAC THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,unitProds] THEN
SRW_TAC [] [] THEN
`!e. MEM e rhs ==> isTmnlSym e` by FULL_SIMP_TAC (srw_ss()) [EVERY_MEM] THEN
`~  (rhs = [] ++ [NTS nt] ++ []) /\ isNonTmnlSym (NTS nt)` by METIS_TAC [sym_r3,isNonTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) []
);


val upgr_r6 = prove(
``RTC (derives (negr g)) [NTS x] [NTS y] ==> (NTS x IN nonTerminals (negr g)) ==>(NTS y IN nonTerminals (negr g))  ==>  (NTS x,NTS y) IN (allDeps (negr g))``,
SRW_TAC [] [allDeps] THEN SRW_TAC [] []
);

val negr_r16 = prove(
``!v v'.derives (negr g) v v' ==> ~(v'=[])``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,negr_runs,munge_def] THEN
SRW_TAC [] []
);


val negr_r17 = prove(
``rule l r IN rules (negr g) ==> ~(r=[])``,
SRW_TAC [] [negr_runs,munge_def]
);

val eqSymsToStr = Define (`(eqSyms (NTS nt1) (NTS nt2) = (nt1=nt2))
/\ (eqSyms (TS ts1) (TS ts2) = (ts1=ts2))`);


val eqNTs = Define (`(eqNTs (nt1) (nt2) = (NTS nt1 = NTS nt2))`)


val rel_r1 = prove(
``!x y.RTC R x y /\ ~(x=y) ==> TC R x y``,
SRW_TAC [] [] THEN
`RC R x y \/ TC R x y` by METIS_TAC [RTC_TC_RC]  THEN
FULL_SIMP_TAC (srw_ss()) [RC_DEF] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_TRANSITIVE,TC_DEF]
);


val upgr_r8 = prove(
``derives (negr g) [NTS lhs] [NTS nt] ==> derives (negr g) [NTS nt] r ==> ~(?n.r=[NTS n]) ==> derives (upgr (negr g)) [NTS lhs] r``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [upgr_runs] THEN
`(s1=[]) /\ (s2=[]) /\ (s1'=[]) /\ (s2'=[])` by METIS_TAC [lres] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
SRW_TAC [] [upgr_runs] THEN
DISJ2_TAC THEN
SRW_TAC [] [nonUnitProds,allDeps,newProds ] THEN
Q.EXISTS_TAC `lhs''` THEN
SRW_TAC [] [] THENL[
 SRW_TAC [] [unitProds],
 MATCH_MP_TAC RTC_SUBSET THEN
`derives (negr g) [NTS lhs] [NTS lhs'']` by METIS_TAC [res1] THEN
 SRW_TAC [] [unitProds,derives_def,rules_def] THEN
 METIS_TAC [APPEND]
]);
 

val upgr_r9 = prove(
``derives (upgr g) [NTS n] v ==> ?nt. RTC (derives (G (unitProds g) (startSym g))) [NTS n] [NTS nt] /\ derives g [NTS nt] v``,
SRW_TAC [] [derives_def] THEN
`(s1=[]) /\ (s2=[]) /\ (NTS lhs= NTS n)` by METIS_TAC [lres] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [upgr_runs] THENL[
Q.EXISTS_TAC `lhs` THEN
SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [nonUnitProds] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`lhs`] THEN
SRW_TAC [] [],

FULL_SIMP_TAC (srw_ss()) [newProds,allDeps] THEN
Q.EXISTS_TAC `b` THEN
SRW_TAC [] [] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`b`] THEN
FULL_SIMP_TAC (srw_ss()) [nonUnitProds]
])


val upgr_r10 = prove(
``derives (negr g) [NTS nt1] [NTS nt2] ==> derives (G (unitProds (negr g)) (startSym (negr g))) [NTS nt1] [NTS nt2]``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
SRW_TAC [] [rules_def,unitProds] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] []
);


val upgr_r12 = prove(
``rule l r IN rules (upgr g) ==> ~(rule l r IN unitProds g)``,
SRW_TAC [] [unitProds,upgr_runs] THENL[
FULL_SIMP_TAC (srw_ss()) [nonUnitProds,unitProds] THEN METIS_TAC [],
FULL_SIMP_TAC (srw_ss()) [newProds,nonUnitProds,allDeps,unitProds] THEN METIS_TAC []
]);



val upgr_r13 = prove(
``rule l r IN rules (upgr g) ==> ~(?n.r=[NTS n])``,
SRW_TAC [] [] THEN
`~(rule l r IN unitProds g)` by METIS_TAC [upgr_r12]THEN
FULL_SIMP_TAC (srw_ss()) [unitProds,upgr_runs] THENL[
FULL_SIMP_TAC (srw_ss()) [nonUnitProds,unitProds] THEN METIS_TAC [],
FULL_SIMP_TAC (srw_ss()) [nonUnitProds,newProds,allDeps,unitProds] THEN METIS_TAC []
]);


val upgr_r14 = prove(
``derives (negr g) [NTS nt1] [NTS nt2] ==> derives (upgr (negr g)) [NTS nt2] v ==> derives (upgr (negr g)) [NTS nt1] v``,
SRW_TAC [] [] THEN 
`?nt. RTC (derives (G (unitProds (negr g)) (startSym (negr g)))) [NTS nt2] [NTS nt] /\ derives (negr g) [NTS nt] v` by METIS_TAC [upgr_r9] THEN

`derives (G (unitProds (negr g)) (startSym (negr g))) [NTS nt1] [NTS nt2]` by METIS_TAC [upgr_r10] THEN
`RTC (derives (G (unitProds (negr g)) (startSym (negr g)))) [NTS nt1] [NTS nt]` by METIS_TAC [RTC_RULES] THEN
SRW_TAC [] [derives_def,upgr_runs] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`v`,`nt1`] THEN
SRW_TAC [] [] THEN
DISJ2_TAC THEN
SRW_TAC [] [nonUnitProds,newProds,allDeps] THEN
Q.EXISTS_TAC `nt` THEN
SRW_TAC [] [] THENL[
      FULL_SIMP_TAC (srw_ss()) [derives_def] THEN FULL_SIMP_TAC (srw_ss()) [lreseq] THEN SRW_TAC [] [],
      FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN
`~ ?n. v = [NTS n]` by METIS_TAC [upgr_r13] THEN SRW_TAC [] [unitProds]
]);


val up_r1 = prove (
``rule lhs (s1++[NTS nt]++s2) IN unitProds g = (s1=[]) /\ (s2=[]) /\ rule lhs [NTS nt] IN unitProds g``,
SRW_TAC [][EQ_IMP_THM] THENL[

FULL_SIMP_TAC (srw_ss()) [unitProds] THEN METIS_TAC [lres],

FULL_SIMP_TAC (srw_ss()) [unitProds] THEN METIS_TAC [lres],

FULL_SIMP_TAC (srw_ss()) [unitProds] THEN METIS_TAC [lres]
]);


val up_r2 = prove(
``rule lhs rhs IN unitProds (negr g) ==> rule lhs rhs IN rules (negr g)``,
SRW_TAC [] [unitProds]
);

val upgr_r20 = prove(
``!u v.RTC (derives (negr g)) u v ==> EVERY isTmnlSym v ==> RTC (derives (upgr (negr g))) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`?s1' rhs' s2'. (v = s1' ++  rhs' ++ s2') /\ RTC (derives (upgr(negr g))) s1 s1' /\ RTC (derives (upgr (negr g))) rhs rhs' /\ RTC (derives (upgr (negr g))) s2 s2'` by SRW_TAC [] [upgr_r19] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND] THEN
`derives (negr g) [NTS lhs] rhs` by METIS_TAC [res1] THEN
Cases_on `rhs=rhs'` THENL[
  SRW_TAC [] [] THEN METIS_TAC [derives_append,upgr_r5,RTC_SUBSET,RTC_RULES,RTC_REFLEXIVE],
  `?sf.derives (upgr(negr g)) rhs sf /\ RTC (derives (upgr (negr g))) sf rhs'` by METIS_TAC [rtc_r1] THEN
  Cases_on `~(rule lhs rhs IN unitProds (negr g))` THENL[
    SRW_TAC [] [] THEN   `rule lhs rhs IN rules (upgr(negr g))` by FULL_SIMP_TAC (srw_ss()) [unitProds,upgr_runs] THENL[
      DISJ1_TAC THEN FULL_SIMP_TAC (srw_ss()) [nonUnitProds,unitProds] THEN METIS_TAC [RTC_SUBSET, res1, derives_append,RTC_RULES],
      SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [derives_def] THEN SRW_TAC [] [] THEN 
      METIS_TAC [res1,derives_same_append_right,derives_same_append_left,RTC_RULES]],
   SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [derives_def] THEN SRW_TAC [] [] 
   THEN  `(s1'''=[]) /\ (s2'''=[]) /\ rule lhs [NTS lhs''] IN unitProds (negr g)` by METIS_TAC [up_r1] THEN
`rule lhs [NTS lhs''] IN rules (negr g)` by METIS_TAC [up_r2] THEN
`derives (upgr (negr g)) [NTS lhs] rhs'''`by METIS_TAC [res1,upgr_r14] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES,derives_append]]]
);



(* Should this be just upgr g????????*)
val thm4_4 = prove(
``~([] IN language g) ==> (language (negr g) = language (upgr (negr g)))``,
SRW_TAC [] [language_def,EXTENSION,EQ_IMP_THM]
THENL[
METIS_TAC [upgr_r20,eq_supgr],
METIS_TAC [upgr_r4,eq_supgr]
])


val _ = export_theory ();
