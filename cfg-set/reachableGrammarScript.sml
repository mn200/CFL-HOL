(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory relationTheory listTheory;
open pred_setTheory grammarDefTheory listLemmaTheory;

val _ = new_theory "reachableGrammar";

val rgr = Define `rgr g = G { rule l r | rule l r IN (rules g) /\ ?a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b)} (startSym g)`;

val eq_srgr = store_thm ("eq_srgr",
``startSym (rgr g) = startSym g``,
Cases_on `g` THEN METIS_TAC [startSym_def,rgr]
);

val rgr_runs = prove(
``rules (rgr g) = {rule l r | rule l r IN rules g /\ (? a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b))}``,
Cases_on `g` THEN SRW_TAC [] [rules_def,rgr,startSym_def,rules_def]);


val rgr_subr1 = prove(
``!l r. rule l r IN rules (rgr g) ==> rule l r IN rules g ``,
Cases_on `g` THEN SRW_TAC [] [rules_def,rgr]
);

val rgr_subr2 = prove(
``! a b.derives (rgr g) a b ==> derives g a b``,
 Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [rgr,derives_def,rules_def,gaw_def] THEN SRW_TAC [] [] THEN 
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] []);

val rgr_subr3 = prove(
``!v.derives g [NTS (startSym g)] v ==> derives (rgr g) [NTS (startSym (rgr g))] v``,
Cases_on `g` THEN
SRW_TAC [] [startSym_def,eq_srgr] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,rules_def,rgr] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`] THEN
ASM_REWRITE_TAC [RTC_RULES] 
);

val rgr_subr3g = prove(
``!u v.derives g u v ==> (u=[NTS (startSym g)]) ==> derives (rgr g) u v``,
METIS_TAC [rgr_subr3,startSym_def,eq_srgr]
);


val rgr_subr3_rtc = store_thm ("rgr_subr3_rtc",
``!u v.RTC (derives (rgr g)) u v ==> RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_INDUCT THEN
SRW_TAC [] [] THENL
[
SRW_TAC [] [RTC_RULES],
METIS_TAC [rgr_subr2,RTC_RULES]
]
);

val rgr_subr3b = prove(
``!u v.(u=[NTS (startSym (rgr g))]) ==> derives g u v ==> derives (rgr g) u v``,
Cases_on `g`THEN SRW_TAC [] [eq_srgr,startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,rules_def,rgr] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] [startSym_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`] THEN
ASM_REWRITE_TAC [RTC_RULES] 
);

val rgr_r1 = prove(
``rule l r IN rules g ==> (?a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b)) ==> rule l r IN rules (rgr g)``,
Cases_on `g` THEN
SRW_TAC [] [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def,rgr,startSym_def] THEN
MAP_EVERY Q.EXISTS_TAC [`a`,`b`] THEN
SRW_TAC [] []
);

val rgr_r2 = prove (
``rule l r IN rules g ==> (? a b.RTC (derives (rgr g)) [NTS (startSym g)] (a++[NTS l]++b)) ==> rule l r IN rules (rgr g)``,SRW_TAC [] [] THEN
Cases_on `g` THEN 
FULL_SIMP_TAC (srw_ss()) [startSym_def,rgr_runs] THEN
MAP_EVERY Q.EXISTS_TAC [`a`,`b`] THEN
METIS_TAC [rgr_subr3_rtc]
);

val rgr_r3 = prove(
``derives g [NTS l] r ==> (?a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b)) ==> rule l r IN rules (rgr g)``,
Cases_on `g` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def,rules_def,rgr,derives_def]  THEN
SRW_TAC [] [] THENL
[
`(s1=[]) /\ (s2=[])`  by METIS_TAC [slres2] THEN
`rule l rhs IN f`  by FULL_SIMP_TAC (srw_ss()) [slres] THEN
ASM_REWRITE_TAC [] THEN
SRW_TAC [] [],
MAP_EVERY Q.EXISTS_TAC [`a`,`b`] THEN
SRW_TAC [] []
]
);

val rgr_r4 = prove(
``(? a b.RTC (derives (rgr g)) [NTS (startSym g)] (a++[NTS l]++b)) ==> derives g [NTS l] r ==> derives  (rgr g) [NTS l] r``,
Cases_on `g` THEN
SRW_TAC [] [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN
SRW_TAC [] [] THEN
`RTC (derives (rgr (G f s))) [NTS s] (a ++ [NTS lhs] ++ b)` by METIS_TAC [slres] THEN
METIS_TAC [rgr_r2,rgr_runs,slres,startSym_def]
);

val rgr_r6 = prove(
``derives g [NTS (startSym g)] v = derives (rgr g) [NTS (startSym (rgr g))] v``,
METIS_TAC [rgr_subr2,rgr_subr3,eq_srgr]
);



val rgr_r5 = prove(
``(? a b.RTC (derives (rgr g)) [NTS (startSym g)] (a++[NTS l]++b)) ==> derives g [NTS l] v' ==> (? x y.RTC (derives (rgr g)) [NTS (startSym g)] (x++v'++y))``,
Cases_on `g` THEN
SRW_TAC [] [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,startSym_def] THEN
` lhs=l` by METIS_TAC [slres] THEN
`(s1=[]) /\ (s2=[])`  by METIS_TAC [slres2] THEN
`rhs=v'` by FULL_SIMP_TAC (srw_ss()) [] THEN
`derives (rgr (G f s)) [NTS l] v'` by METIS_TAC [rgr_r4,startSym_def,res1] THEN
`derives (rgr (G f s)) (a++[NTS l]++b) (a++v'++b)` by METIS_TAC [derives_same_append_right,derives_same_append_left] THEN
MAP_EVERY Q.EXISTS_TAC [`a`,`b`] THEN
METIS_TAC [RTC_RULES_RIGHT1] 
);

val rgr_r7 = store_thm("rgr_r7",
``!u v. RTC (derives g) u v ==> (u=[NTS (startSym g)]) ==> RTC (derives (rgr g)) u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`derives g [NTS lhs] rhs` by METIS_TAC [res1] THEN
`derives (rgr g) [NTS lhs] rhs` by METIS_TAC [rgr_r4] THEN
METIS_TAC [derives_same_append_right,derives_same_append_left,RTC_RULES_RIGHT1]
);


val rgr_r11 = prove(
``rule (startSym g) u IN rules g ==> RTC (derives g) u v ==> RTC (derives (rgr g)) [NTS (startSym (rgr g))] v``,
METIS_TAC [rgr_r7,eq_srgr,RTC_RULES,res1]
);

val rgr_r12 = prove(
``rule l r IN rules (rgr g) ==> (?a b.RTC (derives (rgr g)) [NTS (startSym (rgr g))] (a++[NTS l]++b))``,
SRW_TAC [] [rgr_runs] THEN
METIS_TAC [rgr_r7,eq_srgr]
);

val rgr_r13 = prove(
``derives (rgr g) [NTS l] r  ==>  (? a b.RTC (derives (rgr g)) [NTS (startSym (rgr g))] (a++[NTS l]++b))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,rgr_runs] THEN
`lhs=l` by METIS_TAC [slres] THEN
METIS_TAC [eq_srgr,rgr_r7] 
);

val rgr_tmnls = prove(
``terminals (rgr (G f s)) = BIGUNION (IMAGE rule_terminals (rules (rgr (G f s))))``,
METIS_TAC [rgr_runs,terminals_def,rgr]
);

(*
Theorem 4.2
Every non-empty CFL is generated by a CFG with no useless symbols.
*)

val thm4_2 = prove(
``~(language g = {}) ==> (language g = language (rgr g))``,
SRW_TAC [] [language_def,EXTENSION,EQ_IMP_THM] THENL
[
METIS_TAC [rgr_r7,eq_srgr],
METIS_TAC [rgr_subr2,RTC_MONOTONE,eq_srgr]
])

val _ = export_theory ();
