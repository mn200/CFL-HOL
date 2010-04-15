(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory relationTheory listTheory;
open pred_setTheory grammarDefTheory listLemmasTheory containerLemmasTheory;

val _ = new_theory "reachableGrammar";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

val rgrRules = Define
    `rgrRules g = 
    { rule l r | MEM (rule l r) (rules g) ∧ 
     ∃a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b)}`;

val rgr = Define 
`rgr g g' = (set (rules g') = rgrRules g) ∧
            (startSym g' = startSym g)`;


val finitergrRules = store_thm
("finitergrRules",
``FINITE (rgrRules g)``,

 SRW_TAC [][rgrRules] THEN
 Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
 Q.ABBREV_TAC `f = \r. case (r : (α,β)rule) of 
                        rule N rhs -> if (∃a b.
					  (derives g)^* [NTS (startSym g)]
					  (a ++ [NTS N] ++ b)) then
			{rule N rhs} else {} `
 THEN
Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f (set (rules g)))`
 THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN 
	Cases_on `r` THEN SRW_TAC [][]) THEN

    ONCE_REWRITE_TAC [EXTENSION] THEN 
   SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss, 
	    boolSimps.CONJ_ss][EXISTS_rule, 
			       Abbr`f`, Abbr`Horrible`] THEN 
   METIS_TAC [NOT_EVERY]); 

val rgr_exists = store_thm
("rgr_exists",
``∀g.∃g'.rgr g g'``, 

SRW_TAC [][rgr] THEN
METIS_TAC [finitergrRules, listExists4Set, startSym_def, rules_def]);


val eq_srgr = store_thm ("eq_srgr",
``rgr g g' ⇒ (startSym g' = startSym g)``,
SRW_TAC [][rgr]);

(*
val rgr_runs = prove(
``rgr g g' ⇒
rules g' = {rule l r | rule l r IN rules g ∧ (∃ a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b))}``,
Cases_on `g` THEN SRW_TAC [] [rules_def,rgr,startSym_def,rules_def]);
*)

val rgr_subr1 = prove(
``∀l r. rgr g g' ⇒ MEM (rule l r) (rules g') ⇒ MEM (rule l r) (rules g)``,
Cases_on `g` THEN SRW_TAC [] [rules_def,rgr, rgrRules, EXTENSION]);

val rgr_subr2 = store_thm("rgr_subr2",
``∀ a b.rgr g g' ⇒ derives g' a b ⇒ derives g a b``,
 Cases_on `g` THEN 
FULL_SIMP_TAC (srw_ss()) [rgr,derives_def,rules_def,gaw_def,rgrRules, EXTENSION] 
			  THEN SRW_TAC [] [] THEN 
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] []);

val rgr_subr3 = prove(
``∀v.rgr g g' ⇒ derives g [NTS (startSym g)] v ⇒ 
derives g' [NTS (startSym g')] v``,
Cases_on `g` THEN
SRW_TAC [] [startSym_def,eq_srgr] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,rules_def,rgr,rgrRules,EXTENSION] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`] THEN
ASM_REWRITE_TAC [RTC_RULES] );

val rgr_subr3g = prove(
``∀u v.rgr g g' ⇒
derives g u v ⇒ (u=[NTS (startSym g)]) ⇒ derives g' u v``,
METIS_TAC [rgr_subr3,startSym_def,eq_srgr]);


val rgr_subr3_rtc = store_thm ("rgr_subr3_rtc",
``∀u v.RTC (derives g') u v ⇒ rgr g g' ⇒ RTC (derives g) u v``,

HO_MATCH_MP_TAC RTC_INDUCT THEN
SRW_TAC [] [] THEN
METIS_TAC [rgr_subr2,RTC_RULES]);

val rgr_subr3b = prove(
``∀u v.(u=[NTS (startSym g')]) ⇒ rgr g g' ⇒ derives g u v ⇒ derives g' u v``,

Cases_on `g`THEN SRW_TAC [] [eq_srgr,startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,rules_def,rgr,rgrRules,EXTENSION] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] [startSym_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
SRW_TAC [][startSym_def]);

val rgr_r1 = prove(
``MEM (rule l r) (rules g) ⇒ rgr g g' ⇒
(∃a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b)) ⇒
 MEM (rule l r) (rules g')``,

Cases_on `g` THEN
SRW_TAC [] [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def,rgr,startSym_def,rgrRules,EXTENSION] THEN
MAP_EVERY Q.EXISTS_TAC [`a`,`b`] THEN
SRW_TAC [] []);

val rgr_r2 = prove (
``MEM (rule l r) (rules g) ⇒ rgr g g' ⇒
(∃ a b.RTC (derives g') [NTS (startSym g)] (a++[NTS l]++b)) ⇒ 
MEM (rule l r) (rules g')``,

SRW_TAC [] [] THEN
Cases_on `g` THEN 
FULL_SIMP_TAC (srw_ss()) [startSym_def,rules_def,rgr,rgrRules,EXTENSION] THEN
SRW_TAC [][] THEN
`rgr (G l' (startSym g')) g'` by FULL_SIMP_TAC (srw_ss()) [rules_def,rgr,
 startSym_def,rgrRules,EXTENSION] THEN
MAP_EVERY Q.EXISTS_TAC [`a`,`b`] THEN
METIS_TAC [rgr_subr3_rtc,rule_11]);

val rgr_r3 = prove(
``rgr g g' ⇒ rgr g g' ⇒
derives g [NTS l] r ⇒ (∃a b.RTC (derives g) [NTS (startSym g)] (a++[NTS l]++b)) ⇒ 
MEM (rule l r) (rules g')``,
Cases_on `g` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def,rules_def,rgr,derives_def,rgrRules,
			  EXTENSION]  THEN
SRW_TAC [] [] THENL
[
`(s1=[]) ∧ (s2=[])`  by METIS_TAC [slres2] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][],
MAP_EVERY Q.EXISTS_TAC [`a`,`b`] THEN
SRW_TAC [] []
]);

val rgr_r4 = store_thm("rgr_r4",
``rgr g g' ⇒
(∃ a b.RTC (derives g') [NTS (startSym g)] (a++[NTS l]++b)) ⇒ derives g [NTS l] r 
⇒ derives  g' [NTS l] r``,
Cases_on `g` THEN
SRW_TAC [] [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN
SRW_TAC [] [] THEN
METIS_TAC [rgr_r2,rgr,rules_def,slres,startSym_def,rgrRules,EXTENSION]);

val rgr_r6 = prove(
``rgr g g' ⇒ (derives g [NTS (startSym g)] v = derives g' [NTS (startSym g')] v)``,

METIS_TAC [rgr_subr2,rgr_subr3,eq_srgr,rgr,rgrRules,EXTENSION]);


val rgr_r5 = prove(
``rgr g g' ⇒
(∃ a b.RTC (derives g') [NTS (startSym g)] (a++[NTS l]++b)) ⇒ derives g [NTS l] v'
 ⇒ (∃ x y.RTC (derives g') [NTS (startSym g)] (x++v'++y))``,

Cases_on `g` THEN
SRW_TAC [] [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,startSym_def] THEN
` lhs=l` by METIS_TAC [slres] THEN
`(s1=[]) ∧ (s2=[])`  by METIS_TAC [slres2] THEN
`rhs=v'` by FULL_SIMP_TAC (srw_ss()) [] THEN
`derives g' [NTS l] v'` by METIS_TAC [rgr_r4,startSym_def,res1] THEN
`derives g' (a++[NTS l]++b) (a++v'++b)` by METIS_TAC [derives_same_append_right,derives_same_append_left] THEN
MAP_EVERY Q.EXISTS_TAC [`a`,`b`] THEN
METIS_TAC [RTC_RULES_RIGHT1] );

val rgr_r7 = store_thm("rgr_r7",
``∀u v. RTC (derives g) u v ⇒ rgr g g' ⇒ (u=[NTS (startSym g)]) ⇒ 
RTC (derives g') u v``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`derives g [NTS lhs] rhs` by METIS_TAC [res1] THEN
`derives g' [NTS lhs] rhs` by METIS_TAC [rgr_r4] THEN
METIS_TAC [derives_same_append_right,derives_same_append_left,RTC_RULES_RIGHT1]
);


val rgr_r11 = prove(
``rgr g g' ⇒ MEM (rule (startSym g) u) (rules g) ⇒ RTC (derives g) u v ⇒ 
RTC (derives g') [NTS (startSym g')] v``,
METIS_TAC [rgr_r7,eq_srgr,RTC_RULES,res1]
);

val rgr_r12 = prove(
``MEM (rule l r) (rules g') ⇒ rgr g g' ⇒
(∃a b.RTC (derives g') [NTS (startSym g')] (a++[NTS l]++b))``,

SRW_TAC [] [rules_def,rgr,rgrRules,EXTENSION] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
`rgr g g'`by FULL_SIMP_TAC (srw_ss()) [rules_def, rgr,rgrRules,EXTENSION] THEN
METIS_TAC [rgr_r7,eq_srgr,rgr,rule_11]
);

val rgr_r13 = prove(
``rgr g g' ⇒
derives g' [NTS l] r  ⇒  
(∃ a b.RTC (derives g') [NTS (startSym g')] (a++[NTS l]++b))``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,rgr,rules_def,rgrRules,EXTENSION] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN SRW_TAC [][] THEN
`rgr g g'`by FULL_SIMP_TAC (srw_ss()) [rules_def, rgr,rgrRules,EXTENSION] THEN
METIS_TAC [eq_srgr,rgr_r7] );



(*
Theorem 4.2
Every non-empty CFL is generated by a CFG with no useless symbols.
*)

val thm4_2 = store_thm
("thm4_2",
``rgr g g' ⇒ ~(language g = {}) ⇒ (language g = language g')``,
SRW_TAC [] [language_def,EXTENSION,EQ_IMP_THM] THENL
[
METIS_TAC [rgr_r7,eq_srgr],
METIS_TAC [rgr_subr2,RTC_MONOTONE,eq_srgr]])

val _ = export_theory ();
