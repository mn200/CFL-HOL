(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory listTheory relationTheory;
open pred_setTheory regexpTheory grammarDefTheory listLemmasTheory;

val _ = new_theory "generatingGrammar";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);


val usefulnts = Define 
    `usefulnts (G p s) g' = 
    (∀e.MEM e (rules g') = e ∈ {rule l r | MEM (rule l r) p ∧ 
			       gaw (G p s) (NTS l) ∧ EVERY (gaw (G p s)) r}) ∧
    (startSym g' = s)`;
    
val use_exists = store_thm
("use_exists",
``∀g.∃g'.usefulnts g g'``,
SRW_TAC [][usefulnts] THEN
MAGIC);

val eq_startsym = store_thm ("eq_startsym",
``usefulnts g g' ⇒ (startSym g' = startSym g)``,
Cases_on `g` THEN METIS_TAC [startSym_def,usefulnts]);

val subr1 = prove(
``∀l r. usefulnts g g' ⇒ MEM (rule l r) (rules g') ⇒ MEM (rule l r) (rules g)``,
Cases_on `g` THEN SRW_TAC [] [rules_def,usefulnts]);


val subr2 = prove(
``∀ a b.usefulnts g g' ⇒ derives g' a b ⇒ derives g a b``,
 Cases_on `g` THEN 
FULL_SIMP_TAC (srw_ss()) [usefulnts,derives_def,rules_def,gaw_def] THEN 
SRW_TAC [] [] THEN 
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] []);

val subr3 = prove(
``∀ a b.usefulnts g g' ⇒
derives g a b ⇒ EVERY (gaw g) a ⇒ EVERY (gaw g) b ⇒ derives g' a b``,
Cases_on `g` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [usefulnts,derives_def,gaw_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND,gaw_def,rules_def] THEN Q.EXISTS_TAC `w` THEN
SRW_TAC [] []);

val subr6 = prove(
``∀a b.RTC (derives g) a b ⇒ usefulnts g g' ⇒ 
EVERY (gaw g) b ⇒ RTC (derives g') a b``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
`EVERY (gaw g) b` by METIS_TAC [key_result] THEN
RES_TAC THEN
`derives g' b b'` by METIS_TAC [subr3] THEN
`RTC (derives g') a b` by METIS_TAC [key_result] THEN
METIS_TAC [RTC_RULES_RIGHT1]);


val subr4 = store_thm("subr4",
``∀v w.RTC (derives g) v w ⇒ usefulnts g g' ⇒ 
EVERY isTmnlSym w ⇒ RTC (derives g') v w``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
`EVERY (gaw g) v'` by METIS_TAC [sub_result_rev] THEN
`derives g' v v'` by METIS_TAC [key_result,subr3] THEN
METIS_TAC [RTC_RULES]);

val subr5 = store_thm("subr5",
``gaw g a ⇒ usefulnts g g' ⇒ gaw g' a``,
SRW_TAC [] [gaw_def] THEN METIS_TAC [subr4]);

val subr5' = store_thm("subr5'",
``EVERY (gaw g) b ⇒ usefulnts g g' ⇒ EVERY (gaw g') b``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [gaw_def] THEN
METIS_TAC [subr5,EVERY_MONOTONIC]);

val subr4_rev = store_thm ("subr4_rev",
``∀v w.RTC (derives g') v w ⇒ usefulnts g g' ⇒ RTC (derives g) v w``,
HO_MATCH_MP_TAC RTC_INDUCT THEN 
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RULES,subr2]);


(* changing order of eq for rewrites *)
val lemma4_1a = store_thm(
"lemma4_1a",
``usefulnts g g' ⇒ (language g = language g')``,
    SRW_TAC [][eq_startsym,language_def, EXTENSION] THEN 
    EQ_TAC  THENL [
      Q_TAC SUFF_TAC `∀u v. RTC (derives g) u v ⇒ 
		            usefulnts g g' ⇒
                            EVERY (gaw g) v ⇒
                            (u = [NTS (startSym g)]) ⇒
                            RTC (derives g') [NTS (startSym g)] v`
		   THEN1 (Cases_on `g` THEN
			  METIS_TAC [term_syms_gen_words,usefulnts,
				    startSym_def]) THEN

 HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] THEN 
METIS_TAC [subr3,RTC_RULES_RIGHT1,key_result],
 METIS_TAC [eq_startsym,RTC_MONOTONE,subr2]]);
	
(*
val lemma4_1 = store_thm(
  "lemma4_1",
  ``~ (language g = {}:('nts,'ts) symbol list set) ⇒ usefulnts g g' ⇒ 
                 (language g = language g') ∧
                 ∀nt. nt IN nonTerminals g' 
                       ⇒ gaw g' nt``,

SRW_TAC [][] THEN1
METIS_TAC [lemma4_1a] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [usefulnts,nonTerminals_def,EXTENSION,
			  startSym_def,rules_def] THEN
SRW_TAC [][] THENL[
SRW_TAC [] [gaw_def] THEN
`∃e.e IN language (G l (startSym g'))` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
FULL_SIMP_TAC (srw_ss()) [language_def] THEN
SRW_TAC [] [gaw_def] THEN 
Q.EXISTS_TAC `e` THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
`usefulnts (G l (startSym g')) g'` 
by FULL_SIMP_TAC (srw_ss()) [usefulnts,rules_def,startSym_def] THEN
`RTC (derives (G l (startSym g'))) [NTS (startSym g')] e ⇒ EVERY isTmnlSym e ⇒ 
RTC (derives g') [NTS (startSym g')] e` 
by METIS_TAC [subr4] THEN
Cases_on `nt` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC slemma1_4 THEN
METIS_TAC []
FULL_SIMP_TAC (srw_ss()) [usefulnts,gaw_def],

FULL_SIMP_TAC (srw_ss()) [rule_nonterminals_def] THENL[
METIS_TAC [gaw_def,rules_def,subr5,usefulnts],
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [usefulnts,subr5]
]])
*)


val _ = export_theory ();