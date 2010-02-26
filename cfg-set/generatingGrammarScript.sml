(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory listTheory relationTheory;
open pred_setTheory regexpTheory grammarDefTheory listLemmaTheory;

val _ = new_theory "generatingGrammar";

val useful_def = Define`useful g x =
                           ?a b w.  RTC (derives g) [NTS (startSym g)] (a ++ [x] ++ b) /\
                                    RTC (derives g) (a ++ [x] ++ b) w /\  
                                    EVERY isTmnlSym w`

val usefulnts = Define `usefulnts (G p s) = G {rule l r | rule l r IN p /\ gaw (G p s) (NTS l) /\ EVERY (gaw (G p s)) r} s`;

val eq_startsym = store_thm ("eq_startsym",
``startSym (usefulnts g) = startSym g``,
Cases_on `g` THEN METIS_TAC [startSym_def,usefulnts]);

val runs = prove(
``rules (usefulnts g) = {rule l r | rule l r IN rules g /\ gaw g (NTS l) /\ EVERY (gaw g) r}``,
Cases_on `g` THEN
SRW_TAC [] [usefulnts,rules_def]);
	
val subr1 = prove(
``!l r. rule l r IN rules (usefulnts g) ==> rule l r IN rules g ``,
Cases_on `g` THEN SRW_TAC [] [rules_def,usefulnts]
);


val subr2 = prove(
``! a b.derives (usefulnts g) a b ==> derives g a b``,
 Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [usefulnts,derives_def,rules_def,gaw_def] THEN SRW_TAC [] [] THEN 
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] []);

val subr3 = prove(
``! a b.derives g a b ==> EVERY (gaw g) a ==> EVERY (gaw g) b ==> derives (usefulnts g) a b``,
Cases_on `g` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [usefulnts,derives_def,gaw_def] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND,gaw_def,rules_def] THEN Q.EXISTS_TAC `w` THEN
SRW_TAC [] []
);

val subr6 = prove(
``!a b.RTC (derives g) a b ==> EVERY (gaw g) b ==> RTC (derives (usefulnts g)) a b``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
`EVERY (gaw g) b` by METIS_TAC [key_result] THEN
RES_TAC THEN
`derives (usefulnts g) b b'` by METIS_TAC [subr3] THEN
`RTC (derives (usefulnts g)) a b` by METIS_TAC [key_result] THEN
METIS_TAC [RTC_RULES_RIGHT1]
);


val subr4 = store_thm("subr4",
``!v w.RTC (derives g) v w ==> EVERY isTmnlSym w ==> RTC (derives (usefulnts g)) v w``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
`EVERY (gaw g) v'` by METIS_TAC [sub_result_rev] THEN
`derives (usefulnts g) v v'` by METIS_TAC [key_result,subr3] THEN
METIS_TAC [RTC_RULES]);

val subr5 = prove(
``EVERY (gaw g) b ==> EVERY (gaw (usefulnts g)) b``,
MATCH_MP_TAC EVERY_MONOTONIC THEN SRW_TAC [] [] 
THEN FULL_SIMP_TAC (srw_ss()) [gaw_def] THEN
METIS_TAC [subr4]
);

val subr4_rev = store_thm ("subr4_rev",
``!v w.RTC (derives (usefulnts g)) v w ==> RTC (derives g) v w``,
HO_MATCH_MP_TAC RTC_INDUCT THEN 
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RULES,subr2]
);

val subr5 = prove(
``gaw g a ==> gaw (usefulnts g) a``,
SRW_TAC [] [gaw_def] THEN METIS_TAC [subr4]
);


(* changing order of eq for rewrites *)
val lemma4_1a = store_thm(
"lemma4_1a",
``language g = language (usefulnts g)``,
    SRW_TAC [][eq_startsym,language_def, EXTENSION] THEN 
    EQ_TAC  THENL [
      Q_TAC SUFF_TAC `!u v. RTC (derives g) u v ==> 
                            EVERY (gaw g) v ==>
                            (u = [NTS (startSym g)]) ==>
                            RTC (derives (usefulnts g)) [NTS (startSym g)] v`
            THEN1 METIS_TAC [term_syms_gen_words] THEN

 HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] THEN 
METIS_TAC [subr3,RTC_RULES_RIGHT1,key_result],
 METIS_TAC [eq_startsym,RTC_MONOTONE,subr2]]
);
	

val lemma4_1 = store_thm(
  "lemma4_1",
  ``~ (language g = {}:symbol list set) ==> 
                          (language g = language (usefulnts g)) /\ 
                              !nt. nt IN nonTerminals (usefulnts g) ==> gaw (usefulnts g) nt``,
  STRIP_TAC THEN 
  CONJ_TAC THENL [
		  METIS_TAC [lemma4_1a],
SRW_TAC [] [] THEN
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [usefulnts,nonTerminals_def] THENL[
SRW_TAC [] [gaw_def] THEN
`?e.e IN language (G f s)` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
FULL_SIMP_TAC (srw_ss()) [language_def] THEN
SRW_TAC [] [gaw_def] THEN Q.EXISTS_TAC `e` THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
`RTC (derives (G f s)) [NTS s] e ==> EVERY isTmnlSym e ==> RTC (derives (usefulnts (G f s))) [NTS s] e` by METIS_TAC [subr4] THEN
FULL_SIMP_TAC (srw_ss()) [usefulnts,gaw_def],

FULL_SIMP_TAC (srw_ss()) [rule_nonterminals_def] THENL[
METIS_TAC [gaw_def,rules_def,subr5,usefulnts],
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [usefulnts,subr5]
]]])


val _ = export_theory ();
