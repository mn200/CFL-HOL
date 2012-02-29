(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory listTheory relationTheory;
open pred_setTheory symbolDefTheory grammarDefTheory listLemmasTheory
    uselessSymbolsTheory containerLemmasTheory;

val _ = new_theory "generatingGrammar";

val usefulntsRules = Define
`usefulntsRules g =
{rule l r | MEM (rule l r) (rules g) ∧ gaw g (NTS l) ∧ EVERY (gaw g) r}`;

val usefulnts = Define
    `usefulnts g g' =
    (set (rules g') = usefulntsRules g) ∧ (startSym g' = startSym g)`;

val finiteusefulntsRules = store_thm
("finiteusefulntsRules",
``FINITE (usefulntsRules g)``,

 SRW_TAC [][usefulntsRules] THEN
 Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
 Q.ABBREV_TAC `f = \r. case (r : (α,β)rule) of
                        rule N rhs -> if (gaw g (NTS N) ∧ EVERY (gaw g) rhs) then
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

val use_exists = store_thm
("use_exists",
``∀g.∃g'.usefulnts g g'``,

SRW_TAC [][usefulnts] THEN
METIS_TAC [finiteusefulntsRules, listExists4Set, startSym_def, rules_def]);


val eq_startsym = store_thm ("eq_startsym",
``usefulnts g g' ⇒ (startSym g' = startSym g)``,
Cases_on `g` THEN METIS_TAC [startSym_def,usefulnts]);

val subr1 = prove(
``∀l r. usefulnts g g' ⇒ MEM (rule l r) (rules g') ⇒ MEM (rule l r) (rules g)``,
SRW_TAC [] [rules_def,usefulnts, usefulntsRules, EXTENSION]);


val subr2 = prove(
``∀ a b.usefulnts g g' ⇒ derives g' a b ⇒ derives g a b``,
FULL_SIMP_TAC (srw_ss()) [usefulnts,derives_def,rules_def,gaw_def,
			  usefulntsRules, EXTENSION] THEN
SRW_TAC [] [] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN SRW_TAC [] []);


val subr3 = store_thm("subr3",
``∀ a b.usefulnts g g' ⇒
derives g a b ⇒ EVERY (gaw g) a ⇒ EVERY (gaw g) b ⇒ derives g' a b``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [usefulnts,derives_def,gaw_def, usefulntsRules,
			  EXTENSION] THEN
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


val lemma4_1 = store_thm(
  "lemma4_1",
  ``~ (language g = {}:('nts,'ts) symbol list set) ⇒ usefulnts g g' ⇒
                 (language g = language g') ∧
                 ∀nt. nt IN nonTerminals g'
                       ⇒ gaw g' nt``,

SRW_TAC [][] THEN1
METIS_TAC [lemma4_1a] THEN
FULL_SIMP_TAC (srw_ss()) [usefulnts,nonTerminals_def,EXTENSION,usefulntsRules,
			  startSym_def,rules_def] THEN
`usefulnts g g'`
by FULL_SIMP_TAC (srw_ss()) [usefulnts,rules_def,startSym_def, usefulntsRules,
			     EXTENSION] THEN
SRW_TAC [][] THEN

SRW_TAC [] [gaw_def] THEN
Cases_on `nt` THEN1
(`∃rhs.
     rule n rhs ∈ rules g' ∨
     ∃l p s.
       rule l (p ++ [NTS n] ++ s) ∈ rules g' ∨
       (n = startSym g')` by METIS_TAC [slemma1_4] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [gaw_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [subr4] THEN1

(FULL_SIMP_TAC (srw_ss()) [gaw_def] THEN
 METIS_TAC [subr4]) THEN

`∃e.e IN language g` by METIS_TAC [MEMBER_NOT_EMPTY] THEN
FULL_SIMP_TAC (srw_ss()) [language_def] THEN
SRW_TAC [] [gaw_def] THEN
Q.EXISTS_TAC `e` THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
METIS_TAC [subr4, startSym_def]) THEN
METIS_TAC [tsNotInNonTmnls]);


val _ = export_theory ();
