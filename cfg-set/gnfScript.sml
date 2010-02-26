(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory relationTheory listTheory string_numTheory
open pred_setTheory regexpTheory grammarDefTheory listLemmaTheory generatingGrammarTheory

val _ = new_theory "gnf";


(* Greibach Normal Form *)

(* 
 Lemma 4.3 
Define an A-production to be a production with variable A on the
left. Let G=(V,T,P,S) be a CFG. Let A->xBy be a production in P and
B->b1|b2... be the set of all B-productions. Let G1=(V,T,P1,S) be
obtained from G by deleting the production A->xBy from P and adding
the productions A->xb1y|xb2y.... Then L(g)=L(G1).
*)

(*
val aProdg = Define `aProdg g g' = ?A r B r' p s.((rule A r) IN (rules g)) /\ (r = (p++[NTS B]++s)) /\ ((rule B r') IN rules g) /\ 
~(A=B) /\ (rules (g') = rules g DIFF {rule A r} UNION {rule A (p++x++s)|(rule B x) IN rules g}) /\ (startSym g = startSym g')`
*)


(* Termination like the CNF form *)
val aProdg = Define `aProdg A B g g' = ?r p s.~(A=B) /\ ((rule A r) IN (rules g)) /\ (r = (p++[NTS B]++s)) /\
(rules (g') = rules g DIFF {rule A r} UNION {rule A (p++x++s)|(rule B x) IN rules g}) /\ (startSym g = startSym g')`


val apg_r1 = prove(
``!g g' A.aProdg A B g g' ==> !u v.derives g u v ==> EVERY isTmnlSym v ==> derives g' u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `lhs=A` THENL[
Cases_on `rhs=p++[NTS B]++s` THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b],
METIS_TAC []],
METIS_TAC []])

val slemma1_r3 = prove(
``!u v.RTC (derives g) u v ==> (u=[NTS nt]) ==> EVERY isTmnlSym v ==> ?x.rule nt x IN rules g /\ RTC (derives g) x v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,isTmnlSym_def,isNonTmnlSym_def,sym_r1b],
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN METIS_TAC []])

val slemma1_r4 = prove(
``!g g'.aProdg A B g g' ==> !l r. rule l r IN rules g' ==> ~(l=A) ==> rule l r IN rules g``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProdg] THEN
`~(rule l r = rule A (p ++ [NTS B] ++ s))` by SRW_TAC [] [] THEN
`~?x.(rule l r = rule A (p ++ x ++ s))` by SRW_TAC [] [] THEN
`rule l r IN (rules g DIFF {rule A (p ++ [NTS B] ++ s)} UNION {rule A (p ++ x ++ s) | rule B x IN rules g})` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
METIS_TAC [])

val apg_r2 = prove(
``!u v.RTC (derives g) u v ==> aProdg A B g g' ==> EVERY isTmnlSym v ==> RTC (derives g') u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
Cases_on `lhs = A` THENL[
Cases_on `rhs = p++[NTS B]++s` THENL[
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b],
`rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]],
`rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]],

FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
SRW_TAC [] [] THEN
Cases_on `lhs=A` THENL[
Cases_on `rhs=p++[NTS B]++s` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b,EVERY_APPEND],
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b,EVERY_APPEND]],
`rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]],

FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
SRW_TAC [] [] THEN
Cases_on `lhs=A` THENL[
Cases_on `rhs=p++[NTS B]++s` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b,EVERY_APPEND],
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b,EVERY_APPEND]],
`rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]],

FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
Cases_on `~(lhs=A)` THEN
Cases_on `~(rhs=p++[NTS B]++s)` THEN
SRW_TAC [] [] THENL[
`rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
`derives g' (s1++[NTS lhs]++s2) (s1++rhs++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS lhs]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS lhs]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
METIS_TAC [RTC_RULES],

`rule lhs (p++[NTS B]++s) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
`derives g' (s1++[NTS lhs]++s2) (s1++(p++[NTS B]++s)++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS lhs]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS lhs]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
METIS_TAC [RTC_RULES],


`rule A rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
`derives g' (s1++[NTS A]++s2) (s1++rhs++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS A]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS A]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
METIS_TAC [RTC_RULES],


DISJ2_TAC THEN
`RTC (derives g') (s1 ++ (p++[NTS B]++s) ++ s2) (s1'' ++ [NTS lhs''] ++ s2'')` by METIS_TAC [RTC_RULES,rtc_derives_same_append_right,rtc_derives_same_append_left] THEN
`derives g' (s1'' ++ [NTS lhs''] ++ s2'') (s1'' ++ rhs'' ++ s2'')` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`RTC (derives g') (s1 ++ (p++[NTS B]++s) ++ s2) v` by METIS_TAC [RTC_RULES] THEN
`?s0.s0 = (p++[NTS B]++s)` by METIS_TAC [] THEN
`RTC (derives g') (s1 ++ s0 ++ s2) v` by METIS_TAC [RTC_RULES] THEN
`(?x' y' z'. ((v=x'++y'++z') /\ RTC (derives g') s1 x' /\ RTC (derives g') s0 y' /\ RTC (derives g') s2 z'))` by METIS_TAC [upgr_r19] THEN
SRW_TAC [] [] THEN
`(?x'' y'' z''. ((y'=x''++y''++z'') /\ RTC (derives g') p x'' /\ RTC (derives g') [NTS B] y'' /\ RTC (derives g') s z''))` by METIS_TAC [upgr_r19] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`?R.rule B R IN rules g' /\ RTC (derives g') R y''` by METIS_TAC [slemma1_r3] THEN
`RTC (derives g') (s1 ++ p ++ R ++ s ++ s2) (x' ++ x'' ++ y'' ++ z'' ++ z')` by METIS_TAC [derives_append] THEN
`rule B R IN rules g` by METIS_TAC [slemma1_r4,aProdg] THEN
`rule A (p++R++s) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
Q.EXISTS_TAC `(s1 ++ p ++ R ++ s ++ s2)` THEN
SRW_TAC [] [] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`p ++ R ++ s`,`A`] THEN
SRW_TAC [] []]])


val apg_r3 = prove(
``!g g'. aProdg A B g g' ==> !u v.derives g' u v ==> RTC (derives g) u v``,
SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
Cases_on `~(lhs=A)` THENL[
`rule lhs rhs IN rules g` by METIS_TAC [slemma1_r4] THEN
METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES],

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProdg] THEN
`rule A rhs IN rules g DIFF {rule A (p ++ [NTS B] ++ s)} UNION {rule A (p ++ x ++ s) | rule B x IN rules g}` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES]
])


val apg_r4 = prove (``!u v.RTC (derives g') u v ==>  aProdg A B g g' ==> RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RTC,apg_r3])


val lemma4_3 = prove (
``!g g'.aProdg A B g g' ==> (language g = language g')``,
SRW_TAC [] [EQ_IMP_THM,EXTENSION,language_def] THENL[
METIS_TAC [apg_r2,aProdg],
METIS_TAC [apg_r4,aProdg]])
	     


(* TERMINATION *)
val apgt_r1 = prove(
``!g g'.RTC (\x y.?a b.aProdg A B x y) g g' ==>  (language g = language g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
METIS_TAC [lemma4_3]
)


(* Lemma 4.4 *)

val leftRecRules = Define `leftRecRules g nt = {rule nt rhs |rhs| rule nt rhs IN rules g /\ ?s.(rhs = [NTS nt] ++ s)}`

val nonLeftRecRules = Define `nonLeftRecRules g nt = {rule nt rhs |rhs| rule nt rhs IN rules g /\ ~(?s.(rhs = [NTS nt] ++ s))}`

val left2Right = Define `left2Right A B g g' = ~((NTS B) IN nonTerminals g) /\
(startSym g = startSym g') /\
(rules g' = (rules g UNION
{rule A (b++[NTS B]) | b | rule A b IN (nonLeftRecRules g A)} UNION
{rule B a | a | rule A ([NTS A]++a) IN (leftRecRules g A)} UNION
{rule B (a++[NTS B]) | a | rule A ([NTS A]++a) IN (leftRecRules g A)} DIFF
(leftRecRules g A)))`


val ntfree = Define `ntfree sf nt = ~(MEM (NTS nt) sf)`

val ntderives = Define 
`(ntderives g nt f lsl rsl = ((f=1) /\ ?s1 s2 rhs lhs.
           ((s1 ++ [NTS lhs] ++ s2 = lsl) /\ (s1 ++ rhs ++ s2 = rsl) /\
           rule lhs rhs IN rules g /\ (lhs=nt))) \/
           ((f=0) /\ ?s1 s2 rhs lhs.
           ((s1 ++ [NTS lhs] ++ s2 = lsl) /\ (s1 ++ rhs ++ s2 = rsl) /\
           rule lhs rhs IN rules g /\ ~(lhs=nt))))`

val pntderives = Define
`(pntderives g nt f 0 lsl rsl  = ntderives g nt f lsl rsl) /\
(pntderives g nt f n lsl rsl = ((f=1) /\ ?s1 s2 rhs lhs.
           ((s1 ++ [NTS lhs] ++ s2 = lsl) /\ (s1 ++ rhs ++ s2 = rsl) /\
           rule lhs rhs IN rules g /\ (lhs=nt)) /\ (LENGTH s1 = n-1)) \/
           ((f=0) /\ ?s1 s2 rhs lhs.
           ((s1 ++ [NTS lhs] ++ s2 = lsl) /\ (s1 ++ rhs ++ s2 = rsl) /\
           rule lhs rhs IN rules g /\ ~(lhs=nt)) /\ (LENGTH s1 = n-1)))`


val ntderives_same_append_left = store_thm ("ntderives_same_append_left",
	``!g u v.ntderives g nt f u v ==> !x.ntderives g nt f (x++u) (x++v)``,
	SRW_TAC [] [ntderives] THEN 
	METIS_TAC []);

val ntderives_same_append_right = store_thm ("ntderives_same_append_right",
	``!g u v.ntderives g nt f u v ==> !x.ntderives g nt f (u++x) (v++x)``,
	SRW_TAC [] [ntderives] THEN METIS_TAC [APPEND,APPEND_ASSOC]);


val rtc_ntderives_same_append_left = store_thm ("rtc_ntderives_same_append_left",
	``!u v.RTC (ntderives g nt f) u v ==> !x. RTC (ntderives g nt f) (x++u) (x++v)``,
	HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN 
	METIS_TAC [relationTheory.RTC_RULES,ntderives_same_append_left]
);


val rtc_ntderives_same_append_right = store_thm ("rtc_ntderives_same_append_right",
	``!u v.RTC (ntderives g nt f) u v ==> !x. RTC (ntderives g nt f) (u++x) (v++x)``,
	HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN 
	METIS_TAC [relationTheory.RTC_RULES,ntderives_same_append_right]
);

val ntderives_append = store_thm ("ntderives_append",
  ``RTC (ntderives g nt f) M N /\ RTC (ntderives g nt f) P Q ==>
    RTC (ntderives g nt f) (M ++ P) (N ++ Q)``,
  Q_TAC SUFF_TAC `!x y. RTC (ntderives g nt f) x y ==> 
                        !u v. RTC (ntderives g nt f) u v ==>  
                              RTC (ntderives g nt f) (x ++ u) (y ++ v)`
        THEN1 METIS_TAC [] THEN 
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THENL [
    		METIS_TAC [rtc_ntderives_same_append_left],
		METIS_TAC [ntderives_same_append_right,RTC_RULES]]);


val ntlemma2 = store_thm("ntlemma2",
``!s1 s2 s1' s2'.ntderives g nt f (s1++s2) s ==> (?s1'.ntderives g nt f s1 s1' /\ (s=s1'++s2)) \/ (?s2'.ntderives g nt f s2 s2' /\ (s=s1++s2'))``,
Cases_on `f` THENL[
SRW_TAC [] [] THEN
RULE_ASSUM_TAC (REWRITE_RULE [ntderives]) THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
`?l1 l2.((s1=s1'++[NTS lhs]++l1) /\ (s2=l2) /\ (s2'=l1++l2)) \/ ((s2=l2++[NTS lhs]++s2') /\ (s1=l1) /\ (s1'=l1++l2))` by METIS_TAC [list_r6] THENL[
DISJ1_TAC THEN SRW_TAC [] [ntderives] THEN METIS_TAC [],
DISJ2_TAC THEN SRW_TAC [] [ntderives] THEN METIS_TAC [APPEND_ASSOC]
],
SRW_TAC [] [] THEN
RULE_ASSUM_TAC (REWRITE_RULE [ntderives]) THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
`?l1 l2.((s1=s1'++[NTS nt]++l1) /\ (s2=l2) /\ (s2'=l1++l2)) \/ ((s2=l2++[NTS nt]++s2') /\ (s1=l1) /\ (s1'=l1++l2))` by METIS_TAC [list_r6] THENL[
DISJ1_TAC THEN SRW_TAC [] [ntderives] THEN METIS_TAC [],
DISJ2_TAC THEN SRW_TAC [] [ntderives] THEN METIS_TAC [APPEND_ASSOC]
]])


val ntupgr_r17 = store_thm("ntupgr_r17",
``! u v.RTC (ntderives g nt f) u v ==> (u=x++y) ==> (?x' y'. ((v=x'++y') /\ RTC (ntderives g nt f) x x' /\ RTC (ntderives g nt f) y y' ))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,RTC_REFLEXIVE],
`(?x''.ntderives g nt f x' x'' /\ (v'=x''++y')) \/ (?y''.ntderives g nt f y' y'' /\ (v'=x'++y''))` by METIS_TAC [ntlemma2] THEN
METIS_TAC [RTC_RULES_RIGHT1]
])

val ntupgr_r19 = store_thm("ntupgr_r19",
``! u v.RTC (ntderives g nt f) u v ==> (u=x++y++z) ==> (?x' y' z'. ((v=x'++y'++z') /\ RTC (ntderives g nt f) x x' /\ RTC (ntderives g nt f) y y' /\ RTC (ntderives g nt f) z z'))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THEN
`ntderives g nt f (x' ++ (y' ++ z')) v' ==> (?x''.ntderives g nt f x' x'' /\ (v'=x''++(y'++z'))) \/ (?y''.ntderives g nt f (y'++z') y'' /\ (v'=x'++y''))` by SRW_TAC [][ntlemma2,APPEND,APPEND_ASSOC] THEN
  `ntderives g nt f (x' ++ y' ++ z') v' =  ntderives g nt f (x' ++ (y' ++ z')) v'` by SRW_TAC [] [] THEN
  RES_TAC THENL[
  METIS_TAC [APPEND,APPEND_ASSOC,RTC_RULES_RIGHT1],

  RES_TAC THEN
`ntderives g nt f (y' ++ z') y'' ==> (?s1'.ntderives g nt f y' s1' /\ (y''=s1'++z')) \/ (?s2'.ntderives g nt f z' s2' /\ (y''=y'++s2'))` by METIS_TAC [ntlemma2] THEN
   RES_TAC THEN
   METIS_TAC [RTC_RULES_RIGHT1,APPEND_ASSOC,APPEND]])

val l2r_r6 = prove(
``!u v nt.ntderives g nt f u v ==> derives g u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,ntderives] THEN
METIS_TAC [])

val l2r_r7 = prove(
``!u v.RTC (ntderives g nt f) u v ==> RTC (derives g) u v``,
METIS_TAC [l2r_r6,RTC_MONOTONE])

val l2r_r8 = prove(
``!nt v.derives g [NTS nt] v ==> ntderives g nt 1 [NTS nt] v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,ntderives,lreseq] THEN
SRW_TAC [] [])

val l2r_r11 = prove(
``~(MEM (NTS nt) u) = ntfree u nt``,
SRW_TAC [] [ntfree])

val ntfree_append = prove(
``ntfree (x++y) nt = ntfree x nt /\ ntfree y nt``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [ntfree])





val l2r_r1 = prove (
``!g g'.left2Right A B g g' ==> rule lhs rhs IN rules g ==> EVERY isTmnlSym rhs ==> rule lhs rhs IN rules g'``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [left2Right] THEN
SRW_TAC [] [leftRecRules] THEN
METIS_TAC [sym_r6,isTmnlSym_def,isNonTmnlSym_def,sym_r1b,APPEND]
)

val l2r_r2 = prove (
``!g g'.left2Right A B g g' ==> (rule lhs rhs IN rules g ==> (~?s.(rhs=[NTS lhs]++s)) ==> rule lhs rhs IN rules g')``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [left2Right] THEN
SRW_TAC [] [leftRecRules] THEN
Cases_on `lhs=A` THEN METIS_TAC []
)

val l2r_r3a = prove(
``rule lhs rhs IN rules g ==> ~(lhs=A) ==> ~(rule lhs rhs IN leftRecRules g A)``,
FULL_SIMP_TAC (srw_ss()) [leftRecRules])

val l2r_r3b = prove(
``rule lhs rhs IN rules g ==> ~(lhs=A) ==> ~(rule lhs rhs IN nonLeftRecRules g A)``,
FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules]) 

val l2r_r3c = prove(
``rule A rhs IN rules g ==> ~(?s.rhs=[NTS A]++s) ==> ~(rule lhs rhs IN leftRecRules g A)``,
FULL_SIMP_TAC (srw_ss()) [leftRecRules])

val l2r_r3d = prove(
``rule A rhs IN rules g ==> ~(?s.rhs=[NTS A]++s) ==> (rule A rhs IN nonLeftRecRules g A)``,
FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules])

val l2r_r3e = prove(
``!l r nt g.rule l r IN leftRecRules g nt ==> ~(rule l r IN nonLeftRecRules g nt)``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [leftRecRules,nonLeftRecRules])

val l2r_r3f = prove(
``!l p nt.rule l (p++[NTS nt]) IN rules g ==> (NTS nt) IN nonTerminals g``,
Cases_on `g` THEN
SRW_TAC [] [nonTerminals_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN
DISJ2_TAC  THEN
Q.EXISTS_TAC `rule_nonterminals (rule l (p++[NTS nt]))` THEN
CONJ_TAC THENL[
SRW_TAC [] [rule_nonterminals_def] THEN
METIS_TAC [isNonTmnlSym_def],
METIS_TAC []])

val l2r_r3g = prove(
``!l p nt.rule nt p IN rules g ==> ~(rule nt p IN leftRecRules g nt) ==> ~(?s.p=[NTS nt]++s)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [leftRecRules] THEN
METIS_TAC [])

val l2r_r3h = prove(
``!g g'.left2Right A B g g' ==> rule A (p++[NTS B]) IN rules g' ==> (rule A p IN nonLeftRecRules g A)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [left2Right] THEN
`rule A (p++[NTS B]) IN rules g UNION
          {rule A (b ++ [NTS B]) |
           b |
           rule A b IN nonLeftRecRules g A} UNION
          {rule B a | rule A (NTS A::a) IN leftRecRules g A} UNION
          {rule B (a ++ [NTS B]) |
           rule A (NTS A::a) IN leftRecRules g A} DIFF leftRecRules g A` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [l2r_r3f],
SRW_TAC [] [] THEN
`rule A (NTS A::(p++[NTS A])) IN rules g` by FULL_SIMP_TAC (srw_ss()) [leftRecRules] THEN
METIS_TAC [slemma1_3],
SRW_TAC [] [] THEN
`rule A (NTS A::p) IN rules g` by FULL_SIMP_TAC (srw_ss()) [leftRecRules] THEN
METIS_TAC [slemma1_3]])


val l2r_r3i = prove(
``!g g'.left2Right A B g g' ==> rule A r IN rules g' ==> ((?p.(r=p++[NTS B]) /\ rule A p IN nonLeftRecRules g A) \/ (~?s.(r=s++[NTS B]) /\ rule A r IN rules g))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [left2Right] THEN
`rule A r IN rules g UNION
          {rule A (b ++ [NTS B]) |
           b |
           rule A b IN nonLeftRecRules g A} UNION
          {rule B a | rule A (NTS A::a) IN leftRecRules g A} UNION
          {rule B (a ++ [NTS B]) |
           rule A (NTS A::a) IN leftRecRules g A} DIFF leftRecRules g A` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [l2r_r3f])


val l2r_r3j = prove(
``!l r g.rule l r IN leftRecRules g l ==> ~(rule l r IN nonLeftRecRules g l)``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [leftRecRules,nonLeftRecRules])

val l2r_r3k = prove(
``!l r g.rule l r IN nonLeftRecRules g l ==> ~(rule l r IN leftRecRules g l)``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [leftRecRules,nonLeftRecRules])


val l2r_r3l = mk_thm([],
``!g g'.left2Right A B g g' ==> !b.rule B b IN rules g' ==> ((?p.(b=p++[NTS B]) /\ rule A (NTS A::p) IN rules g) \/ (~(?s.(b=s++[NTS B])) /\ rule A  (NTS A::b) IN rules g))``)

val l2r_r4 = prove(
``!g g'.left2Right A B g g' ==> derives g u v  ==> EVERY isTmnlSym v ==> derives g' u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`rule lhs rhs IN rules g'` by METIS_TAC [l2r_r1] THEN
METIS_TAC []
)

val l2r_r51 = prove (
``!v nt.EVERY isTmnlSym v ==> ntfree v nt``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [ntfree,rgr_r9eq,sym_r6] THEN
METIS_TAC [isNonTmnlSym_def])


val l2r_r5 = mk_thm ([],
``!u v.RTC (derives g) u v ==> (?u0 u1 p. RTC (ntderives g nt 0) u u0 /\ RTC (pntderives g nt 1 p) u0 u1 /\ RTC (derives g) u1 v /\ ~((EL p u1)=(NTS nt)))``)
(*



*)

(*
val l2r_r5a = mk_thm ([], ``!u v.RTC (derives g) u v ==> left2Right A B g g' ==> ntfree v A ==> ?u'.RTC (ntderives g A) u u' /\ RTC (derives g') u' v /\ (ntfree u' A)``)
(*
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES],


RES_TAC
*)

val l2r_r5 = mk_thm ([],``!u v.RTC (derives g) u v ==> left2Right A B g g' ==> EVERY isTmnlSym v ==> RTC (derives g') u v``)
(*

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
RES_TAC THEN 
`ntfree v A` by METIS_TAC [l2r_r51]

METIS_TAC [l2r_r5a,RTC_RULES,l2r_r51]
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THENL[

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
`rule lhs rhs IN rules g'` by METIS_TAC [l2r_r1,EVERY_APPEND] THEN
METIS_TAC [RTC_RULES,res1],


SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
`rule lhs rhs IN rules g'` by METIS_TAC [l2r_r1,EVERY_APPEND] THEN
METIS_TAC [RTC_RULES,res1],

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
`rule lhs rhs IN rules g'` by METIS_TAC [l2r_r1,EVERY_APPEND] THEN
METIS_TAC [RTC_RULES,res1],

FULL_SIMP_TAC (srw_ss()) [derives_def,left2Right] THEN
Cases_on `~(lhs=A)` THEN
Cases_on `~?s.(rhs=[NTS lhs]++s)` THEN
SRW_TAC [] [] THENL[
DISJ2_TAC THEN
`rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF,nonLeftRecRules,leftRecRules] THEN
`~(rule lhs rhs IN leftRecRules g lhs)` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF,nonLeftRecRules,leftRecRules] THEN
SRW_TAC [] [] THEN
`derives g' (s1++[NTS lhs]++s2) (s1++rhs++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS lhs]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS lhs]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
`RTC (derives g') (s1 ++ rhs ++ s2) (s1'' ++ rhs'' ++ s2'')` by METIS_TAC [res2,RTC_RULES] THEN 
Q.EXISTS_TAC `(s1 ++ rhs ++ s2)` THEN
SRW_TAC [] [] THENL[
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`lhs`] THEN METIS_TAC [RTC_RULES,l2r_r3a],
METIS_TAC [RTC_RULES,leftRecRules,nonLeftRecRules,RTC_RULES_RIGHT1]],


`rule lhs (NTS lhs::s) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF,l2r_r3a,l2r_r3b] THEN
`derives g' (s1++[NTS lhs]++s2) (s1++(NTS lhs::s)++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS lhs]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS lhs]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
`RTC (derives g') (s1 ++ (NTS lhs::s) ++ s2) (s1'' ++ rhs'' ++ s2'')` by METIS_TAC [res2,RTC_RULES] THEN 
DISJ2_TAC THEN
Q.EXISTS_TAC `(s1 ++ (NTS lhs::s) ++ s2)` THEN
SRW_TAC [] [] THENL[
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`(NTS lhs::s)`,`lhs`] THEN 
METIS_TAC [RTC_RULES,leftRecRules,nonLeftRecRules,APPEND,CONS,APPEND_ASSOC,l2r_r3a],
METIS_TAC [RTC_RULES,leftRecRules,nonLeftRecRules,RTC_RULES_RIGHT1]],


`~(rule A rhs IN leftRecRules g A)` by METIS_TAC [l2r_r3c] THEN
`(rule A rhs IN nonLeftRecRules g A)` by METIS_TAC [l2r_r3d] THEN
`rule A rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
`derives g' (s1++[NTS A]++s2) (s1++rhs++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS A]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS A]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
`RTC (derives g') (s1 ++ rhs ++ s2) (s1'' ++ rhs'' ++ s2'')` by METIS_TAC [res2,RTC_RULES] THEN 
DISJ2_TAC THEN
Q.EXISTS_TAC `(s1 ++ rhs ++ s2)` THEN
SRW_TAC [] [] THENL[
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`rhs`,`A`] THEN 
METIS_TAC [RTC_RULES,leftRecRules,nonLeftRecRules],
METIS_TAC [RTC_RULES,leftRecRules,nonLeftRecRules,RTC_RULES_RIGHT1]],



DISJ2_TAC THEN
`RTC (derives g') (s1 ++ (NTS A)::s ++ s2) (s1'' ++ [NTS lhs''] ++ s2'')` by METIS_TAC [RTC_RULES,rtc_derives_same_append_right,rtc_derives_same_append_left] THEN
`derives g' (s1'' ++ [NTS lhs''] ++ s2'') (s1'' ++ rhs'' ++ s2'')` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`RTC (derives g') (s1 ++ (NTS A)::s ++ s2) v` by METIS_TAC [RTC_RULES] THEN
`?s0.s0 = (NTS A::s)` by METIS_TAC [] THEN
`RTC (derives g') (s1 ++ s0 ++ s2) v` by METIS_TAC [RTC_RULES] THEN
`(?x' y' z'. ((v=x'++y'++z') /\ RTC (derives g') s1 x' /\ RTC (derives g') s0 y' /\ RTC (derives g') s2 z'))` by METIS_TAC [upgr_r19] THEN
SRW_TAC [] [] THEN
`(?x'' y''. ((y'=x''++y'') /\ RTC (derives g') [NTS A] x'' /\ RTC (derives g') s y'' ))` by METIS_TAC [upgr_r17,APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`?r.rule A r IN rules g' /\ RTC (derives g') r x''` by METIS_TAC [slemma1_r3] THEN
`((?p.(r=p++[NTS B]) /\ rule A p IN nonLeftRecRules g A) \/ (~?s.(r=s++[NTS B]) /\ rule A r IN rules g))` by METIS_TAC [left2Right,l2r_r3h,APPEND]
`rule A p IN rules g'` by FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules,UNION_DEF,DIFF_DEF,l2r_r3k]
`~(B=A)` by METIS_TAC [slemma1_3]
`rule B s IN rules g'` by FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules,UNION_DEF,DIFF_DEF,leftRecRules]
`rule B (s++[NTS B]) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules,UNION_DEF,DIFF_DEF,leftRecRules]
`rule A (p++[NTS B]) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules,UNION_DEF,DIFF_DEF,leftRecRules]
SRW_TAC [] []
`(?l' m'.(x''=l'++m') /\ RTC (derives g') p l' /\ RTC (derives g') [NTS B] m')` by METIS_TAC [upgr_r17]
SRW_TAC [] []
FULL_SIMP_TAC (srw_ss()) []
`?b.rule B b IN rules g' /\ RTC (derives g') b m'` by METIS_TAC [slemma1_r3] THEN
`((?p.(b=p++[NTS B]) /\ rule A (NTS A::p) IN rules g) \/ (~(?s.(b=s++[NTS B])) /\ rule A  (NTS A::b) IN rules g))` by METIS_TAC [l2r_r3l,left2Right,APPEND]
SRW_TAC [] []
`rule B p' IN rules g'` by FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules,UNION_DEF,DIFF_DEF,leftRecRules]
`derives g' [NTS A] (p++[NTS B])` by METIS_TAC [res1]
`derives g' (p++[NTS B]) (p++p'++[NTS B])` by METIS_TAC [res1,derives_same_append_left,APPEND_ASSOC]
`RTC (derives g') [NTS A] (p++p'++[NTS B])` by METIS_TAC [res2]
`RTC (derives g') (p++p'++[NTS B]) (l'++m')` by METIS_TAC [derives_append,APPEND_ASSOC]
`RTC (derives g') [NTS A] (l'++m')` by METIS_TAC [RTC_RULES]
`RTC (derives g') (s1++[NTS A]++s2) (l'++m')` by METIS_TAC [RTC_RULES]

*)

val l2r_r9 = mk_thm ([], ``!u v.RTC (derives g') u v ==> left2Right A B g g' ==> ntfree v B ==> ?u'.RTC (ntderives g' B) u u' /\ RTC (derives g) u' v /\ (ntfree u' B)``)
(*
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES],
RES_TAC
`RTC (derives g') u' u''` by METIS_TAC [l2r_r7]
FULL_SIMP_TAC (srw_ss()) [derives_def]
Cases_on `lhs=B`
SRW_TAC [] []
`ntderives g' B [NTS B] rhs` by METIS_TAC [l2r_r8,res1]
METIS_TAC [RTC_RULES,RTC_RTC,RTC_SUBSET,rtc_ntderives_same_append_left,rtc_ntderives_same_append_right],


` RTC (derives g') (s1 ++ rhs ++ s2) u''` by METIS_TAC [l2r_r7]
` RTC (derives g') (s1 ++ rhs ++ s2) v` by METIS_TAC [RTC_RTC]

`(?x' y' z'. ((v=x'++y'++z') /\ RTC (derives g') s1 x' /\ RTC (derives g') rhs y' /\ RTC (derives g') s2 z'))` by METIS_TAC [upgr_r19]
SRW_TAC [] []
FULL_SIMP_TAC (srw_ss()) [ntfree_append]
Cases_on `MEM (NTS B) s1` THEN Cases_on `MEM (NTS B) s2` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [] []
Q.EXISTS_TAC `(x' ++ [NTS lhs] ++ z')`
SRW_TAC [] []
METIS_TAC [l2r_r11,ntupgr_r19]
*)


val l2r_r10 = mk_thm ([],
``RTC (derives g') (b++ast++[NTS B]) M ==> star (allSyms g) ast ==> RTC (derives g) A M``)


val l2r_r6 = mk_thm ([], ``!u v.RTC (derives g') u v ==> (u=[NTS (startSym g')]) ==> EVERY isTmnlSym v ==> left2Right A B g g' ==> RTC (derives g) u v``)
(*
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
RES_TAC
FULL_SIMP_TAC (srw_ss()) [derives_def]


SRW_TAC [] []
FULL_SIMP_TAC (srw_ss()) []
FULL_SIMP_TAC (srw_ss()) [left2Right]
FULL_SIMP_TAC (srw_ss()) [lreseq]
SRW_TAC [] []


METIS_TAC [res1,derives_same_append_left,derives_same_append_right,RTC_RULES_RIGHT1]

`rule lhs rhs IN ` by METIS_TAC [l2r_r2]

*)
*)



val lemma4_4 = prove (
``!g g'.left2Right A B g g' ==> (language g = language g')``,
SRW_TAC [] [EQ_IMP_THM,EXTENSION,language_def] THENL[
METIS_TAC [l2r_r5,left2Right],
METIS_TAC [l2r_r6,left2Right]])

(* 
Theorem 4.6 
Every CFL L without can be generated by a grammar for
which every production is of the form A->aalph, where A is a variable,
a is a terminal and alpha (possibly empty) is a string of variables.
*)


val numVars = Define `numVars g = {NTS (n2s (s2n (nt))) | ((NTS nt) IN nonTerminals g)}`



val _ = export_theory ();
