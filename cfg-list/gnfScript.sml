(* A theory about regular expressions *)
open HolKernel boolLib bossLib Parse
open stringTheory relationTheory listTheory
    rich_listTheory

open pred_setTheory regexpTheory grammarDefTheory listLemmasTheory
relationLemmasTheory

val _ = new_theory "gnf";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);


val ldsubderivs = store_thm
("ldsubderivs",
``∀dl1 dl2. R ⊢ dl1++dl2 ◁ x → y ⇒ 
(dl1 ≠ [] ⇒ R ⊢ dl1 ◁ HD dl1 → LAST dl1 ∧ (HD dl1 = x)) ∧
(dl2 ≠ [] ⇒ R ⊢ dl2 ◁ HD dl2 → LAST dl2 ∧ (LAST dl2 = y)) ∧
((dl1≠[]) ∧ (dl2≠[]) ⇒ R (LAST dl1) (HD dl2))``,

MAGIC);

val ldAdjElem = store_thm
("ldAdjElem",
``∀x p.R ⊢ (p++[e1;e2]++s) ◁ x → y
⇒
R e1 e2``,
MAGIC);

val ldAppend = store_thm
("ldAppend",
``R ⊢ dl ◁ x → y ∧ R ⊢ dl' ◁  y → LAST dl' ⇒
R ⊢ dl ++ TL dl' ◁ x → LAST dl'``,
MAGIC);

val memld = store_thm
("memld",
``R ⊢ dl ◁ x → y ⇒ MEM x dl ∧ MEM y dl``,

Cases_on `dl` THEN SRW_TAC [][listderiv_def] THEN
Cases_on `t=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [last_append, APPEND, APPEND_FRONT_LAST, MEM_APPEND,MEM]);


val listDerivLastBrk = store_thm
("listDerivLastBrk",
``R ⊢ l ++ [e] ◁  x → z ∧ (l ≠ [])
 ⇒
R ⊢ l ◁ x → LAST l ∧ (e = z) ∧ R (LAST l) e``,

SRW_TAC [][listderiv_def] THEN1
METIS_TAC [rtc2list_distrib_append_fst] THEN1
(Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
`l=FRONT l ++ [LAST l]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`rtc2list R ([LAST l]++[e])` 
 by METIS_TAC [MEM, MEM_APPEND, rtc2list_distrib_append_snd, APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) []);

val ldImprtc2list = store_thm
("ldImprtc2list",
``∀dl x y.R ⊢ dl ◁ x → y ⇒ R^* x y``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN
RES_TAC THEN
`h = x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
METIS_TAC [RTC_RULES]);


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
val aProdg = Define `aProdg g g' = ∃A r B r' p s.((rule A r) ∈ (rules
g)) ∧ (r = (p++[NTS B]++s)) ∧ ((rule B r') ∈ rules g) ∧ ~(A=B) ∧
(rules (g') = rules g DIFF {rule A r} ∪ {rule A (p++x++s)|(rule B x) ∈
rules g}) ∧ (startSym g = startSym g')`
*)


(* Termination like the CNF form *)
val aProdg = Define 
`aProdg A B g g' = 
  ∃r p s.~(A=B) ∧ ((rule A r) ∈ (rules g)) ∧ (r = (p++[NTS B]++s)) ∧
  (rules (g') = rules g DIFF {rule A r} ∪ {rule A (p++x++s)|(rule B x) ∈ rules g}) ∧
  (startSym g = startSym g')`


val apg_r1 = prove(
``!g g' A.aProdg A B g g' ⇒ !u v.derives g u v ⇒ EVERY isTmnlSym v 
	    ⇒ 
	  derives g' u v``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `lhs=A` THENL[
Cases_on `rhs=p++[NTS B]++s` THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b],
METIS_TAC []],
METIS_TAC []]);

val slemma1_r3 = prove(
``!u v.RTC (derives g) u v ⇒ (u=[NTS nt]) ⇒ EVERY isTmnlSym v 
	      ⇒ 
	∃x.rule nt x ∈ rules g ∧ RTC (derives g) x v``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,isTmnlSym_def,isNonTmnlSym_def,sym_r1b],
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN METIS_TAC []])

val slemma1_r4 = prove(
``!g g'.aProdg A B g g' ⇒ !l r. rule l r ∈ rules g' ⇒ ~(l=A) 
	    ⇒ 
        rule l r ∈ rules g``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProdg] THEN
`~(rule l r = rule A (p ++ [NTS B] ++ s))` by SRW_TAC [] [] THEN
`~∃x.(rule l r = rule A (p ++ x ++ s))` by SRW_TAC [] [] THEN
`rule l r ∈ (rules g DIFF {rule A (p ++ [NTS B] ++ s)} ∪ {rule A (p ++ x ++ s) | rule B x ∈ rules g})` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
METIS_TAC [])

val apg_r2 = prove(
``!u v.RTC (derives g) u v ⇒ aProdg A B g g' ⇒ EVERY isTmnlSym v ⇒ RTC (derives g') u v``,
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
`rule lhs rhs ∈ rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]],
`rule lhs rhs ∈ rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
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
`rule lhs rhs ∈ rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
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
`rule lhs rhs ∈ rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]],

FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
Cases_on `~(lhs=A)` THEN
Cases_on `~(rhs=p++[NTS B]++s)` THEN
SRW_TAC [] [] THENL[
`rule lhs rhs ∈ rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
`derives g' (s1++[NTS lhs]++s2) (s1++rhs++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS lhs]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS lhs]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
METIS_TAC [RTC_RULES],

`rule lhs (p++[NTS B]++s) ∈ rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
SRW_TAC [] [] THEN
`derives g' (s1++[NTS lhs]++s2) (s1++(p++[NTS B]++s)++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS lhs]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS lhs]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
METIS_TAC [RTC_RULES],


`rule A rhs ∈ rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
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
`∃s0.s0 = (p++[NTS B]++s)` by METIS_TAC [] THEN
`RTC (derives g') (s1 ++ s0 ++ s2) v` by METIS_TAC [RTC_RULES] THEN
`(∃x' y' z'. ((v=x'++y'++z') ∧ RTC (derives g') s1 x' ∧ RTC (derives g') s0 y' ∧ RTC (derives g') s2 z'))` by METIS_TAC [upgr_r19] THEN
SRW_TAC [] [] THEN
`(∃x'' y'' z''. ((y'=x''++y''++z'') ∧ RTC (derives g') p x'' ∧ RTC (derives g') [NTS B] y'' ∧ RTC (derives g') s z''))` by METIS_TAC [upgr_r19] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃R.rule B R ∈ rules g' ∧ RTC (derives g') R y''` by METIS_TAC [slemma1_r3] THEN
`RTC (derives g') (s1 ++ p ++ R ++ s ++ s2) (x' ++ x'' ++ y'' ++ z'' ++ z')` by METIS_TAC [derives_append] THEN
`rule B R ∈ rules g` by METIS_TAC [slemma1_r4,aProdg] THEN
`rule A (p++R++s) ∈ rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
Q.EXISTS_TAC `(s1 ++ p ++ R ++ s ++ s2)` THEN
SRW_TAC [] [] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`p ++ R ++ s`,`A`] THEN
SRW_TAC [] []]])


val apg_r3 = prove(
``!g g'. aProdg A B g g' ⇒ !u v.derives g' u v ⇒ RTC (derives g) u v``,
SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
Cases_on `~(lhs=A)` THENL[
`rule lhs rhs ∈ rules g` by METIS_TAC [slemma1_r4] THEN
METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES],

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProdg] THEN
`rule A rhs ∈ rules g DIFF {rule A (p ++ [NTS B] ++ s)} ∪ {rule A (p ++ x ++ s) | rule B x ∈ rules g}` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES]
])


val apg_r4 = prove (``!u v.RTC (derives g') u v ⇒  aProdg A B g g' ⇒ RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RTC,apg_r3])


val lemma4_3 = prove (
``!g g'.aProdg A B g g' ⇒ (language g = language g')``,
SRW_TAC [] [EQ_IMP_THM,EXTENSION,language_def] THENL[
METIS_TAC [apg_r2,aProdg],
METIS_TAC [apg_r4,aProdg]]);
	     


(* TERMINATION *)
val apgt_r1 = prove(
``!g g'.RTC (\x y.∃a b.aProdg A B x y) g g' ⇒  (language g = language g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
METIS_TAC [lemma4_3]
);


(* Lemma 4.4 *)

val leftRecRules = Define 
`leftRecRules g nt = 
{rule nt rhs |rhs| rule nt rhs ∈ rules g ∧ ∃s.(rhs = [NTS nt] ++ s)}`;

val nonLeftRecRules = Define 
`nonLeftRecRules g nt = 
{rule nt rhs |rhs| rule nt rhs ∈ rules g ∧ ~(∃s.(rhs = [NTS nt] ++ s))}`;

val left2Right = Define 
`left2Right A B g g' = ~((NTS B) ∈ nonTerminals g) ∧
(startSym g = startSym g') ∧
(rules g' = (rules g ∪
{rule A (b++[NTS B]) | b | rule A b ∈ (nonLeftRecRules g A)} ∪
{rule B a | a | rule A ([NTS A]++a) ∈ (leftRecRules g A)} ∪
{rule B (a++[NTS B]) | a | rule A ([NTS A]++a) ∈ (leftRecRules g A)} DIFF
(leftRecRules g A)))`;


val ntfree = Define `ntfree sf nt = ~(MEM (NTS nt) sf)`;

val ntderives = Define 
`(ntderives g nt f lsl rsl = ((f=1) ∧ ∃s1 s2 rhs lhs.
           ((s1 ++ [NTS lhs] ++ s2 = lsl) ∧ (s1 ++ rhs ++ s2 = rsl) ∧
           rule lhs rhs ∈ rules g ∧ (lhs=nt))) \/
           ((f=0) ∧ ∃s1 s2 rhs lhs.
           ((s1 ++ [NTS lhs] ++ s2 = lsl) ∧ (s1 ++ rhs ++ s2 = rsl) ∧
           rule lhs rhs ∈ rules g ∧ ~(lhs=nt))))`;

val pntderives = Define
`(pntderives g nt f 0 lsl rsl  = ntderives g nt f lsl rsl) ∧
(pntderives g nt f n lsl rsl = ((f=1) ∧ ∃s1 s2 rhs lhs.
           ((s1 ++ [NTS lhs] ++ s2 = lsl) ∧ (s1 ++ rhs ++ s2 = rsl) ∧
           rule lhs rhs ∈ rules g ∧ (lhs=nt)) ∧ (LENGTH s1 = n-1)) \/
           ((f=0) ∧ ∃s1 s2 rhs lhs.
           ((s1 ++ [NTS lhs] ++ s2 = lsl) ∧ (s1 ++ rhs ++ s2 = rsl) ∧
           rule lhs rhs ∈ rules g ∧ ~(lhs=nt)) ∧ (LENGTH s1 = n-1)))`;


val ntderives_same_append_left = store_thm 
("ntderives_same_append_left",
 ``!g u v.ntderives g nt f u v ⇒ !x.ntderives g nt f (x++u) (x++v)``,
 SRW_TAC [] [ntderives] THEN 
 METIS_TAC []);

val ntderives_same_append_right = store_thm 
("ntderives_same_append_right",
 ``!g u v.ntderives g nt f u v ⇒ !x.ntderives g nt f (u++x) (v++x)``,
 SRW_TAC [] [ntderives] THEN METIS_TAC [APPEND,APPEND_ASSOC]);


val rtc_ntderives_same_append_left = store_thm 
("rtc_ntderives_same_append_left",
 ``!u v.RTC (ntderives g nt f) u v ⇒ !x. RTC (ntderives g nt f) (x++u) (x++v)``,
 HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN 
 METIS_TAC [relationTheory.RTC_RULES,ntderives_same_append_left]
 );


val rtc_ntderives_same_append_right = store_thm 
("rtc_ntderives_same_append_right",
 ``!u v.RTC (ntderives g nt f) u v ⇒ !x. RTC (ntderives g nt f) (u++x) (v++x)``,
 HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN 
 METIS_TAC [relationTheory.RTC_RULES,ntderives_same_append_right]
 );


val ntderives_append = store_thm 
("ntderives_append",
 ``RTC (ntderives g nt f) M N ∧ RTC (ntderives g nt f) P Q ⇒
 RTC (ntderives g nt f) (M ++ P) (N ++ Q)``,
 Q_TAC SUFF_TAC `!x y. RTC (ntderives g nt f) x y ⇒ 
 !u v. RTC (ntderives g nt f) u v ⇒  
 RTC (ntderives g nt f) (x ++ u) (y ++ v)`
 THEN1 METIS_TAC [] THEN 
 HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] 
 THENL [
	METIS_TAC [rtc_ntderives_same_append_left],
	METIS_TAC [ntderives_same_append_right,RTC_RULES]]);


val ntlemma2 = store_thm
("ntlemma2",
``!s1 s2 s1' s2'.ntderives g nt f (s1++s2) s 
 ⇒ 
 (∃s1'.ntderives g nt f s1 s1' ∧ (s=s1'++s2)) ∨ 
 (∃s2'.ntderives g nt f s2 s2' ∧ (s=s1++s2'))``,

Cases_on `f` 
 THENL[
       SRW_TAC [] [] THEN
       RULE_ASSUM_TAC (REWRITE_RULE [ntderives]) THEN 
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `∃l1 l2.((s1=s1'++[NTS lhs]++l1) ∧ (s2=l2) ∧ (s2'=l1++l2)) \/ ((s2=l2++[NTS lhs]++s2') ∧ (s1=l1) ∧ (s1'=l1++l2))` by METIS_TAC [list_r6] 
       THENL[
	     DISJ1_TAC THEN SRW_TAC [] [ntderives] THEN METIS_TAC [],
	     DISJ2_TAC THEN SRW_TAC [] [ntderives] THEN METIS_TAC [APPEND_ASSOC]
	     ],
       SRW_TAC [] [] THEN
       RULE_ASSUM_TAC (REWRITE_RULE [ntderives]) THEN 
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `∃l1 l2.((s1=s1'++[NTS nt]++l1) ∧ (s2=l2) ∧ (s2'=l1++l2)) ∨ 
       ((s2=l2++[NTS nt]++s2') ∧ (s1=l1) ∧ (s1'=l1++l2))` 
       by METIS_TAC [list_r6] 
       THENL[
	     DISJ1_TAC THEN SRW_TAC [] [ntderives] THEN METIS_TAC [],
	     DISJ2_TAC THEN SRW_TAC [] [ntderives] THEN METIS_TAC [APPEND_ASSOC]
	     ]]);


val ntupgr_r17 = store_thm
("ntupgr_r17",
``! u v.RTC (ntderives g nt f) u v ⇒ (u=x++y) 
 ⇒ 
 (∃x' y'. ((v=x'++y') ∧ RTC (ntderives g nt f) x x' ∧ 
	   RTC (ntderives g nt f) y y' ))``,

HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,RTC_REFLEXIVE],
`(∃x''.ntderives g nt f x' x'' ∧ (v'=x''++y')) ∨ 
(∃y''.ntderives g nt f y' y'' ∧ (v'=x'++y''))` by METIS_TAC [ntlemma2] THEN
METIS_TAC [RTC_RULES_RIGHT1]
]);

val ntupgr_r19 = store_thm
("ntupgr_r19",
``! u v.RTC (ntderives g nt f) u v ⇒ (u=x++y++z) 
       ⇒ 
 (∃x' y' z'. ((v=x'++y'++z') ∧ RTC (ntderives g nt f) x x' ∧ 
	      RTC (ntderives g nt f) y y' ∧ RTC (ntderives g nt f) z z'))``,

HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [] THEN
`ntderives g nt f (x' ++ (y' ++ z')) v' ⇒ 
 (∃x''.ntderives g nt f x' x'' ∧ (v'=x''++(y'++z'))) ∨ 
 (∃y''.ntderives g nt f (y'++z') y'' ∧ (v'=x'++y''))` 
 by SRW_TAC [][ntlemma2,APPEND,APPEND_ASSOC] THEN
 `ntderives g nt f (x' ++ y' ++ z') v' = 
 ntderives g nt f (x' ++ (y' ++ z')) v'` by SRW_TAC [] [] THEN
 RES_TAC 
 THENL[
       METIS_TAC [APPEND,APPEND_ASSOC,RTC_RULES_RIGHT1],
       
       RES_TAC THEN
       `ntderives g nt f (y' ++ z') y'' ⇒ 
       (∃s1'.ntderives g nt f y' s1' ∧ (y''=s1'++z')) ∨ 
       (∃s2'.ntderives g nt f z' s2' ∧ (y''=y'++s2'))` by METIS_TAC [ntlemma2] THEN
       RES_TAC THEN
       METIS_TAC [RTC_RULES_RIGHT1,APPEND_ASSOC,APPEND]]);

val l2r_r6 = prove(
``!u v nt.ntderives g nt f u v ⇒ derives g u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def, ntderives] THEN
METIS_TAC []);

val l2r_r7 = prove(
``!u v.RTC (ntderives g nt f) u v ⇒ RTC (derives g) u v``,
METIS_TAC [l2r_r6,RTC_MONOTONE]);

val l2r_r8 = prove(
``!nt v.derives g [NTS nt] v ⇒ ntderives g nt 1 [NTS nt] v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,ntderives,lreseq] THEN
SRW_TAC [] []);

val l2r_r11 = prove(
``~(MEM (NTS nt) u) = ntfree u nt``,
SRW_TAC [] [ntfree]);

val ntfree_append = prove(
``ntfree (x++y) nt = ntfree x nt ∧ ntfree y nt``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [ntfree]);



val l2r_r1 = prove (
 ``!g g'.left2Right A B g g' ⇒ rule lhs rhs ∈ rules g ⇒ EVERY isTmnlSym rhs 
    ⇒ 
 rule lhs rhs ∈ rules g'``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [left2Right] THEN
SRW_TAC [] [leftRecRules] THEN
METIS_TAC [sym_r6,isTmnlSym_def,isNonTmnlSym_def,sym_r1b,APPEND]
);

val l2r_r2 = prove (
``!g g'.left2Right A B g g' ⇒ (rule lhs rhs ∈ rules g ⇒ (~∃s.(rhs=[NTS lhs]++s)) 
     ⇒ 
   rule lhs rhs ∈ rules g')``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [left2Right] THEN
SRW_TAC [] [leftRecRules] THEN
Cases_on `lhs=A` THEN METIS_TAC []
);

val l2r_r3a = prove(
``rule lhs rhs ∈ rules g ⇒ ~(lhs=A) ⇒ ~(rule lhs rhs ∈ leftRecRules g A)``,
FULL_SIMP_TAC (srw_ss()) [leftRecRules]);

val l2r_r3b = prove(
``rule lhs rhs ∈ rules g ⇒ ~(lhs=A) ⇒ ~(rule lhs rhs ∈ nonLeftRecRules g A)``,
FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules]); 

val l2r_r3c = prove(
``rule A rhs ∈ rules g ⇒ ~(∃s.rhs=[NTS A]++s) ⇒ ~(rule lhs rhs ∈ leftRecRules g A)``,
FULL_SIMP_TAC (srw_ss()) [leftRecRules]);

val l2r_r3d = prove(
``rule A rhs ∈ rules g ⇒ ~(∃s.rhs=[NTS A]++s) ⇒ (rule A rhs ∈ nonLeftRecRules g A)``,
FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules]);

val l2r_r3e = prove(
``!l r nt g.rule l r ∈ leftRecRules g nt ⇒ ~(rule l r ∈ nonLeftRecRules g nt)``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [leftRecRules,nonLeftRecRules])

val l2r_r3f = prove(
``!l p nt.rule l (p++[NTS nt]) ∈ rules g 
       ⇒ (NTS nt) ∈ nonTerminals g``,
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
``!l p nt.rule nt p ∈ rules g ⇒ ~(rule nt p ∈ leftRecRules g nt) ⇒ ~(∃s.p=[NTS nt]++s)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [leftRecRules] THEN
METIS_TAC [])

val l2r_r3h = prove(
``!g g'.left2Right A B g g' ⇒ rule A (p++[NTS B]) ∈ rules g' 
     ⇒ (rule A p ∈ nonLeftRecRules g A)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [left2Right] THEN
`rule A (p++[NTS B]) ∈ rules g ∪
          {rule A (b ++ [NTS B]) |
           b |
           rule A b ∈ nonLeftRecRules g A} ∪
          {rule B a | rule A (NTS A::a) ∈ leftRecRules g A} ∪
          {rule B (a ++ [NTS B]) |
           rule A (NTS A::a) ∈ leftRecRules g A} DIFF leftRecRules g A` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [l2r_r3f],
SRW_TAC [] [] THEN
`rule A (NTS A::(p++[NTS A])) ∈ rules g` by FULL_SIMP_TAC (srw_ss()) [leftRecRules] THEN
METIS_TAC [slemma1_3],
SRW_TAC [] [] THEN
`rule A (NTS A::p) ∈ rules g` by FULL_SIMP_TAC (srw_ss()) [leftRecRules] THEN
METIS_TAC [slemma1_3]])


val l2r_r3i = prove(
``!g g'.left2Right A B g g' ⇒ rule A r ∈ rules g' 
     ⇒ 
((∃p.(r=p++[NTS B]) ∧ rule A p ∈ nonLeftRecRules g A) ∨
 (~∃s.(r=s++[NTS B]) ∧ rule A r ∈ rules g))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [left2Right] THEN
`rule A r ∈ rules g ∪
          {rule A (b ++ [NTS B]) |
           b |
           rule A b ∈ nonLeftRecRules g A} ∪
          {rule B a | rule A (NTS A::a) ∈ leftRecRules g A} ∪
          {rule B (a ++ [NTS B]) |
           rule A (NTS A::a) ∈ leftRecRules g A} DIFF leftRecRules g A` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [l2r_r3f])


val l2r_r3j = prove(
``!l r g.rule l r ∈ leftRecRules g l ⇒ ~(rule l r ∈ nonLeftRecRules g l)``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [leftRecRules,nonLeftRecRules])

val l2r_r3k = prove(
``!l r g.rule l r ∈ nonLeftRecRules g l ⇒ ~(rule l r ∈ leftRecRules g l)``,
SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [leftRecRules,nonLeftRecRules])



val l2r_r4 = prove(
``!g g'.left2Right A B g g' ⇒ derives g u v  ⇒ EVERY isTmnlSym v 
     ⇒ 
derives g' u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`rule lhs rhs ∈ rules g'` by METIS_TAC [l2r_r1] THEN
METIS_TAC []
)

val l2r_r51 = prove (
``!v nt.EVERY isTmnlSym v ⇒ ntfree v nt``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [ntfree,rgr_r9eq,sym_r6] THEN
METIS_TAC [isNonTmnlSym_def])


val hdNts = Define
`(hdNts [] = []) ∧
(hdNts ([]::t) = hdNts t) ∧
(hdNts (h::t) = HD h:: hdNts t)`; 


val lastNts = Define
`(lastNts [] = []) ∧
(lastNts ([]::t) = lastNts t) ∧
(lastNts (h::t) = LAST h:: lastNts t)`; 


val hdNtsApp = store_thm
("hdNtsApp",
``∀l1 l2.hdNts (l1 ++ l2) = hdNts l1 ++ hdNts l2``,

Induct_on `l1` THEN SRW_TAC [][] THEN
Cases_on `l2` THEN SRW_TAC [][hdNts] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [hdNts]);

val lastNtsApp = store_thm
("lastNtsApp",
``∀l1 l2.lastNts (l1 ++ l2) = lastNts l1 ++ lastNts l2``,

Induct_on `l1` THEN SRW_TAC [][] THEN
Cases_on `l2` THEN SRW_TAC [][lastNts] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [lastNts]);

val sfxSame = Define
`sfxSame sfx dl = ∀e.MEM e dl ⇒ isSuffix sfx e`;

val hdNtsSame = Define
`hdNtsSame A dl = ∀e.MEM e dl ⇒ (e≠[]) ⇒ (HD e = NTS A)`;

val expSyms = Define
`expSyms l = { NTS nts | ∃tsl sfx.MEM (tsl ++ [NTS nts] ++ sfx) l ∧ 
	     EVERY isTmnlSym tsl}`;


val blocks = Define
`blocks dl A = 
{ mid | ∃pfx sfx.(dl = pfx ++ mid ++ sfx) ∧ LENGTH mid > 1 ∧
∃pm sm.(HD mid = pm++[NTS A]++sm) ∧ EVERY isTmnlSym pm ∧
(∀e1 e2 p s.(p++[e1;e2]++s= mid) 
 ⇒ ∃m.(e2 = pm++[NTS A]++m++TL (DROP (LENGTH pm) e1))) }`;

val blocksb = Define
`blocksb dl A = 
{ mid | ∃pfx sfx.(dl = pfx ++ mid ++ sfx) ∧ LENGTH mid > 1 ∧
∃pm sm.(HD mid = pm++[NTS A]++sm) ∧ EVERY isTmnlSym pm ∧
(∀e1 e2 p s.(p++[e1;e2]++s= FRONT mid) 
 ⇒ ∃m.(e2 = pm++[NTS A]++m++TL (DROP (LENGTH pm) e1))) ∧
 ((LAST mid = pm++TL(DROP (LENGTH pm) (LAST (FRONT mid)))) ∨
  (∃nt m.(LAST mid = pm++[NTS nt]++m++TL (DROP (LENGTH pm) (LAST(FRONT mid)))) ∧ 
   (nt ≠ A)) ∨
  (∃ts m.(LAST mid = pm++[TS ts]++m++TL (DROP (LENGTH pm) (LAST(FRONT mid)))))) }`;

val expSymsApp = store_thm
("expSymsApp",
``∀l1 l2.nt ∉ expSyms (l1 ++ l2) = nt ∉ expSyms l1 ∧ nt ∉ expSyms l2``,

Induct_on `l1` THEN SRW_TAC [][expSyms] THEN
FULL_SIMP_TAC (srw_ss()) [expSyms, EXTENSION] THEN
METIS_TAC []);

val rulegImpg' = store_thm
("rulegImpg'",
``left2Right A B g g' ∧ (rule lhs rhs) ∈  (rules g) ∧ (lhs ≠ A)
⇒
(rule lhs rhs) ∈ (rules g')``,

SRW_TAC [][left2Right, rules_def] THEN
SRW_TAC [][leftRecRules]);


val rulegImpg'2 = store_thm
("rulegImpg'2",
``left2Right A B g g' ∧ rule A ([NTS A]++m) ∈  (rules g)
⇒
rule B (m++[NTS B]) ∈ (rules g')``,

SRW_TAC [][left2Right, rules_def] THEN
SRW_TAC [][leftRecRules] THEN
METIS_TAC [slemma1_4]);

val rulegImpg'3 = store_thm
("rulegImpg'3",
``left2Right A B g g' ∧ rule A ([NTS A]++m) ∈  (rules g)
⇒
rule B m ∈ (rules g')``,

SRW_TAC [][left2Right, rules_def] THEN
SRW_TAC [][leftRecRules] THEN
METIS_TAC [slemma1_4]);


val rulegImpg'4 = store_thm
("rulegImpg'4",
``left2Right A B g g' ∧ rule A rhs ∈  (rules g) ∧ ¬(∃rst.rhs = NTS A::rst)
⇒
rule A rhs ∈ (rules g')``,

SRW_TAC [][left2Right, rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules,leftRecRules]);


val gImpg'NotA = store_thm
("gImpg'NotA",
``∀dl x y.lderives g ⊢ dl ◁ x → y ∧ left2Right A B g g' ∧
(NTS A) ∉ expSyms dl
⇒
lderives g' ⊢ dl ◁ x → y``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
`(NTS A) ∉ (expSyms dl)` by METIS_TAC [expSymsApp, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def, listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
 `lhs ≠ A` by (FULL_SIMP_TAC (srw_ss()) [expSyms, EXTENSION] THEN
	       METIS_TAC [NOT_EVERY]) THEN
`rule lhs rhs ∈ rules g'` by METIS_TAC [rulegImpg'] THEN
METIS_TAC []);


val blkFront = store_thm
("blkFront",
``∀dl.LENGTH (FRONT dl) > 1 ⇒ (dl ∈ blocks dl A ⇒ FRONT dl ∈ blocks dl A)``,

Induct_on `dl` THEN SRW_TAC [][blocks] THEN
FULL_SIMP_TAC (srw_ss()) [blocks, EXTENSION] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `[]` THEN
Q.EXISTS_TAC `[LAST (h'::t')]`  THEN
SRW_TAC [][] THEN1
METIS_TAC [NOT_CONS_NIL, APPEND_FRONT_LAST] THEN
Q.EXISTS_TAC `pm` THEN
Q.EXISTS_TAC `sm` THEN
SRW_TAC [][] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
METIS_TAC [BUTFIRSTN_LENGTH_APPEND, TL, APPEND] THEN
`LENGTH ((pm ++ [NTS A] ++ sm)::h::h'::t') =
 LENGTH (pfx ++ (pm ++ [NTS A] ++ sm)::h::h'::t' ++ sfx)` by METIS_TAC [] THEN
`pfx=[]` by (Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    DECIDE_TAC) THEN
`sfx=[]` by (Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    DECIDE_TAC) THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND, APPEND_ASSOC, APPEND_FRONT_LAST, NOT_CONS_NIL]);


val blkFront2 = store_thm
("blkFront2",
``∀dl.LENGTH (FRONT dl) > 1 ⇒ 
 (dl ∈ blocks dl A ⇒ FRONT dl ∈ blocks (FRONT dl) A)``,

Induct_on `dl` THEN SRW_TAC [][blocks] THEN
FULL_SIMP_TAC (srw_ss()) [blocks, EXTENSION] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `[]` THEN
Q.EXISTS_TAC `[]`  THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `pm` THEN
Q.EXISTS_TAC `sm`  THEN
SRW_TAC [][] THEN
`LENGTH ((pm ++ [NTS A] ++ sm)::h::t) =
 LENGTH (pfx ++ (pm ++ [NTS A] ++ sm)::h::t ++ sfx)` by METIS_TAC [] THEN
`pfx=[]` by (Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    DECIDE_TAC) THEN
`sfx=[]` by (Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    DECIDE_TAC) THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND, APPEND_ASSOC, APPEND_FRONT_LAST, NOT_CONS_NIL]);



val leftRecRulegImpg' = store_thm
("leftRecRulegImpg'",
``rule A (NTS A::m) ∈ rules g ∧ left2Right A B g g' 
 ⇒ rule B (m++[NTS B]) ∈ (rules g')``,

SRW_TAC [][left2Right, rules_def, leftRecRules] THEN

`A ≠ B` by (SPOSE_NOT_THEN ASSUME_TAC THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [slemma1_4]) THEN
METIS_TAC []);

val addFrontrtc2listd = store_thm
("addFrontrtc2listd",
``∀l.rtc2list (derives g) l 
    ⇒
    rtc2list (derives g) (MAP (addFront rhs) l)``,

Induct_on `l` THEN SRW_TAC [][addFront_def] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [addFront_def] THEN
METIS_TAC [derives_same_append_left]);

val ntderivl = Define
`ntderivl (nt:('a,'b) symbol) (l:('a, 'b) symbol list list) = 
(∀e.MEM e l ⇒ (HD e = nt)) ∧ 
(∀e1 e2 p s.(l = p++[e1;e2]++s) ⇒ LENGTH e2 ≥ LENGTH e1)`;

val ntderivlg' = Define
`ntderivlg' (nt:('a,'b) symbol) (l:('a, 'b) symbol list list) = 
(∀e.MEM e l ⇒ (LAST e = nt)) ∧ 
(∀e1 e2 p s.(l = p++[e1;e2]++s) ⇒ LENGTH e2 ≥ LENGTH e1)`;


val blocksnt = Define
`blocksnt dl nt = { l | ∃pfx sfx.(dl = pfx ++ l ++ sfx) ∧ 
		   ntderivl nt (FRONT l) ∧ (HD (LAST l) ≠ nt) }`; 


val ntdlApp = store_thm
("ntdlApp",
``∀l1 l2.ntderivl nt (l1 ++ l2) ⇒ ntderivl nt l1 ∧ ntderivl nt l2``,

Induct_on `l1` THEN SRW_TAC [][ntderivl] THEN
 METIS_TAC [APPEND, APPEND_ASSOC]);


val ntdlg'App = store_thm
("ntdlg'App",
``∀l1 l2.ntderivlg' nt (l1 ++ l2) ⇒ ntderivlg' nt l1 ∧ ntderivlg' nt l2``,

Induct_on `l1` THEN SRW_TAC [][ntderivlg'] THEN
 METIS_TAC [APPEND, APPEND_ASSOC]);


val ntdlgImpg' = store_thm
("ntdlgImpg'",
``∀dl y.lderives g ⊢ dl ◁ [NTS A] → y ∧ left2Right A B g g' ∧ LENGTH dl > 1 ∧
ntderivl (NTS A) dl
⇒
∃dl'.derives g' ⊢ dl' ◁ [NTS B] → (TL y ++ [NTS B])``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [][SNOC_APPEND] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
IMP_RES_TAC listDerivLastBrk THEN
Cases_on `FRONT dl=[]` THEN SRW_TAC [][] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [lderives_def, listderiv_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ntderivl] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`[NTS A]`,`rhs`,`[]`,`[]`] MP_TAC) THEN
      SRW_TAC [][] THEN
      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `h = NTS A` by METIS_TAC [HD] THEN
      SRW_TAC [][] THEN
      `rule B (t++[NTS B]) ∈ rules g'` by METIS_TAC [rulegImpg'2, APPEND] THEN
      Q.EXISTS_TAC `[[NTS B];t++[NTS B]]` THEN
      SRW_TAC [][] THEN
      METIS_TAC [res1],

      `LENGTH dl > 1` by (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  DECIDE_TAC) THEN
      `dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
      `∃dl'.derives g' ⊢ dl' ◁ [NTS B] → (TL (LAST dl) ++ [NTS B])` 
      by METIS_TAC [ntdlApp] THEN
      FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ntderivl] THEN
      `MEM (LAST dl) dl` by METIS_TAC [MEM_APPEND,MEM] THEN
      `HD (s1 ++ [NTS lhs] ++ s2 ) = NTS A` by METIS_TAC [] THEN
      Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
      `HD (rhs++s2) = NTS A` by METIS_TAC [] THEN
      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
      (`LENGTH s2 ≥ LENGTH (NTS A::s2)` by METIS_TAC [APPEND,APPEND_ASSOC,
						      APPEND_NIL] THEN
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
      SRW_TAC [][] THEN
      `TL (LAST dl) = s2` by METIS_TAC [TL] THEN
      SRW_TAC [][] THEN
      `rule B (t++[NTS B]) ∈ rules g'`by METIS_TAC [rulegImpg'2, APPEND] THEN
      `derives g' [NTS B] (t++[NTS B])` by METIS_TAC [res1] THEN      
      `(derives g')^* [NTS B] (TL (LAST dl) ++ [NTS B])` 
      by METIS_TAC [ldImprtc2list] THEN
      METIS_TAC [RTC_RULES, rtc_derives_same_append_left,rtc2list_exists',
		 APPEND_ASSOC]
      ]);


val ntdlgImpg'' = store_thm
("ntdlgImpg''",
``∀dl y.lderives g ⊢ dl ◁ [NTS A] → y ∧ left2Right A B g g' ∧ LENGTH dl > 1 ∧
ntderivl (NTS A) dl
⇒
∃dl'.derives g' ⊢ dl' ◁ [NTS B] → TL y``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [][SNOC_APPEND] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
IMP_RES_TAC listDerivLastBrk THEN
Cases_on `FRONT dl=[]` THEN SRW_TAC [][] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [lderives_def, listderiv_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ntderivl] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`[NTS A]`,`rhs`,`[]`,`[]`] MP_TAC) THEN
      SRW_TAC [][] THEN
      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `h = NTS A` by METIS_TAC [HD] THEN
      SRW_TAC [][] THEN
      `rule B t ∈ rules g'` by METIS_TAC [rulegImpg'3, APPEND] THEN
      Q.EXISTS_TAC `[[NTS B];t]` THEN
      SRW_TAC [][] THEN
      METIS_TAC [res1],

      `LENGTH dl > 1` by (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  DECIDE_TAC) THEN
      `dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
      `∃dl'.derives g' ⊢ dl' ◁ [NTS B] → TL (LAST dl)` 
      by METIS_TAC [ntdlApp] THEN
      FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ntderivl] THEN
      `MEM (LAST dl) dl` by METIS_TAC [MEM_APPEND,MEM] THEN
      `HD (s1 ++ [NTS lhs] ++ s2 ) = NTS A` by METIS_TAC [] THEN
      Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
      `HD (rhs++s2) = NTS A` by METIS_TAC [] THEN
      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
      (`LENGTH s2 ≥ LENGTH (NTS A::s2)` by METIS_TAC [APPEND,APPEND_ASSOC,
						      APPEND_NIL] THEN
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
      SRW_TAC [][] THEN
      `TL (LAST dl) = s2` by METIS_TAC [TL] THEN
      SRW_TAC [][] THEN
      `rule B (t++[NTS B]) ∈ rules g'`by METIS_TAC [rulegImpg'2, APPEND] THEN
      IMP_RES_TAC ldImprtc2list THEN
      METIS_TAC [RTC_RULES, rtc_derives_same_append_left,rtc2list_exists',
		 APPEND_ASSOC,res1]
      ]);


(*
val ntdlg'Impg2 = store_thm
("ntdlg'Impg2",
``∀dl y.rderives g' ⊢ dl ◁ [NTS B] → y ∧ left2Right A B g g' ∧ LENGTH dl > 1 ∧
ntderivlg' (NTS B) dl
⇒
∃dl'.derives g ⊢ dl' ◁ [NTS A] → FRONT y``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [][SNOC_APPEND] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
IMP_RES_TAC listDerivLastBrk THEN
Cases_on `FRONT dl=[]` THEN SRW_TAC [][] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [rderives_def, listderiv_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ntderivlg'] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`[NTS B]`,`rhs`,`[]`,`[]`] MP_TAC) THEN
      SRW_TAC [][] THEN
      Cases_on `rhs=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `rhs = FRONT rhs++[LAST rhs]` by METIS_TAC [APPEND_FRONT_LAST] THEN
      `LAST rhs = NTS B` by METIS_TAC [last_elem] THEN
      SRW_TAC [][] THEN
      `rule A ([NTS A]++FRONT rhs) ∈ rules g` by METIS_TAC [ruleg'ImpgRec] THEN
      `rule A`
      Q.EXISTS_TAC `[[NTS A];FRONT rhs]` THEN
      SRW_TAC [][] THEN
      METIS_TAC [res1],

      `LENGTH dl > 1` by (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  DECIDE_TAC) THEN
      `dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
      `∃dl'.derives g' ⊢ dl' ◁ [NTS B] → TL (LAST dl)` 
      by METIS_TAC [ntdlApp] THEN
      FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ntderivl] THEN
      `MEM (LAST dl) dl` by METIS_TAC [MEM_APPEND,MEM] THEN
      `HD (s1 ++ [NTS lhs] ++ s2 ) = NTS A` by METIS_TAC [] THEN
      Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
      `HD (rhs++s2) = NTS A` by METIS_TAC [] THEN
      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
      (`LENGTH s2 ≥ LENGTH (NTS A::s2)` by METIS_TAC [APPEND,APPEND_ASSOC,
						      APPEND_NIL] THEN
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
      SRW_TAC [][] THEN
      `TL (LAST dl) = s2` by METIS_TAC [TL] THEN
      SRW_TAC [][] THEN
      `rule B (t++[NTS B]) ∈ rules g'`by METIS_TAC [rulegImpg'2, APPEND] THEN
      IMP_RES_TAC ldImprtc2list THEN
      METIS_TAC [RTC_RULES, rtc_derives_same_append_left,rtc2list_exists',
		 APPEND_ASSOC,res1]
      ]);
*)

val ruleg'ImpgRec = store_thm
("ruleg'ImpgRec",
``left2Right A B g g' ∧ rule B (rhs++[NTS B]) ∈ rules g'
⇒
rule A ([NTS A]++rhs) ∈ rules g``,

SRW_TAC [][left2Right,leftRecRules, nonLeftRecRules,rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`rule B (rhs++[NTS B])`] MP_TAC) THEN SRW_TAC [][] THEN
METIS_TAC [slemma1_4,MEM,MEM_APPEND,APPEND,APPEND_ASSOC,APPEND_NIL]);


val ntdlg'Impg = store_thm
("ntdlg'Impg",
``∀dl y.rderives g' ⊢ dl ◁ [NTS B] → y ∧ left2Right A B g g' ∧ LENGTH dl > 1 ∧
ntderivlg' (NTS B) dl
⇒
∃dl'.derives g ⊢ dl' ◁ [NTS A] → ([NTS A] ++ FRONT y)``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [][SNOC_APPEND] THEN
Cases_on `dl=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
IMP_RES_TAC listDerivLastBrk THEN
Cases_on `FRONT dl=[]` THEN SRW_TAC [][] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [rderives_def, listderiv_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ntderivlg'] THEN
      Cases_on `rhs=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
      (FIRST_X_ASSUM (Q.SPECL_THEN [`[NTS B]`,`[]`,`[]`,`[]`] MP_TAC) THEN 
       SRW_TAC [][]) THEN
      `rhs = FRONT rhs ++ [NTS B]` by METIS_TAC [APPEND_FRONT_LAST,
						    lastElemEq] THEN
      Q.EXISTS_TAC `[[NTS A];NTS A::FRONT rhs]` THEN
      SRW_TAC [][] THEN
      METIS_TAC [res1,ruleg'ImpgRec,APPEND],

      
      `LENGTH dl > 1` by (Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  DECIDE_TAC) THEN
      `dl = FRONT dl ++ [LAST dl]` by METIS_TAC [APPEND_FRONT_LAST] THEN
      `∃dl'.derives g ⊢ dl' ◁ [NTS A] → (NTS A::FRONT (LAST dl))` 
      by METIS_TAC [ntdlg'App] THEN
      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [ntderivlg'] THEN
      `MEM (LAST dl) dl` by METIS_TAC [MEM_APPEND,MEM] THEN
      `LAST (s1 ++ [NTS lhs] ++ s2 ) = NTS B` by METIS_TAC [] THEN
      Cases_on `s2≠[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
      (`s2 = FRONT s2 ++ [LAST s2]` by METIS_TAC [APPEND_FRONT_LAST] THEN
       `NTS B = LAST s2` by METIS_TAC [APPEND_FRONT_LAST, lastElemEq,last_append] THEN
       SRW_TAC [][] THEN
       `EVERY isTmnlSym (FRONT s2++[NTS B])` by METIS_TAC [] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
      Cases_on `rhs=[]` THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN1
      (`LENGTH s1 ≥ LENGTH (s1++[NTS B])` by METIS_TAC [APPEND_NIL,APPEND,
							APPEND_ASSOC] THEN
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
      `rhs = FRONT rhs ++ [NTS B]` by METIS_TAC [APPEND_FRONT_LAST,
						    lastElemEq,last_append] THEN
      SRW_TAC [][] THEN
      `rule A ([NTS A]++ FRONT rhs) ∈ rules g` by METIS_TAC [ruleg'ImpgRec] THEN      
      `FRONT (LAST dl) = s1` by METIS_TAC [frontAppendFst] THEN
      SRW_TAC [][] THEN
      `derives g [NTS A] ([NTS A]++FRONT rhs)` by METIS_TAC [res1] THEN
      `(derives g)^* [NTS A] (NTS A::FRONT (LAST dl)++FRONT rhs)`
      by METIS_TAC [ldImprtc2list,RTC_RULES,rtc_derives_same_append_right] THEN
      METIS_TAC [rtc2list_exists',frontAppendFst,APPEND_ASSOC,APPEND]      
      ]);



val leftnt = Define
`leftnt nt l =  ∃pfx sfx.EVERY isTmnlSym pfx ∧ (l = (pfx++[nt]++sfx))`;

val ldNumNt = Define 
`ldNumNt nt dl = LENGTH (FILTER (leftnt nt) dl)`;


val rightnt = Define
`rightnt nt l =  ∃pfx sfx.EVERY isTmnlSym sfx ∧ (l = (pfx++[nt]++sfx))`;

val rdNumNt = Define 
`rdNumNt nt dl = LENGTH (FILTER (rightnt nt) dl)`;


val ldNumNtApp = store_thm
("ldNumNtApp",
 ``∀l1 l2.(ldNumNt (NTS A) (l1 ++ l2) = 0) =
(ldNumNt (NTS A) l1 = 0) ∧ (ldNumNt (NTS A) l2 = 0)``,

Induct_on `l1` THEN SRW_TAC [][ldNumNt] THEN
FULL_SIMP_TAC (srw_ss()) [ldNumNt] THEN
METIS_TAC []);

val ldNumNtNeq = store_thm
("ldNumNtNeq",
``(ldNumNt (NTS A) [s1++[NTS lhs]++s2] = 0) ∧ EVERY isTmnlSym s1
⇒
lhs ≠ A``,

SRW_TAC [][ldNumNt] THEN
FULL_SIMP_TAC (srw_ss()) [leftnt] THEN
METIS_TAC [NOT_EVERY]);



val rdNumNtApp = store_thm
("rdNumNtApp",
 ``∀l1 l2.(rdNumNt (NTS A) (l1 ++ l2) = 0) =
(rdNumNt (NTS A) l1 = 0) ∧ (rdNumNt (NTS A) l2 = 0)``,

Induct_on `l1` THEN SRW_TAC [][rdNumNt] THEN
FULL_SIMP_TAC (srw_ss()) [rdNumNt] THEN
METIS_TAC []);

val rdNumNtNeq = store_thm
("rdNumNtNeq",
``(rdNumNt (NTS A) [s1++[NTS lhs]++s2] = 0) ∧ EVERY isTmnlSym s2
⇒
lhs ≠ A``,

SRW_TAC [][rdNumNt] THEN
FULL_SIMP_TAC (srw_ss()) [rightnt] THEN
METIS_TAC [NOT_EVERY]);


val listNtEq = store_thm
("listNtEq",
``(s1++[NTS nt]++s2 = pfx++[NTS nt']++sfx) ∧ EVERY isTmnlSym s1 ∧ EVERY isTmnlSym pfx
⇒
(s1=pfx) ∧ (nt=nt') ∧ (s2=sfx)``,

SRW_TAC [][] THEN
IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] 
 THENL[
       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) []]);



val listNtEq' = store_thm
("listNtEq'",
``(s1++[NTS nt]++s2 = pfx++[NTS nt']++sfx) ∧ EVERY isTmnlSym s2 ∧ EVERY isTmnlSym sfx
⇒
(s1=pfx) ∧ (nt=nt') ∧ (s2=sfx)``,

SRW_TAC [][] THEN
IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] 
 THENL[
       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [],

       IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       Cases_on `s1''`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
       IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) []]);


val ldNumNtEq = store_thm
("ldNumNtEq",
``(ldNumNt (NTS A) [s1++[NTS lhs]++s2] ≠ 0) ∧ EVERY isTmnlSym s1
⇒
(lhs = A)``,

SRW_TAC [][ldNumNt] THEN
FULL_SIMP_TAC (srw_ss()) [leftnt] THEN
METIS_TAC [listNtEq]);


val lnnSing = store_thm
("lnnSing",
``ldNumNt nt [e] ≠ 0 = 
∃pfx sfx.EVERY isTmnlSym pfx ∧ (e = pfx ++ [nt] ++ sfx)``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [ldNumNt, leftnt, EQ_IMP_THM] THEN
METIS_TAC [LENGTH_NIL,NOT_CONS_NIL]);


val dlsplit = store_thm
("dlsplit",
``∀dl x y.lderives g ⊢ dl ◁ x → y ∧ ldNumNt (NTS A) dl ≠ 0 ∧ LENGTH dl > 1
⇒
∃dl1 dl2 dl3. (dl = dl1++dl2++dl3) ∧ (ldNumNt (NTS A) dl1 = 0) ∧
 (∀e1 e2 p s.(dl2 = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1) ∧
 ∃pfx.EVERY isTmnlSym pfx  ∧ (∀e.MEM e dl2 ⇒ ∃sfx.(e=pfx++[NTS A]++sfx)) ∧ dl2≠[] ∧
 (dl3≠[] ⇒ LENGTH (LAST dl2) ≤ LENGTH (HD dl3) ⇒ 
  ¬IS_PREFIX (HD dl3) (pfx++[NTS A]))``,
 
Induct_on `dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN1 
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1

 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN SRW_TAC [][] THEN
  Cases_on `∃rst.rhs=NTS A::rst`
  THENL[
	`ldNumNt (NTS A) [s1++rhs++s2] ≠ 0` by 
	(SRW_TAC [][ldNumNt] THEN
	 FULL_SIMP_TAC (srw_ss()) [leftnt] THEN
	 METIS_TAC [NOT_EVERY, APPEND, APPEND_ASSOC]) THEN	
	Cases_on `ldNumNt (NTS A) [s1++[NTS lhs]++s2] = 0`
	THENL[
	      MAP_EVERY Q.EXISTS_TAC [`[s1++[NTS lhs]++s2]`,`[s1++rhs++s2]`,`[]`] THEN
	      SRW_TAC [][] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      METIS_TAC [lnnSing],

	      `lhs=A` by METIS_TAC [ldNumNtEq] THEN
	      SRW_TAC [][] THEN
	      MAP_EVERY Q.EXISTS_TAC [`[]`,`[s1++[NTS A]++s2;s1++NTS A::rst++s2]`,
				      `[]`] THEN
	      SRW_TAC [][ldNumNt] THEN
	      IMP_RES_TAC lnnSing THEN
	      SRW_TAC [][] THEN
	      `pfx=s1` by METIS_TAC [listNtEq] THEN
	      SRW_TAC [][] THEN
	      `s2=sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	      SRW_TAC [][] THEN
	      `pfx=pfx'` by METIS_TAC [listNtEq,APPEND,APPEND_ASSOC] THEN
	      SRW_TAC [][] THEN
	      `rst++s2 = sfx'` by METIS_TAC [APPEND_11, APPEND_ASSOC,APPEND] THEN
	      SRW_TAC [][] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	       SRW_TAC [][] THEN1
	       (Cases_on `rst` THEN SRW_TAC [ARITH_ss][]) THEN
	       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      METIS_TAC [APPEND_ASSOC]
	      ],
	      
	FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `ldNumNt (NTS A) [s1++rhs++s2] = 0` THEN
	Cases_on `ldNumNt (NTS A) [s1++[NTS lhs]++s2] = 0`
	THENL[
	      METIS_TAC [ldNumNtApp,APPEND],

	      `lhs=A` by METIS_TAC [ldNumNtEq] THEN
	      SRW_TAC [][] THEN
	      MAP_EVERY Q.EXISTS_TAC [`[]`,`[s1++[NTS A]++s2]`,`[s1++rhs++s2]`] THEN
	      SRW_TAC [][ldNumNt] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      Q.EXISTS_TAC `s1` THEN
	      SRW_TAC [][] THEN
	      SRW_TAC [][IS_PREFIX_APPEND] THEN
	      FULL_SIMP_TAC (srw_ss()) [ldNumNt,leftnt] THEN
	      `∀e.LENGTH [e] ≠ 0 ` by FULL_SIMP_TAC (srw_ss()) [] THEN
	      METIS_TAC [LENGTH_NIL, NOT_CONS_NIL],
	      
	      MAP_EVERY Q.EXISTS_TAC [`[s1++[NTS lhs]++s2]`,`[s1++rhs++s2]`,
				      `[]`] THEN
	      SRW_TAC [][ldNumNt] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      METIS_TAC [lnnSing],
	      
	      `lhs=A` by METIS_TAC [ldNumNtEq] THEN
	      SRW_TAC [][] THEN
	      MAP_EVERY Q.EXISTS_TAC [`[]`,`[s1++[NTS A]++s2]`,`[s1++rhs++s2]`] THEN
	      SRW_TAC [][ldNumNt] THEN
	      SRW_TAC [][] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      Q.EXISTS_TAC `s1` THEN
	      SRW_TAC [][] THEN
	      SRW_TAC [][IS_PREFIX_APPEND] THEN
	      IMP_RES_TAC lnnSing THEN
	      `(s1 = pfx) ∧ (s2=sfx)` by METIS_TAC [listNtEq] THEN
	      SRW_TAC [][] THEN
	      SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
	      `(pfx=pfx') ∧ (sfx'=l)`by METIS_TAC [listNtEq] THEN
	      SRW_TAC [][] THEN
	      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN
	      METIS_TAC [APPEND_11, APPEND_ASSOC,APPEND, APPEND_NIL, HD]
	      ]]) THEN

IMP_RES_TAC listDerivHdBrk THEN
Cases_on `ldNumNt (NTS A) (h'::h''::t') = 0` THEN1
(FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `ldNumNt (NTS A) [h] = 0` THEN1
  (`ldNumNt (NTS A) ([h]++h'::h''::t') = 0` by METIS_TAC [ldNumNtApp] THEN
   FULL_SIMP_TAC (srw_ss()) []) THEN
    MAP_EVERY Q.EXISTS_TAC [`[]`,`[h]`,`h'::h''::t'`] THEN
  SRW_TAC [][ldNumNt] THEN1
  (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
  SRW_TAC [][] THEN
  Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
  METIS_TAC [ldNumNtEq] THEN
  Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
  SRW_TAC [][] THEN1
  (`ldNumNt (NTS A) [s1++[h]++s2] = 0` by METIS_TAC [ldNumNtApp, APPEND] THEN
   `¬∃pfx sfx.EVERY isTmnlSym pfx ∧ (s1++[h]++s2=pfx++[NTS A]++sfx)` 
   by METIS_TAC [lnnSing] THEN
   SPOSE_NOT_THEN ASSUME_TAC THEN
   FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
   METIS_TAC [NOT_EVERY, listNtEq]) THEN
`ldNumNt (NTS A) [s1 ++ h::h'::t'' ++ s2] = 0` 
 by METIS_TAC [ldNumNtApp, APPEND] THEN
`¬∃pfx sfx.EVERY isTmnlSym pfx ∧ (s1 ++ h::h'::t'' ++ s2=pfx++[NTS A]++sfx)` 
 by METIS_TAC [lnnSing] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
METIS_TAC [NOT_EVERY, listNtEq]) THEN

 FULL_SIMP_TAC (arith_ss) [] THEN
 `∃dl1 dl2 dl3.
 (h'::h''::t' = dl1 ++ dl2 ++ dl3) ∧
 (ldNumNt (NTS A) dl1 = 0) ∧
 (∀e1 e2 p s.(dl2 = p ++ [e1; e2] ++ s) ⇒
  LENGTH e2 ≥ LENGTH e1) ∧
 ∃pfx.
 EVERY isTmnlSym pfx ∧
 (∀e.MEM e dl2 ⇒
  ∃sfx. e = pfx ++ [NTS A] ++ sfx) ∧ dl2 ≠ [] ∧
 (dl3 ≠ [] ⇒ LENGTH (LAST dl2) ≤ LENGTH (HD dl3) ⇒
  ¬(pfx ++ [NTS A] ≼ HD dl3))` by METIS_TAC [] THEN
 Cases_on `ldNumNt (NTS A) [h] = 0` THEN1
 (MAP_EVERY Q.EXISTS_TAC [`h::dl1`,`dl2`,`dl3`] THEN
  SRW_TAC [][] THEN
  METIS_TAC [APPEND, ldNumNtApp]) THEN
 Cases_on `dl1=[]` THEN SRW_TAC [][]
 THENL[
       Cases_on `dl3=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
       THENL[
	      FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
	      SRW_TAC [][] THEN
	      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) []
	      THENL[
		    MAP_EVERY Q.EXISTS_TAC [`[]`,`[s1++[NTS lhs]++s2]`,
					    `(s1 ++ s2)::h''::t'`] THEN
		    SRW_TAC [][] THEN1
		    (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
		    Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
		    METIS_TAC [ldNumNtEq] THEN
		    FULL_SIMP_TAC (arith_ss) [],

		    Cases_on `pfx=s1` THEN SRW_TAC [][]
		    THENL[			  
			  MAP_EVERY Q.EXISTS_TAC 
			  [`[]`,`[pfx++[NTS lhs]++s2]++
			   (pfx ++ h::t++s2)::h''::t'`,`[]`] THEN
			  SRW_TAC [][] THEN1		    
			  (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			   SRW_TAC [][] THEN1
			   DECIDE_TAC THEN METIS_TAC []) THEN
			  Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			  METIS_TAC [ldNumNtEq] THEN1
			  (`∃sfx.pfx++h::t++s2 =pfx++[NTS A]++sfx` by METIS_TAC [] THEN
			   `h::t++s2 = [NTS A]++sfx` by METIS_TAC [APPEND_11,
								   APPEND_ASSOC] THEN
			   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]) THEN    
			  METIS_TAC [listNtEq,APPEND,APPEND_ASSOC],

			  MAP_EVERY Q.EXISTS_TAC 
			  [`[]`,`[s1++[NTS lhs]++s2]`,
			   `(s1 ++ h::t++s2)::h''::t'`] THEN
			  SRW_TAC [][] THEN1		    
			  (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
			  Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
			  METIS_TAC [ldNumNtEq] THEN
			  `∃sfx.s1++h::t++s2 =pfx++[NTS A]++sfx` by METIS_TAC [] THEN
			  SPOSE_NOT_THEN ASSUME_TAC THEN
			  FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND]  THEN
			  `h::t++s2 = [NTS A]++l` by METIS_TAC [APPEND_11,
								  APPEND_ASSOC] THEN
			   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN    
			  METIS_TAC [listNtEq,APPEND,APPEND_ASSOC]
			  ]],

	     FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
	     SRW_TAC [][] THEN
	     Cases_on `s1=pfx` THEN SRW_TAC [][]
	     THENL[			     
 		   Cases_on `rhs` THEN SRW_TAC [][] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN1
		   (MAP_EVERY Q.EXISTS_TAC 
		    [`[]`,`[pfx ++ [NTS lhs] ++ s2]`,`(pfx ++ s2)::h''::t'`] THEN
		    SRW_TAC [][] THEN1
		    (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
		     SRW_TAC [][]) THEN
		    Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN
		    FULL_SIMP_TAC (arith_ss) [] THEN
		    METIS_TAC [lnnSing, ldNumNtEq]) THEN
		   `dl2 ++ dl3 = [pfx ++ h::t ++ s2]++h''::t'` 
		   by METIS_TAC [APPEND] THEN
		   IMP_RES_TAC twoListAppEq THEN 
		   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
		   THENL[
			 `h::t++s2 = [NTS A]++sfx` by METIS_TAC [APPEND_11,
								 APPEND_ASSOC] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
			 MAP_EVERY Q.EXISTS_TAC 
			 [`[]`,`(pfx ++ [NTS lhs] ++ s2)::[pfx ++ [NTS A] ++ t ++ s2]`,
			  `h''::t'`] THEN
			 SRW_TAC [][] THEN1			 
			 (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  SRW_TAC [][] THEN1
			  DECIDE_TAC THEN
			  Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
			 Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			 METIS_TAC [ldNumNtEq] THEN1
			 METIS_TAC [APPEND_ASSOC] THEN
			 FULL_SIMP_TAC (arith_ss) [],

			 `s1'++dl3= [h'']++t'` by METIS_TAC [APPEND] THEN
			 IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			 SRW_TAC [][]
			 THENL[
			       MAP_EVERY Q.EXISTS_TAC 
			       [`[]`,`(pfx ++ [NTS lhs] ++ s2)::(pfx ++ h::t ++ s2)::
				[h'']`,`dl3`] THEN SRW_TAC [][] THEN1
			       (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				SRW_TAC [][] THEN1
				DECIDE_TAC THEN
				METIS_TAC [APPEND, APPEND_NIL]) THEN
			       Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			       METIS_TAC [ldNumNtEq] THEN1
			       METIS_TAC [APPEND_ASSOC] THEN
			       FULL_SIMP_TAC (arith_ss) [],

			       MAP_EVERY Q.EXISTS_TAC 
			       [`[]`,`(pfx ++ [NTS lhs] ++ s2)::(pfx ++ h::t ++ s2)::
				[h'']++s1''`,`dl3`] THEN SRW_TAC [][] THEN1
			       (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				SRW_TAC [][] THEN1
				DECIDE_TAC THEN
				METIS_TAC [APPEND, APPEND_NIL]) THEN
			       Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			       METIS_TAC [ldNumNtEq] THEN1
			       METIS_TAC [APPEND_ASSOC] THEN
			       FULL_SIMP_TAC (arith_ss) [],

			       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			       SRW_TAC [][] THEN
			       `h::t++s2 = [NTS A]++sfx` 
			       by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
			       FULL_SIMP_TAC (srw_ss()) [] THEN
			       SRW_TAC [][] THEN
			       MAP_EVERY Q.EXISTS_TAC 
			       [`[]`,`(pfx ++ [NTS lhs] ++ s2)::[pfx ++ [NTS A] ++ (t ++ s2)]`,
				`h''::s2'`] THEN SRW_TAC [][] THEN1
			       (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				SRW_TAC [][] THEN1
				DECIDE_TAC THEN
				METIS_TAC [APPEND, APPEND_NIL]) THEN
			       Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			       METIS_TAC [ldNumNtEq] THEN1
			       METIS_TAC [APPEND_ASSOC] THEN
			       FULL_SIMP_TAC (arith_ss) [],
				     	
			       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			       SRW_TAC [][] 
			       THENL[
				     `h::t++s2 = [NTS A]++sfx` 
				     by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
				     FULL_SIMP_TAC (srw_ss()) [] THEN
				     SRW_TAC [][] THEN
				     MAP_EVERY Q.EXISTS_TAC 
				     [`[]`,`(pfx ++ [NTS lhs] ++ s2)::[pfx ++ [NTS A] ++ (t ++ s2)]`,
				      `h''::s2'`] THEN SRW_TAC [][] THEN1
				     (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				      SRW_TAC [][] THEN1
				      DECIDE_TAC THEN
				      METIS_TAC [APPEND, APPEND_NIL]) THEN
				     Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
				     METIS_TAC [ldNumNtEq] THEN1
				     METIS_TAC [APPEND_ASSOC] THEN
				     FULL_SIMP_TAC (arith_ss) [],
				     
				     MAP_EVERY Q.EXISTS_TAC
				     [`[]`,`(pfx ++ [NTS lhs] ++ s2)::[pfx ++ h::t ++ s2;h']`,
				      `s2'`] THEN SRW_TAC [][] THEN1
				     (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				      SRW_TAC [][] THEN1
				      DECIDE_TAC THEN
				      METIS_TAC []) THEN
				     Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
				     METIS_TAC [ldNumNtEq] THEN1
				     METIS_TAC [APPEND_ASSOC] THEN
				     FULL_SIMP_TAC (arith_ss) []
				     ]],

			 
		   Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN
		   `h::t++s2 = [NTS A]++sfx`by METIS_TAC [APPEND_ASSOC,
							  APPEND_11] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],

		   Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN		   
		   `h::t++s2 = [NTS A]++sfx`by METIS_TAC [APPEND_ASSOC,
							  APPEND_11] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
		   MAP_EVERY Q.EXISTS_TAC [`[]`,`(pfx ++ [NTS lhs] ++ s2)::
					   [pfx ++ [NTS A] ++ t ++ s2]`,
					   `h''::t'`] THEN SRW_TAC [][] THEN1
		   (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    SRW_TAC [][] THEN1 DECIDE_TAC THEN  METIS_TAC []) THEN
		   Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
		   METIS_TAC [ldNumNtEq] THEN1
		   METIS_TAC [APPEND_ASSOC] THEN
		   FULL_SIMP_TAC (arith_ss) []
		   ],
		   
	     (* s1 ≠ pfx *)
	     MAP_EVERY Q.EXISTS_TAC 
	     [`[]`,`[s1 ++ [NTS lhs] ++ s2]`,`dl2++dl3`] THEN
	     SRW_TAC [][] THEN1
	     (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	     Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
	     METIS_TAC [ldNumNtEq] THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     `∃sfx.s1++rhs++s2 = pfx++[NTS A]++sfx` by METIS_TAC [] THEN
	     SRW_TAC [][IS_PREFIX_APPEND] THEN
	     SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
	     METIS_TAC [listNtEq]
	     ]],
       
       Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN              
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       MAP_EVERY Q.EXISTS_TAC [`[]`,`[h]`,`h'::t++dl2++dl3`] THEN		  
       SRW_TAC [][ldNumNt] THEN1
       (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN SRW_TAC [][] THEN
       Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
       METIS_TAC [ldNumNtEq] THEN
       `¬∃pfx sfx.EVERY isTmnlSym pfx ∧ (s1++rhs++s2 = pfx ++ [NTS A]++sfx)`
       by METIS_TAC [lnnSing,ldNumNtApp,APPEND] THEN
       FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
       SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
       METIS_TAC [NOT_EVERY]
       ]);




val dlsplitB = store_thm
("dlsplitB",
``∀dl x y.lderives g ⊢ dl ◁ x → y ∧ rdNumNt (NTS B) dl ≠ 0 ∧ LENGTH dl > 1
⇒
∃dl1 dl2 dl3. (dl = dl1++dl2++dl3) ∧ (rdNumNt (NTS B) dl1 = 0) ∧
 (∀e1 e2 p s.(dl2 = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1) ∧
 ∃sfx.EVERY isTmnlSym sfx  ∧ (∀e.MEM e dl2 ⇒ ∃pfx.(e=pfx++[NTS B]++sfx)) ∧ dl2≠[] ∧
 (dl3≠[] ⇒ LENGTH (LAST dl2) ≤ LENGTH (HD dl3) ⇒ 
  ¬isSuffix ([NTS B]++sfx)) (HD dl3)``,
 
Induct_on `dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN1 
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1

 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN SRW_TAC [][] THEN
  Cases_on `∃rst.rhs=NTS A::rst`
  THENL[
	`ldNumNt (NTS A) [s1++rhs++s2] ≠ 0` by 
	(SRW_TAC [][ldNumNt] THEN
	 FULL_SIMP_TAC (srw_ss()) [leftnt] THEN
	 METIS_TAC [NOT_EVERY, APPEND, APPEND_ASSOC]) THEN	
	Cases_on `ldNumNt (NTS A) [s1++[NTS lhs]++s2] = 0`
	THENL[
	      MAP_EVERY Q.EXISTS_TAC [`[s1++[NTS lhs]++s2]`,`[s1++rhs++s2]`,`[]`] THEN
	      SRW_TAC [][] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      METIS_TAC [lnnSing],

	      `lhs=A` by METIS_TAC [ldNumNtEq] THEN
	      SRW_TAC [][] THEN
	      MAP_EVERY Q.EXISTS_TAC [`[]`,`[s1++[NTS A]++s2;s1++NTS A::rst++s2]`,
				      `[]`] THEN
	      SRW_TAC [][ldNumNt] THEN
	      IMP_RES_TAC lnnSing THEN
	      SRW_TAC [][] THEN
	      `pfx=s1` by METIS_TAC [listNtEq] THEN
	      SRW_TAC [][] THEN
	      `s2=sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	      SRW_TAC [][] THEN
	      `pfx=pfx'` by METIS_TAC [listNtEq,APPEND,APPEND_ASSOC] THEN
	      SRW_TAC [][] THEN
	      `rst++s2 = sfx'` by METIS_TAC [APPEND_11, APPEND_ASSOC,APPEND] THEN
	      SRW_TAC [][] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	       SRW_TAC [][] THEN1
	       (Cases_on `rst` THEN SRW_TAC [ARITH_ss][]) THEN
	       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      METIS_TAC [APPEND_ASSOC]
	      ],
	      
	FULL_SIMP_TAC (srw_ss()) [] THEN
	Cases_on `ldNumNt (NTS A) [s1++rhs++s2] = 0` THEN
	Cases_on `ldNumNt (NTS A) [s1++[NTS lhs]++s2] = 0`
	THENL[
	      METIS_TAC [ldNumNtApp,APPEND],

	      `lhs=A` by METIS_TAC [ldNumNtEq] THEN
	      SRW_TAC [][] THEN
	      MAP_EVERY Q.EXISTS_TAC [`[]`,`[s1++[NTS A]++s2]`,`[s1++rhs++s2]`] THEN
	      SRW_TAC [][ldNumNt] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      Q.EXISTS_TAC `s1` THEN
	      SRW_TAC [][] THEN
	      SRW_TAC [][IS_PREFIX_APPEND] THEN
	      FULL_SIMP_TAC (srw_ss()) [ldNumNt,leftnt] THEN
	      `∀e.LENGTH [e] ≠ 0 ` by FULL_SIMP_TAC (srw_ss()) [] THEN
	      METIS_TAC [LENGTH_NIL, NOT_CONS_NIL],
	      
	      MAP_EVERY Q.EXISTS_TAC [`[s1++[NTS lhs]++s2]`,`[s1++rhs++s2]`,
				      `[]`] THEN
	      SRW_TAC [][ldNumNt] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      METIS_TAC [lnnSing],
	      
	      `lhs=A` by METIS_TAC [ldNumNtEq] THEN
	      SRW_TAC [][] THEN
	      MAP_EVERY Q.EXISTS_TAC [`[]`,`[s1++[NTS A]++s2]`,`[s1++rhs++s2]`] THEN
	      SRW_TAC [][ldNumNt] THEN
	      SRW_TAC [][] THEN1
	      (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	      Q.EXISTS_TAC `s1` THEN
	      SRW_TAC [][] THEN
	      SRW_TAC [][IS_PREFIX_APPEND] THEN
	      IMP_RES_TAC lnnSing THEN
	      `(s1 = pfx) ∧ (s2=sfx)` by METIS_TAC [listNtEq] THEN
	      SRW_TAC [][] THEN
	      SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
	      `(pfx=pfx') ∧ (sfx'=l)`by METIS_TAC [listNtEq] THEN
	      SRW_TAC [][] THEN
	      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [][] THEN
	      METIS_TAC [APPEND_11, APPEND_ASSOC,APPEND, APPEND_NIL, HD]
	      ]]) THEN

IMP_RES_TAC listDerivHdBrk THEN
Cases_on `ldNumNt (NTS A) (h'::h''::t') = 0` THEN1
(FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `ldNumNt (NTS A) [h] = 0` THEN1
  (`ldNumNt (NTS A) ([h]++h'::h''::t') = 0` by METIS_TAC [ldNumNtApp] THEN
   FULL_SIMP_TAC (srw_ss()) []) THEN
    MAP_EVERY Q.EXISTS_TAC [`[]`,`[h]`,`h'::h''::t'`] THEN
  SRW_TAC [][ldNumNt] THEN1
  (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
  SRW_TAC [][] THEN
  Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
  METIS_TAC [ldNumNtEq] THEN
  Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
  SRW_TAC [][] THEN1
  (`ldNumNt (NTS A) [s1++[h]++s2] = 0` by METIS_TAC [ldNumNtApp, APPEND] THEN
   `¬∃pfx sfx.EVERY isTmnlSym pfx ∧ (s1++[h]++s2=pfx++[NTS A]++sfx)` 
   by METIS_TAC [lnnSing] THEN
   SPOSE_NOT_THEN ASSUME_TAC THEN
   FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
   METIS_TAC [NOT_EVERY, listNtEq]) THEN
`ldNumNt (NTS A) [s1 ++ h::h'::t'' ++ s2] = 0` 
 by METIS_TAC [ldNumNtApp, APPEND] THEN
`¬∃pfx sfx.EVERY isTmnlSym pfx ∧ (s1 ++ h::h'::t'' ++ s2=pfx++[NTS A]++sfx)` 
 by METIS_TAC [lnnSing] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
METIS_TAC [NOT_EVERY, listNtEq]) THEN

 FULL_SIMP_TAC (arith_ss) [] THEN
 `∃dl1 dl2 dl3.
 (h'::h''::t' = dl1 ++ dl2 ++ dl3) ∧
 (ldNumNt (NTS A) dl1 = 0) ∧
 (∀e1 e2 p s.(dl2 = p ++ [e1; e2] ++ s) ⇒
  LENGTH e2 ≥ LENGTH e1) ∧
 ∃pfx.
 EVERY isTmnlSym pfx ∧
 (∀e.MEM e dl2 ⇒
  ∃sfx. e = pfx ++ [NTS A] ++ sfx) ∧ dl2 ≠ [] ∧
 (dl3 ≠ [] ⇒ LENGTH (LAST dl2) ≤ LENGTH (HD dl3) ⇒
  ¬(pfx ++ [NTS A] ≼ HD dl3))` by METIS_TAC [] THEN
 Cases_on `ldNumNt (NTS A) [h] = 0` THEN1
 (MAP_EVERY Q.EXISTS_TAC [`h::dl1`,`dl2`,`dl3`] THEN
  SRW_TAC [][] THEN
  METIS_TAC [APPEND, ldNumNtApp]) THEN
 Cases_on `dl1=[]` THEN SRW_TAC [][]
 THENL[
       Cases_on `dl3=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
       THENL[
	      FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
	      SRW_TAC [][] THEN
	      Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) []
	      THENL[
		    MAP_EVERY Q.EXISTS_TAC [`[]`,`[s1++[NTS lhs]++s2]`,
					    `(s1 ++ s2)::h''::t'`] THEN
		    SRW_TAC [][] THEN1
		    (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
		    Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
		    METIS_TAC [ldNumNtEq] THEN
		    FULL_SIMP_TAC (arith_ss) [],

		    Cases_on `pfx=s1` THEN SRW_TAC [][]
		    THENL[			  
			  MAP_EVERY Q.EXISTS_TAC 
			  [`[]`,`[pfx++[NTS lhs]++s2]++
			   (pfx ++ h::t++s2)::h''::t'`,`[]`] THEN
			  SRW_TAC [][] THEN1		    
			  (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			   SRW_TAC [][] THEN1
			   DECIDE_TAC THEN METIS_TAC []) THEN
			  Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			  METIS_TAC [ldNumNtEq] THEN1
			  (`∃sfx.pfx++h::t++s2 =pfx++[NTS A]++sfx` by METIS_TAC [] THEN
			   `h::t++s2 = [NTS A]++sfx` by METIS_TAC [APPEND_11,
								   APPEND_ASSOC] THEN
			   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]) THEN    
			  METIS_TAC [listNtEq,APPEND,APPEND_ASSOC],

			  MAP_EVERY Q.EXISTS_TAC 
			  [`[]`,`[s1++[NTS lhs]++s2]`,
			   `(s1 ++ h::t++s2)::h''::t'`] THEN
			  SRW_TAC [][] THEN1		    
			  (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
			  Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
			  METIS_TAC [ldNumNtEq] THEN
			  `∃sfx.s1++h::t++s2 =pfx++[NTS A]++sfx` by METIS_TAC [] THEN
			  SPOSE_NOT_THEN ASSUME_TAC THEN
			  FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND]  THEN
			  `h::t++s2 = [NTS A]++l` by METIS_TAC [APPEND_11,
								  APPEND_ASSOC] THEN
			   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN    
			  METIS_TAC [listNtEq,APPEND,APPEND_ASSOC]
			  ]],

	     FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
	     SRW_TAC [][] THEN
	     Cases_on `s1=pfx` THEN SRW_TAC [][]
	     THENL[			     
 		   Cases_on `rhs` THEN SRW_TAC [][] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN1
		   (MAP_EVERY Q.EXISTS_TAC 
		    [`[]`,`[pfx ++ [NTS lhs] ++ s2]`,`(pfx ++ s2)::h''::t'`] THEN
		    SRW_TAC [][] THEN1
		    (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
		     SRW_TAC [][]) THEN
		    Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN
		    FULL_SIMP_TAC (arith_ss) [] THEN
		    METIS_TAC [lnnSing, ldNumNtEq]) THEN
		   `dl2 ++ dl3 = [pfx ++ h::t ++ s2]++h''::t'` 
		   by METIS_TAC [APPEND] THEN
		   IMP_RES_TAC twoListAppEq THEN 
		   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
		   THENL[
			 `h::t++s2 = [NTS A]++sfx` by METIS_TAC [APPEND_11,
								 APPEND_ASSOC] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
			 MAP_EVERY Q.EXISTS_TAC 
			 [`[]`,`(pfx ++ [NTS lhs] ++ s2)::[pfx ++ [NTS A] ++ t ++ s2]`,
			  `h''::t'`] THEN
			 SRW_TAC [][] THEN1			 
			 (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			  SRW_TAC [][] THEN1
			  DECIDE_TAC THEN
			  Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
			 Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			 METIS_TAC [ldNumNtEq] THEN1
			 METIS_TAC [APPEND_ASSOC] THEN
			 FULL_SIMP_TAC (arith_ss) [],

			 `s1'++dl3= [h'']++t'` by METIS_TAC [APPEND] THEN
			 IMP_RES_TAC twoListAppEq THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			 SRW_TAC [][]
			 THENL[
			       MAP_EVERY Q.EXISTS_TAC 
			       [`[]`,`(pfx ++ [NTS lhs] ++ s2)::(pfx ++ h::t ++ s2)::
				[h'']`,`dl3`] THEN SRW_TAC [][] THEN1
			       (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				SRW_TAC [][] THEN1
				DECIDE_TAC THEN
				METIS_TAC [APPEND, APPEND_NIL]) THEN
			       Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			       METIS_TAC [ldNumNtEq] THEN1
			       METIS_TAC [APPEND_ASSOC] THEN
			       FULL_SIMP_TAC (arith_ss) [],

			       MAP_EVERY Q.EXISTS_TAC 
			       [`[]`,`(pfx ++ [NTS lhs] ++ s2)::(pfx ++ h::t ++ s2)::
				[h'']++s1''`,`dl3`] THEN SRW_TAC [][] THEN1
			       (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				SRW_TAC [][] THEN1
				DECIDE_TAC THEN
				METIS_TAC [APPEND, APPEND_NIL]) THEN
			       Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			       METIS_TAC [ldNumNtEq] THEN1
			       METIS_TAC [APPEND_ASSOC] THEN
			       FULL_SIMP_TAC (arith_ss) [],

			       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			       SRW_TAC [][] THEN
			       `h::t++s2 = [NTS A]++sfx` 
			       by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
			       FULL_SIMP_TAC (srw_ss()) [] THEN
			       SRW_TAC [][] THEN
			       MAP_EVERY Q.EXISTS_TAC 
			       [`[]`,`(pfx ++ [NTS lhs] ++ s2)::[pfx ++ [NTS A] ++ (t ++ s2)]`,
				`h''::s2'`] THEN SRW_TAC [][] THEN1
			       (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				SRW_TAC [][] THEN1
				DECIDE_TAC THEN
				METIS_TAC [APPEND, APPEND_NIL]) THEN
			       Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
			       METIS_TAC [ldNumNtEq] THEN1
			       METIS_TAC [APPEND_ASSOC] THEN
			       FULL_SIMP_TAC (arith_ss) [],
				     	
			       Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			       SRW_TAC [][] 
			       THENL[
				     `h::t++s2 = [NTS A]++sfx` 
				     by METIS_TAC [APPEND_ASSOC,APPEND_11] THEN
				     FULL_SIMP_TAC (srw_ss()) [] THEN
				     SRW_TAC [][] THEN
				     MAP_EVERY Q.EXISTS_TAC 
				     [`[]`,`(pfx ++ [NTS lhs] ++ s2)::[pfx ++ [NTS A] ++ (t ++ s2)]`,
				      `h''::s2'`] THEN SRW_TAC [][] THEN1
				     (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				      SRW_TAC [][] THEN1
				      DECIDE_TAC THEN
				      METIS_TAC [APPEND, APPEND_NIL]) THEN
				     Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
				     METIS_TAC [ldNumNtEq] THEN1
				     METIS_TAC [APPEND_ASSOC] THEN
				     FULL_SIMP_TAC (arith_ss) [],
				     
				     MAP_EVERY Q.EXISTS_TAC
				     [`[]`,`(pfx ++ [NTS lhs] ++ s2)::[pfx ++ h::t ++ s2;h']`,
				      `s2'`] THEN SRW_TAC [][] THEN1
				     (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
				      SRW_TAC [][] THEN1
				      DECIDE_TAC THEN
				      METIS_TAC []) THEN
				     Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
				     METIS_TAC [ldNumNtEq] THEN1
				     METIS_TAC [APPEND_ASSOC] THEN
				     FULL_SIMP_TAC (arith_ss) []
				     ]],

			 
		   Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN
		   `h::t++s2 = [NTS A]++sfx`by METIS_TAC [APPEND_ASSOC,
							  APPEND_11] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][],

		   Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][] THEN		   
		   `h::t++s2 = [NTS A]++sfx`by METIS_TAC [APPEND_ASSOC,
							  APPEND_11] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
		   MAP_EVERY Q.EXISTS_TAC [`[]`,`(pfx ++ [NTS lhs] ++ s2)::
					   [pfx ++ [NTS A] ++ t ++ s2]`,
					   `h''::t'`] THEN SRW_TAC [][] THEN1
		   (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		    SRW_TAC [][] THEN1 DECIDE_TAC THEN  METIS_TAC []) THEN
		   Q.EXISTS_TAC `pfx` THEN SRW_TAC [][] THEN1
		   METIS_TAC [ldNumNtEq] THEN1
		   METIS_TAC [APPEND_ASSOC] THEN
		   FULL_SIMP_TAC (arith_ss) []
		   ],
		   
	     (* s1 ≠ pfx *)
	     MAP_EVERY Q.EXISTS_TAC 
	     [`[]`,`[s1 ++ [NTS lhs] ++ s2]`,`dl2++dl3`] THEN
	     SRW_TAC [][] THEN1
	     (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	     Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
	     METIS_TAC [ldNumNtEq] THEN
	     Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [][] THEN
	     `∃sfx.s1++rhs++s2 = pfx++[NTS A]++sfx` by METIS_TAC [] THEN
	     SRW_TAC [][IS_PREFIX_APPEND] THEN
	     SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
	     METIS_TAC [listNtEq]
	     ]],
       
       Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN              
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       MAP_EVERY Q.EXISTS_TAC [`[]`,`[h]`,`h'::t++dl2++dl3`] THEN		  
       SRW_TAC [][ldNumNt] THEN1
       (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN SRW_TAC [][] THEN
       Q.EXISTS_TAC `s1` THEN SRW_TAC [][] THEN1
       METIS_TAC [ldNumNtEq] THEN
       `¬∃pfx sfx.EVERY isTmnlSym pfx ∧ (s1++rhs++s2 = pfx ++ [NTS A]++sfx)`
       by METIS_TAC [lnnSing,ldNumNtApp,APPEND] THEN
       FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
       SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
       METIS_TAC [NOT_EVERY]
       ]);


val blkNilgImpg' = store_thm
("blkNilgImpg'",
``∀dl x.lderives g ⊢ dl ◁ x → y ∧ left2Right A B g g' ∧ 
(ldNumNt (NTS A) dl = 0) ⇒
lderives g' ⊢ dl ◁ x → y``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][]) THEN

IMP_RES_TAC listDerivHdBrk THEN
`h = x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
`ldNumNt (NTS A) (h'::t) = 0` by METIS_TAC [ldNumNtApp, APPEND] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h'`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
`lhs ≠ A` by METIS_TAC [ldNumNtApp, APPEND, ldNumNtNeq] THEN
`rule lhs rhs ∈ rules g'` by METIS_TAC [rulegImpg'] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
METIS_TAC [ldres1, lderives_same_append_right, lderives_same_append_left]);


val blkNilgImpg'd = store_thm
("blkNilgImpg'd",
``∀dl x.lderives g ⊢ dl ◁ x → y ∧ left2Right A B g g' ∧ 
(ldNumNt (NTS A) dl = 0) ⇒
derives g' ⊢ dl ◁ x → y``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][]) THEN

IMP_RES_TAC listDerivHdBrk THEN
`h = x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
`ldNumNt (NTS A) (h'::t) = 0` by METIS_TAC [ldNumNtApp, APPEND] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h'`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
`lhs ≠ A` by METIS_TAC [ldNumNtApp, APPEND, ldNumNtNeq] THEN
`rule lhs rhs ∈ rules g'` by METIS_TAC [rulegImpg'] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
METIS_TAC [res1, derives_same_append_right, derives_same_append_left]);

val ruleg'Impg = store_thm
("ruleg'Impg",
``left2Right A B g g' ∧ rule lhs rhs ∈ rules g' ∧ lhs ≠ B ∧
((rhs =[]) ∨ (LAST rhs ≠ NTS B))
⇒
rule lhs rhs ∈ rules g``,

SRW_TAC [][left2Right, nonLeftRecRules, leftRecRules,EXTENSION] THEN1
(FIRST_X_ASSUM (Q.SPECL_THEN [`rule lhs []`] MP_TAC) THEN SRW_TAC [][]) THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`rule lhs rhs`] MP_TAC) THEN SRW_TAC [][] THEN
METIS_TAC [last_elem,MEM]);


val rdNumNt0 = store_thm
("rdNumNt0",
``(rdNumNt (NTS B) [s1 ++ rhs ++ s2] = 0) ∧ EVERY isTmnlSym s2 ⇒
((rhs = []) ∨ (LAST rhs ≠ NTS B))``,

SRW_TAC [][rdNumNt] THEN
FULL_SIMP_TAC (srw_ss()) [rightnt] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s1++FRONT rhs`,`s2`] MP_TAC) THEN SRW_TAC [][] THEN1
METIS_TAC [everyNotTwice] THEN
METIS_TAC [NOT_EVERY,APPEND_FRONT_LAST,APPEND_ASSOC]);



val blkNilg'Impgd = store_thm
("blkNilg'Impgd",
``∀dl x.rderives g' ⊢ dl ◁ x → y ∧ left2Right A B g g' ∧ 
(rdNumNt (NTS B) dl = 0) ⇒
derives g ⊢ dl ◁ x → y``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][]) THEN

IMP_RES_TAC listDerivHdBrk THEN
`h = x` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
`rdNumNt (NTS B) (h'::t) = 0` by METIS_TAC [rdNumNtApp, APPEND] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h'`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [][] THEN
`lhs ≠ B` by METIS_TAC [rdNumNtApp, APPEND, rdNumNtNeq] THEN
`(rhs = []) ∨ LAST rhs ≠ NTS B` by METIS_TAC [rdNumNt0,rdNumNtApp,APPEND] THEN
`rule lhs rhs ∈ rules g` by METIS_TAC [ruleg'Impg] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
METIS_TAC [res1, derives_same_append_right, derives_same_append_left,APPEND_NIL]);


val ldAstream = store_thm
("ldAstream",
``∀dl pfx m sfx.lderives (g:(α,α,α,β) grammar) ⊢ 
 dl ◁ (pfx++([NTS A]++m)++sfx) → y ∧ 
EVERY isTmnlSym pfx ∧
(∀e. MEM e dl ⇒ ∃sfx. e = pfx ++ [NTS A] ++ sfx) ∧
(∀e1 e2 p s.(dl = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1)
⇒
∃dl' y'.lderives g ⊢ dl' ◁ ([NTS A]++m) → y' ∧ 
(dl = MAP (λe.addLast e sfx) (MAP (addFront pfx) dl')) ∧
(∀e.MEM e dl' ⇒ (HD e = (NTS A))) ∧
(∀e1 e2 p s.(dl' = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1)``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][] THEN
 Q.EXISTS_TAC `[[NTS A]++m]` THEN SRW_TAC [][] THEN
 SRW_TAC [][addFront_def, addLast_def] THEN1
 METIS_TAC [APPEND,APPEND_ASSOC] THEN
 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN

 IMP_RES_TAC listDerivHdBrk THEN
`h = pfx++[NTS A]++m++sfx`by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN SRW_TAC [][] THEN
`(s1=pfx) ∧ (lhs=A) ∧ (s2=m++sfx)` by METIS_TAC [listNtEq,APPEND_ASSOC] THEN
SRW_TAC [][] THEN
Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(`LENGTH (pfx++m++sfx) ≥ LENGTH (pfx++[NTS A]++m++sfx)` 
 by METIS_TAC [APPEND,APPEND_NIL] THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`∃sfx'.pfx++h::t'++m++sfx = pfx++[NTS A]++sfx'` by METIS_TAC [] THEN
`h::t'++m++sfx = [NTS A]++sfx'` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
`(∀e1 e2 p s.
  ((pfx ++ [NTS A] ++ t' ++ m ++ sfx)::t =
   p ++ [e1; e2] ++ s) ⇒
  LENGTH e2 ≥ LENGTH e1)` by METIS_TAC [APPEND,APPEND_ASSOC] THEN
`(∀e. (e = pfx ++ [NTS A] ++ t' ++ m ++ sfx) ∨ MEM e t ⇒
  ∃sfx. e = pfx ++ [NTS A] ++ sfx)` by METIS_TAC [APPEND_ASSOC] THEN
`lderives g ⊢ (pfx ++ [NTS A] ++ t' ++ m ++ sfx)::t ◁
pfx ++ [NTS A] ++ t' ++ m ++ sfx → y` by METIS_TAC [APPEND_ASSOC,APPEND] THEN
Q.PAT_ASSUM `∀e.P e` MP_TAC THEN
Q.PAT_ASSUM `∀e.P e` MP_TAC THEN
Q.PAT_ASSUM `∀e.P e` MP_TAC THEN
Q.PAT_ASSUM `∀e.P e` MP_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`,`t'++m`,`sfx`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃dl' y'.
lderives g ⊢ dl' ◁ NTS A::(t' ++ m) → y' ∧
((pfx ++ [NTS A] ++ t' ++ m ++ sfx)::t =
 MAP (λe. addLast e sfx) (MAP (addFront pfx) dl')) ∧
(∀e. MEM e dl' ⇒ (HD e = NTS A)) ∧
∀e1 e2 p s.
(dl' = p ++ [e1; e2] ++ s) ⇒
LENGTH e2 ≥ LENGTH e1` by METIS_TAC [] THEN
MAP_EVERY Q.EXISTS_TAC [`[NTS A::m]++dl'`,`y'`] THEN
SRW_TAC [][] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [ldres1,APPEND,APPEND_ASSOC,lderives_same_append_right],

      SRW_TAC [][addFront_def, addLast_def] THEN
      METIS_TAC [APPEND,APPEND_ASSOC],

      SRW_TAC [][],

      METIS_TAC [],

      Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN1
      (`e2 = NTS A::(t'++m)` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       SRW_TAC [][] THEN
       DECIDE_TAC) THEN
      METIS_TAC [APPEND,APPEND_ASSOC]
      ]);


val ldBstream = store_thm
("ldBstream",
``∀dl pfx m sfx.rderives (g:(α,α,α,β) grammar) ⊢ 
 dl ◁ (pfx++(m++[NTS B])++sfx) → y ∧ 
EVERY isTmnlSym sfx ∧
(∀e. MEM e dl ⇒ ∃pfx. e = pfx ++ [NTS B] ++ sfx) ∧
(∀e1 e2 p s.(dl = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1)
⇒
∃dl' y'.rderives g ⊢ dl' ◁ (m++[NTS B]) → y' ∧ 
(dl = MAP (λe.addLast e sfx) (MAP (addFront pfx) dl')) ∧
(∀e.MEM e dl' ⇒ (LAST e = (NTS B))) ∧
(∀e1 e2 p s.(dl' = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1)``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN SRW_TAC [][] THEN
 Q.EXISTS_TAC `[m++[NTS B]]` THEN SRW_TAC [][] THEN
 SRW_TAC [][addFront_def, addLast_def] THEN
 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []) THEN

 IMP_RES_TAC listDerivHdBrk THEN
`h = pfx++m++[NTS B]++sfx`by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN SRW_TAC [][] THEN
`(s1=pfx++m) ∧ (lhs=B) ∧ (s2=sfx)` by METIS_TAC [listNtEq'] THEN
SRW_TAC [][] THEN
`∃pfx'.pfx++m++rhs++s2 = pfx'++[NTS B]++s2` by METIS_TAC [] THEN
`pfx++m++rhs = pfx'++[NTS B]` by METIS_TAC [APPEND_11] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `rhs=[]` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
(`LENGTH (pfx' ++ [NTS B] ++ s2) ≥ LENGTH (pfx' ++ [NTS B] ++ [NTS B] ++ s2)`
 by METIS_TAC [APPEND,APPEND_NIL] THEN
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`rhs = FRONT rhs++[LAST rhs]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`LAST rhs = NTS B` by METIS_TAC [lastElemEq,APPEND_ASSOC] THEN
SRW_TAC [][] THEN
`(∀e.(e = pfx' ++ [NTS B] ++ s2) ∨ MEM e t ⇒ ∃pfx. e = pfx ++ [NTS B] ++ s2)`
by METIS_TAC [] THEN
`(∀e1 e2 p s.((pfx' ++ [NTS B] ++ s2)::t = p ++ [e1; e2] ++ s) ⇒
  LENGTH e2 ≥ LENGTH e1)` by METIS_TAC [APPEND,APPEND_ASSOC] THEN
`pfx'=pfx++m++FRONT rhs`by METIS_TAC [APPEND_11,symbol_11,APPEND_ASSOC] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`,`m++FRONT rhs`,`s2`] MP_TAC) THEN 
SRW_TAC [][] THEN
RES_TAC THEN
Q.EXISTS_TAC `(m++[NTS B])::dl'` THEN
Q.EXISTS_TAC `y'` THEN
SRW_TAC [][] THEN1
(Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 METIS_TAC [rdres1,rderives_same_append_left,APPEND_ASSOC]) THEN1
SRW_TAC [][addFront_def,addLast_def] THEN1
METIS_TAC [] THEN1
METIS_TAC [last_elem] THEN1
METIS_TAC [] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN1
(`e2 = m ++ FRONT rhs++[NTS B]` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 SRW_TAC [][] THEN DECIDE_TAC) THEN
METIS_TAC []);



val ldgImpg' = store_thm
("ldgImpg'",
``lderives g (pfx++[NTS A]++sfx) y' ∧ EVERY isTmnlSym pfx ∧
left2Right A B g g' ∧
(LENGTH (pfx++[NTS A]++sfx) ≤ LENGTH y' ⇒ ¬(pfx ++ [NTS A] ≼ y'))
⇒
derives g' (pfx++[NTS A]++sfx) y'``,

SRW_TAC [][lderives_def] THEN
`(s1=pfx) ∧ (lhs=A) ∧ (s2=sfx)`by METIS_TAC [listNtEq] THEN
SRW_TAC [][] THEN
Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (`rule A [] ∈ rules g'`
  by FULL_SIMP_TAC (srw_ss()) [left2Right,nonLeftRecRules,leftRecRules] THEN
  METIS_TAC [res1, derives_same_append_left,derives_same_append_right,
	   rulegImpg'4,APPEND_NIL]) THEN
FULL_SIMP_TAC (arith_ss) [] THEN
`¬∃rst.h::t = NTS A::rst` 
 by (SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
     FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND]THEN
     METIS_TAC [APPEND,APPEND_ASSOC,NOT_EVERY]) THEN
 METIS_TAC [res1, derives_same_append_left,derives_same_append_right,
	    rulegImpg'4]);


val ldAddFrontLast = store_thm
("ldAddFrontLast",
``∀dl x.derives g ⊢ dl ◁ x → y ⇒
derives g ⊢ (MAP (λe. e ++ sfx) (MAP (addFront pfx) dl)) ◁ 
(pfx++x++sfx) → (pfx++y++sfx)``,

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [listderiv_def, addFront_def, addLast_def] THEN
  SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN
`h = x`by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h'`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][addFront_def, addLast_def] THEN
METIS_TAC [derives_same_append_left, derives_same_append_right]);


val elemNotNil = store_thm
("elemNotNil",
``∀dl' e.lderives g ⊢ dl' ◁ e → LAST dl' ∧ e ≠ [] ∧
(∀e1 e2 p s. (dl' = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1)
⇒
(LAST dl' ≠ [])``,

Induct_on `dl'` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
IMP_RES_TAC listDerivHdBrk THEN
`e=h` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
`(∀e1 e2 p s.(h'::t = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1)`
 by METIS_TAC [APPEND,APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
SRW_TAC [][] THEN
Cases_on `s1++rhs++s2=[]` THEN1
(SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
 Q.PAT_ASSUM `∀e.P e` MP_TAC THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`[NTS lhs]`,`[]`,`[]`,`t`] MP_TAC) THEN 
 SRW_TAC [][]) THEN
METIS_TAC []);

val nlrecgImpg' = store_thm
("nlrecgImpg'",
``left2Right A B g g' ∧ rule A rhs ∈ nonLeftRecRules g A
⇒
rule A (rhs++[NTS B]) ∈ rules g'``,

SRW_TAC [][left2Right,nonLeftRecRules,leftRecRules] THEN
METIS_TAC [slemma1_4,APPEND_NIL]);




val ntdlgImpg'3 = store_thm
("ntdlgImpg'3",
``∀dl.lderives g ⊢ dl ◁ (pfx++[NTS A]++sfx) → y ∧ left2Right A B g g' ∧ 
EVERY isTmnlSym pfx ∧ 
(∀e. MEM e dl ⇒ ∃sfx. e = pfx ++ [NTS A] ++ sfx) ∧
(∀e1 e2 p s.(dl = p ++ [e1; e2] ++ s) ⇒ LENGTH e2 ≥ LENGTH e1) ∧
(LENGTH y ≤ LENGTH y' ⇒ ¬(pfx ++ [NTS A] ≼ y')) ∧
lderives g y y'
⇒
∃dl'.derives g' ⊢ dl' ◁ (pfx++[NTS A]++sfx) → y'``,

SRW_TAC [][] THEN
IMP_RES_TAC ldAstream THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`y`,`sfx`,`[]:(α,β) symbol list`,`g`] MP_TAC) THEN 
SRW_TAC [][] THEN
Cases_on `LENGTH dl' > 1` 
THENL[
      `ntderivl (NTS A) dl'` by METIS_TAC [ntderivl] THEN
      `∃dl''. derives g' ⊢ dl'' ◁ [NTS B] → TL y''` by METIS_TAC [ntdlgImpg''] THEN
      `LAST dl' = y''` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `LAST (MAP (λe. addLast e sfx) (MAP (addFront pfx) dl')) = y` by
      FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `dl' ≠ []` by (Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
      `dl' = FRONT dl' ++ [y'']`by METIS_TAC [APPEND_FRONT_LAST] THEN
      `y = LAST (MAP (λe. addLast e sfx) (MAP (addFront pfx) (FRONT dl'++[y''])))`
      by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN     
      FULL_SIMP_TAC (srw_ss()) [addFront_def,addLast_def] THEN
      SRW_TAC [][] THEN
      `LAST dl' ≠ []` by METIS_TAC [elemNotNil,MEM] THEN
      Cases_on `LAST dl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      `h = NTS A` by METIS_TAC [HD,memld] THEN
      SRW_TAC [][] THEN
      `pfx++NTS A::t++sfx = pfx++[NTS A]++(t++sfx)`by METIS_TAC [APPEND_ASSOC,
								 APPEND] THEN
      `LENGTH pfx + SUC (LENGTH t) + LENGTH sfx = LENGTH(pfx++NTS A::t++sfx)`
      by FULL_SIMP_TAC (srw_ss()) [] THEN
      `derives g' (pfx++NTS A::t++sfx) y'` by METIS_TAC [ldgImpg'] THEN
      FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
      SRW_TAC [][] THEN
      `(s1=pfx) ∧(lhs=A) ∧ (s2=t++sfx)` by METIS_TAC [listNtEq,APPEND_ASSOC] THEN
      SRW_TAC [][] THEN
      `rule A rhs ∈ nonLeftRecRules g A` by
      (FULL_SIMP_TAC (srw_ss()) [nonLeftRecRules] THEN
       SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) [IS_PREFIX_APPEND] THEN
       METIS_TAC [listNtEq,APPEND_ASSOC,APPEND,NOT_EVERY]) THEN
      `rule A (rhs++[NTS B]) ∈ rules g'` by METIS_TAC [nlrecgImpg'] THEN
      `derives g' (pfx++ [NTS A]++sfx) (pfx++rhs++[NTS B]++sfx)`
      by METIS_TAC [res1,derives_same_append_right,derives_same_append_left,
		    APPEND_ASSOC] THEN
      `derives g' ⊢ (MAP (λe. e ++ sfx) (MAP (addFront (pfx++rhs)) dl'')) ◁ 
        (pfx++rhs++[NTS B]++sfx) → (pfx++rhs++t++sfx)`
      by METIS_TAC [ldAddFrontLast,APPEND_ASSOC] THEN
      Q.EXISTS_TAC `(pfx ++ [NTS A] ++ sfx)::
	MAP (λe. e ++ sfx)(MAP (addFront (pfx ++ rhs)) dl'')` THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      SRW_TAC [][] THEN1
      (Cases_on `dl''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       `dl'' ≠ []` by (Cases_on `dl''` THEN FULL_SIMP_TAC (srw_ss()) [])) THEN
       `MAP (λe. e ++ sfx) (MAP (addFront (pfx ++ rhs)) dl'') ≠ []`
       by (Cases_on `dl''` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
       METIS_TAC [last_append,APPEND],

      Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `[pfx++[NTS A]++sfx;y']` THEN
      SRW_TAC [][] THEN
      METIS_TAC [ldgImpg']
      ]);




val ldNumNtAppEq = store_thm
("ldNumNtAppEq",
``∀dl1 dl2.ldNumNt (NTS A) (dl1++dl2) = ldNumNt (NTS A) dl1 + ldNumNt (NTS A) dl2``,

Induct_on `dl1` THEN SRW_TAC [][ldNumNt] THEN
FULL_SIMP_TAC (srw_ss()) [ldNumNt] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`dl2`] MP_TAC) THEN SRW_TAC [][] THEN
DECIDE_TAC);

val gImpg'Nt0 = store_thm
("gImpg'Nt0",
``lderives g x y ∧ (ldNumNt (NTS A) [x] = 0) ∧ left2Right A B g g'
⇒
derives g' x y``,

SRW_TAC [][lderives_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [ldNumNt,leftnt] THEN
Cases_on `∃pfx sfx.EVERY isTmnlSym pfx ∧ 
 (s1 ++ [NTS lhs] ++ s2 = pfx ++ [NTS A] ++ sfx)` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s1`,`s2`] MP_TAC) THEN SRW_TAC [][] THEN1
METIS_TAC [NOT_EVERY] THEN
METIS_TAC [derives_same_append_left,derives_same_append_right,rulegImpg',res1]);


val ldgImpg' = store_thm
("ldgImpg'",
``∀x y.lderives g ⊢ dl ◁ x → y ∧ EVERY isTmnlSym y ∧ left2Right A B g g' 
 ⇒ 
 ∃dl'.derives g' ⊢ dl' ◁ x → y``,

completeInduct_on `ldNumNt (NTS A) dl` THEN
SRW_TAC [][] THEN
Cases_on `ldNumNt (NTS A) dl = 0` THEN1
METIS_TAC [blkNilgImpg'd] THEN
Cases_on `LENGTH dl > 1` 
THENL[
      `∃dl1 dl2 dl3.
           (dl = dl1 ++ dl2 ++ dl3) ∧
           (ldNumNt (NTS A) dl1 = 0) ∧
           (∀e1 e2 p s.
              (dl2 = p ++ [e1; e2] ++ s) ⇒
              LENGTH e2 ≥ LENGTH e1) ∧
           ∃pfx.
             EVERY isTmnlSym pfx ∧
             (∀e. MEM e dl2 ⇒ ∃sfx. e = pfx ++ [NTS A] ++ sfx) ∧
             dl2 ≠ [] ∧
             (dl3 ≠ [] ⇒
              LENGTH (LAST dl2) ≤ LENGTH (HD dl3) ⇒
              ¬(pfx ++ [NTS A] ≼ HD dl3))` by MAGIC (* METIS_TAC [dlsplit]*) THEN
      SRW_TAC [][] THEN
      `ldNumNt (NTS A) dl2 > 0` by
      (Cases_on `dl2` THEN 
       FULL_SIMP_TAC (srw_ss()) [ldNumNt,leftnt] THEN
       `∃pfx sfx.EVERY isTmnlSym pfx ∧ (h = pfx ++ [NTS A] ++ sfx)`
       by METIS_TAC [] THEN
       SRW_TAC [][] THEN
       METIS_TAC []) THEN
      `ldNumNt (NTS A) (dl1++dl2++dl3) = 
	     ldNumNt (NTS A) dl1 + ldNumNt (NTS A) dl2 + ldNumNt (NTS A) dl3` 
      by METIS_TAC [ldNumNtAppEq,APPEND_ASSOC] THEN
      `ldNumNt (NTS A) dl3 < ldNumNt (NTS A) (dl1++dl2++dl3)` by DECIDE_TAC THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`ldNumNt (NTS A) dl3`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `dl3 ≠ []` 
      by (SRW_TAC [][] THEN
	  SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
	  FULL_SIMP_TAC (srw_ss()) [] THEN
	  `LAST dl2 = y` by METIS_TAC [listderiv_def,APPEND_FRONT_LAST,APPEND_ASSOC,
				       lastElemEq,last_append] THEN
	  `∃sfx.y = pfx++[NTS A]++sfx`by METIS_TAC [MEM_APPEND,MEM,
						    APPEND_FRONT_LAST] THEN
	  SRW_TAC [][] THEN
	  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
      `lderives g ⊢ dl3 ◁ HD dl3 → y` by METIS_TAC [ldsubderivs,
						    APPEND_ASSOC] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`A`,`dl3`] MP_TAC) THEN SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`HD dl3`,`y`] MP_TAC ) THEN
      SRW_TAC [][] THEN      
      `lderives g ⊢ dl2 ◁ HD dl2 → LAST dl2` by METIS_TAC [ldsubderivs,
							   APPEND_ASSOC] THEN
      `∃sfx.HD dl2 = pfx++[NTS A]++sfx` by METIS_TAC [MEM,CONS,NULL_EQ_NIL] THEN
      `dl3 = HD dl3::TL dl3` by METIS_TAC [CONS,NULL_EQ_NIL] THEN
      `lderives g (LAST dl2) (HD dl3)` by METIS_TAC [ldAdjElem,APPEND_FRONT_LAST,
						     APPEND_ASSOC,APPEND] THEN
      `∃dl''. derives g' ⊢ dl'' ◁ pfx ++ [NTS A] ++ sfx → HD dl3` 
      by METIS_TAC [ntdlgImpg'3] THEN
      `LAST dl' = y` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `HD dl' = HD dl3` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      `derives g' ⊢ (dl'' ++ TL dl') ◁ (pfx++[NTS A]++sfx) → y`
      by METIS_TAC [ldAppend] THEN
      Cases_on `dl1=[]` THEN FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `dl''++TL dl'`  THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    Cases_on `dl''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [],
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `dl''++TL dl'`  THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    Cases_on `dl''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [],
	    
	    `lderives g ⊢ dl1 ◁ HD dl1 → LAST dl1` 
	    by METIS_TAC [ldsubderivs,APPEND_ASSOC] THEN
	    `dl2 = HD dl2::TL dl2` by METIS_TAC [CONS,NULL_EQ_NIL] THEN
	    `lderives g (LAST dl1) (HD dl2)` by METIS_TAC [ldAdjElem,APPEND,
							   APPEND_FRONT_LAST,
							   APPEND_ASSOC] THEN
	    `derives g' (LAST dl1) (HD dl2)` by
	    METIS_TAC [gImpg'Nt0,APPEND_FRONT_LAST,ldNumNtApp] THEN
	    `derives g' ⊢ dl1 ◁ HD dl1 → LAST dl1` by METIS_TAC [blkNilgImpg'd] THEN
	    IMP_RES_TAC ldImprtc2list THEN
	    `HD dl1 = x` by (Cases_on `dl1` THEN 
			     FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	    SRW_TAC [][] THEN
	    `(derives g')^* (HD dl1) (HD dl2)` by METIS_TAC [RTC_RULES_RIGHT1] THEN
	    METIS_TAC [RTC_RTC,RTC_RULES,rtc2list_exists'],
	    `derives g' (LAST dl1) (HD dl2)` by
	    METIS_TAC [gImpg'Nt0,APPEND_FRONT_LAST,ldNumNtApp] THEN
	    `derives g' ⊢ dl1 ◁ HD dl1 → LAST dl1` by METIS_TAC [blkNilgImpg'd] THEN
	    IMP_RES_TAC ldImprtc2list THEN
	    `HD dl1 = x` by (Cases_on `dl1` THEN 
			     FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	    SRW_TAC [][] THEN
	    `(derives g')^* (HD dl1) (HD dl2)` by METIS_TAC [RTC_RULES_RIGHT1] THEN
	    METIS_TAC [RTC_RTC,RTC_RULES,rtc2list_exists']
	    ],

      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `[h]` THEN SRW_TAC [][] 
     ]);



val ldg'Impg = store_thm
("ldg'Impg",
``∀x y.rderives g' ⊢ dl ◁ x → y ∧ EVERY isTmnlSym y ∧ left2Right A B g g' 
 ⇒ 
 ∃dl'.derives g ⊢ dl' ◁ x → y``,

completeInduct_on `rdNumNt (NTS B) dl` THEN
SRW_TAC [][] THEN
Cases_on `rdNumNt (NTS B) dl = 0` THEN1
 METIS_TAC [blkNilg'Impgd] THEN
Cases_on `LENGTH dl > 1` 
THENL[
      `∃dl1 dl2 dl3.
           (dl = dl1 ++ dl2 ++ dl3) ∧
           (rdNumNt (NTS B) dl1 = 0) ∧
           (∀e1 e2 p s.
              (dl2 = p ++ [e1; e2] ++ s) ⇒
              LENGTH e2 ≥ LENGTH e1) ∧
           ∃sfx.
             EVERY isTmnlSym sfx ∧
             (∀e. MEM e dl2 ⇒ ∃pfx. e = pfx ++ [NTS B] ++ sfx) ∧
             dl2 ≠ [] ∧
             (dl3 ≠ [] ⇒
              LENGTH (LAST dl2) ≤ LENGTH (HD dl3) ⇒
              ¬(isSuffix ([NTS B]++sfx) (HD dl3)))` by MAGIC (* METIS_TAC [dlsplit]*) THEN

      SRW_TAC [][] THEN
      `rdNumNt (NTS B) dl3 < rdNumNt (NTS B) (dl1++dl2++dl3)` by MAGIC THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`rdNumNt (NTS B) dl3`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `dl3 ≠ []` by MAGIC THEN
      `rderives g' ⊢ dl3 ◁ HD dl3 → y` by MAGIC THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`B`,`dl3`] MP_TAC) THEN SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`HD dl3`,`y`] MP_TAC ) THEN
      SRW_TAC [][] THEN      
      `rderives g' ⊢ dl2 ◁ HD dl2 → LAST dl2` by MAGIC THEN
      `∃pfx.HD dl2 = pfx++[NTS B]++sfx` by METIS_TAC [MEM,CONS,NULL_EQ_NIL] THEN
      `rderives g' (LAST dl2) (HD dl3)` by MAGIC THEN
      `¬(isSuffix ([NTS B]++sfx) (HD dl3))`
      by MAGIC THEN
      `∃dl''. derives g ⊢ dl'' ◁ pfx ++ [NTS B] ++ sfx → HD dl3` 
      by METIS_TAC [ntdlgImpg'3] THEN
      `derives g' ⊢ (dl'' ++ TL dl3) ◁ (pfx++[NTS B]++sfx) → y`
      by MAGIC THEN
      Cases_on `dl1=[]` THEN FULL_SIMP_TAC (srw_ss()) [] 
      THENL[
	    SRW_TAC [][] THEN
	    Q.EXISTS_TAC `dl''++TL dl3`  THEN SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    Cases_on `dl''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [],
	    
	    `rderives g ⊢ dl1 ◁ HD dl1 → LAST dl1` by MAGIC THEN
	    `rderives g (LAST dl1) (HD dl2)` by MAGIC THEN
	    `derives g' (LAST dl1) (HD dl2)` by MAGIC THEN
	    `derives g' ⊢ dl1 ◁ HD dl1 → LAST dl1` by METIS_TAC [blkNilgImpg'd] THEN
	    Q.EXISTS_TAC `dl1 ++ dl'' ++ TL dl3` THEN SRW_TAC [][] THEN
	    Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	    Cases_on `dl''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    MAGIC
	    ],

      Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
      SRW_TAC [][] THEN
      Q.EXISTS_TAC `[h]` THEN SRW_TAC [][]
      ]);





val lemma4_4 = store_thm
("lemma4_4",
``∀g g'.left2Right A B g g' ⇒ (language g = language g')``,
MAGIC);


(* 
Theorem 4.6 
Every CFL L without can be generated by a grammar for
which every production is of the form A->aalph, where A is a variable,
a is a terminal and alpha (possibly empty) is a string of variables.
*)





val _ = export_theory ();
