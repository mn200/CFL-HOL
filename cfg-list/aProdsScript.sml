open HolKernel boolLib bossLib Parse

open stringTheory relationTheory listTheory
    rich_listTheory

open pred_setTheory symbolDefTheory grammarDefTheory listLemmasTheory
relationLemmasTheory

open containerLemmasTheory

val _ = new_theory "aProds";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

infix byA;
val op byA = BasicProvers.byA;

(* Greibach Normal Form *)

(*
 Lemma 4.3
Define an A-production to be a production with variable A on the
left. Let G=(V,T,P,S) be a CFG. Let A->xBy be a production in P and
B->b1|b2... be the set of all B-productions. Let G1=(V,T,P1,S) be
obtained from G by deleting the production A->xBy from P and adding
the productions A->xb1y|xb2y.... Then L(g)=L(G1).
*)


(* Termination like the CNF form *)

val aProdg = Define
`aProdg A B g g' =
  ∃r p s. A≠B ∧ MEM (rule A r) (rules g) ∧ (r = (p++[NTS B]++s)) ∧
  (set (rules g') = (set (rules g) DIFF {rule A r} ∪
                     {rule A (p++x++s) | rule B x ∈ set (rules g)})) ∧
  (startSym g = startSym g')`;


val apg_r1 = prove(
``∀g g' A.aProdg A B g g' ⇒ ∀u v.derives g u v ⇒ EVERY isTmnlSym v
            ⇒
          derives g' u v``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `lhs=A` THENL[
Cases_on `rhs=p++[NTS B]++s` THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b],
FULL_SIMP_TAC (srw_ss()) [DIFF_DEF, UNION_DEF, EXTENSION] THEN
METIS_TAC []],

FULL_SIMP_TAC (srw_ss()) [DIFF_DEF, UNION_DEF, EXTENSION] THEN
METIS_TAC []]);


val slemma1_r3 = prove(
``∀u v.RTC (derives g) u v ⇒ (u=[NTS nt]) ⇒ EVERY isTmnlSym v
              ⇒
        ∃x.MEM (rule nt x) (rules g) ∧ RTC (derives g) x v``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES,isTmnlSym_def,isNonTmnlSym_def,sym_r1b],
FULL_SIMP_TAC (srw_ss()) [derives_def,lreseq] THEN METIS_TAC []]);

val slemma1_r4 = prove(
``∀g g'.aProdg A B g g' ⇒ ∀l r. MEM (rule l r) (rules g') ⇒ ~(l=A)
            ⇒
        MEM (rule l r) (rules g)``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProdg] THEN
`~(rule l r = rule A (p ++ [NTS B] ++ s))` by SRW_TAC [] [] THEN
`~∃x.(rule l r = rule A (p ++ x ++ s))` by SRW_TAC [] [] THEN
`rule l r ∈ (set (rules g) DIFF {rule A (p ++ [NTS B] ++ s)} ∪
              {rule A (p ++ x ++ s) | MEM (rule B x) (rules g)})`
             by (FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF, EXTENSION] THEN
                 METIS_TAC [rule_11]) THEN
FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF, EXTENSION] THEN
METIS_TAC []);


val apg_r2 = store_thm("apg_r2",
``∀u v.RTC (derives g) u v ⇒ aProdg A B g g' ⇒ EVERY isTmnlSym v
                   ⇒ RTC (derives g') u v``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1] THEN
SRW_TAC [] []
THENL[
FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
Cases_on `lhs = A` THENL[
Cases_on `rhs = p++[NTS B]++s` THENL[
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b],
`MEM (rule lhs rhs) (rules g')`
by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF, EXTENSION] THEN
    METIS_TAC []) THEN
METIS_TAC [RTC_RULES]],
`MEM (rule lhs rhs) (rules g')`
by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF, EXTENSION] THEN
    METIS_TAC []) THEN
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
`MEM (rule lhs rhs) (rules g')` by
(FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF,EXTENSION] THEN
 METIS_TAC []) THEN
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
`MEM (rule lhs rhs) (rules g')` by
(FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF,EXTENSION] THEN
METIS_TAC []) THEN
SRW_TAC [] [] THEN
METIS_TAC [RTC_RULES]],

FULL_SIMP_TAC (srw_ss()) [derives_def,aProdg] THEN
Cases_on `~(lhs=A)` THEN
Cases_on `~(rhs=p++[NTS B]++s)` THEN
SRW_TAC [] [] THENL[
`MEM (rule lhs rhs) (rules g')` by
                    (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF,EXTENSION] THEN
                     METIS_TAC []) THEN
SRW_TAC [] [] THEN
`derives g' (s1++[NTS lhs]++s2) (s1++rhs++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS lhs]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS lhs]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
METIS_TAC [RTC_RULES],

`MEM (rule lhs (p++[NTS B]++s)) (rules g')`
                    by (FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF,EXTENSION] THEN
                        METIS_TAC []) THEN
SRW_TAC [] [] THEN
`derives g' (s1++[NTS lhs]++s2) (s1++(p++[NTS B]++s)++s2)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' (s1++[NTS lhs]++s2) (s1''++[NTS lhs'']++s2'')` by METIS_TAC [] THEN
`derives g' (s1''++[NTS lhs'']++s2'') (s1''++rhs''++s2'')` by METIS_TAC [res1,derives_same_append_left,derives_same_append_right] THEN
`RTC (derives g') (s1++[NTS lhs]++s2) (s1''++rhs''++s2'')` by METIS_TAC [res2] THEN
METIS_TAC [RTC_RULES],


`MEM (rule A rhs) (rules g')` by
(FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF,EXTENSION] THEN
METIS_TAC []) THEN
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
`∃R.MEM (rule B R) (rules g') ∧ RTC (derives g') R y''`
by METIS_TAC [slemma1_r3] THEN
`RTC (derives g') (s1 ++ p ++ R ++ s ++ s2) (x' ++ x'' ++ y'' ++ z'' ++ z')`
by METIS_TAC [derives_append] THEN
`aProdg A B g g'`
by (FULL_SIMP_TAC (srw_ss()) [aProdg, UNION_DEF, DIFF_DEF,
                                               EXTENSION] THEN
    METIS_TAC []) THEN
`MEM (rule B R) (rules g)` by METIS_TAC [slemma1_r4] THEN
`MEM (rule A (p++R++s))  (rules g')` by
(FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF,EXTENSION] THEN
 METIS_TAC []) THEN

Q.EXISTS_TAC `(s1 ++ p ++ R ++ s ++ s2)` THEN
SRW_TAC [] [] THEN
MAP_EVERY Q.EXISTS_TAC [`s1`,`s2`,`p ++ R ++ s`,`A`] THEN
SRW_TAC [] []]]);


val apg_r3 = prove(
``∀g g'. aProdg A B g g' ⇒ ∀u v.derives g' u v ⇒ RTC (derives g) u v``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
Cases_on `~(lhs=A)` THENL[
`MEM (rule lhs rhs) (rules g)` by METIS_TAC [slemma1_r4] THEN
METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,
           rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES],

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProdg] THEN
`rule A rhs ∈ (set (rules g)) DIFF {rule A (p ++ [NTS B] ++ s)} ∪
               {rule A (p ++ x ++ s) | MEM (rule B x) (rules g)}`
                          by (FULL_SIMP_TAC (srw_ss()) [UNION_DEF, DIFF_DEF,
                                                        EXTENSION] THEN
                              METIS_TAC [rule_11]) THEN
FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF,EXTENSION] THEN
METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,
           rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES]]);


val apg_r4 = store_thm (
"apg_r4",
``∀u v.RTC (derives g') u v ⇒  aProdg A B g g'
⇒ RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RTC,apg_r3]);


val lemma4_3 = store_thm("lemma4_3",
``∀g g'.aProdg A B g g' ⇒ (language g = language g')``,
SRW_TAC [] [EQ_IMP_THM,EXTENSION,language_def] THENL[
METIS_TAC [apg_r2,aProdg],
METIS_TAC [apg_r4,aProdg]]);



(* TERMINATION *)
val apgt_r1 = store_thm("apgt_r1",
``∀g g'.RTC (\x y.∃a b.aProdg a b x y) g g' ⇒  (language g = language g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
METIS_TAC [lemma4_3]
);

(*********************************************************************************)

val aProdAllRules = Define
`aProdAllRules A B PP ru =
  ru DIFF {rule A (p ++ [NTS B] ++ s) | p, s |
            PP p ∧ (rule A (p++ [NTS B] ++ s)) IN ru } ∪
   { rule A (p++x++s) | p, x, s | PP p ∧
    (rule A (p++ [NTS B] ++ s)) IN ru ∧ (rule B x) IN ru }`;

val aProdgAll = Define
`aProdgAll A B PP g g' <=>
  (A≠B) ∧
  (startSym g = startSym g') ∧
  (set (rules g') = aProdAllRules A B PP (set (rules g)))`;

val derivgImpNewgall = store_thm
("derivgImpNewgall",
 ``∀u v. lderives g ⊢ dl ◁ u → v ⇒ aProdgAll A B PP g g' ⇒ isWord v ⇒
 (lderives g')^* u v``,

completeInduct_on `LENGTH dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [lderives_def, listderiv_def] THEN
  SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN
`h = u` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def, aProdgAll, aProdAllRules] THEN
SRW_TAC [][] THEN
Cases_on `rule lhs rhs ∈ {rule A (p ++ [NTS B] ++ s) |
       (p,s) |
       PP p ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g}`
THENL[

FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
Cases_on `isWord p`
 THENL[
       Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
       (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
        SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN

       `lderives g (s1 ++ p ++ [NTS B] ++ s ++ s2) h ∧
       lderives g ⊢ h::t ◁ h → v'` by METIS_TAC [listDerivHdBrk] THEN
       FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH (h::t)`] MP_TAC) THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
       FIRST_X_ASSUM (Q.SPECL_THEN [`h::t`] MP_TAC) THEN SRW_TAC [][] THEN
       FIRST_X_ASSUM (Q.SPECL_THEN [`h`,`v'`] MP_TAC) THEN SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       `EVERY isNonTmnlSym [NTS B]` by SRW_TAC [][isNonTmnlSym_def] THEN
       `s1 ++ p ++ [NTS B] ++ s ++ s2 = (s1++p) ++ [NTS B] ++ (s++s2)`
       by METIS_TAC [APPEND_ASSOC] THEN
       `isWord (s1++p)` by SRW_TAC [][] THEN
       `(s1' = s1 ++ p) ∧ ([NTS lhs] ++ s2' = [NTS B] ++ (s ++ s2))`
       by METIS_TAC [symlistdiv3, MEM] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       `rule B rhs ∈ rules g'` by
       (Q_TAC SUFF_TAC `rule B rhs ∈ (set (rules g'))` THEN1
        METIS_TAC [mem_in] THEN ONCE_ASM_REWRITE_TAC[] THEN SRW_TAC [][]) THEN
       `rule A (p ++ rhs ++ s) ∈ rules g'` by
       (Q_TAC SUFF_TAC `rule A (p++rhs++s) ∈ (set (rules g'))` THEN1
        METIS_TAC [mem_in] THEN ONCE_ASM_REWRITE_TAC[] THEN SRW_TAC [][] THEN
        METIS_TAC []) THEN
       METIS_TAC [ldres1, lderives_same_append_right,
                  lderives_same_append_left, RTC_RULES, APPEND_ASSOC],

       `∃p1 p2 n.(p = p1 ++ [NTS n] ++ p2) ∧ isWord p1` by METIS_TAC [leftnt] THEN
       SRW_TAC [][] THEN
       `s1 ++ (p1 ++ [NTS n] ++ p2 ++ [NTS B] ++ s) ++ s2 =
       (s1 ++ p1 ++ [NTS n] ++ p2) ++ ([NTS B]++s++s2)`
       by METIS_TAC [APPEND_ASSOC] THEN
       `∃dl1 dl2 y1 y2.
       lderives g ⊢ dl1 ◁ (s1 ++ p1 ++ [NTS n] ++ p2) → y1 ∧
       lderives g ⊢ dl2 ◁ ([NTS B]++s++s2) → y2 ∧ (v' = y1 ++ y2) ∧
       ((s1 ++ (p1 ++ [NTS n] ++ p2 ++ [NTS B] ++ s) ++ s2)::t' =
        MAP (λl. addLast l ([NTS B]++s++s2)) dl1 ++
        MAP (addFront y1) (TL dl2))` by METIS_TAC [ldStreams] THEN
       SRW_TAC [][] THEN
       Cases_on `dl2` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN1
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
       (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
       IMP_RES_TAC listDerivHdBrk THEN
       `h = NTS B::(s++s2)` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
       SRW_TAC [][] THEN
       `(s1' = []) ∧ ([NTS lhs]++s2' = NTS B::(s++s2))` by
       (Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       `rule A (p1 ++ [NTS n] ++ p2 ++ rhs ++ s) ∈ rules g'`
       by (Q_TAC SUFF_TAC `rule A (p1 ++ [NTS n] ++ p2 ++ rhs ++ s) ∈
        (set (rules g'))` THEN1
        METIS_TAC [mem_in] THEN ONCE_ASM_REWRITE_TAC[] THEN SRW_TAC [][] THEN
        METIS_TAC []) THEN
       `(lderives g')^* (rhs ++ s ++ s2) y2` by
       (`LENGTH ((rhs ++ s ++ s2)::t'') < SUC (SUC (LENGTH t'))`
        by (FULL_SIMP_TAC (srw_ss()) [] THEN
            Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
            SRW_TAC [][] THEN DECIDE_TAC) THEN
        METIS_TAC []) THEN
       `(lderives g')^* (s1 ++ p1 ++ [NTS n] ++ p2) y1` by
       (`LENGTH dl1 < SUC (SUC (LENGTH t'))`
        by (FULL_SIMP_TAC (srw_ss()) [] THEN
            Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
            SRW_TAC [][] THEN DECIDE_TAC) THEN
        METIS_TAC []) THEN
       IMP_RES_TAC lderivesImpDerives THEN
       `(derives g')^* (s1 ++ p1 ++ [NTS n] ++ p2 ++ rhs ++ s ++ s2) (y1++y2)`
       by METIS_TAC [derives_append, APPEND_ASSOC] THEN
       `derives g' (s1++[NTS A]++s2) (s1++p1 ++ [NTS n] ++ p2 ++ rhs ++ s++s2)`
       by METIS_TAC [res1, derives_same_append_left, derives_same_append_right,
                     APPEND_ASSOC] THEN
       METIS_TAC [RTC_RULES, derivesImplderives,EVERY_APPEND]
       ],

 `rule lhs rhs ∈ (rules g')` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF, UNION_DEF,
                                                          EXTENSION] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((s1 ++ rhs ++ s2)::t')`] MP_TAC) THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`(s1 ++ rhs ++ s2)::t'`] MP_TAC) THEN
 SRW_TAC [][] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`s1++rhs++s2`] MP_TAC) THEN
 SRW_TAC [][] THEN
 METIS_TAC [ldres1, RTC_RULES, lderives_same_append_left, lderives_same_append_right]
 ]);



val slemma1_r4all = prove(
``∀g g'.aProdgAll A B PP g g' ⇒ ∀l r. MEM (rule l r) (rules g') ⇒ ~(l=A)
            ⇒
        MEM (rule l r) (rules g)``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProdgAll,aProdAllRules] THEN
`rule l r ∈ set (rules g) DIFF
      {rule A (p ++ [NTS B] ++ s) |
       (p,s) |
       PP p ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g} ∪
      {rule A (p ++ x ++ s) | p, x, s |
       PP p ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g ∧
       rule B x ∈ rules g}` by METIS_TAC [mem_in] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]);


val apg_r3all = prove
(``∀g g'. aProdgAll A B PP g g' ⇒ ∀u v.derives g' u v ⇒ RTC (derives g) u v``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
Cases_on `~(lhs=A)`
 THENL[
       `MEM (rule lhs rhs) (rules g)` by METIS_TAC [slemma1_r4all] THEN
       METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,
                  rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES],

       SRW_TAC [] [] THEN
       FULL_SIMP_TAC (srw_ss()) [aProdgAll,aProdAllRules] THEN
       `rule A rhs ∈ set (rules g) DIFF
       {rule A (p ++ [NTS B] ++ s) |
        (p,s) |
        PP p ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g} ∪
       {rule A (p ++ x ++ s) | p, x, s|
        PP p ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g ∧
        rule B x ∈ rules g}`
       by METIS_TAC [mem_in] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,
                  rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES]]);


val apg_r4all = store_thm (
"apg_r4all",
``∀u v.RTC (derives g') u v ⇒  aProdgAll A B PP g g'
⇒ RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RTC,apg_r3all]);



val lemma4_3all = store_thm
("lemma4_3all",
 ``∀g g'.aProdgAll A B PP g g' ⇒ (language g = language g')``,

 SRW_TAC [][EQ_IMP_THM, EXTENSION, language_def] THEN
 METIS_TAC [derivesImplderives, lderivesImpDerives,
            derivgImpNewgall, rtc2list_exists', aProdgAll, apg_r4all]);


(*********************************************************************************)

val aProdgAlt = Define
`aProdgAlt A l g g' <=>
  ¬MEM A l ∧
  (set (rules g') =
   set (rules g) DIFF {rule A (p ++ [NTS B] ++ s) | p, B, s |
                       MEM B l ∧
                       MEM (rule A (p++ [NTS B] ++ s)) (rules g) } ∪
    { rule A (p++x++s) | p, x, s | ∃B.MEM B l ∧
                         MEM (rule A (p++ [NTS B] ++ s)) (rules g) ∧
                         MEM (rule B x) (rules g) }) ∧
  (startSym g = startSym g')`;


val derivgImpNewgalt = store_thm
("derivgImpNewgalt",
 ``∀u v. lderives g ⊢ dl ◁ u → v ⇒ 
          aProdgAlt A l g g' ⇒ isWord v ⇒
          (lderives g')^* u v``,

completeInduct_on `LENGTH dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [lderives_def, listderiv_def] THEN
  SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN
`h = u` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def, aProdgAlt] THEN
SRW_TAC [][] THEN
Cases_on `rule lhs rhs 
           ∈ {rule A (p ++ [NTS B] ++ s) | (p,B,s) |
              B ∈ l ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g}`
 >- (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] 
      >> Cases_on `isWord p`
         >- (Cases_on `t'` 
             >> FULL_SIMP_TAC (srw_ss()) [] THEN1
                  (FULL_SIMP_TAC (srw_ss()) [listderiv_def] >>
                   SRW_TAC [][] >>
                   FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def])
             >> `lderives g (s1 ++ p ++ [NTS B] ++ s ++ s2) h ∧
                 lderives g ⊢ h::t ◁ h → v'` 
                   by METIS_TAC [listDerivHdBrk] 
             >> FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH (h::t)`] MP_TAC) 
             >> SRW_TAC [][]
             >> FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] 
             >> FIRST_X_ASSUM (Q.SPECL_THEN [`h::t`] MP_TAC) 
             >> SRW_TAC [][]
             >> FIRST_X_ASSUM (Q.SPECL_THEN [`h`,`v'`] MP_TAC) 
             >> SRW_TAC [][]
             >> FULL_SIMP_TAC (srw_ss()) [lderives_def]
             >> SRW_TAC [][] 
             >> FULL_SIMP_TAC (srw_ss()) [listderiv_def]
             >> `EVERY isNonTmnlSym [NTS B]` 
                  by SRW_TAC [][isNonTmnlSym_def]
             >> `s1 ++ p ++ [NTS B] ++ s ++ s2 = 
                 (s1++p) ++ [NTS B] ++ (s++s2)`
                   by METIS_TAC [APPEND_ASSOC]
             >> `isWord (s1++p)` by SRW_TAC [][]
             >> `(s1' = s1 ++ p) ∧ 
                 ([NTS lhs] ++ s2' = [NTS B] ++ (s ++ s2))`
                    by METIS_TAC [symlistdiv3, MEM]
             >> FULL_SIMP_TAC (srw_ss()) []
             >> SRW_TAC [][] 
             >> `rule B rhs ∈ rules g'`
                by (Q_TAC SUFF_TAC `rule B rhs ∈ (set (rules g'))` THEN1
                    METIS_TAC [mem_in] THEN
                    ONCE_ASM_REWRITE_TAC[] THEN SRW_TAC [][]
                     >> metis_tac[]) 
             >> `rule A (p ++ rhs ++ s) ∈ rules g'` 
                 by (Q_TAC SUFF_TAC `rule A (p++rhs++s) ∈ set (rules g')` 
                      THEN1 METIS_TAC [mem_in] 
                     >> ONCE_ASM_REWRITE_TAC[] THEN SRW_TAC [][] 
                     >> METIS_TAC []) 
             >> METIS_TAC [ldres1, lderives_same_append_right,
                  lderives_same_append_left, RTC_RULES, APPEND_ASSOC])

         >- (`∃p1 p2 n.(p = p1 ++ [NTS n] ++ p2) ∧ isWord p1` 
                by METIS_TAC [leftnt] THEN SRW_TAC [][] 
              >> `s1 ++ (p1 ++ [NTS n] ++ p2 ++ [NTS B] ++ s) ++ s2 =
                 (s1 ++ p1 ++ [NTS n] ++ p2) ++ ([NTS B]++s++s2)`
                    by METIS_TAC [APPEND_ASSOC] 
              >> `∃dl1 dl2 y1 y2.
                   lderives g ⊢ dl1 ◁ (s1 ++ p1 ++ [NTS n] ++ p2) → y1 ∧
                   lderives g ⊢ dl2 ◁ ([NTS B]++s++s2) → y2 ∧ (v' = y1 ++ y2) ∧
                   ((s1 ++ (p1 ++ [NTS n] ++ p2 ++ [NTS B] ++ s) ++ s2)::t' =
                    MAP (λl. addLast l 
                             ([NTS B]++s++s2)) dl1 ++ MAP (addFront y1) (TL dl2))`
                  by METIS_TAC [ldStreams]
               >> SRW_TAC [][]
               >> Cases_on `dl2` 
               >> FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] 
                    THEN1 FULL_SIMP_TAC (srw_ss()) [listderiv_def]
               >> Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] 
                    THEN1 (FULL_SIMP_TAC (srw_ss()) [listderiv_def] 
                           >> SRW_TAC [][]
                           >> FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) 
               >> IMP_RES_TAC listDerivHdBrk 
               >> `h = NTS B::(s++s2)` 
                    by FULL_SIMP_TAC (srw_ss()) [listderiv_def]
               >> SRW_TAC [][] 
               >> FULL_SIMP_TAC (srw_ss()) [lderives_def]
               >> SRW_TAC [][]
               >> `(s1' = []) ∧ ([NTS lhs]++s2' = NTS B::(s++s2))`
                    by (Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] 
                         >> SRW_TAC [][] 
                         >> FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) 
               >> FULL_SIMP_TAC (srw_ss()) []
               >> SRW_TAC [][]
               >> `rule A (p1 ++ [NTS n] ++ p2 ++ rhs ++ s) ∈ rules g'`
                     by (Q_TAC SUFF_TAC 
                            `rule A (p1 ++ [NTS n] ++ p2 ++ rhs ++ s)
                               ∈ set (rules g')` 
                            THEN1 METIS_TAC [mem_in] 
                         >> ONCE_ASM_REWRITE_TAC[] THEN SRW_TAC [][]
                         >> METIS_TAC [])
               >> `(lderives g')^* (rhs ++ s ++ s2) y2`
                    by (`LENGTH ((rhs ++ s ++ s2)::t'') < SUC (SUC (LENGTH t'))`
                         by (FULL_SIMP_TAC (srw_ss()) [] THEN
                             Cases_on `dl1` THEN 
                             FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
                             SRW_TAC [][] THEN DECIDE_TAC) 
                        >> METIS_TAC []) 
               >> `(lderives g')^* (s1 ++ p1 ++ [NTS n] ++ p2) y1` 
                    by (`LENGTH dl1 < SUC (SUC (LENGTH t'))`
                        by (FULL_SIMP_TAC (srw_ss()) [] THEN
                            Cases_on `dl1` THEN 
                            FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
                            SRW_TAC [][] THEN DECIDE_TAC)
                        >> METIS_TAC []) 
               >> IMP_RES_TAC lderivesImpDerives 
               >> `(derives g')^* (s1 ++ p1 ++ [NTS n] ++ p2 ++ rhs ++ s ++ s2) 
                                  (y1++y2)`
                     by METIS_TAC [derives_append, APPEND_ASSOC] 
               >> `derives g' (s1++[NTS A]++s2) 
                              (s1++p1 ++ [NTS n] ++ p2 ++ rhs ++ s++s2)`
                     by METIS_TAC [res1, derives_same_append_left, 
                        derives_same_append_right, APPEND_ASSOC] 
               >> METIS_TAC [RTC_RULES, derivesImplderives,EVERY_APPEND])
    )

  >- (`rule lhs rhs ∈ (rules g')` 
        by FULL_SIMP_TAC (srw_ss()) 
              [DIFF_DEF, UNION_DEF, EXTENSION]
       >> FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((s1 ++ rhs ++ s2)::t')`] MP_TAC)
       >> SRW_TAC [][] 
       >> FULL_SIMP_TAC (srw_ss()++ARITH_ss) []
       >> FIRST_X_ASSUM (Q.SPECL_THEN [`(s1 ++ rhs ++ s2)::t'`] MP_TAC)
       >> SRW_TAC [][]
       >> FIRST_X_ASSUM (Q.SPECL_THEN [`s1++rhs++s2`] MP_TAC)
       >> SRW_TAC [][]
       >> METIS_TAC [ldres1, RTC_RULES, lderives_same_append_left, 
                    lderives_same_append_right])
);


val slemma1_r4alt = prove(
``∀g g'.aProdgAlt A l g g' ⇒ ∀l r. MEM (rule lhs r) (rules g') ⇒ ~(lhs=A)
            ⇒
        MEM (rule lhs r) (rules g)``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProdgAlt] THEN
`rule lhs r ∈ set (rules g) DIFF
      {rule A (p ++ [NTS B] ++ s) |
       (p,B,s) |
       B ∈ l ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g} ∪
      {rule A (p ++ x ++ s) |
       (p,x,s) |
       ∃B.
         B ∈ l ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g ∧
         rule B x ∈ rules g}` by METIS_TAC [mem_in] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]);


val apg_r3alt = prove
(``∀g g'. aProdgAlt A l g g' ⇒ ∀u v.derives g' u v ⇒ RTC (derives g) u v``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
Cases_on `~(lhs=A)`
 THENL[
       `MEM (rule lhs rhs) (rules g)` by METIS_TAC [slemma1_r4alt] THEN
       METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,
                  rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES],

       SRW_TAC [] [] THEN
       FULL_SIMP_TAC (srw_ss()) [aProdgAlt] THEN
       `rule A rhs ∈ set (rules g) DIFF
      {rule A (p ++ [NTS B] ++ s) |
       (p,B,s) |
       B ∈ l ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g} ∪
      {rule A (p ++ x ++ s) |
       (p,x,s) |
       ∃B.
         B ∈ l ∧ rule A (p ++ [NTS B] ++ s) ∈ rules g ∧
         rule B x ∈ rules g}`
       by METIS_TAC [mem_in] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,
                  rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES]]);


val apg_r4alt = store_thm (
"apg_r4alt",
``∀u v.RTC (derives g') u v ⇒  aProdgAlt A l g g'
⇒ RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RTC,apg_r3alt]);


val lemma4_3alt = store_thm
("lemma4_3alt",
 ``∀g g'.aProdgAlt A B g g' ⇒ (language g = language g')``,

 SRW_TAC [][EQ_IMP_THM, EXTENSION, language_def] THEN
 METIS_TAC [derivesImplderives, lderivesImpDerives,
            derivgImpNewgalt, rtc2list_exists', aProdgAlt, apg_r4alt]);


(*********************************************************************************)

val aProdsRules = Define
`aProdsRules A l ru =
  ru DIFF {rule A ([NTS B] ++ s) | B, s |
           MEM B l ∧
                 (rule A ([NTS B] ++ s)) IN ru } ∪
   { rule A (x++s) | x, s | ∃B. MEM B l ∧
    (rule A ([NTS B] ++ s)) IN ru ∧ (rule B x) IN ru }`;

val aProds = Define
`aProds A l g g' <=>
  ¬MEM A l ∧
  (startSym g = startSym g') ∧
  (set (rules g') = aProdsRules A l (set (rules g)))`;



val finiteaProdsRules = store_thm
("finiteaProdsRules",
``∀ru. FINITE ru ⇒ FINITE (aProdsRules A l ru)``,

SRW_TAC[][aProdsRules] THEN
`∀NT r. { rule NT r | F } = ∅` by SRW_TAC [][EXTENSION] THEN
Q.MATCH_ABBREV_TAC `FINITE Horrible` THEN
Q.ABBREV_TAC `f = \r. case (r : (α,β)rule) of
                        rule N rhs => if N ≠ A then {}
                                      else { rule A (x ++ r0) | x,r0 |
                                            ?B. B ∈ l ∧ rule B x ∈ ru ∧
                                                (rhs = NTS B :: r0)}`  THEN
Q_TAC SUFF_TAC `Horrible = BIGUNION (IMAGE f ru)`
 THEN1 (DISCH_THEN SUBST1_TAC THEN SRW_TAC [][Abbr`f`] THEN
        Cases_on `r` THEN SRW_TAC [][] THEN
        Q.MATCH_ABBREV_TAC `FINITE Horrible2` THEN
        Q.ABBREV_TAC
            `g = \r. case r of
                       rule M rr => if M ∈ l then
                                      {rule A (rr ++ r0) | r0 | l' = NTS M :: r0}
                                    else {}` THEN
          Q_TAC SUFF_TAC `Horrible2 = BIGUNION (IMAGE g ru)`
          THEN1 (DISCH_THEN SUBST1_TAC THEN
                   SRW_TAC [][Abbr`g`] THEN
                   Cases_on `r` THEN SRW_TAC [][] THEN
                   Cases_on `l'` THEN SRW_TAC [][] THEN
                   Cases_on `h` THEN SRW_TAC [][] THEN
                   Q.MATCH_ABBREV_TAC `FINITE FOO` THEN
                   Q_TAC SUFF_TAC `FOO = if n = n' then {rule A (l'' ++ t)}
                                         else {}` THEN
                   SRW_TAC [][] THEN SRW_TAC [][Abbr`FOO`, EXTENSION]) THEN
          ONCE_REWRITE_TAC [EXTENSION] THEN
          SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
                   boolSimps.CONJ_ss][EXISTS_rule,
                                      Abbr`g`, Abbr`Horrible2`] THEN
          SRW_TAC [][EXTENSION] THEN
          METIS_TAC []) THEN
   ONCE_REWRITE_TAC [EXTENSION] THEN
   SRW_TAC [boolSimps.COND_elim_ss, boolSimps.DNF_ss,
            boolSimps.CONJ_ss][EXISTS_rule,
                               Abbr`f`, Abbr`Horrible`] THEN
   METIS_TAC []);

val aProdsRulesAllEq = store_thm
("aProdsRulesAllEq",
``(aProdsRules  ntk [se]  (set ru0) =
   aProdAllRules ntk se NULL (set ru0))``,

SRW_TAC [][aProdAllRules, aProdsRules] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION, NULL_EQ_NIL]);

val finiteaProdAllRules = store_thm
("finiteaProdAllRules",
``∀ru. FINITE ru ⇒ FINITE (aProdAllRules A B NULL ru)``,

SRW_TAC [][] THEN
`aProdAllRules A B NULL ru = aProdsRules A [B] ru`
 by (SRW_TAC [][aProdAllRules, aProdsRules] THEN
     FULL_SIMP_TAC (srw_ss()) [EXTENSION, NULL_EQ_NIL]) THEN
METIS_TAC [finiteaProdsRules, FINITE_LIST_TO_SET]);


val derivgImpNewgGen = store_thm
("derivgImpNewgGen",
 ``∀u v. lderives g ⊢ dl ◁ u → v ⇒ aProds A l g g' ⇒ isWord v ⇒
 (lderives g')^* u v``,

completeInduct_on `LENGTH dl` THEN SRW_TAC [][] THEN
Cases_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
 (FULL_SIMP_TAC (srw_ss()) [lderives_def, listderiv_def] THEN
  SRW_TAC [][]) THEN
IMP_RES_TAC listDerivHdBrk THEN
`h = u` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [lderives_def, aProds, aProdsRules] THEN
SRW_TAC [][] THEN
Cases_on `rule lhs rhs ∈ {rule A ([NTS B] ++ s) |
                          (B,s) |
                          B ∈ l ∧ rule A ([NTS B] ++ s) ∈ rules g}`
THENL[

       Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
       (FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
        SRW_TAC [][] THEN
        FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
       SRW_TAC [][] THEN
       `lderives g (s1 ++ [NTS B] ++ s ++ s2) h ∧
       lderives g ⊢ h::t ◁ h → v'` by METIS_TAC [listDerivHdBrk, APPEND,
                                                 APPEND_ASSOC] THEN
       FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH (h::t)`] MP_TAC) THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
       FIRST_X_ASSUM (Q.SPECL_THEN [`h::t`] MP_TAC) THEN SRW_TAC [][] THEN
       FIRST_X_ASSUM (Q.SPECL_THEN [`h`,`v'`] MP_TAC) THEN SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
       SRW_TAC [][] THEN
       FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
       `EVERY isNonTmnlSym [NTS B]` by SRW_TAC [][isNonTmnlSym_def] THEN
       `s1 ++ [NTS B] ++ s ++ s2 = (s1) ++ [NTS B] ++ (s++s2)`
       by METIS_TAC [APPEND_ASSOC] THEN
       `(s1' = s1) ∧ ([NTS lhs] ++ s2' = [NTS B] ++ (s ++ s2))`
       by METIS_TAC [symlistdiv3, MEM] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       `rule B rhs ∈ rules g'` by
       (Q_TAC SUFF_TAC `rule B rhs ∈ (set (rules g'))` THEN1
        METIS_TAC [mem_in] THEN
        ONCE_ASM_REWRITE_TAC[] THEN SRW_TAC [][] THEN
        METIS_TAC []) THEN
       `rule A (rhs ++ s) ∈ rules g'` by
       (Q_TAC SUFF_TAC `rule A (rhs++s) ∈ (set (rules g'))` THEN1
        METIS_TAC [mem_in] THEN ONCE_ASM_REWRITE_TAC[] THEN SRW_TAC [][] THEN
        METIS_TAC []) THEN
       METIS_TAC [ldres1, lderives_same_append_right,
                  lderives_same_append_left, RTC_RULES, APPEND_ASSOC],


 `rule lhs rhs ∈ (rules g')` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF, UNION_DEF,
                                                          EXTENSION] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ((s1 ++ rhs ++ s2)::t')`] MP_TAC) THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`(s1 ++ rhs ++ s2)::t'`] MP_TAC) THEN
 SRW_TAC [][] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`s1++rhs++s2`] MP_TAC) THEN
 SRW_TAC [][] THEN
 METIS_TAC [ldres1, RTC_RULES, lderives_same_append_left, lderives_same_append_right]
 ]);



val slemma1_r4Gen = prove(
``∀g g'.aProds A l g g' ⇒ ∀l r. MEM (rule lhs r) (rules g') ⇒ ~(lhs=A)
            ⇒
        MEM (rule lhs r) (rules g)``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [aProds, aProdsRules] THEN
`rule lhs r ∈ set (rules g) DIFF
      {rule A (NTS B::s) |
       (B,s) |
       B ∈ l ∧ rule A (NTS B::s) ∈ rules g} ∪
      {rule A (x ++ s) |
       (x,s) |
       ∃B.
         B ∈ l ∧ rule A (NTS B::s) ∈ rules g ∧
         rule B x ∈ rules g}` by METIS_TAC [mem_in] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]);


val apg_r3Gen = prove
(``∀g g'. aProds A l g g' ⇒ ∀u v.derives g' u v ⇒ RTC (derives g) u v``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
Cases_on `~(lhs=A)`
 THENL[
       `MEM (rule lhs rhs) (rules g)` by METIS_TAC [slemma1_r4Gen] THEN
       METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,
                  rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES],

       SRW_TAC [] [] THEN
       FULL_SIMP_TAC (srw_ss()) [aProds, aProdsRules] THEN
       `rule A rhs ∈ set (rules g) DIFF
      {rule A (NTS B::s) |
       (B,s) |
       B ∈ l ∧ rule A (NTS B::s) ∈ rules g} ∪
      {rule A (x ++ s) |
       (x,s) |
       ∃B.
         B ∈ l ∧ rule A (NTS B::s) ∈ rules g ∧
         rule B x ∈ rules g}`
       by METIS_TAC [mem_in] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [res1,RTC_SUBSET,rtc_derives_same_append_right,
                  rtc_derives_same_append_left,APPEND_ASSOC,RTC_RTC,RTC_RULES,
                  APPEND, APPEND_NIL]]);


val apg_r4Gen = store_thm (
"apg_r4Gen",
``∀u v.RTC (derives g') u v ⇒  aProds A l g g'
⇒ RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RTC,apg_r3Gen]);

val aProdsExists = store_thm(
"aProdsExists",
``A ∉ l ⇒ ∀g. ∃g'. aProds A l g g'``,
SRW_TAC [][aProds] THEN
`FINITE (aProdsRules A l (set (rules g)))` by METIS_TAC [finiteaProdsRules,
                                                         FINITE_LIST_TO_SET] THEN
`∃r. set r = aProdsRules A l (set (rules g))` by METIS_TAC [listExists4Set] THEN
Q.EXISTS_TAC `G r (startSym g)` THEN
SRW_TAC [][startSym_def, rules_def]);




val lemma4_3Gen = store_thm
("lemma4_3Gen",
 ``∀g g'.aProds A l g g' ⇒ (language g = language g')``,

 SRW_TAC [][EQ_IMP_THM, EXTENSION, language_def] THEN
 METIS_TAC [derivesImplderives, lderivesImpDerives,
            derivgImpNewgGen, rtc2list_exists', aProds, apg_r4Gen]);


(*********************************************************************************)

val _ = export_theory();
