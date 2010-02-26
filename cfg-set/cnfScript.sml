(* A theory about Chomsky Normal Form *)
open HolKernel boolLib bossLib Parse BasicProvers
open stringTheory relationTheory pred_setTheory listTheory
open grammarDefTheory listLemmaTheory regexpTheory setLemmasTheory containerTheory

val _ = new_theory "cnf";

(* Chomsky Normal Form *)

val trans1Tmnl = Define `trans1Tmnl nt t g g' = ?l r p s. rule l r IN rules g /\ (r=p++[t]++s) /\ (~NULL p \/ ~NULL s)
/\ isTmnlSym t /\ ~((NTS nt) IN (nonTerminals g)) /\ (rules(g') = rules(g) DIFF {rule l r} UNION {rule nt [t];rule l (p++[NTS nt]++s)}) /\ (startSym g' = startSym g)`

open arithmeticTheory

(* BasicProvers.export_rewrites (["ruleTmnlsAlt"]) *)

val ruleTmnls = Define `(ruleTmnls (rule l [t]) = 0) /\
(ruleTmnls (rule l r) = LENGTH (FILTER (isTmnlSym) r))`


val ruleTmnlsAlt = prove(
``!l r.ruleTmnls (rule l r) = if LENGTH r <= 1 then 0 else LENGTH (FILTER (isTmnlSym) r)``,
Induct_on `r` THEN
SRW_TAC [] [ruleTmnls] THENL[
SRW_TAC [] [] THEN
`(LENGTH r) + 1 <= 1` by METIS_TAC [ADD1] THEN
`LENGTH r <= 0` by FULL_SIMP_TAC arith_ss [] THEN
`r=[]` by FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [ruleTmnls],
`?h' r'.(r=(h'::r'))` by FULL_SIMP_TAC (srw_ss()) [l_lemma1] THEN
FULL_SIMP_TAC (srw_ss()) [ruleTmnls],
`?h' r'.(r=(h'::r'))` by FULL_SIMP_TAC (srw_ss()) [l_lemma1] THEN
FULL_SIMP_TAC (srw_ss()) [ruleTmnls]
])

val ruleNonTmnls = Define ` (ruleNonTmnls (rule l []) = 0) /\
(ruleNonTmnls (rule l [t]) = 0) /\
(ruleNonTmnls (rule l [t1;t2]) = 0) /\
(ruleNonTmnls (rule l r) = LENGTH (FILTER (isNonTmnlSym) r))`

val ruleNonTmnlsAlt = prove(
``!l r.ruleNonTmnls (rule l r) = if LENGTH r <= 2 then 0 else LENGTH (FILTER (isNonTmnlSym) r)``,
SRW_TAC [] [] THENL[
`(LENGTH r=2) \/ (LENGTH r<2)` by METIS_TAC [LESS_OR_EQ] THENL[
 METIS_TAC [ruleNonTmnls,list_lem2],
`(LENGTH r = 0) \/ (LENGTH r = 1)` by DECIDE_TAC THENL[
METIS_TAC [LENGTH_NIL, ruleNonTmnls],
METIS_TAC [list_lem1, ruleNonTmnls]]],
`LENGTH r >= 3` by DECIDE_TAC THEN METIS_TAC [ruleNonTmnls,APPEND,list_lem3]])

val badTmnlRules = Define `(badTmnlRules g = SIGMA ruleTmnls (rules g))`

val badNtRules = Define `(badNtRules g = SIGMA ruleNonTmnls (rules g))`

val cnf = Define `cnf g = (badNtRules g = 0) /\ (badTmnlRules g = 0)`


val trans2NT = Define 
`trans2NT nt nt1 nt2 g g' = 
    ?l r p s. rule l r IN rules g /\ (r=p++[nt1;nt2]++s) 
    /\ (~NULL p \/ ~NULL s) /\ isNonTmnlSym nt1 /\ isNonTmnlSym nt2 
    /\ ~((NTS nt) IN (nonTerminals g)) /\ 
    (rules(g') = rules(g) DIFF {rule l r} UNION 
                 {rule nt [nt1;nt2];rule l (p++[NTS nt]++s)}) 
    /\ (startSym g' = startSym g)`

val cnf_r1 = prove(
``!g g' nt t.trans1Tmnl nt t g g' ==> derives g u v ==> RTC (derives g') u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,trans1Tmnl] THEN
Cases_on `l=lhs` THEN
SRW_TAC [] [] THEN
Cases_on `EVERY isNonTmnlSym rhs` THENL[

  `~((rhs = p ++ [t] ++ s) /\ isTmnlSym t)` by METIS_TAC [sym_r3b] THEN
   FULL_SIMP_TAC (srw_ss()) [] THENL[
     `rule l rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [DIFF_DEF,UNION_DEF] THEN
      METIS_TAC [res1, derives_same_append_left,derives_same_append_right,RTC_SUBSET],
      METIS_TAC [sym_r1b]
   ],


  Cases_on `rhs=(p ++ [t] ++ s)` THENL[
    SRW_TAC [] [] THEN 
    `rule nt [t] IN rules g' /\ rule l (p ++ [NTS nt] ++ s) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF, DIFF_DEF] THEN
    `RTC (derives g') (p++[NTS nt]++s) (p++[t]++s)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left,RTC_SUBSET] THEN
   METIS_TAC [RTC_SUBSET,res1,RTC_RULES,rtc_derives_same_append_left,rtc_derives_same_append_right,APPEND_ASSOC],
   `rule l rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
    METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right]
   ],


  `rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
   METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right],

  `rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
   METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right],
  
  `~?n s1 s2. (rhs = s1 ++ [n] ++ s2) /\ isTmnlSym n` by METIS_TAC [sym_r3b] THEN
  `rule l rhs IN rules g'` by (FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN SRW_TAC [] [] THEN DISJ1_TAC THEN METIS_TAC []) THEN METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right],

  
  Cases_on `rhs=(p ++ [t] ++ s)` THENL[
    SRW_TAC [] [] THEN 
    `rule nt [t] IN rules g' /\ rule l (p ++ [NTS nt] ++ s) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF, DIFF_DEF] THEN
    `RTC (derives g') (p++[NTS nt]++s) (p++[t]++s)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left,RTC_SUBSET] THEN
   METIS_TAC [RTC_SUBSET,res1,RTC_RULES,rtc_derives_same_append_left,rtc_derives_same_append_right,APPEND_ASSOC],
   `rule l rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
    METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right]
   ],


  `rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
   METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right],

  `rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [UNION_DEF,DIFF_DEF] THEN
  METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right]
])


val cnf_r1NT = prove(
``!g g' nt t.trans2NT nt nt1 nt2 g g' ==> derives g u v ==> RTC (derives g') u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,trans2NT] THEN
(Cases_on `lhs=l` THENL[
Cases_on `rhs=p ++ [nt1; nt2] ++ s`  THENL[
`rule l (p ++ [NTS nt] ++ s) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [] THEN 
`rule nt [nt1; nt2] IN rules g'` by  FULL_SIMP_TAC (srw_ss()) []  THEN SRW_TAC [] [] THEN
`derives g' (p++[NTS nt]++s) (p++[nt1;nt2]++s)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' [NTS l] (p ++ [NTS nt] ++ s)` by METIS_TAC [res1] THEN
METIS_TAC [rtc_derives_same_append_left,rtc_derives_same_append_right,APPEND_ASSOC,res2],

Cases_on `rhs=(p ++ [NTS nt] ++ s)` THENL[
SRW_TAC [] [] THEN
`rule l (p ++ [NTS nt] ++ s) IN rules g'` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [res1,RTC_SUBSET,derives_same_append_left,derives_same_append_right,APPEND_ASSOC],

SRW_TAC [] [] THEN
`rule l rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [res1,RTC_SUBSET,derives_same_append_left,derives_same_append_right,APPEND_ASSOC]
]],

`rule lhs rhs IN rules g'` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [res1,RTC_SUBSET,derives_same_append_left,derives_same_append_right,APPEND_ASSOC]]))


(* Replace the new non-terminal nt in sentential form sf by terminal t *)
val elim = Define `elim sf (rule nt [t]) = MAP (\e.if (e=(NTS nt)) then t else e) sf`

val elimNT = Define `(elimNT [] (rule nt [nt1;nt2]) = [])
/\ (elimNT (s::sf) (rule nt [nt1;nt2]) = 
    if (s=(NTS nt)) then 
	([nt1;nt2]++(elimNT sf (rule nt [nt1;nt2]))) 
    else (s::elimNT sf (rule nt [nt1;nt2])))`

(* Does sentential form sf from new grammar g' has any new nonterminals, i.e. ones not in g *)
val noNewNts = Define `noNewNts g sf = !e.MEM e sf ==> isNonTmnlSym e ==> e IN (nonTerminals g)`


val slemma1_1 = prove(
``!g g' nt t.trans1Tmnl nt t g g' ==> rule nt rhs IN rules g' ==> (rhs=[t])``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [trans1Tmnl] THEN
`~?r.rule nt r IN rules g /\ ~?l p s.rule l (p++[NTS nt]++s) IN rules g /\ ~(nt=startSym g)` by METIS_TAC [slemma1_3] THEN
Cases_on `rhs=[t]` THEN
Cases_on `nt=l` THENL[
METIS_TAC [],
METIS_TAC [],
METIS_TAC [slemma1_4],
`rule nt rhs IN (rules g DIFF {rule l (p ++ [t] ++ s)} UNION {rule nt [t]; rule l (p ++ [NTS nt] ++ s)})` by METIS_TAC [] THEN
`rule nt rhs IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma1_4],
METIS_TAC [],
METIS_TAC [],
METIS_TAC [slemma1_4],
`rule nt rhs IN (rules g DIFF {rule l (p ++ [t] ++ s)} UNION {rule nt [t]; rule l (p ++ [NTS nt] ++ s)})` by METIS_TAC [] THEN
`rule nt rhs IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma1_4]
])

val slemma1_1NT = prove(
``!g g' nt t.trans2NT nt nt1 nt2 g g' ==> rule nt rhs IN rules g' ==> (rhs=[nt1;nt2])``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [trans2NT] THEN
`~?r.rule nt r IN rules g /\ ~?l p s.rule l (p++[NTS nt]++s) IN rules g /\ ~(nt=startSym g)` by METIS_TAC [slemma1_3] THEN
Cases_on `rhs=[nt1;nt2]` THEN
Cases_on `nt=l` THENL[
METIS_TAC [],
METIS_TAC [],
METIS_TAC [slemma1_4],
`rule nt rhs IN (rules g DIFF {rule l (p ++ [nt1;nt2] ++ s)} UNION {rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)})` by METIS_TAC [] THEN
`rule nt rhs IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma1_4],
METIS_TAC [],
METIS_TAC [],
METIS_TAC [slemma1_4],
`rule nt rhs IN (rules g DIFF {rule l (p ++ [nt1;nt2] ++ s)} UNION {rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)})` by METIS_TAC [] THEN
`rule nt rhs IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma1_4]
])

val slemma4_0 = prove(
``!u v nt t.elim (u++v) (rule nt [t]) = elim u (rule nt [t]) ++ elim v (rule nt [t])``,
SRW_TAC [] [elim]
)

val slemma4_0NT = prove(
``!u v nt t.elimNT (u++v) (rule nt [nt1;nt2]) = elimNT u (rule nt [nt1;nt2]) ++ elimNT v (rule nt [nt1;nt2])``,
Induct_on `u` THEN
SRW_TAC [] [elimNT]
)

val slemma4_2_0 = prove (
``(lhs=nt)=(NTS lhs=NTS nt)``,
SRW_TAC [] []
)

val slemma4_2_1 = prove(
``~(h=(NTS nt)) ==> ([h] = elim [h] (rule nt [t]))``,
SRW_TAC [] [elim]
)

val slemma4_2_1NT = prove(
``~(h=(NTS nt)) ==> ([h] = elimNT [h] (rule nt [nt1;nt2]))``,
SRW_TAC [] [elimNT]
)

val slemma4_1 = prove(
``!l r v.~MEM (NTS l) v ==> (v=elim v (rule l [r]))``,
Induct_on `v` THEN
SRW_TAC [] [] THEN
RES_TAC THENL[
SRW_TAC [] [elim],
`h::v = h::(elim v (rule l [r]))` by (FULL_SIMP_TAC (srw_ss()) []  THEN METIS_TAC []) THEN
Cases_on `(h=NTS l)` THENL[
SRW_TAC [] [],
`h::v=[h]++v` by METIS_TAC [CONS,APPEND] THEN
ONCE_ASM_REWRITE_TAC [] THEN 
METIS_TAC [slemma4_0,slemma4_2_1]
]])

val slemma4_1NT = prove(
``!l r1 r2 v.~MEM (NTS l) v ==> (v=elimNT v (rule l [r1;r2]))``,
Induct_on `v` THEN
SRW_TAC [] [] THEN
RES_TAC THENL[
SRW_TAC [] [elimNT],
`h::v = h::(elimNT v (rule l [r1;r2]))` by (FULL_SIMP_TAC (srw_ss()) []  THEN METIS_TAC []) THEN
Cases_on `(h=NTS l)` THENL[
SRW_TAC [] [],
`h::v=[h]++v` by METIS_TAC [CONS,APPEND] THEN
ONCE_ASM_REWRITE_TAC [] THEN 
METIS_TAC [slemma4_0NT,slemma4_2_1NT]
]])


val slemma4_3_1 = prove(
``(lhs=nt) ==> ([t] = elim [NTS lhs] (rule nt [t]))``,
SRW_TAC [] [elim]
)

val slemma4_3_1NT = prove(
``(lhs=nt) ==> ([nt1;nt2] = elimNT [NTS lhs] (rule nt [nt1;nt2]))``,
SRW_TAC [] [elimNT]
)


val slemma4_4 = prove (``!g g' nt t.trans1Tmnl nt t g g' ==> rule l r IN rules g ==> ~MEM (NTS nt) r``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [trans1Tmnl] THEN
Cases_on `MEM (NTS nt) r` THEN
METIS_TAC [slemma1_4,rgr_r9eq]
)

val slemma4_4NT = prove (``!g g' nt t.trans2NT nt nt1 nt2 g g' ==> rule l r IN rules g ==> ~MEM (NTS nt) r``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [trans2NT] THEN
Cases_on `MEM (NTS nt) r` THEN
METIS_TAC [slemma1_4,rgr_r9eq]
)


val lemma1 = prove(
``!g g' nt t.trans1Tmnl nt t g g' ==> derives g' u v ==> 
		   ((elim u (rule nt [t])=elim v (rule nt [t])) \/ 
		    (derives g (elim u (rule nt [t])) (elim v (rule nt [t]))))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,trans1Tmnl] THEN
(Cases_on `lhs=nt` THENL[
  Cases_on `rhs=[t]` THENL[
    SRW_TAC [] [] THEN
    DISJ1_TAC THEN
    SRW_TAC [] [slemma4_0,elim],

    METIS_TAC [slemma1_1,trans1Tmnl]
  ],

  DISJ2_TAC THEN
  MAP_EVERY Q.EXISTS_TAC [`elim s1 (rule nt [t])`,`elim s2 (rule nt [t])`,`elim rhs (rule nt [t])`,`lhs`] THEN
  SRW_TAC [] [slemma4_0] THENL[
    METIS_TAC [slemma4_2_1,slemma4_2_0],

    Cases_on `lhs=l` THEN
      Cases_on `rhs=(p ++ [NTS nt] ++ s)` THEN
        SRW_TAC [] [] THENL[
	Cases_on `MEM (NTS nt) p` THEN
          Cases_on `MEM (NTS nt) s` THENL[

            METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
            METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
       	    METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
	
	    METIS_TAC [slemma4_1,slemma4_2_1,slemma4_2_0,slemma4_0,slemma4_3_1]],


SRW_TAC [] [] THEN
`rule l rhs IN rules g DIFF {rule l (p ++ [t] ++ s)} UNION {rule nt [t]; rule l (p ++ [NTS nt] ++ s)}` by METIS_TAC [] THEN
`rule l rhs IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
Cases_on `MEM (NTS nt) rhs` THENL[
	METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
	METIS_TAC [slemma4_1]
] THEN
`rule lhs (p ++ [NTS nt] ++ s) IN rules g DIFF {rule l (p ++ [t] ++ s)} UNION {rule nt [t]; rule l (p ++ [NTS nt] ++ s)}` by METIS_TAC [] THEN
`rule lhs (p++[NTS nt]++s) IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma1_4],

`rule lhs (p ++ [NTS nt] ++ s) IN rules g DIFF {rule l (p ++ [t] ++ s)} UNION {rule nt [t]; rule l (p ++ [NTS nt] ++ s)}` by METIS_TAC [] THEN
`rule lhs (p++[NTS nt]++s) IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma1_4],

`rule lhs rhs IN rules g DIFF {rule l (p ++ [t] ++ s)} UNION {rule nt [t]; rule l (p ++ [NTS nt] ++ s)}` by METIS_TAC [] THEN
`rule lhs rhs IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma4_4,slemma4_0,slemma4_1,trans1Tmnl]
]]]))

val lemma1NT = prove(
``!g g' nt nt1 nt2.trans2NT nt nt1 nt2 g g' ==> derives g' u v ==> ((elimNT u (rule nt [nt1;nt2])=elimNT v (rule nt [nt1;nt2])) \/ (derives g (elimNT u (rule nt [nt1;nt2])) (elimNT v (rule nt [nt1;nt2]))))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,trans2NT] THEN
(Cases_on `lhs=nt` THENL[
  Cases_on `rhs=[nt1;nt2]` THENL[
    SRW_TAC [] [] THEN
    DISJ1_TAC THEN
    SRW_TAC [] [slemma4_0NT,elimNT] THENL[
    METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq,APPEND], 
    METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq,APPEND], 
    FULL_SIMP_TAC (srw_ss()) [slemma1_4] THEN METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq,CONS,APPEND]
    ],
    METIS_TAC [slemma1_1NT,trans2NT]
  ],

  DISJ2_TAC THEN
  MAP_EVERY Q.EXISTS_TAC [`elimNT s1 (rule nt [nt1;nt2])`,`elimNT s2 (rule nt [nt1;nt2])`,`elimNT rhs (rule nt [nt1;nt2])`,`lhs`] THEN
  SRW_TAC [] [slemma4_0NT] THENL[
    METIS_TAC [slemma4_2_1NT,slemma4_2_0],

    Cases_on `lhs=l` THEN
      Cases_on `rhs=(p ++ [NTS nt] ++ s)` THEN
        SRW_TAC [] [] THENL[
	Cases_on `MEM (NTS nt) p` THEN
          Cases_on `MEM (NTS nt) s` THENL[

            METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
            METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
       	    METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
	
	    METIS_TAC [slemma4_1NT,slemma4_2_0,slemma4_0NT,slemma4_3_1NT]],


SRW_TAC [] [] THEN
`rule l rhs IN rules g DIFF {rule l (p ++ [nt1;nt2] ++ s)} UNION {rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)}` by METIS_TAC [] THEN
`rule l rhs IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
Cases_on `MEM (NTS nt) rhs` THENL[
	METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
	METIS_TAC [slemma4_1NT]
] THEN
`rule lhs (p ++ [NTS nt] ++ s) IN rules g DIFF {rule l (p ++ [nt1;nt2] ++ s)} UNION {rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)}` by METIS_TAC [] THEN
`rule lhs (p++[NTS nt]++s) IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma1_4],

`rule lhs (p ++ [NTS nt] ++ s) IN rules g DIFF {rule l (p ++ [nt1;nt2] ++ s)} UNION {rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)}` by METIS_TAC [] THEN
`rule lhs (p++[NTS nt]++s) IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma1_4],

`rule lhs rhs IN rules g DIFF {rule l (p ++ [nt1;nt2] ++ s)} UNION {rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)}` by METIS_TAC [] THEN
`rule lhs rhs IN rules g` by (FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []) THEN
METIS_TAC [slemma4_4NT,slemma4_0NT,slemma4_1NT,trans2NT]
]]]))


val lemma3 = prove (
``!u v.RTC (derives g') u v ==> trans1Tmnl nt t g g' ==> RTC (derives g) (elim u (rule nt [t])) (elim v (rule nt [t]))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
`((elim v (rule nt [t])=elim v' (rule nt [t])) \/ (derives g (elim v (rule nt [t])) (elim v' (rule nt [t]))))` by METIS_TAC [lemma1] THEN
METIS_TAC [lemma1,RTC_SUBSET,RTC_RTC]
)

val lemma3NT = prove (
``!u v.RTC (derives g') u v ==> trans2NT nt nt1 nt2 g g' ==> RTC (derives g) (elimNT u (rule nt [nt1;nt2])) (elimNT v (rule nt [nt1;nt2]))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
`((elimNT v (rule nt [nt1;nt2])=elimNT v' (rule nt [nt1;nt2])) \/ (derives g (elimNT v (rule nt [nt1;nt2])) (elimNT v' (rule nt [nt1;nt2]))))` by METIS_TAC [lemma1NT] THEN
METIS_TAC [lemma1NT,RTC_SUBSET,RTC_RTC]
)


val slemma4_7 = prove(
``!u nt t.EVERY isTmnlSym u ==> (u=elim u (rule nt [t]))``,
Induct_on `u` THENL [
SRW_TAC [] [elim],
SRW_TAC [] [] THEN
`EVERY isTmnlSym [h]` by METIS_TAC [EVERY_MEM,EVERY_DEF] THEN
`EVERY isTmnlSym [h] ==> ([h] = elim [h] (rule nt [t]))` by (SRW_TAC [] [elim,EVERY_MEM] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,isTmnlSym_def]) 
THEN METIS_TAC [slemma4_0,APPEND]]
)


val slemma4_7NT = prove(
``!u nt t.EVERY isTmnlSym u ==> (u=elimNT u (rule nt [nt1;nt2]))``,
Induct_on `u` THENL [
SRW_TAC [] [elimNT],
SRW_TAC [] [] THEN
`EVERY isTmnlSym [h]` by METIS_TAC [EVERY_MEM,EVERY_DEF] THEN
`EVERY isTmnlSym [h] ==> ([h] = elimNT [h] (rule nt [nt1;nt2]))` by (SRW_TAC [] [elimNT,EVERY_MEM] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,isTmnlSym_def]) 
THEN METIS_TAC [slemma4_0NT,APPEND]]
)


val slemma4_2 = prove(
``!u g g' nt t.trans1Tmnl nt t g g' ==> u IN nonTerminals g ==> ([u]=elim [u] (rule nt [t]))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [elim,trans1Tmnl] THEN
Cases_on `u = (NTS nt)` THEN
METIS_TAC []
)

val slemma4_2NT = prove(
``!u g g' nt t.trans2NT nt nt1 nt2 g g' ==> u IN nonTerminals g ==> ([u]=elimNT [u] (rule nt [nt1;nt2]))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [elimNT,trans2NT] THEN
Cases_on `u = (NTS nt)` THEN
METIS_TAC []
)


val slemma4_3 = prove(
``!g. (NTS (startSym g)) IN nonTerminals g``,
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [nonTerminals_def,startSym_def]
)

val lemma4 = prove(
``trans1Tmnl nt t g g' ==> (language g') SUBSET (language g) ``,
SRW_TAC [] [language_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [lemma3,slemma4_7,slemma4_2,slemma4_3,trans1Tmnl]
)

val lemma4NT = prove(
``trans2NT nt nt1 nt2 g g' ==> (language g') SUBSET (language g) ``,
SRW_TAC [] [language_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [lemma3NT,slemma4_7NT,slemma4_2NT,slemma4_3,trans2NT]
)

val slemma5_1 = prove( 
``!u v.RTC (derives g) u v ==> (u=[NTS (startSym g)]) ==> trans1Tmnl nt t g g' ==> RTC (derives g') u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [cnf_r1,RTC_RTC]
)

val slemma5_1NT = prove( 
``!u v.RTC (derives g) u v ==> (u=[NTS (startSym g)]) ==> trans2NT nt nt1 nt2 g g' ==> RTC (derives g') u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [cnf_r1NT,RTC_RTC]
)


val lemma5 = prove(
``trans1Tmnl nt t g g' ==> (language g) SUBSET (language g')``,
SRW_TAC [] [language_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [slemma5_1,trans1Tmnl]
)

val lemma5NT = prove(
``trans2NT nt nt1 nt2 g g' ==> (language g) SUBSET (language g')``,
SRW_TAC [] [language_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [slemma5_1NT,trans2NT]
)

val cnf_lemma1 = prove(
``!g g' nt t.trans1Tmnl nt t g g'  ==> (language g = language g')``,
METIS_TAC [lemma4,lemma5,SET_EQ_SUBSET]
)

val cnf_lemma1NT = prove(
``!g g' nt t.trans2NT nt nt1 nt2 g g'  ==> (language g = language g')``,
METIS_TAC [lemma4NT,lemma5NT,SET_EQ_SUBSET]
)

val eqLang = Define `eqLang g g' = (language g = language g')`

(* TERMINATION *)
val cnf_lemma2 = prove(
``!g g'.RTC (\x y.?nt t.trans1Tmnl nt t x y) g g' ==>  eqLang g g'``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [eqLang] THEN
METIS_TAC [cnf_lemma1]
)

val cnf_lemma2NT = prove(
``!g g'.RTC (\x y.?nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ==>  eqLang g g'``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [eqLang] THEN
METIS_TAC [cnf_lemma1NT]
)

val cnf_lemma = prove(
``!g g' g''.RTC (\x y.?nt t.trans1Tmnl nt t x y) g g' ==>  RTC (\x y.?nt nt1 nt2.trans2NT nt nt1 nt2 x y) g' g'' ==> eqLang g g''``,
METIS_TAC [cnf_lemma2,cnf_lemma2NT,language_def,eqLang]
);


val lemma10_a = prove (
``!g g'.trans1Tmnl nt t g g' ==> FINITE (rules g) ==> FINITE (rules g')``,
SRW_TAC [] [trans1Tmnl] THEN SRW_TAC [] [FINITE_UNION,FINITE_DIFF]
)

val lemma10_b = prove (
``!g g'.trans2NT nt nt1 nt2 g g' ==> FINITE (rules g) ==> FINITE (rules g')``,
SRW_TAC [] [trans2NT] THEN SRW_TAC [] [FINITE_UNION,FINITE_DIFF]
)

val lemma10_artc = prove (
``!g g'.RTC (\x y.?nt t.trans1Tmnl nt t x y) g g' ==> FINITE (rules g) ==> FINITE (rules g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [lemma10_a]
)

val lemma10_brtc = prove (
``!g g'.RTC (\x y.?nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ==> FINITE (rules g) ==> FINITE (rules g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [lemma10_b]
)

val lemma16_b = prove(
``!g.FINITE (rules g) ==> (badTmnlRules g = 0) ==> (!r.r IN (rules g) ==> (ruleTmnls r = 0))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlRules] THEN
Cases_on `ruleTmnls r = 0` THENL[
SRW_TAC [] [],
METIS_TAC [set_l2,NOT_ZERO_LT_ZERO]
])

val lemma16_bNT = prove(
``!g.FINITE (rules g) ==> (badNtRules g = 0) ==> (!r.r IN (rules g) ==> (ruleNonTmnls r = 0))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badNtRules] THEN
Cases_on `ruleNonTmnls r = 0` THENL[
SRW_TAC [] [],
METIS_TAC [set_l2,NOT_ZERO_LT_ZERO]
])


val lemma16_a = prove (``!g.FINITE (rules g) ==> (badTmnlRules g = 0) ==> (!r.r IN (rules g) ==> ((SIGMA ruleTmnls ((rules g) DIFF {r})) = 0))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlRules] THEN
`ruleTmnls r = 0` by METIS_TAC [lemma16_b,badTmnlRules] THEN
SRW_TAC [] [f_diff]
)

val lemma16_aNT = prove (``!g.FINITE (rules g) ==> (badNtRules g = 0) ==> (!r.r IN (rules g) ==> ((SIGMA ruleNonTmnls ((rules g) DIFF {r})) = 0))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badNtRules] THEN
`ruleNonTmnls r = 0` by METIS_TAC [lemma16_bNT,badNtRules] THEN
SRW_TAC [] [f_diff]
)


val slemma12_a_2a = prove(
``!e.(ruleTmnls e > 0) ==> ?l p s t. ((e=rule l (p ++ [TS t] ++ s)) /\ (~NULL p \/ ~NULL s))``,
SRW_TAC [] [] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [ruleTmnlsAlt] THEN
Cases_on `LENGTH l <= 1` THENL[
`ruleTmnls (rule s l) = 0` by METIS_TAC [ruleTmnlsAlt] THEN FULL_SIMP_TAC (srw_ss()) [],

`LENGTH l > 1` by DECIDE_TAC THEN
`LENGTH (FILTER isTmnlSym l) > 0` by METIS_TAC [ruleTmnlsAlt] THEN
`?e.MEM e l /\ isTmnlSym e` by FULL_SIMP_TAC list_ss [filter_l1] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH r1 >= 1 \/ LENGTH r2 >= 1` by DECIDE_TAC THENL[
`~(LENGTH r1 = 0)` by DECIDE_TAC THEN `~(r1 = [])` by FULL_SIMP_TAC list_ss [LENGTH_NIL,NULL_DEF] THEN METIS_TAC [isTmnlSym_def,list_l1],
`~(LENGTH r2 = 0)` by DECIDE_TAC THEN `~(r2 = [])` by FULL_SIMP_TAC list_ss [LENGTH_NIL,NULL_DEF] THEN METIS_TAC [isTmnlSym_def,list_l1]
]])

(* because it will give 1 in case there's one nontmnls and others r all tmnls! *)
val slemma12_a_2aNT = prove(
``!e.(ruleNonTmnls e > 0) ==> ?l r p s t1. ((e=rule l r) /\ (r=(p ++ [NTS t1] ++ s)) /\ (LENGTH r >= 3))``,
SRW_TAC [] [] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [ruleNonTmnlsAlt] THEN
Cases_on `LENGTH l <= 2` THENL[
`ruleNonTmnls (rule s l) = 0` by METIS_TAC [ruleNonTmnlsAlt] THEN FULL_SIMP_TAC (srw_ss()) [],
` LENGTH (FILTER isNonTmnlSym l) > 0` by FULL_SIMP_TAC (srw_ss()) [] THEN
`?e.MEM e l /\ isNonTmnlSym e` by FULL_SIMP_TAC list_ss [filter_l1] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
`?e'.(e=NTS e')` by METIS_TAC [isNonTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH r1 + 1 + LENGTH r2 >= 3)` by DECIDE_TAC THEN METIS_TAC []])


val slemma12_a_2b = prove(
``!e. (?l p s t. ((e=rule l (p ++ [TS t] ++ s)) /\ (~NULL p \/ ~NULL s))) ==> (ruleTmnls e > 0) ``,
SRW_TAC [] [] THEN
SRW_TAC [] [ruleTmnlsAlt] THENL[
`~(p=[])` by METIS_TAC [list_l1] THEN `~(LENGTH p = 0)` by FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL] THEN DECIDE_TAC,
SRW_TAC [] [LENGTH_APPEND,FILTER_APPEND_DISTRIB] THENL[
DECIDE_TAC, METIS_TAC [isTmnlSym_def]],
`~(s=[])` by METIS_TAC [list_l1] THEN `~(LENGTH s = 0)` by FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL] THEN DECIDE_TAC,
SRW_TAC [] [LENGTH_APPEND,FILTER_APPEND_DISTRIB] THENL[ 
DECIDE_TAC, METIS_TAC [isTmnlSym_def]]
])

val slemma12_a_2bNT = prove (
``!e. (?l r p s t1. ((e=rule l r) /\ (r=(p ++ [NTS t1] ++ s)) /\ (LENGTH r >=3))) ==> (ruleNonTmnls e > 0) ``,
SRW_TAC [] [] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THENL[
DECIDE_TAC,
SRW_TAC [] [LENGTH_APPEND,FILTER_APPEND_DISTRIB] THENL[
DECIDE_TAC,
METIS_TAC [isNonTmnlSym_def]]]
)

val slemma12_a_2 = prove (
``!e.(ruleTmnls e > 0) = ?l p s t. ((e=rule l (p ++ [TS t] ++ s)) /\ (~NULL p \/ ~NULL s))``,
METIS_TAC [slemma12_a_2a,slemma12_a_2b]
)

val slemma12_a_2NT = prove (
``!e.(ruleNonTmnls e > 0) = ?l r p s t1. ((e=rule l r) /\ (r = (p ++ [NTS t1] ++ s)) /\ (LENGTH r >= 3))``,
METIS_TAC [slemma12_a_2aNT,slemma12_a_2bNT]
)

val slemma12_a_1 = prove(
``!e.(ruleTmnls e = 0) = ~(?l p s t.((e=rule l (p++[TS t]++s)) /\ (~NULL p \/ ~NULL s)))``,
SRW_TAC [] [] THEN
`(ruleTmnls e = 0) = ~(ruleTmnls e > 0)` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [slemma12_a_2]
)

val slemma12_a_1NT = prove(
``!e.(ruleNonTmnls e = 0) = ~(?l r p s t1.((e=rule l r) /\ (r=(p++[NTS t1]++s))) /\ (LENGTH r >= 3))``,
SRW_TAC [] [] THEN
`(ruleNonTmnls e = 0) = ~(ruleNonTmnls e > 0)` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [slemma12_a_2NT]
)

val slemma12_a_1NT2 = prove(
``!e.(ruleNonTmnls e = 0) ==> ~(?p s t1 t2.(e = rule l (p++[NTS t1;NTS t2]++s)) /\ (~NULL p \/ ~NULL s))``,
SRW_TAC [] [] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [ruleNonTmnlsAlt] THEN
Cases_on `LENGTH l' <= 2` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
`(LENGTH l' <= 1) \/ (LENGTH l' = 2)` by DECIDE_TAC THENL[
`(LENGTH l' = 0) \/ (LENGTH l' = 1)` by DECIDE_TAC THENL[
SRW_TAC [] [] THEN `l'=[]` by METIS_TAC [LENGTH_NIL] THEN FULL_SIMP_TAC (srw_ss()) [],
`?e.l'=[e]` by METIS_TAC [list_lem1] THEN SRW_TAC [] [] THEN METIS_TAC [sl_l4]],

`?e1 e2.l'=[e1;e2]` by METIS_TAC [list_lem2] THEN
SRW_TAC [] [] THEN
Cases_on `([e1; e2] = p ++ [NTS t1; NTS t2] ++ s)` THEN
METIS_TAC [sl_l5]],
`LENGTH l' >= 3` by DECIDE_TAC THEN
`?e1 e2 e3 r.(l'=[e1;e2;e3]++r)` by METIS_TAC [list_lem3] THEN
`LENGTH (FILTER isNonTmnlSym l') = 0` by METIS_TAC [] THEN
`(FILTER isNonTmnlSym l') = []` by METIS_TAC [LENGTH_NIL] THEN
`~(?m.MEM m l' /\ isNonTmnlSym m)` by METIS_TAC [filter_l2] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
`(EVERY isTmnlSym l')` by METIS_TAC [sym_r6,rgr_r9eq] THEN
Cases_on `l'=p ++ [NTS t1; NTS t2] ++ s` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b]]
)

val lemma12_a = prove (``!g. FINITE (rules g) ==> (badTmnlRules g = 0) ==> ~?g' nt t.trans1Tmnl nt t g g'``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlRules,trans1Tmnl] THEN
`!r. r IN rules g ==> (ruleTmnls r = 0)` by METIS_TAC [lemma16_b,badTmnlRules] THEN
METIS_TAC [slemma12_a_1,isTmnlSym_def]
)


val slemma8_a_2 = prove (
``!s.FINITE s ==> !p.(SIGMA f s > 0) ==> (?e.e IN s /\ f e > 0)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [SUM_IMAGE_THM] THEN
`(f e >= 1) \/ (SIGMA f (s DELETE e) >= 1)` by DECIDE_TAC THENL[
`f e > 0` by DECIDE_TAC THEN METIS_TAC [],
`SIGMA f (s DELETE e) > 0` by DECIDE_TAC THEN METIS_TAC [DELETE_NON_ELEMENT]]
)

val lemma12_b = prove (
``!g.FINITE (rules g) ==> ((badNtRules g = 0) ==> ~?g' nt nt1 nt2.trans2NT nt nt1 nt2 g g')``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badNtRules,trans2NT] THEN
`!r. r IN rules g ==> (ruleNonTmnls r = 0)` by METIS_TAC [lemma16_bNT,badNtRules] THEN
METIS_TAC [slemma12_a_1NT2,isNonTmnlSym_def,NOT_EXISTS_THM,NOT_FORALL_THM,CONS,APPEND_ASSOC,APPEND]
)

val lemma13_a = prove (``!l l' p s nt t.ruleTmnls (rule l (p++[NTS nt]++s)) <= ruleTmnls (rule l' (p++[TS t]++s))``,
SRW_TAC [] [] THEN
Induct_on `p` THEN
SRW_TAC [] [] THENL[
SRW_TAC [] [ruleTmnlsAlt] THEN  METIS_TAC [isTmnlSym_def,LESS_EQ_SUC_REFL],
SRW_TAC [] [ruleTmnlsAlt] THEN 
SRW_TAC [] [FILTER_APPEND_DISTRIB,isTmnlSym_def]
])


val lemma13_aNT = prove(
``!l l' p s nt t.ruleNonTmnls (rule l (p++[TS t]++s)) <= ruleNonTmnls (rule l' (p++[NTS nt]++s))``,
SRW_TAC [] [] THEN
Induct_on `p` THEN

SRW_TAC [] [] THENL[
SRW_TAC [] [ruleNonTmnlsAlt] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,LESS_EQ_SUC_REFL],
SRW_TAC [] [ruleNonTmnlsAlt] THEN 
SRW_TAC [] [FILTER_APPEND_DISTRIB,isNonTmnlSym_def]
])



val slemma6_a_1 = prove (``!t.isTmnlSym t ==> !nt.(SIGMA ruleTmnls {rule nt [t]} = 0)``,
SRW_TAC [] [ruleTmnls,SUM_IMAGE_SING]
)

val slemma6_a_1NT = prove (``!nt nt1 nt2.(SIGMA ruleNonTmnls {rule nt [nt1;nt2]} = 0)``,
SRW_TAC [] [ruleNonTmnls,SUM_IMAGE_SING]
)

val slemma6_a_2 = prove (``!p s.~NULL p \/ ~NULL s ==> (!l x t nt.ruleTmnls (rule l (p++[TS t]++s)) = ruleTmnls (rule l (p++[NTS nt]++s)) + 1)``,
SRW_TAC [] [ruleTmnlsAlt] THENL[
`~(LENGTH p = 0)` by METIS_TAC [NULL_DEF,LENGTH_NIL] THEN
`LENGTH p >= 1` by DECIDE_TAC THEN
SRW_TAC [] [] THENL[
DECIDE_TAC,
SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND,isTmnlSym_def,isNonTmnlSym_def] THEN
DECIDE_TAC],
`~(LENGTH s = 0)` by METIS_TAC [NULL_DEF,LENGTH_NIL] THEN
`LENGTH s >= 1` by DECIDE_TAC THEN
SRW_TAC [] [] THENL[
DECIDE_TAC,
SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND,isTmnlSym_def,isNonTmnlSym_def] THEN
DECIDE_TAC]]
)

val lemma6_a = prove (``!g g'.FINITE (rules g) ==> trans1Tmnl nt t g g' ==> (badTmnlRules g' < badTmnlRules g)``,
FULL_SIMP_TAC arith_ss [badTmnlRules,trans1Tmnl] THEN
SRW_TAC [] [] THEN
(ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [SUM_IMAGE_UNION,FINITE_DIFF,f_diff,FINITE_UNION] THEN
`~(rule nt [t] IN rules g)` by METIS_TAC [slemma1_4] THEN
`~(rule l (p++[NTS nt]++s) IN rules g)` by METIS_TAC [slemma1_4] THEN
`~(rule l (p++[t]++s) = rule nt [t])` by METIS_TAC [] THEN
`~(rule l (p++[t]++s) = rule l (p++[NTS nt]++s))` by METIS_TAC [] THEN
`{rule nt [t]; rule l (p ++ [NTS nt] ++ s)} = {rule nt [t]} UNION {rule l (p++[NTS nt]++s)}` by FULL_SIMP_TAC (srw_ss()) [EXTENSION,EQ_IMP_THM] THEN
ASM_REWRITE_TAC [] THEN
SRW_TAC [] [UNION_OVER_INTER] THENL[
   FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
   SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
   `ruleTmnls (rule nt [t]) = 0` by METIS_TAC [slemma6_a_1,SUM_IMAGE_SING] THEN
   `ruleTmnls (rule l (p ++ [t] ++ s)) = ruleTmnls (rule l (p ++ [NTS nt] ++ s)) + 1` by METIS_TAC [slemma6_a_2,isTmnlSym_def,isNonTmnlSym_def] THEN
   SRW_TAC [] [SUB_RIGHT_ADD] THENL[
       `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
       ONCE_ASM_REWRITE_TAC [] THEN
       `ruleTmnls (rule l (p++ [t]++s)) <= SIGMA ruleTmnls (rules g)` by METIS_TAC [SUM_IMAGE_IN_LE] THEN
       DECIDE_TAC,
       `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
       ONCE_ASM_REWRITE_TAC [] THEN
       `ruleTmnls (rule l (p++ [t]++s)) <= SIGMA ruleTmnls (rules g)` by METIS_TAC [SUM_IMAGE_IN_LE] THEN
       DECIDE_TAC],
    FULL_SIMP_TAC (srw_ss()) [inter_l1,inter_l2] THEN
    SRW_TAC [] [SUM_IMAGE_THM,SUM_IMAGE_SING,SUM_IMAGE_UNION] THEN
    `ruleTmnls (rule nt [t]) = 0` by METIS_TAC [slemma6_a_1,SUM_IMAGE_SING] THEN
    `ruleTmnls (rule l (p ++ [t] ++ s)) = ruleTmnls (rule l (p ++ [NTS nt] ++ s)) + 1` by METIS_TAC [slemma6_a_2,isTmnlSym_def,isNonTmnlSym_def] THEN
    `~(l=nt)` by METIS_TAC [slemma1_4] THEN
    `~((rule nt [t]) = (rule l (p++[NTS nt]++s)))` by SRW_TAC [] [] THEN
    FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THENL[
        SRW_TAC [] [SUB_RIGHT_ADD] THENL[
           `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
           ONCE_ASM_REWRITE_TAC [] THEN
           `ruleTmnls (rule l (p++ [t]++s)) <= SIGMA ruleTmnls (rules g)` by METIS_TAC [SUM_IMAGE_IN_LE] THEN
           DECIDE_TAC,
           `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
           ONCE_ASM_REWRITE_TAC [] THEN
           `ruleTmnls (rule l (p++ [t]++s)) <= SIGMA ruleTmnls (rules g)` by METIS_TAC [SUM_IMAGE_IN_LE] THEN
           DECIDE_TAC],
        SRW_TAC [] [SUB_RIGHT_ADD] THENL[
           `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
           ONCE_ASM_REWRITE_TAC [] THEN
           `ruleTmnls (rule l (p++ [t]++s)) <= SIGMA ruleTmnls (rules g)` by METIS_TAC [SUM_IMAGE_IN_LE] THEN
           DECIDE_TAC,
           `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
           ONCE_ASM_REWRITE_TAC [] THEN
           `ruleTmnls (rule l (p++ [t]++s)) <= SIGMA ruleTmnls (rules g)` by METIS_TAC [SUM_IMAGE_IN_LE] THEN
           DECIDE_TAC]],
`ruleTmnls (rule l (p ++ [t] ++ s)) = ruleTmnls (rule l (p ++ [NTS nt] ++ s)) + 1` by METIS_TAC [slemma6_a_2,isTmnlSym_def,isNonTmnlSym_def] THEN
`0 < ruleTmnls (rule l (p++[t]++s))` by DECIDE_TAC THEN
METIS_TAC [set_l2],
`ruleTmnls (rule l (p ++ [t] ++ s)) = ruleTmnls (rule l (p ++ [NTS nt] ++ s)) + 1` by METIS_TAC [slemma6_a_2,isTmnlSym_def,isNonTmnlSym_def] THEN 
`0 < ruleTmnls (rule l (p++[t]++s))` by DECIDE_TAC THEN
METIS_TAC [set_l2]])
)

val slemma6_a_2NT = prove(
``!s p.(NULL p /\ (LENGTH s >= 1)) \/ (NULL s /\ (LENGTH p >= 1)) ==>  (ruleNonTmnls (rule l (p++[NTS nt1;NTS nt2]++s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2) ``,
SRW_TAC [] [] THENL[
`p=[]` by METIS_TAC [list_l1] THEN
`(LENGTH s = 1) \/ (LENGTH s > 1)` by DECIDE_TAC THENL[
`?e.s=[e]` by METIS_TAC [list_lem1] THEN
SRW_TAC [] [] THENL[
`?nt3.e=NTS nt3` by METIS_TAC [isNonTmnlSym_def] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN METIS_TAC [isNonTmnlSym_def],
`?ts.e=TS ts` by METIS_TAC [isTmnlSym_def,sym_r1b] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN METIS_TAC [isNonTmnlSym_def]],
`LENGTH s >= 2` by DECIDE_TAC THEN
`?e1 e2 r.s=[e1;e2]++r` by METIS_TAC [list_lem4] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN (DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def])],

`s=[]` by METIS_TAC [list_l1] THEN
`(LENGTH p = 1) \/ (LENGTH p > 1)` by DECIDE_TAC THENL[
`?e.p=[e]` by METIS_TAC [list_lem1] THEN
SRW_TAC [] [] THENL[
`?nt3.e=NTS nt3` by METIS_TAC [isNonTmnlSym_def] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN METIS_TAC [isNonTmnlSym_def],
`?ts.e=TS ts` by METIS_TAC [isTmnlSym_def,sym_r1b] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN METIS_TAC [isNonTmnlSym_def]],
`LENGTH p >= 2` by DECIDE_TAC THEN
`?e1 e2 r.p=[e1;e2]++r` by METIS_TAC [list_lem4] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN (DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def] ORELSE
(SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def])))]]
)

val slemma6_a_3NT = prove(
``!s p. (~NULL p /\ (LENGTH s >= 1)) \/ (~NULL s /\ (LENGTH p >= 1)) ==>  (ruleNonTmnls (rule l (p++[NTS nt1;NTS nt2]++s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)``,
SRW_TAC [] [] THENL[
`?h t.p=h::t` by METIS_TAC [listNotNull] THEN
`(LENGTH s = 1) \/  LENGTH s > 1` by DECIDE_TAC THENL[
`?e.s=[e]` by METIS_TAC [list_lem1] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN
(DECIDE_TAC ORELSE (SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def]))),

`LENGTH s >= 2` by DECIDE_TAC THEN
`?e1 e2 r.s=[e1;e2]++r` by METIS_TAC [list_lem4] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN
(DECIDE_TAC ORELSE (SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def])))],

`?h t.s=h::t` by METIS_TAC [listNotNull] THEN
`(LENGTH p = 1) \/  LENGTH p > 1` by DECIDE_TAC THENL[
`?e.p=[e]` by METIS_TAC [list_lem1] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN
(DECIDE_TAC ORELSE (SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def]))),

`LENGTH p >= 2` by DECIDE_TAC THEN
`?e1 e2 r.p=[e1;e2]++r` by METIS_TAC [list_lem4] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN
(DECIDE_TAC ORELSE (SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def])))]]
)


val lemma6_b = prove(
``!g g'.FINITE (rules g) ==> trans2NT nt nt1 nt2 g g' ==> (badNtRules g' < badNtRules g)``,
FULL_SIMP_TAC arith_ss [badNtRules,trans2NT] THEN
SRW_TAC [] [] 
THENL[ (* ~NULL p *)
	ASM_REWRITE_TAC [] THEN
	FULL_SIMP_TAC (srw_ss()) [SUM_IMAGE_UNION,FINITE_DIFF,f_diff,FINITE_UNION] THEN
	`~(rule nt [nt1;nt2] IN rules g)` by METIS_TAC [slemma1_4] THEN
	`~(rule l (p++[NTS nt]++s) IN rules g)` by METIS_TAC [slemma1_4] THEN
	`~(rule l (p++[nt1;nt2]++s) = rule nt [nt1;nt2])` by METIS_TAC [] THEN
	`~(rule l (p++[nt1;nt2]++s) = rule l (p++[NTS nt]++s))` by METIS_TAC [] THEN
	`{rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)} = {rule nt [nt1;nt2]} UNION {rule l (p++[NTS nt]++s)}` by FULL_SIMP_TAC (srw_ss()) [EXTENSION,EQ_IMP_THM] THEN
	ASM_REWRITE_TAC [] THEN
	SRW_TAC [] [UNION_OVER_INTER] 
	THENL[ (* 4 subgoals *)
		FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
		SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
		`ruleNonTmnls (rule nt [nt1;nt2]) = 0` by METIS_TAC [slemma6_a_1NT,SUM_IMAGE_SING] THEN
		`~(LENGTH p = 0)` by METIS_TAC [NULL_DEF,LENGTH_NIL] THEN
		FULL_SIMP_TAC (srw_ss()) [] THEN
		`(LENGTH p = 1) \/ (LENGTH p > 1)` by DECIDE_TAC THEN
		SRW_TAC [] [ruleNonTmnlsAlt]
		THENL[ (* 10 subgoals *)
		       DECIDE_TAC,
		       DECIDE_TAC,
		       SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN DECIDE_TAC,
		       `LENGTH s = 0` by DECIDE_TAC THEN
		       `LENGTH p >= 1` by DECIDE_TAC THEN
		       `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,NULL_DEF,LENGTH_NIL] THEN
		       `0 < ruleNonTmnls (rule l (p++[nt1;nt2]++s))` by DECIDE_TAC THEN METIS_TAC [set_l2],

		       `LENGTH s >= 1` by DECIDE_TAC THEN
		       SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN SRW_TAC [] [SUB_RIGHT_ADD] THEN
		       `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_3NT,isNonTmnlSym_def]  THEN
		       `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))` by DECIDE_TAC THEN
		       `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= SIGMA ruleNonTmnls (rules g)` by METIS_TAC [set_l3] THEN
		       DECIDE_TAC,
		       DECIDE_TAC,
		       DECIDE_TAC,
		       DECIDE_TAC,
		       DECIDE_TAC,
		       SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN SRW_TAC [] [SUB_RIGHT_ADD] THEN
		       `LENGTH p >= 2` by DECIDE_TAC THEN
		       `LENGTH p >= 1` by DECIDE_TAC THEN
		       `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,NULL_DEF,LENGTH_NIL,slemma6_a_3NT]  THEN
		       `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))` by DECIDE_TAC THEN
		       `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= SIGMA ruleNonTmnls (rules g)` by METIS_TAC [set_l3] THEN
DECIDE_TAC
		],

		FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
		SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
		`ruleNonTmnls (rule nt [nt1;nt2]) = 0` by METIS_TAC [slemma6_a_1NT,SUM_IMAGE_SING] THEN
		`~(LENGTH p = 0)` by METIS_TAC [NULL_DEF,LENGTH_NIL] THEN
		FULL_SIMP_TAC (srw_ss()) [] THEN
		`(LENGTH p = 1) \/ (LENGTH p > 1)` by DECIDE_TAC THEN
		SRW_TAC [] [ruleNonTmnlsAlt]
		THENL[ (* 10 subgoals *)
		       DECIDE_TAC,
		       DECIDE_TAC,
		       SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN DECIDE_TAC,
		       `LENGTH s = 0` by DECIDE_TAC THEN
		       `LENGTH p >= 1` by DECIDE_TAC THEN
		       `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,NULL_DEF,LENGTH_NIL] THEN
		       `0 < ruleNonTmnls (rule l (p++[nt1;nt2]++s))` by DECIDE_TAC THEN METIS_TAC [set_l2],

		       `LENGTH s >= 1` by DECIDE_TAC THEN
		       SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN SRW_TAC [] [SUB_RIGHT_ADD] THEN
		       `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_3NT,isNonTmnlSym_def]  THEN
		       `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))` by DECIDE_TAC THEN
		       `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= SIGMA ruleNonTmnls (rules g)` by METIS_TAC [set_l3] THEN
		       DECIDE_TAC,
		       DECIDE_TAC,
		       DECIDE_TAC,
		       DECIDE_TAC,
		       DECIDE_TAC,
		       SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN SRW_TAC [] [SUB_RIGHT_ADD] THEN
		       `LENGTH p >= 2` by DECIDE_TAC THEN
		       `LENGTH p >= 1` by DECIDE_TAC THEN
		       `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,NULL_DEF,LENGTH_NIL,slemma6_a_3NT]  THEN
		       `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))` by DECIDE_TAC THEN
		       `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= SIGMA ruleNonTmnls (rules g)` by METIS_TAC [set_l3] THEN
DECIDE_TAC
		],

`~(p=[])` by METIS_TAC [list_l1] THEN
`~(LENGTH p = 0)` by METIS_TAC [LENGTH_NIL] THEN
`LENGTH p >= 1` by DECIDE_TAC THEN
`(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,slemma6_a_3NT] THEN
`0 < ruleNonTmnls (rule l (p++[nt1;nt2]++s))` by DECIDE_TAC THEN METIS_TAC [set_l2],

`~(p=[])` by METIS_TAC [list_l1] THEN
`~(LENGTH p = 0)` by METIS_TAC [LENGTH_NIL] THEN
`LENGTH p >= 1` by DECIDE_TAC THEN
`(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,slemma6_a_3NT] THEN
`0 < ruleNonTmnls (rule l (p++[nt1;nt2]++s))` by DECIDE_TAC THEN METIS_TAC [set_l2]],

(* ~NULL s *)
ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [SUM_IMAGE_UNION,FINITE_DIFF,f_diff,FINITE_UNION] THEN
`~(rule nt [nt1;nt2] IN rules g)` by METIS_TAC [slemma1_4] THEN
`~(rule l (p++[NTS nt]++s) IN rules g)` by METIS_TAC [slemma1_4] THEN
`~(rule l (p++[nt1;nt2]++s) = rule nt [nt1;nt2])` by METIS_TAC [] THEN
`~(rule l (p++[nt1;nt2]++s) = rule l (p++[NTS nt]++s))` by METIS_TAC [] THEN
`{rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)} = {rule nt [nt1;nt2]} UNION {rule l (p++[NTS nt]++s)}` by FULL_SIMP_TAC (srw_ss()) [EXTENSION,EQ_IMP_THM] THEN
ASM_REWRITE_TAC [] THEN
SRW_TAC [] [UNION_OVER_INTER] THENL[
FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
`ruleNonTmnls (rule nt [nt1;nt2]) = 0` by METIS_TAC [slemma6_a_1NT,SUM_IMAGE_SING] THEN
`~(LENGTH s = 0)` by METIS_TAC [NULL_DEF,LENGTH_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH s = 1) \/ (LENGTH s > 1)` by DECIDE_TAC THEN
SRW_TAC [] [ruleNonTmnlsAlt] THENL[
			     DECIDE_TAC,
			     DECIDE_TAC,
			     SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN DECIDE_TAC,
			     `LENGTH s >= 1` by DECIDE_TAC THEN
			     `LENGTH p = 0` by DECIDE_TAC THEN
			     `NULL p` by METIS_TAC [list_l1,LENGTH_NIL] THEN
			     `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def] THEN
			     `0 < ruleNonTmnls (rule l (p++[nt1;nt2]++s))` by DECIDE_TAC THEN METIS_TAC [set_l2],
			     `LENGTH s >= 1` by DECIDE_TAC THEN
			     `~(LENGTH p = 0)` by DECIDE_TAC THEN
			     `~NULL p` by METIS_TAC [list_l1,LENGTH_NIL] THEN
			     SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN SRW_TAC [] [SUB_RIGHT_ADD] THEN
			     `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,slemma6_a_3NT]  THEN
			     `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))` by DECIDE_TAC THEN
			     `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= SIGMA ruleNonTmnls (rules g)` by METIS_TAC [set_l3] THEN
			     DECIDE_TAC,
			     DECIDE_TAC,
			     DECIDE_TAC,
			     DECIDE_TAC,
			     DECIDE_TAC,
			     SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN SRW_TAC [] [SUB_RIGHT_ADD] THEN
			     `LENGTH s >= 1` by DECIDE_TAC THEN
			     `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,slemma6_a_3NT]  THEN
			     `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))` by DECIDE_TAC THEN
			     `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= SIGMA ruleNonTmnls (rules g)` by METIS_TAC [set_l3] THEN
			     DECIDE_TAC],
FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
`ruleNonTmnls (rule nt [nt1;nt2]) = 0` by METIS_TAC [slemma6_a_1NT,SUM_IMAGE_SING] THEN
`~(LENGTH s = 0)` by METIS_TAC [NULL_DEF,LENGTH_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH s = 1) \/ (LENGTH s > 1)` by DECIDE_TAC THEN
SRW_TAC [] [ruleNonTmnlsAlt] THENL[
			     DECIDE_TAC,
			     DECIDE_TAC,
			     SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN DECIDE_TAC,
			     `LENGTH s >= 1` by DECIDE_TAC THEN
			     `LENGTH p = 0` by DECIDE_TAC THEN
			     `NULL p` by METIS_TAC [list_l1,LENGTH_NIL] THEN
			     `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def] THEN
			     `0 < ruleNonTmnls (rule l (p++[nt1;nt2]++s))` by DECIDE_TAC THEN METIS_TAC [set_l2],
			     `LENGTH s >= 1` by DECIDE_TAC THEN
			     `~(LENGTH p = 0)` by DECIDE_TAC THEN
			     `~NULL p` by METIS_TAC [list_l1,LENGTH_NIL] THEN
			     SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN SRW_TAC [] [SUB_RIGHT_ADD] THEN
			     `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,slemma6_a_3NT]  THEN
			     `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))` by DECIDE_TAC THEN
			     `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= SIGMA ruleNonTmnls (rules g)` by METIS_TAC [set_l3] THEN
			     DECIDE_TAC,
			     DECIDE_TAC,
			     DECIDE_TAC,
			     DECIDE_TAC,
			     DECIDE_TAC,
			     SRW_TAC [] [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN SRW_TAC [] [SUB_RIGHT_ADD] THEN
			     `LENGTH s >= 1` by DECIDE_TAC THEN
			     `(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,slemma6_a_3NT]  THEN
			     `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))` by DECIDE_TAC THEN
			     `LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2 <= SIGMA ruleNonTmnls (rules g)` by METIS_TAC [set_l3] THEN
			     DECIDE_TAC],
`~(LENGTH s = 0)` by METIS_TAC [LENGTH_NIL,list_l1] THEN
`LENGTH s >= 1` by DECIDE_TAC THEN
`(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,slemma6_a_3NT] THEN
`0 < ruleNonTmnls (rule l (p++[nt1;nt2]++s))` by DECIDE_TAC THEN METIS_TAC [set_l2],
`~(LENGTH s = 0)` by METIS_TAC [LENGTH_NIL,list_l1] THEN
`LENGTH s >= 1` by DECIDE_TAC THEN
`(ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)` by METIS_TAC [slemma6_a_2NT,isNonTmnlSym_def,slemma6_a_3NT] THEN
`0 < ruleNonTmnls (rule l (p++[nt1;nt2]++s))` by DECIDE_TAC THEN METIS_TAC [set_l2]]]
)

val lemma7_a = prove (``!g g'.FINITE (rules g) ==> trans1Tmnl nt t g g' ==> (badTmnlRules g > 0)``,
SRW_TAC [] [] THEN
`badTmnlRules g' < badTmnlRules g` by METIS_TAC [lemma6_a] THEN
FULL_SIMP_TAC arith_ss [LESS_EQ,SUC_NOT]
)

val lemma7_b = prove (``FINITE (rules g) ==> trans2NT nt nt1 nt2 g g' ==> (badNtRules g > 0)``,
SRW_TAC [] [] THEN
`badNtRules g' < badNtRules g` by METIS_TAC [lemma6_b] THEN
FULL_SIMP_TAC arith_ss [LESS_EQ,SUC_NOT]
)

val lemma15_a = prove(
``!g g'.FINITE (rules g) ==> (badTmnlRules g = 0) ==> (\x y.?nt nt1 nt2.trans2NT nt nt1 nt2 x y)g g' ==> (badTmnlRules g' = 0)``,
SRW_TAC [] [trans2NT] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlRules] THEN
FULL_SIMP_TAC (srw_ss()) [SUM_IMAGE_UNION,FINITE_DIFF,f_diff,FINITE_UNION] THEN
`~(rule nt [nt1;nt2] IN rules g)` by METIS_TAC [slemma1_4] THEN
`~(rule l (p++[NTS nt]++s) IN rules g)` by METIS_TAC [slemma1_4] THEN
`~(rule l (p++[nt1;nt2]++s) = rule nt [nt1;nt2])` by METIS_TAC [] THEN
`~(rule l (p++[nt1;nt2]++s) = rule l (p++[NTS nt]++s))` by METIS_TAC [] THEN
`{rule nt [nt1;nt2]; rule l (p ++ [NTS nt] ++ s)} = {rule nt [nt1;nt2]} UNION {rule l (p++[NTS nt]++s)}` by FULL_SIMP_TAC (srw_ss()) [EXTENSION,EQ_IMP_THM] THEN
ASM_REWRITE_TAC [] THEN
SRW_TAC [] [UNION_OVER_INTER] THENL[ (* 4 subgoals *)
   FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
   SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
   SRW_TAC [] [ruleTmnlsAlt] 
   THENL[ (* 4 subgoals *)
      METIS_TAC [sym_r1b],
      METIS_TAC [sym_r1b],
      METIS_TAC [sym_r1b],
      SRW_TAC [] [ruleTmnlsAlt] THEN
      `SIGMA ruleTmnls {(rule l (p++[nt1;nt2]++s))} = 0` by METIS_TAC [SUM_IMAGE_SING,set_l4] THEN
      FULL_SIMP_TAC (srw_ss()) [ruleTmnlsAlt,SUM_IMAGE_SING] THEN
      `~(LENGTH p + 2 + LENGTH s <= 1)` by DECIDE_TAC THEN
      `~isTmnlSym nt1` by METIS_TAC [sym_r1b] THEN
      `~isTmnlSym nt2` by METIS_TAC [sym_r1b] THEN
      `FILTER isTmnlSym (p ++ [nt1; nt2] ++ s) = FILTER isTmnlSym p ++ FILTER isTmnlSym [nt1; nt2] ++ FILTER isTmnlSym s` by METIS_TAC [FILTER_APPEND_DISTRIB] THEN
      `FILTER isTmnlSym [nt1; nt2] = []` by FULL_SIMP_TAC (srw_ss()) [FILTER] THEN
      `LENGTH (FILTER isTmnlSym (p ++ [nt1; nt2] ++ s)) = (LENGTH (FILTER isTmnlSym p)) + (LENGTH (FILTER isTmnlSym [nt1;nt2])) + (LENGTH (FILTER isTmnlSym s))` by METIS_TAC [LENGTH_APPEND] THEN
      `(LENGTH (FILTER isTmnlSym [nt1;nt2])) = 0` by METIS_TAC [LENGTH_NIL] THEN
      `LENGTH (FILTER isTmnlSym p) + LENGTH (FILTER isTmnlSym [nt1; nt2]) + LENGTH (FILTER isTmnlSym s) = 0` by METIS_TAC [] THEN
      `(LENGTH (FILTER isTmnlSym p) = 0) /\ (LENGTH (FILTER isTmnlSym s) = 0)` by DECIDE_TAC THEN
      SRW_TAC []  [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b]],
   
   FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
   SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
   `ruleTmnls (rule nt [nt1;nt2]) = 0` by (SRW_TAC [] [ruleTmnlsAlt] 
   THENL [METIS_TAC [sym_r1b],METIS_TAC [sym_r1b],METIS_TAC [sym_r1b]]) THEN
   `~(l=nt)` by METIS_TAC [slemma1_4] THEN
   `~((rule nt [nt1;nt2]) = (rule l (p++[NTS nt]++s)))` by SRW_TAC [] [] THEN
   `({rule nt [nt1; nt2]} INTER {rule l (p ++ [NTS nt] ++ s)})= {}` by SRW_TAC [] [] THEN
   FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM]  THEN
   `SIGMA ruleTmnls {(rule l (p++[nt1;nt2]++s))} = 0` by METIS_TAC [SUM_IMAGE_SING,set_l4] THEN
   FULL_SIMP_TAC (srw_ss()) [ruleTmnlsAlt,SUM_IMAGE_SING] THEN
   `~(LENGTH p + 2 + LENGTH s <= 1)` by DECIDE_TAC THEN
   `~isTmnlSym nt1` by METIS_TAC [sym_r1b] THEN
   `~isTmnlSym nt2` by METIS_TAC [sym_r1b] THEN
   `FILTER isTmnlSym (p ++ [nt1; nt2] ++ s) = FILTER isTmnlSym p ++ FILTER isTmnlSym [nt1; nt2] ++ FILTER isTmnlSym s` by METIS_TAC [FILTER_APPEND_DISTRIB] THEN
   `FILTER isTmnlSym [nt1; nt2] = []` by FULL_SIMP_TAC (srw_ss()) [FILTER] THEN
   `LENGTH (FILTER isTmnlSym (p ++ [nt1; nt2] ++ s)) = (LENGTH (FILTER isTmnlSym p)) + (LENGTH (FILTER isTmnlSym [nt1;nt2])) + (LENGTH (FILTER isTmnlSym s))` by METIS_TAC [LENGTH_APPEND] THEN
   `(LENGTH (FILTER isTmnlSym [nt1;nt2])) = 0` by METIS_TAC [LENGTH_NIL] THEN
   `LENGTH (FILTER isTmnlSym p) + LENGTH (FILTER isTmnlSym [nt1; nt2]) + LENGTH (FILTER isTmnlSym s) = 0` by METIS_TAC [] THEN
   `(LENGTH (FILTER isTmnlSym p) = 0) /\ (LENGTH (FILTER isTmnlSym s) = 0)` by DECIDE_TAC THEN
   SRW_TAC []  [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN
   METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b],


   FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
   SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
   `ruleTmnls (rule nt [nt1;nt2]) = 0` by (SRW_TAC [] [ruleTmnlsAlt] 
   THENL [METIS_TAC [sym_r1b],METIS_TAC [sym_r1b],METIS_TAC [sym_r1b]]) THEN
   `~(l=nt)` by METIS_TAC [slemma1_4] THEN
   `~((rule nt [nt1;nt2]) = (rule l (p++[NTS nt]++s)))` by SRW_TAC [] [] THEN
   `({rule nt [nt1; nt2]} INTER {rule l (p ++ [NTS nt] ++ s)})= {}` by SRW_TAC [] [] THEN
   FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM]  THEN
   `SIGMA ruleTmnls {(rule l (p++[nt1;nt2]++s))} = 0` by METIS_TAC [SUM_IMAGE_SING,set_l4] THEN
   FULL_SIMP_TAC (srw_ss()) [ruleTmnlsAlt,SUM_IMAGE_SING] THEN
   `~(LENGTH p + 2 + LENGTH s <= 1)` by DECIDE_TAC THEN
   `~isTmnlSym nt1` by METIS_TAC [sym_r1b] THEN
   `~isTmnlSym nt2` by METIS_TAC [sym_r1b] THEN
   `FILTER isTmnlSym (p ++ [nt1; nt2] ++ s) = FILTER isTmnlSym p ++ FILTER isTmnlSym [nt1; nt2] ++ FILTER isTmnlSym s` by METIS_TAC [FILTER_APPEND_DISTRIB] THEN
   `FILTER isTmnlSym [nt1; nt2] = []` by FULL_SIMP_TAC (srw_ss()) [FILTER] THEN
   `LENGTH (FILTER isTmnlSym (p ++ [nt1; nt2] ++ s)) = (LENGTH (FILTER isTmnlSym p)) + (LENGTH (FILTER isTmnlSym [nt1;nt2])) + (LENGTH (FILTER isTmnlSym s))` by METIS_TAC [LENGTH_APPEND] THEN
   `(LENGTH (FILTER isTmnlSym [nt1;nt2])) = 0` by METIS_TAC [LENGTH_NIL] THEN
   `LENGTH (FILTER isTmnlSym p) + LENGTH (FILTER isTmnlSym [nt1; nt2]) + LENGTH (FILTER isTmnlSym s) = 0` by METIS_TAC [] THEN
   `(LENGTH (FILTER isTmnlSym p) = 0) /\ (LENGTH (FILTER isTmnlSym s) = 0)` by DECIDE_TAC THEN
   SRW_TAC []  [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN
   METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b],

   FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
   SRW_TAC [] [SUM_IMAGE_UNION,SUM_IMAGE_SING,inter_l1,inter_l2,SUM_IMAGE_THM] THEN
   `ruleTmnls (rule nt [nt1;nt2]) = 0` by (SRW_TAC [] [ruleTmnlsAlt] 
   THENL [METIS_TAC [sym_r1b],METIS_TAC [sym_r1b],METIS_TAC [sym_r1b]]) THEN
   `~(l=nt)` by METIS_TAC [slemma1_4] THEN
   `~((rule nt [nt1;nt2]) = (rule l (p++[NTS nt]++s)))` by SRW_TAC [] [] THEN
   `({rule nt [nt1; nt2]} INTER {rule l (p ++ [NTS nt] ++ s)})= {}` by SRW_TAC [] [] THEN
   FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM]  THEN
   `SIGMA ruleTmnls {(rule l (p++[nt1;nt2]++s))} = 0` by METIS_TAC [SUM_IMAGE_SING,set_l4] THEN
   FULL_SIMP_TAC (srw_ss()) [ruleTmnlsAlt,SUM_IMAGE_SING] THEN
   `~(LENGTH p + 2 + LENGTH s <= 1)` by DECIDE_TAC THEN
   `~isTmnlSym nt1` by METIS_TAC [sym_r1b] THEN
   `~isTmnlSym nt2` by METIS_TAC [sym_r1b] THEN
   `FILTER isTmnlSym (p ++ [nt1; nt2] ++ s) = FILTER isTmnlSym p ++ FILTER isTmnlSym [nt1; nt2] ++ FILTER isTmnlSym s` by METIS_TAC [FILTER_APPEND_DISTRIB] THEN
   `FILTER isTmnlSym [nt1; nt2] = []` by FULL_SIMP_TAC (srw_ss()) [FILTER] THEN
   `LENGTH (FILTER isTmnlSym (p ++ [nt1; nt2] ++ s)) = (LENGTH (FILTER isTmnlSym p)) + (LENGTH (FILTER isTmnlSym [nt1;nt2])) + (LENGTH (FILTER isTmnlSym s))` by METIS_TAC [LENGTH_APPEND] THEN
   `(LENGTH (FILTER isTmnlSym [nt1;nt2])) = 0` by METIS_TAC [LENGTH_NIL] THEN
   `LENGTH (FILTER isTmnlSym p) + LENGTH (FILTER isTmnlSym [nt1; nt2]) + LENGTH (FILTER isTmnlSym s) = 0` by METIS_TAC [] THEN
   `(LENGTH (FILTER isTmnlSym p) = 0) /\ (LENGTH (FILTER isTmnlSym s) = 0)` by DECIDE_TAC THEN
   SRW_TAC []  [FILTER_APPEND_DISTRIB,LENGTH_APPEND] THEN
   METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b]]
)


val lemma14_b = prove(
``!g g'.RTC (\x y. ?nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ==> FINITE (rules g) ==> (badTmnlRules g = 0) ==> (badTmnlRules g' = 0)``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [lemma15_a,lemma10_b]
)

val INFINITE_STR_UNIV = store_thm(
  "INFINITE_STR_UNIV",
  ``INFINITE (UNIV : string set)``,
  SRW_TAC [][pred_setTheory.INFINITE_UNIV] THEN
  Q.EXISTS_TAC `\st. STRING (CHR 0) st` THEN SRW_TAC [][] THEN
  Q.EXISTS_TAC `""` THEN SRW_TAC [][])


val finiteNts = prove(
``!s.FINITE s ==> !g.(s=rules g) ==> FINITE (nonTerminals g)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
Cases_on `g`  THEN
SRW_TAC [] [nonTerminals_def] THENL[
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN METIS_TAC [FINITE_EMPTY,IMAGE_FINITE],
METIS_TAC [NOT_IN_EMPTY,rules_def]],
Cases_on `g`  THEN
SRW_TAC [] [nonTerminals_def] THENL[
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN
`FINITE f` by METIS_TAC [FINITE_INSERT] THEN
 METIS_TAC [IMAGE_FINITE],
Cases_on `x` THEN
`FINITE (LIST_TO_SET l)` by METIS_TAC [finiteLists] THEN
SRW_TAC [] [rule_nonterminals_def] THEN
`{nt | isNonTmnlSym nt /\ MEM nt l} = {nt | isNonTmnlSym nt /\ nt IN (LIST_TO_SET l)}` by SRW_TAC [] [SET_TO_LIST_IN_MEM] THEN
ASM_REWRITE_TAC [] THEN
`{nt | isNonTmnlSym nt /\ nt IN (LIST_TO_SET l)} SUBSET (LIST_TO_SET l)` by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]  THEN
METIS_TAC [SUBSET_FINITE]]]
)

val finiteNts2str = prove(
``!s.FINITE s ==> !g.(s=(nonTerminals g)) ==> FINITE (IMAGE nts2str (nonTerminals g))``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
METIS_TAC [FINITE_EMPTY,IMAGE_FINITE],
`FINITE (nonTerminals g)` by METIS_TAC [FINITE_INSERT] THEN METIS_TAC [IMAGE_FINITE]]
)

val existsNewNt = prove (
``!x.~(x IN (IMAGE nts2str (nonTerminals g))) ==> ~(NTS x IN nonTerminals g)``,
SRW_TAC [] [] THEN
`~(x = nts2str (NTS x)) \/ ~((NTS x) IN nonTerminals g)` by METIS_TAC [] THEN
METIS_TAC [nts2str_def]
)


val new_exists = store_thm(
  "new_exists",
  ``!s : string set. FINITE s ==> ?x. ~(x IN s)``,
  Q_TAC SUFF_TAC `INFINITE (UNIV : string set)`
        THEN1 METIS_TAC [pred_setTheory.IN_UNIV,
                         pred_setTheory.IN_INFINITE_NOT_FINITE] THEN
  SRW_TAC [][INFINITE_STR_UNIV]);

val lemma8_a = prove(
``FINITE (rules g) ==> (badTmnlRules g > 0) ==> ?g' nt t.trans1Tmnl nt t g g' ``,
SRW_TAC [] [badTmnlRules] THEN
`?e.e IN (rules g) /\ ruleTmnls e > 0` by METIS_TAC [slemma8_a_2] THEN
`?l p s t. (e=rule l (p ++ [TS t] ++ s)) /\ (~NULL p \/ ~NULL s)` by METIS_TAC [slemma12_a_2] THEN
(FULL_SIMP_TAC (srw_ss()) [trans1Tmnl] THEN
`INFINITE (UNIV : string set)` by SRW_TAC [] [] THEN1 SRW_TAC [] [INFINITE_STR_UNIV] THEN
`FINITE (nonTerminals g)` by METIS_TAC [finiteNts] THEN
`FINITE (IMAGE nts2str (nonTerminals g))` by METIS_TAC [finiteNts2str] THEN
`?nt.nt IN UNIV /\ ~(nt IN (IMAGE nts2str (nonTerminals g)))` by METIS_TAC [IN_INFINITE_NOT_FINITE] THEN
`~(NTS nt IN nonTerminals g)` by METIS_TAC [existsNewNt] THEN
METIS_TAC [isTmnlSym_def,startSym_def,rules_def])
)

val noTmnls = prove(
``!l r.(ruleTmnls (rule l r) = 0) = ((LENGTH r <= 1) \/ (EVERY isNonTmnlSym r))``,
SRW_TAC [] [ruleTmnlsAlt] THEN
SRW_TAC [] [EQ_IMP_THM] THENL[
`(FILTER isTmnlSym r) = []` by METIS_TAC [LENGTH_NIL] THEN
`~(?e.MEM e r /\ isTmnlSym e)` by METIS_TAC [filter_l2] THEN METIS_TAC [sym_r7b,rgr_r9eq],
METIS_TAC [sym_r3b,rgr_r9eq,filter_l2]
])


val lemma8_b = prove (
``FINITE (rules g) ==> (badTmnlRules g = 0) ==> ((badNtRules g > 0) ==> ?g' nt nt1 nt2.trans2NT nt nt1 nt2 g g')``,
SRW_TAC [] [badNtRules] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlRules] THEN
`!r.r IN (rules g) ==> (ruleTmnls r = 0)`  by METIS_TAC [lemma16_b,badTmnlRules] THEN
`?e.e IN (rules g) /\ ruleNonTmnls e > 0` by METIS_TAC [slemma8_a_2] THEN
`ruleTmnls e = 0` by METIS_TAC [] THEN
` ~?l p s t. (e = rule l (p ++ [TS t] ++ s)) /\ (~NULL p \/ ~NULL s)` by METIS_TAC [slemma12_a_1] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`?l r p s t1. (e=rule l (p ++ [NTS t1] ++ s)) /\ (LENGTH (p ++ [NTS t1] ++ s) >= 3)` by METIS_TAC [slemma12_a_2NT] THEN
`(~NULL p \/ ~NULL s)` by METIS_TAC [sl] THENL[
` ~(e = rule l (p ++ [TS t] ++ s))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [trans2NT] THEN
`INFINITE (UNIV : string set)` by SRW_TAC [] [] THEN1 SRW_TAC [] [INFINITE_STR_UNIV] THEN
`FINITE (nonTerminals g)` by METIS_TAC [finiteNts] THEN
`FINITE (IMAGE nts2str (nonTerminals g))` by METIS_TAC [finiteNts2str] THEN
`?nt.nt IN UNIV /\ ~(nt IN (IMAGE nts2str (nonTerminals g)))` by METIS_TAC [IN_INFINITE_NOT_FINITE] THEN
`~(NTS nt IN nonTerminals g)` by METIS_TAC [existsNewNt] THEN
`~(p=[])` by METIS_TAC [NULL_DEF] THEN
`p = FRONT p ++ [LAST p]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`~(LENGTH (p ++ [NTS t1] ++ s) <= 1)` by METIS_TAC [notLen1] THEN
`EVERY isNonTmnlSym (p ++ [NTS t1] ++ s)` by METIS_TAC [noTmnls] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`EVERY isNonTmnlSym (FRONT p) /\ isNonTmnlSym (LAST p)` by METIS_TAC [EVERY_APPEND,EVERY_DEF] THEN
`?ntx.LAST p = (NTS ntx)` by METIS_TAC [isNonTmnlSym_def] THEN

MAP_EVERY Q.EXISTS_TAC [`G (rules g DIFF {rule l (FRONT p ++ [NTS ntx; NTS t1] ++ s)} UNION {rule nt [NTS ntx; NTS t1]; rule l (FRONT p ++ [NTS nt] ++ s)}) (startSym g)`,`nt`,`NTS ntx`,`NTS t1`,`l`,`FRONT p`,`s`] THEN
SRW_TAC [] [] THENL[
METIS_TAC [APPEND,CONS,APPEND_ASSOC],

`LENGTH (FRONT p ++ [LAST p]) + 1 + LENGTH s >= 3`  by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (FRONT p) + LENGTH s >= 1` by DECIDE_TAC THEN
Cases_on `~NULL s` THENL[
METIS_TAC [],
SRW_TAC [] [] THEN 
`LENGTH s = 0` by FULL_SIMP_TAC list_ss [len0] THEN
`LENGTH (FRONT p) >= 1` by DECIDE_TAC THEN
`1 <= LENGTH (FRONT p)` by DECIDE_TAC THEN
`?a0 a1.(FRONT p=a0::a1)` by METIS_TAC [l_lemma1] THEN
SRW_TAC [] [] THEN
Cases_on `FRONT p` THEN FULL_SIMP_TAC (srw_ss()) []],
METIS_TAC [isNonTmnlSym_def],
METIS_TAC [rules_def],
METIS_TAC [startSym_def]],

` ~(e = rule l (p ++ [TS t] ++ s))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [trans2NT] THEN
`INFINITE (UNIV : string set)` by SRW_TAC [] [] THEN1 SRW_TAC [] [INFINITE_STR_UNIV] THEN
`FINITE (nonTerminals g)` by METIS_TAC [finiteNts] THEN
`FINITE (IMAGE nts2str (nonTerminals g))` by METIS_TAC [finiteNts2str] THEN
`?nt.nt IN UNIV /\ ~(nt IN (IMAGE nts2str (nonTerminals g)))` by METIS_TAC [IN_INFINITE_NOT_FINITE] THEN
`~(NTS nt IN nonTerminals g)` by METIS_TAC [existsNewNt] THEN
`~(s=[])` by METIS_TAC [NULL_DEF] THEN
`?h' t'.s = h'::t'` by METIS_TAC [listNotNull] THEN
`~(LENGTH (p ++ [NTS t1] ++ s) <= 1)` by METIS_TAC [notLen1] THEN
`EVERY isNonTmnlSym (p ++ [NTS t1] ++ s)` by METIS_TAC [noTmnls] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`isNonTmnlSym h' /\ EVERY isNonTmnlSym t'` by METIS_TAC [EVERY_APPEND,EVERY_DEF,APPEND,CONS] THEN
`?ntx.h' = (NTS ntx)` by METIS_TAC [isNonTmnlSym_def] THEN

MAP_EVERY Q.EXISTS_TAC [`G (rules g DIFF {rule l (p ++ [NTS t1;NTS ntx] ++ t')} UNION {rule nt [NTS t1;NTS ntx]; rule l (p ++ [NTS nt] ++ t')}) (startSym g)`,`nt`,`NTS t1`,`NTS ntx`,`l`,`p`,`t'`] THEN
SRW_TAC [] [] THENL[
METIS_TAC [APPEND,CONS,APPEND_ASSOC],

FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH p + LENGTH t' >= 1` by DECIDE_TAC THEN
Cases_on `~NULL p` THENL[
METIS_TAC [],
SRW_TAC [] [] THEN 
`LENGTH p = 0` by FULL_SIMP_TAC list_ss [len0] THEN
`LENGTH (t') >= 1` by DECIDE_TAC THEN
`1 <= LENGTH (t')` by DECIDE_TAC THEN
`?a0 a1.(t'=a0::a1)` by METIS_TAC [l_lemma1] THEN
SRW_TAC [] [] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) []],
METIS_TAC [rules_def],
METIS_TAC [startSym_def]]]
)


val lemma11_a = prove(
``!g.FINITE (rules g) ==> ~(?g' nt t.trans1Tmnl nt t g g') ==> (badTmnlRules g = 0)``,
SRW_TAC [] [] THEN
`~(?g' nt t.trans1Tmnl nt t g g') ==> ~(badTmnlRules g > 0)` by METIS_TAC [MONO_NOT,lemma8_a] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`badTmnlRules g <= 0` by FULL_SIMP_TAC arith_ss [] THEN
FULL_SIMP_TAC arith_ss [LE]
)

val lemma11_b = prove(
``!g.FINITE (rules g) ==> (badTmnlRules g = 0) ==> (~(?g' nt nt1 nt2.trans2NT nt nt1 nt2 g g') ==> (badNtRules g = 0))``,
SRW_TAC [] [] THEN
`~(?g' nt nt1 nt2.trans2NT nt nt1 nt2 g g') ==> ~(badNtRules g > 0)` by METIS_TAC [MONO_NOT,lemma8_b] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`badNtRules g <= 0` by FULL_SIMP_TAC arith_ss [] THEN
FULL_SIMP_TAC arith_ss [LE]
)

val lemma9_a = prove (
``!g. FINITE (rules g) ==> (?g'.RTC (\x y.?nt t.trans1Tmnl nt t x y) g g' /\ (badTmnlRules g' = 0))``,
completeInduct_on `badTmnlRules g` THEN
Cases_on `v=0` THENL[
METIS_TAC [RTC_RULES],
SRW_TAC [] [] THEN
`?g' nt t. trans1Tmnl nt t g g'` by  METIS_TAC [MONO_NOT,lemma11_a] THEN
`(badTmnlRules g' < badTmnlRules g)` by METIS_TAC [lemma6_a] THEN
`FINITE (rules g')` by METIS_TAC [lemma10_a] THEN
`?g''.RTC (\x y.?nt t.trans1Tmnl nt t x y) g' g'' /\ (badTmnlRules g'' = 0)` by  METIS_TAC [] THEN
Q.EXISTS_TAC `g''` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.ABBREV_TAC `r=(\x y. ?nt t. trans1Tmnl nt t x y)` THEN
`r g g'` by (SRW_TAC [] [Abbr `r`] THEN METIS_TAC []) THEN
METIS_TAC [RTC_RULES]
])


val lemma9_b = prove(
``!g. FINITE (rules g) ==> (badTmnlRules g = 0) ==> (?g'.RTC (\x y.?nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' /\ (badNtRules g' = 0))``,
completeInduct_on `badNtRules g` THEN
Cases_on `v=0` THENL[
METIS_TAC [RTC_RULES],
SRW_TAC [] [] THEN
`?g' nt nt1 nt2. trans2NT nt nt1 nt2 g g'` by  METIS_TAC [MONO_NOT,lemma11_b] THEN
`(badNtRules g' < badNtRules g)` by METIS_TAC [lemma6_b] THEN
`FINITE (rules g')` by METIS_TAC [lemma10_b] THEN
`?g''.RTC (\x y.?nt nt1 nt2.trans2NT nt nt1 nt2 x y) g' g'' /\ (badTmnlRules g' = 0) /\ (badNtRules g'' = 0)` by  METIS_TAC [lemma15_a] THEN
Q.EXISTS_TAC `g''` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.ABBREV_TAC `r=(\x y. ?nt nt1 nt2. trans2NT nt nt1 nt2 x y)` THEN
`r g g'` by (SRW_TAC [] [Abbr `r`] THEN METIS_TAC []) THEN
METIS_TAC [RTC_RULES]
])


val thm4_5 = prove(
``!g.FINITE (rules g) ==> ?g'. (cnf g') /\ (eqLang g g')``,
SRW_TAC [] [cnf] THEN
METIS_TAC [cnf,lemma14_b,lemma10_artc,lemma9_a,lemma9_b,cnf_lemma]
)

val _ = export_theory ();
