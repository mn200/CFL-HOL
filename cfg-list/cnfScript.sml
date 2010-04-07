(* A theory about Chomsky Normal Form *)
open HolKernel boolLib bossLib Parse BasicProvers

open stringTheory relationTheory pred_setTheory listTheory
arithmeticTheory rich_listTheory

open grammarDefTheory listLemmasTheory symbolDefTheory setLemmasTheory
containerTheory relationLemmasTheory unitProdsTheory eProdsTheory

val _ = new_theory "cnf";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);

val noeProds = Define
`noeProds ru = ¬∃l. rule l [] ∈ ru`;

val noUnitProds = Define
`noUnitProds ru = ¬∃l nt. rule l [NTS nt] ∈ ru`;

val negrImpnoeProds = store_thm
("negrImpnoeProds",
``negr g g' ⇒ noeProds (rules g')``,

SRW_TAC [][noeProds, negr_def] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [munge_def, EXTENSION] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) []);


val upgrImpnoUnitProds = store_thm
("upgrImpnoUnitProds",
``upgr g g' ⇒ noUnitProds (rules g')``,

SRW_TAC [][noUnitProds, upgr_def, upgr_rules_def, nonUnitProds_def,
	   nonUnitProds_def, newProds_def, unitProds_def, EXTENSION]);


val upgr_noeProds = store_thm
("upgr_noeProds",
``noeProds (rules g) ⇒ upgr g g' ⇒ noeProds (rules g')``,

SRW_TAC [][upgr_def, noeProds, upgr_rules_def, newProds_def, nonUnitProds_def,
	   unitProds_def, EXTENSION]);


(* Chomsky Normal Form *)

val trans1Tmnl = Define `trans1Tmnl nt t g g' = 
∃l r p s. MEM (rule l r) (rules g) ∧ 
(r=p++[t]++s) ∧ (p ≠ [] ∨ s ≠[]) ∧ isTmnlSym t ∧ 
((NTS nt) ∉ (nonTerminals g)) ∧ 
(rules(g')=(delete (rule l r) (rules g)) ++[rule nt [t];rule l (p++[NTS nt]++s)]) ∧ 
(startSym g' = startSym g)`;

val trans1Tmnl_noeProds = store_thm
("trans1Tmnl_noeProds",
``noeProds (rules g) ∧
trans1Tmnl nt t g g' ⇒
noeProds (rules g')``,

SRW_TAC [][noeProds, trans1Tmnl] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
`rule l' [] ∈ delete (rule l (p ++ [t] ++ s)) (rules g) ++
[rule nt [t]; rule l (p ++ [NTS nt] ++ s)]` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [memdel]);


val trans1Tmnl_noUnitProds = store_thm
("trans1Tmnl_noUnitProds",
``noUnitProds (rules g) ∧
trans1Tmnl nt t g g' ⇒
noUnitProds (rules g')``,

SRW_TAC [][noUnitProds, trans1Tmnl] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
`rule l' [NTS nt'] ∈ delete (rule l (p ++ [t] ++ s)) (rules g) ++
[rule nt [t]; rule l (p ++ [NTS nt] ++ s)]` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, lreseq] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [memdel]);


(* BasicProvers.export_rewrites (["ruleTmnlsAlt"]) *)

val ruleTmnls = Define `(ruleTmnls (rule l [t]) = 0) ∧
(ruleTmnls (rule l r) = LENGTH (FILTER (isTmnlSym) r))`


val ruleTmnlsAlt = store_thm("ruleTmnlsAlt",
``∀l r.ruleTmnls (rule l r) = if LENGTH r <= 1 then 0 else LENGTH (FILTER (isTmnlSym) r)``,
Induct_on `r` THEN
SRW_TAC [] [ruleTmnls] THENL[
SRW_TAC [] [] THEN
`(LENGTH r) + 1 <= 1` by METIS_TAC [ADD1] THEN
`LENGTH r <= 0` by FULL_SIMP_TAC arith_ss [] THEN
`r=[]` by FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [ruleTmnls],
`∃h' r'.(r=(h'::r'))` by FULL_SIMP_TAC (srw_ss()) [l_lemma1] THEN
FULL_SIMP_TAC (srw_ss()) [ruleTmnls],
`∃h' r'.(r=(h'::r'))` by FULL_SIMP_TAC (srw_ss()) [l_lemma1] THEN
FULL_SIMP_TAC (srw_ss()) [ruleTmnls]
])

val ruleNonTmnls = Define ` (ruleNonTmnls (rule l []) = 0) ∧
(ruleNonTmnls (rule l [t]) = 0) ∧
(ruleNonTmnls (rule l [t1;t2]) = 0) ∧
(ruleNonTmnls (rule l r) = LENGTH (FILTER (isNonTmnlSym) r))`

val ruleNonTmnlsAlt = prove(
``∀l r.ruleNonTmnls (rule l r) = if LENGTH r <= 2 then 0 else LENGTH (FILTER (isNonTmnlSym) r)``,
SRW_TAC [] [] THENL[
`(LENGTH r=2) ∨ (LENGTH r<2)` by METIS_TAC [LESS_OR_EQ] THENL[
 METIS_TAC [ruleNonTmnls,list_lem2],
`(LENGTH r = 0) ∨ (LENGTH r = 1)` by DECIDE_TAC THENL[
METIS_TAC [LENGTH_NIL, ruleNonTmnls],
METIS_TAC [list_lem1, ruleNonTmnls]]],
`LENGTH r >= 3` by DECIDE_TAC THEN METIS_TAC [ruleNonTmnls,APPEND,list_lem3]])

val badTmnlsCount = Define `(badTmnlsCount g = SUM (MAP ruleTmnls (rules g)))`

val badNtmsCount = Define `(badNtmsCount g = SUM  (MAP ruleNonTmnls (rules g)))`

val cnf = Define 
    `cnf g = (badNtmsCount g = 0) ∧ (badTmnlsCount g = 0)`


val trans2NT = Define 
`trans2NT nt nt1 nt2 g g' = 
    ∃l r p s. MEM (rule l r) (rules g) ∧ (r=p++[nt1;nt2]++s) 
    ∧ (p≠[] ∨ s≠[]) ∧ isNonTmnlSym nt1 ∧ isNonTmnlSym nt2 
    ∧ ((NTS nt) ∉ (nonTerminals g)) ∧ 
    (rules g' = delete (rule l r) (rules g) ++ 
     [rule nt [nt1;nt2];rule l (p++[NTS nt]++s)]) 
    ∧ (startSym g' = startSym g)`;

val trans2NT_noeProds = store_thm
("trans2NT_noeProds",
``noeProds (rules g) ∧
trans2NT nt1 nt2 t g g' ⇒
noeProds (rules g')``,

SRW_TAC [][noeProds, trans2NT] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
`rule l' [] ∈ delete (rule l (p ++ [nt2; t] ++ s)) (rules g) ++
      [rule nt1 [nt2; t]; rule l (p ++ [NTS nt1] ++ s)]` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [memdel]);


val trans2NT_noUnitProds = store_thm
("trans2NT_noUnitProds",
``noUnitProds (rules g) ∧
trans2NT nt1 nt2 t g g' ⇒
noUnitProds (rules g')``,

SRW_TAC [][noUnitProds, trans2NT] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
`rule l' [NTS nt] ∈ delete (rule l (p ++ [nt2; t] ++ s)) (rules g) ++
      [rule nt1 [nt2; t]; rule l (p ++ [NTS nt1] ++ s)]` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, lreseq] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [memdel]);

val cnf_r1 = prove(
``∀g g' nt t.trans1Tmnl nt t g g' ⇒ derives g u v ⇒ RTC (derives g') u v``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,trans1Tmnl] THEN
Cases_on `l=lhs` THEN
SRW_TAC [] [] THEN
Cases_on `EVERY isNonTmnlSym rhs` THENL[

  `~((rhs = p ++ [t] ++ s) ∧ isTmnlSym t)` by METIS_TAC [sym_r3b] THEN
   FULL_SIMP_TAC (srw_ss()) [] THENL[
     `MEM (rule l rhs) (rules g')` by METIS_TAC [not_mem_delete,rule_11,
						 delete_mem_list,MEM,MEM_APPEND] THEN
      METIS_TAC [res1, derives_same_append_left,derives_same_append_right,
		 RTC_SUBSET],
      METIS_TAC [sym_r1b]
   ],


  Cases_on `rhs=(p ++ [t] ++ s)` 
   THENL[
    SRW_TAC [] [] THEN 
    `MEM (rule nt [t]) (rules g') ∧ MEM (rule l (p ++ [NTS nt] ++ s)) (rules g')`
	 by METIS_TAC [APPEND,MEM,MEM_APPEND] THEN				       
	 `RTC (derives g') (p++[NTS nt]++s) (p++[t]++s)` 
	 by METIS_TAC [res1,derives_same_append_right,derives_same_append_left,RTC_SUBSET] THEN
	 METIS_TAC [RTC_SUBSET,res1,RTC_RULES,rtc_derives_same_append_left,rtc_derives_same_append_right,
		    APPEND_ASSOC],
	 `MEM (rule l rhs) (rules g')` by  METIS_TAC [not_mem_delete,rule_11,
						 delete_mem_list,MEM,MEM_APPEND] THEN
    METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right]
   ],


  `MEM (rule lhs rhs) (rules g')` by METIS_TAC [not_mem_delete,rule_11,
						 delete_mem_list,MEM,MEM_APPEND] THEN
   METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right],

  `MEM (rule lhs rhs) (rules g')` by METIS_TAC [not_mem_delete,rule_11,
						 delete_mem_list,MEM,MEM_APPEND] THEN
   METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right],
  
  `~∃n s1 s2. (rhs = s1 ++ [n] ++ s2) ∧ isTmnlSym n` by METIS_TAC [sym_r3b] THEN
    `MEM (rule l rhs) (rules g')`  by 
    METIS_TAC [not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
    METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right],

  
  Cases_on `rhs=(p ++ [t] ++ s)` 
   THENL[
	 SRW_TAC [] [] THEN 
	 `MEM (rule nt [t]) (rules g') ∧ MEM (rule l (p ++ [NTS nt] ++ s)) (rules g')` 
	 by METIS_TAC [MEM,MEM_APPEND,APPEND] THEN
	 `RTC (derives g') (p++[NTS nt]++s) (p++[t]++s)` 
	 by METIS_TAC [res1,derives_same_append_right,derives_same_append_left,
		       RTC_SUBSET] THEN
	 METIS_TAC [RTC_SUBSET,res1,RTC_RULES,rtc_derives_same_append_left,
		    rtc_derives_same_append_right,APPEND_ASSOC],
	 `MEM (rule l rhs) (rules g')` by METIS_TAC [not_mem_delete,rule_11,
						     delete_mem_list,MEM,
						     MEM_APPEND] THEN
	 METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,
		    derives_same_append_right]
   ],


  `MEM (rule lhs rhs) (rules g')` by METIS_TAC [not_mem_delete,rule_11,
						delete_mem_list,MEM,MEM_APPEND] THEN
   METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right],

  `MEM (rule lhs rhs) (rules g')` by METIS_TAC [not_mem_delete,rule_11,
					   delete_mem_list,MEM,MEM_APPEND] THEN
  METIS_TAC [res1, RTC_SUBSET,derives_same_append_left,derives_same_append_right]
  ]);


val cnf_r1NT = prove(
``∀g g' nt t.trans2NT nt nt1 nt2 g g' ⇒ derives g u v ⇒ RTC (derives g') u v``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def,trans2NT] THEN
(Cases_on `lhs=l` THENL[
Cases_on `rhs=p ++ [nt1; nt2] ++ s`  
THENL[
`MEM (rule l (p ++ [NTS nt] ++ s)) (rules g')` by METIS_TAC [MEM,MEM_APPEND,APPEND] THEN
`MEM (rule nt [nt1; nt2]) (rules g')` by METIS_TAC [MEM,MEM_APPEND,APPEND] THEN
`derives g' (p++[NTS nt]++s) (p++[nt1;nt2]++s)` by METIS_TAC [res1,derives_same_append_right,derives_same_append_left] THEN
`derives g' [NTS l] (p ++ [NTS nt] ++ s)` by METIS_TAC [res1] THEN
METIS_TAC [rtc_derives_same_append_left,rtc_derives_same_append_right,APPEND_ASSOC,res2],

Cases_on `rhs=(p ++ [NTS nt] ++ s)` THENL[
SRW_TAC [] [] THEN
`MEM (rule l (p ++ [NTS nt] ++ s)) (rules g')` by METIS_TAC [MEM,MEM_APPEND,APPEND] THEN
METIS_TAC [res1,RTC_SUBSET,derives_same_append_left,derives_same_append_right,APPEND_ASSOC],

SRW_TAC [] [] THEN
`MEM (rule l rhs) (rules g')` by METIS_TAC [not_mem_delete,rule_11,
					    delete_mem_list,MEM,MEM_APPEND] THEN
METIS_TAC [res1,RTC_SUBSET,derives_same_append_left,derives_same_append_right,APPEND_ASSOC]
]],

`MEM (rule lhs rhs) (rules g')` by METIS_TAC [not_mem_delete,rule_11,
					    delete_mem_list,MEM,MEM_APPEND] THEN
METIS_TAC [res1,RTC_SUBSET,derives_same_append_left,derives_same_append_right,APPEND_ASSOC]]));


(* Replace the new non-terminal nt in sentential form sf by terminal t *)
val elim = Define 
`elim sf (rule nt [t]) = MAP (\e.if (e=(NTS nt)) then t else e) sf`

val elimNT = Define 
`(elimNT [] (rule nt [nt1;nt2]) = [])
∧ (elimNT (s::sf) (rule nt [nt1;nt2]) = 
    if (s=(NTS nt)) then 
	([nt1;nt2]++(elimNT sf (rule nt [nt1;nt2]))) 
    else (s::elimNT sf (rule nt [nt1;nt2])))`

(* Does sentential form sf from new grammar g' has any new nonterminals, i.e. ones not in g *)
val noNewNts = Define 
`noNewNts g sf = ∀e.MEM e sf ⇒ isNonTmnlSym e ⇒ e IN (nonTerminals g)`


val slemma1_1 = prove(
``∀g g' nt t.trans1Tmnl nt t g g' ⇒ MEM (rule nt rhs) (rules g') ⇒ (rhs=[t])``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [trans1Tmnl] THEN
`~∃r.MEM (rule nt r) (rules g) ∧ ~∃l p s.MEM (rule l (p++[NTS nt]++s)) (rules g) ∧ 
~(nt=startSym g)` by METIS_TAC [slemma1_3] THEN
Cases_on `rhs=[t]` THEN
Cases_on `nt=l` THENL[
METIS_TAC [],
METIS_TAC [],
METIS_TAC [slemma1_4],
METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND],
METIS_TAC [],
METIS_TAC [],
METIS_TAC [slemma1_4],
METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND]
])

val slemma1_1NT = prove(
``∀g g' nt t.trans2NT nt nt1 nt2 g g' ⇒ MEM (rule nt rhs) (rules g') ⇒ (rhs=[nt1;nt2])``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [trans2NT] THEN
`~∃r.MEM (rule nt r) (rules g) ∧ 
~∃l p s.MEM (rule l (p++[NTS nt]++s)) (rules g) ∧ ~(nt=startSym g)` by METIS_TAC [slemma1_3] THEN
Cases_on `rhs=[nt1;nt2]` THEN
Cases_on `nt=l`  THEN
METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND]);


val slemma4_0 = prove(
``∀u v nt t.elim (u++v) (rule nt [t]) = elim u (rule nt [t]) ++ elim v (rule nt [t])``,
SRW_TAC [] [elim]
)

val slemma4_0NT = prove(
``∀u v nt t.elimNT (u++v) (rule nt [nt1;nt2]) = elimNT u (rule nt [nt1;nt2]) ++ elimNT v (rule nt [nt1;nt2])``,
Induct_on `u` THEN
SRW_TAC [] [elimNT]
)

val slemma4_2_0 = prove (
``(lhs=nt)=(NTS lhs=NTS nt)``,
SRW_TAC [] []
)

val slemma4_2_1 = prove(
``~(h=(NTS nt)) ⇒ ([h] = elim [h] (rule nt [t]))``,
SRW_TAC [] [elim]
)

val slemma4_2_1NT = prove(
``~(h=(NTS nt)) ⇒ ([h] = elimNT [h] (rule nt [nt1;nt2]))``,
SRW_TAC [] [elimNT]
)

val slemma4_1 = prove(
``∀l r v.~MEM (NTS l) v ⇒ (v=elim v (rule l [r]))``,
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
``∀l r1 r2 v.~MEM (NTS l) v ⇒ (v=elimNT v (rule l [r1;r2]))``,
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
``(lhs=nt) ⇒ ([t] = elim [NTS lhs] (rule nt [t]))``,
SRW_TAC [] [elim]
)

val slemma4_3_1NT = prove(
``(lhs=nt) ⇒ ([nt1;nt2] = elimNT [NTS lhs] (rule nt [nt1;nt2]))``,
SRW_TAC [] [elimNT]
)


val slemma4_4 = prove 
(``∀g g' nt t.trans1Tmnl nt t g g' ⇒ MEM (rule l r) (rules g) ⇒ ~MEM (NTS nt) r``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [trans1Tmnl] THEN
Cases_on `MEM (NTS nt) r` THEN
METIS_TAC [slemma1_4,rgr_r9eq]
)

val slemma4_4NT = prove 
(``∀g g' nt t.trans2NT nt nt1 nt2 g g' ⇒ MEM (rule l r) (rules g) ⇒ ~MEM (NTS nt) r``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [trans2NT] THEN
Cases_on `MEM (NTS nt) r` THEN
METIS_TAC [slemma1_4,rgr_r9eq]
)


val lemma1 = prove(
``∀g g' nt t.trans1Tmnl nt t g g' ⇒ derives g' u v ⇒ 
		   ((elim u (rule nt [t])=elim v (rule nt [t])) ∨ 
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
`MEM (rule l rhs) (rules g)` by METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
Cases_on `MEM (NTS nt) rhs` THENL[
	METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
	METIS_TAC [slemma4_1]
] THEN
`MEM (rule lhs (p++[NTS nt]++s)) (rules g)` by METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
METIS_TAC [slemma1_4],

`MEM (rule lhs (p++[NTS nt]++s)) (rules g)` by METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
METIS_TAC [slemma1_4],

`MEM (rule lhs rhs) (rules g)` by METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
METIS_TAC [slemma4_4,slemma4_0,slemma4_1,trans1Tmnl]
]]]))


val lemma1NT = prove(
``∀g g' nt nt1 nt2.trans2NT nt nt1 nt2 g g' ⇒ derives g' u v ⇒ ((elimNT u (rule nt [nt1;nt2])=elimNT v (rule nt [nt1;nt2])) ∨ (derives g (elimNT u (rule nt [nt1;nt2])) (elimNT v (rule nt [nt1;nt2]))))``,
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
`MEM (rule l rhs) (rules g)` by METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
Cases_on `MEM (NTS nt) rhs` THENL[
	METIS_TAC [slemma1_4,APPEND_ASSOC,rgr_r9eq],
	METIS_TAC [slemma4_1NT]
] THEN
`MEM (rule lhs (p++[NTS nt]++s)) (rules g)` by METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
METIS_TAC [slemma1_4],

`MEM (rule lhs (p++[NTS nt]++s)) (rules g)` by METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
METIS_TAC [slemma1_4],

`MEM (rule lhs rhs) (rules g)` by METIS_TAC [slemma1_4,not_mem_delete,rule_11,delete_mem_list,MEM,MEM_APPEND] THEN
METIS_TAC [slemma4_4NT,slemma4_0NT,slemma4_1NT,trans2NT]
]]]))


val lemma3 = prove (
``∀u v.RTC (derives g') u v ⇒ trans1Tmnl nt t g g' ⇒ RTC (derives g) (elim u (rule nt [t])) (elim v (rule nt [t]))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
`((elim v (rule nt [t])=elim v' (rule nt [t])) ∨ (derives g (elim v (rule nt [t])) (elim v' (rule nt [t]))))` by METIS_TAC [lemma1] THEN
METIS_TAC [lemma1,RTC_SUBSET,RTC_RTC]
)

val lemma3NT = prove (
``∀u v.RTC (derives g') u v ⇒ trans2NT nt nt1 nt2 g g' ⇒ RTC (derives g) (elimNT u (rule nt [nt1;nt2])) (elimNT v (rule nt [nt1;nt2]))``,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
`((elimNT v (rule nt [nt1;nt2])=elimNT v' (rule nt [nt1;nt2])) ∨ (derives g (elimNT v (rule nt [nt1;nt2])) (elimNT v' (rule nt [nt1;nt2]))))` by METIS_TAC [lemma1NT] THEN
METIS_TAC [lemma1NT,RTC_SUBSET,RTC_RTC]
)


val slemma4_7 = prove(
``∀u nt t.EVERY isTmnlSym u ⇒ (u=elim u (rule nt [t]))``,
Induct_on `u` THENL [
SRW_TAC [] [elim],
SRW_TAC [] [] THEN
`EVERY isTmnlSym [h]` by METIS_TAC [EVERY_MEM,EVERY_DEF] THEN
`EVERY isTmnlSym [h] ⇒ ([h] = elim [h] (rule nt [t]))` by (SRW_TAC [] [elim,EVERY_MEM] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,isTmnlSym_def]) 
THEN METIS_TAC [slemma4_0,APPEND]]
)


val slemma4_7NT = prove(
``∀u nt t.EVERY isTmnlSym u ⇒ (u=elimNT u (rule nt [nt1;nt2]))``,
Induct_on `u` THENL [
SRW_TAC [] [elimNT],
SRW_TAC [] [] THEN
`EVERY isTmnlSym [h]` by METIS_TAC [EVERY_MEM,EVERY_DEF] THEN
`EVERY isTmnlSym [h] ⇒ ([h] = elimNT [h] (rule nt [nt1;nt2]))` by (SRW_TAC [] [elimNT,EVERY_MEM] THEN FULL_SIMP_TAC (srw_ss()) [EVERY_MEM,isTmnlSym_def]) 
THEN METIS_TAC [slemma4_0NT,APPEND]]
)


val slemma4_2 = prove(
``∀u g g' nt t.trans1Tmnl nt t g g' ⇒ u IN nonTerminals g ⇒ ([u]=elim [u] (rule nt [t]))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [elim,trans1Tmnl] THEN
Cases_on `u = (NTS nt)` THEN
METIS_TAC []
)

val slemma4_2NT = prove(
``∀u g g' nt t.trans2NT nt nt1 nt2 g g' ⇒ u IN nonTerminals g ⇒ ([u]=elimNT [u] (rule nt [nt1;nt2]))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [elimNT,trans2NT] THEN
Cases_on `u = (NTS nt)` THEN
METIS_TAC []
)


val slemma4_3 = prove(
``∀g. (NTS (startSym g)) IN nonTerminals g``,
Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [nonTerminals_def,startSym_def]
)

val lemma4 = prove(
``trans1Tmnl nt t g g' ⇒ (language g') SUBSET (language g) ``,
SRW_TAC [] [language_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [lemma3,slemma4_7,slemma4_2,slemma4_3,trans1Tmnl]
)

val lemma4NT = prove(
``trans2NT nt nt1 nt2 g g' ⇒ (language g') SUBSET (language g) ``,
SRW_TAC [] [language_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [lemma3NT,slemma4_7NT,slemma4_2NT,slemma4_3,trans2NT]
)

val slemma5_1 = prove( 
``∀u v.RTC (derives g) u v ⇒ (u=[NTS (startSym g)]) ⇒ trans1Tmnl nt t g g' ⇒ RTC (derives g') u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [cnf_r1,RTC_RTC]
)

val slemma5_1NT = prove( 
``∀u v.RTC (derives g) u v ⇒ (u=[NTS (startSym g)]) ⇒ trans2NT nt nt1 nt2 g g' ⇒ RTC (derives g') u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [cnf_r1NT,RTC_RTC]
)


val lemma5 = prove(
``trans1Tmnl nt t g g' ⇒ (language g) SUBSET (language g')``,
SRW_TAC [] [language_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [slemma5_1,trans1Tmnl]
)

val lemma5NT = prove(
``trans2NT nt nt1 nt2 g g' ⇒ (language g) SUBSET (language g')``,
SRW_TAC [] [language_def,EXTENSION,SUBSET_DEF] THEN
METIS_TAC [slemma5_1NT,trans2NT]
)

val cnf_lemma1 = store_thm("cnf_lemma1",
``∀g g' nt t.trans1Tmnl nt t g g'  ⇒ (language g = language g')``,
METIS_TAC [lemma4,lemma5,SET_EQ_SUBSET]
)

val cnf_lemma1NT = prove(
``∀g g' nt t.trans2NT nt nt1 nt2 g g'  ⇒ (language g = language g')``,
METIS_TAC [lemma4NT,lemma5NT,SET_EQ_SUBSET]
)

val eqLang = Define `eqLang g g' = (language g = language g')`

val trans1TmnlRtc_noeProds = 
store_thm("trans1TmnlRtc_noeProds",
``∀g g'.RTC (\x y.∃nt t.trans1Tmnl nt t x y) g g' ⇒  noeProds (rules g) ⇒
	  noeProds (rules g')``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
METIS_TAC [trans1Tmnl_noeProds]);

val trans2NTRtc_noeProds = store_thm
("trans2NTRtc_noeProds",
``∀g g'.RTC (\x y.∃nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ⇒ noeProds (rules g)
⇒ noeProds (rules g')``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
METIS_TAC [trans2NT_noeProds]);


val trans1TmnlRtc_noUnitProds = 
store_thm("trans1TmnlRtc_noUnitProds",
``∀g g'.RTC (\x y.∃nt t.trans1Tmnl nt t x y) g g' ⇒  noUnitProds (rules g) ⇒
	  noUnitProds (rules g')``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
METIS_TAC [trans1Tmnl_noUnitProds]);

val trans2NTRtc_noUnitProds = store_thm
("trans2NTRtc_noUnitProds",
``∀g g'.RTC (\x y.∃nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ⇒ noUnitProds (rules g)
⇒ noUnitProds (rules g')``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
METIS_TAC [trans2NT_noUnitProds]);


(* TERMINATION *)
val cnf_lemma2 = store_thm("cnf_lemma2",
``∀g g'.RTC (\x y.∃nt t.trans1Tmnl nt t x y) g g' ⇒  
			   (language g = language g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [eqLang] THEN
METIS_TAC [cnf_lemma1]
)

val cnf_lemma2NT = store_thm("cnf_lemma2NT",
``∀g g'.RTC (\x y.∃nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ⇒  
			     (language g = language g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [] [eqLang] THEN
METIS_TAC [cnf_lemma1NT]
)

val cnf_lemma = store_thm("cnf_lemma",
``∀g g' g''.RTC (\x y.∃nt t.trans1Tmnl nt t x y) g g' ⇒  
RTC (\x y.∃nt nt1 nt2.trans2NT nt nt1 nt2 x y) g' g'' ⇒  (language g = language g'')``,
METIS_TAC [cnf_lemma2,cnf_lemma2NT,language_def,eqLang]
);

(*
val lemma10_a = prove (
``∀g g'.trans1Tmnl nt t g g' ⇒ FINITE (rules g) ⇒ FINITE (rules g')``,
SRW_TAC [] [trans1Tmnl] THEN SRW_TAC [] [FINITE_UNION,FINITE_DIFF]
)

val lemma10_b = prove (
``∀g g'.trans2NT nt nt1 nt2 g g' ⇒ FINITE (rules g) ⇒ FINITE (rules g')``,
SRW_TAC [] [trans2NT] THEN SRW_TAC [] [FINITE_UNION,FINITE_DIFF]
)


val lemma10_artc = prove (
``∀g g'.RTC (\x y.∃nt t.trans1Tmnl nt t x y) g g' ⇒ FINITE (rules g) ⇒ FINITE (rules g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [lemma10_a]
)

val lemma10_brtc = prove (
``∀g g'.RTC (\x y.∃nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ⇒ FINITE (rules g) ⇒ FINITE (rules g')``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN
SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [lemma10_b]
)
*)

val lemma16_b = prove(
``∀g.(badTmnlsCount g = 0) ⇒ (∀r.MEM r (rules g) ⇒ (ruleTmnls r = 0))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlsCount] THEN
Cases_on `ruleTmnls r = 0` THENL[
SRW_TAC [] [],
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [SUM_APPEND]
])

val lemma16_bNT = prove(
``∀g.(badNtmsCount g = 0) ⇒ (∀r.MEM r (rules g) ⇒ (ruleNonTmnls r = 0))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badNtmsCount] THEN
Cases_on `ruleNonTmnls r = 0` THENL[
SRW_TAC [] [],
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [SUM_APPEND]])

val sumMapDel = store_thm
("sumMapDel",
``∀l e.(SUM (MAP f l) = 0) ⇒ (SUM (MAP f (delete e l)) = 0)``,

Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [delete_def] THEN
SRW_TAC [][]);


val lemma16_a = prove 
(``∀g.(badTmnlsCount g = 0) ⇒ 
(∀r.MEM r (rules g) ⇒ (SUM (MAP ruleTmnls (delete r (rules g))) = 0))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlsCount] THEN
`ruleTmnls r = 0` by METIS_TAC [lemma16_b,badTmnlsCount] THEN
METIS_TAC [sumMapDel])


val lemma16_aNT = prove 
(``∀g.(badNtmsCount g = 0) ⇒ 
(∀r.MEM r (rules g) ⇒ (SUM (MAP ruleNonTmnls (delete r (rules g))) = 0))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badNtmsCount] THEN
`ruleNonTmnls r = 0` by METIS_TAC [lemma16_bNT,badNtmsCount] THEN
METIS_TAC [sumMapDel])


val slemma12_a_2a = prove(
``∀e.(ruleTmnls e > 0) ⇒ 
∃l p s t. ((e=rule l (p ++ [TS t] ++ s)) ∧ (p≠[] ∨ s≠[]))``,
SRW_TAC [] [] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [ruleTmnlsAlt] THEN
Cases_on `LENGTH l <= 1` THEN1
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH l > 1` by DECIDE_TAC THEN
`LENGTH (FILTER isTmnlSym l) > 0` by METIS_TAC [ruleTmnlsAlt] THEN
`∃e.MEM e l ∧ isTmnlSym e` by FULL_SIMP_TAC list_ss [filter_l1] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH r1 >= 1 ∨ LENGTH r2 >= 1` by DECIDE_TAC THENL[
`~(LENGTH r1 = 0)` by DECIDE_TAC THEN `~(r1 = [])` by FULL_SIMP_TAC list_ss [LENGTH_NIL,NULL_DEF] THEN METIS_TAC [isTmnlSym_def,list_l1],
`~(LENGTH r2 = 0)` by DECIDE_TAC THEN `~(r2 = [])` by FULL_SIMP_TAC list_ss [LENGTH_NIL,NULL_DEF] THEN METIS_TAC [isTmnlSym_def,list_l1]
])

(* because it will give 1 in case there's one nontmnls and others r all tmnls∀ *)
val slemma12_a_2aNT = prove(
``∀e.(ruleNonTmnls e > 0) ⇒ ∃l r p s t1. ((e=rule l r) ∧ (r=(p ++ [NTS t1] ++ s)) ∧ (LENGTH r >= 3))``,
SRW_TAC [] [] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [ruleNonTmnlsAlt] THEN
Cases_on `LENGTH l <= 2` THENL[
FULL_SIMP_TAC (srw_ss()) [],
` LENGTH (FILTER isNonTmnlSym l) > 0` by FULL_SIMP_TAC (srw_ss()) [] THEN
`∃e.MEM e l ∧ isNonTmnlSym e` by FULL_SIMP_TAC list_ss [filter_l1] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
`∃e'.(e=NTS e')` by METIS_TAC [isNonTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH r1 + 1 + LENGTH r2 >= 3)` by DECIDE_TAC THEN METIS_TAC []])


val slemma12_a_2b = prove(
``∀e. (∃l p s t. ((e=rule l (p ++ [TS t] ++ s)) ∧ (p≠[] ∨ s≠[]))) ⇒ 
			  (ruleTmnls e > 0) ``,
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
``∀e. (∃l r p s t1. ((e=rule l r) ∧ (r=(p ++ [NTS t1] ++ s)) ∧ (LENGTH r >=3))) ⇒ (ruleNonTmnls e > 0) ``,
SRW_TAC [] [] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THENL[
DECIDE_TAC,
SRW_TAC [] [LENGTH_APPEND,FILTER_APPEND_DISTRIB] THENL[
DECIDE_TAC,
METIS_TAC [isNonTmnlSym_def]]]
)

val slemma12_a_2 = prove (
``∀e.(ruleTmnls e > 0) = ∃l p s t. ((e=rule l (p ++ [TS t] ++ s)) ∧ 
				    (p≠[] ∨ s≠[]))``,
METIS_TAC [slemma12_a_2a,slemma12_a_2b]
)

val slemma12_a_2NT = prove (
``∀e.(ruleNonTmnls e > 0) = 
∃l r p s t1. ((e=rule l r) ∧ (r = (p ++ [NTS t1] ++ s)) ∧ (LENGTH r >= 3))``,
METIS_TAC [slemma12_a_2aNT,slemma12_a_2bNT]
)

val slemma12_a_1 = prove(
``∀e.(ruleTmnls e = 0) = ~(∃l p s t.((e=rule l (p++[TS t]++s)) ∧ 
				     (p≠[] ∨ s≠[])))``,
SRW_TAC [] [] THEN
`(ruleTmnls e = 0) = ~(ruleTmnls e > 0)` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [slemma12_a_2]
)

val slemma12_a_1NT = prove(
``∀e.(ruleNonTmnls e = 0) = ~(∃l r p s t1.((e=rule l r) ∧ 
(r=(p++[NTS t1]++s))) ∧ (LENGTH r >= 3))``,
SRW_TAC [] [] THEN
`(ruleNonTmnls e = 0) = ~(ruleNonTmnls e > 0)` by DECIDE_TAC THEN
FULL_SIMP_TAC (srw_ss()) [slemma12_a_2NT]
)

val slemma12_a_1NT2 = prove(
``∀e.(ruleNonTmnls e = 0)
         ⇒ 
       ~(∃p s t1 t2.(e = rule l (p++[NTS t1;NTS t2]++s)) ∧ 
                     (p≠[] ∨ s≠[]))``,
SRW_TAC [] [] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [ruleNonTmnlsAlt] THEN
Cases_on `LENGTH l' <= 2` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
`(LENGTH l' <= 1) ∨ (LENGTH l' = 2)` by DECIDE_TAC THENL[
`(LENGTH l' = 0) ∨ (LENGTH l' = 1)` by DECIDE_TAC THENL[
SRW_TAC [] [] THEN `l'=[]` by METIS_TAC [LENGTH_NIL] THEN FULL_SIMP_TAC (srw_ss()) [],
`∃e.l'=[e]` by METIS_TAC [list_lem1] THEN SRW_TAC [] [] THEN METIS_TAC [sl_l4]],

`∃e1 e2.l'=[e1;e2]` by METIS_TAC [list_lem2] THEN
SRW_TAC [] [] THEN
Cases_on `([e1; e2] = p ++ [NTS t1; NTS t2] ++ s)` THEN
METIS_TAC [sl_l5,NULL_EQ_NIL]],

`LENGTH l' >= 3` by DECIDE_TAC THEN
`∃e1 e2 e3 r.(l'=[e1;e2;e3]++r)` by METIS_TAC [list_lem3] THEN
`LENGTH (FILTER isNonTmnlSym l') = 0` by METIS_TAC [] THEN
`(FILTER isNonTmnlSym l') = []` by METIS_TAC [LENGTH_NIL] THEN
`~(∃m.MEM m l' ∧ isNonTmnlSym m)` by METIS_TAC [filter_l2] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
`(EVERY isTmnlSym l')` by METIS_TAC [sym_r6,rgr_r9eq] THEN
Cases_on `l'=p ++ [NTS t1; NTS t2] ++ s` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [isTmnlSym_def,isNonTmnlSym_def,sym_r1b]]
)

val lemma12_a = prove 
(``(badTmnlsCount g = 0) ⇒ ~∃g' nt t.trans1Tmnl nt t g g'``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlsCount,trans1Tmnl] THEN
`∀r. MEM r (rules g) ⇒ (ruleTmnls r = 0)` by METIS_TAC [lemma16_b,badTmnlsCount] THEN
METIS_TAC [slemma12_a_1,isTmnlSym_def]
)


val slemma8_a_2 = prove (
``∀s.FINITE s ⇒ ∀p.(SIGMA f s > 0) ⇒ (∃e.e IN s ∧ f e > 0)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [SUM_IMAGE_THM] THEN
`(f e >= 1) ∨ (SIGMA f (s DELETE e) >= 1)` by DECIDE_TAC THENL[
`f e > 0` by DECIDE_TAC THEN METIS_TAC [],
`SIGMA f (s DELETE e) > 0` by DECIDE_TAC THEN METIS_TAC [DELETE_NON_ELEMENT]]
)

val lemma12_b = prove (
``∀g.((badNtmsCount g = 0) ⇒ ~∃g' nt nt1 nt2.trans2NT nt nt1 nt2 g g')``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [badNtmsCount,trans2NT] THEN
`∀r. MEM r (rules g) ⇒ (ruleNonTmnls r = 0)` by METIS_TAC [lemma16_bNT,badNtmsCount] THEN
METIS_TAC [slemma12_a_1NT2,isNonTmnlSym_def,NOT_EXISTS_THM,NOT_FORALL_THM,CONS,APPEND_ASSOC,APPEND])

val lemma13_a = prove (``∀l l' p s nt t.ruleTmnls (rule l (p++[NTS nt]++s)) <= ruleTmnls (rule l' (p++[TS t]++s))``,
SRW_TAC [] [] THEN
Induct_on `p` THEN
SRW_TAC [] [] THENL[
SRW_TAC [] [ruleTmnlsAlt] THEN  METIS_TAC [isTmnlSym_def,LESS_EQ_SUC_REFL],
SRW_TAC [] [ruleTmnlsAlt] THEN 
SRW_TAC [] [FILTER_APPEND_DISTRIB,isTmnlSym_def]])


val lemma13_aNT = prove(
``∀l l' p s nt t.ruleNonTmnls (rule l (p++[TS t]++s)) <= ruleNonTmnls (rule l' (p++[NTS nt]++s))``,
SRW_TAC [] [] THEN
Induct_on `p` THEN

SRW_TAC [] [] THENL[
SRW_TAC [] [ruleNonTmnlsAlt] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,LESS_EQ_SUC_REFL],
SRW_TAC [] [ruleNonTmnlsAlt] THEN 
SRW_TAC [] [FILTER_APPEND_DISTRIB,isNonTmnlSym_def]])



val slemma6_a_1 = prove 
(``∀t.isTmnlSym t ⇒ ∀nt.(SUM (MAP ruleTmnls [rule nt [t]]) = 0)``,
SRW_TAC [] [ruleTmnls,SUM]
)

val slemma6_a_1NT = prove 
(``∀nt nt1 nt2.SUM (MAP ruleNonTmnls [rule nt [nt1;nt2]]) = 0``,
SRW_TAC [] [ruleNonTmnls,SUM]
)

val slemma6_a_2 = prove (
``∀p s.p≠[] ∨  s≠[] ⇒ 
(∀l x t nt.ruleTmnls (rule l (p++[TS t]++s)) = ruleTmnls (rule l (p++[NTS nt]++s)) + 1)``,
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



val mapSumDelLeq = store_thm
("mapSumDelLeq",
``∀l.(∀e.MEM e l ⇒ (SUM (MAP f (delete e l)) + f e ≤ SUM (MAP f l)))``,

Induct_on `l` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [delete_def] 
THENL[
      Cases_on `MEM e l` THEN1
      (RES_TAC THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
      `delete e l = l` by METIS_TAC [delete_not_mem1] THEN
      SRW_TAC [][] THEN
      DECIDE_TAC,

      SRW_TAC [][] THEN
      RES_TAC THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []
      ]);
      

      

val lemma6_a = prove 
(``trans1Tmnl nt t g g' ⇒ (badTmnlsCount g' < badTmnlsCount g)``,

FULL_SIMP_TAC arith_ss [badTmnlsCount,trans1Tmnl] THEN
SRW_TAC [] [] THEN1

(ASM_REWRITE_TAC [] THEN
`~(MEM (rule nt [t]) (rules g))` by METIS_TAC [slemma1_4] THEN
`~(MEM (rule l (p++[NTS nt]++s)) (rules g))` by METIS_TAC [slemma1_4] THEN
`~(rule l (p++[t]++s) = rule nt [t])` by METIS_TAC [] THEN
`~(rule l (p++[t]++s) = rule l (p++[NTS nt]++s))` by METIS_TAC [] THEN

 `SUM (MAP ruleTmnls [rule nt [t]]) = 0` by METIS_TAC [slemma6_a_1] THEN
 `ruleTmnls (rule l (p ++ [t] ++ s)) = ruleTmnls (rule l (p ++ [NTS nt] ++ s)) + 1` by METIS_TAC [slemma6_a_2,isTmnlSym_def,isNonTmnlSym_def] THEN
   SRW_TAC [] [SUB_RIGHT_ADD] 
   THENL[
	 `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = 
	 ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
	 ONCE_ASM_REWRITE_TAC [] THEN
	 `ruleTmnls (rule l (p++ [t]++s)) <= SUM (MAP ruleTmnls (rules g))` 
	 by  (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	      SRW_TAC [][SUM_APPEND] THEN
	DECIDE_TAC) THEN
	 FULL_SIMP_TAC (srw_ss()) [SUM_APPEND] THEN
	 `SUM (MAP ruleTmnls (delete (rule l (p ++ [t] ++ s)) (rules g))) +
	 ruleTmnls (rule l (p ++ [t] ++ s)) ≤ SUM (MAP ruleTmnls (rules g))` 
	 by METIS_TAC [mapSumDelLeq] THEN
	 DECIDE_TAC,

	 `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = 
	 ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
	 ONCE_ASM_REWRITE_TAC [] THEN
	 `ruleTmnls (rule l (p++ [t]++s)) <= SUM (MAP ruleTmnls (rules g))` 
	 by  (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	      SRW_TAC [][SUM_APPEND] THEN
	      DECIDE_TAC) THEN
	 FULL_SIMP_TAC (srw_ss()) [SUM_APPEND] THEN
	 `SUM (MAP ruleTmnls (delete (rule l (p ++ [t] ++ s)) (rules g))) +
	 ruleTmnls (rule l (p ++ [t] ++ s)) ≤ SUM (MAP ruleTmnls (rules g))` 
	 by METIS_TAC [mapSumDelLeq] THEN
	 DECIDE_TAC]) THEN

   FULL_SIMP_TAC (srw_ss()) [inter_l1,inter_l2] THEN
   SRW_TAC [] [SUM_IMAGE_THM,SUM_IMAGE_SING,SUM_IMAGE_UNION] THEN
   `SUM (MAP ruleTmnls [rule nt [t]]) = 0` by METIS_TAC [slemma6_a_1] THEN
   FULL_SIMP_TAC (srw_ss()) [] THEN
   `ruleTmnls (rule l (p ++ [t] ++ s)) = ruleTmnls (rule l (p ++ [NTS nt] ++ s)) + 1` 
   by METIS_TAC [slemma6_a_2,isTmnlSym_def,isNonTmnlSym_def] THEN
   `~(l=nt)` by METIS_TAC [slemma1_4] THEN
   `~((rule nt [t]) = (rule l (p++[NTS nt]++s)))` by SRW_TAC [] [] THEN
    FULL_SIMP_TAC (srw_ss()) [inter_l2,SUM_IMAGE_THM] THEN
    `ruleTmnls (rule l (p ++ [NTS nt] ++ s)) = 
    ruleTmnls (rule l (p ++ [t] ++ s)) - 1 ` by DECIDE_TAC THEN
    ONCE_ASM_REWRITE_TAC [] THEN   
    `ruleTmnls (rule l (p++ [t]++s)) <= SUM (MAP ruleTmnls (rules g))` 
    by  (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN 
    SRW_TAC [][SUM_APPEND] THEN
    DECIDE_TAC) THEN
    `SUM (MAP ruleTmnls (delete (rule l (p ++ [t] ++ s)) (rules g))) +
    ruleTmnls (rule l (p ++ [t] ++ s)) ≤ SUM (MAP ruleTmnls (rules g))` 
    by METIS_TAC [mapSumDelLeq] THEN
    FULL_SIMP_TAC (srw_ss()) [SUM_APPEND] THEN
    DECIDE_TAC);



val slemma6_a_2NT = prove(
``∀s p.((p=[]) ∧ (LENGTH s >= 1)) ∨ ((s=[]) ∧ (LENGTH p >= 1)) ⇒  
(ruleNonTmnls (rule l (p++[NTS nt1;NTS nt2]++s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2) ``,
SRW_TAC [] [] THENL[
`(LENGTH s = 1) ∨ (LENGTH s > 1)` by DECIDE_TAC THENL[
`∃e.s=[e]` by METIS_TAC [list_lem1] THEN
SRW_TAC [] [] THENL[
`∃nt3.e=NTS nt3` by METIS_TAC [isNonTmnlSym_def] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN METIS_TAC [isNonTmnlSym_def],
`∃ts.e=TS ts` by METIS_TAC [isTmnlSym_def,sym_r1b] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN METIS_TAC [isNonTmnlSym_def]],
`LENGTH s >= 2` by DECIDE_TAC THEN
`∃e1 e2 r.s=[e1;e2]++r` by METIS_TAC [list_lem4] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN (DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def])],

`(LENGTH p = 1) ∨ (LENGTH p > 1)` by DECIDE_TAC THENL[
`∃e.p=[e]` by METIS_TAC [list_lem1] THEN
SRW_TAC [] [] THENL[
`∃nt3.e=NTS nt3` by METIS_TAC [isNonTmnlSym_def] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN METIS_TAC [isNonTmnlSym_def],
`∃ts.e=TS ts` by METIS_TAC [isTmnlSym_def,sym_r1b] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN METIS_TAC [isNonTmnlSym_def]],
`LENGTH p >= 2` by DECIDE_TAC THEN
`∃e1 e2 r.p=[e1;e2]++r` by METIS_TAC [list_lem4] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN (DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def] ORELSE
(SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def])))]]
)

val slemma6_a_3NT = prove(
``∀s p. (p ≠[] ∧ (LENGTH s >= 1)) ∨ (s≠[] ∧ (LENGTH p >= 1)) ⇒  (ruleNonTmnls (rule l (p++[NTS nt1;NTS nt2]++s)) = LENGTH (FILTER isNonTmnlSym p) + LENGTH (FILTER isNonTmnlSym s) + 2)``,
SRW_TAC [] [] THENL[
`∃h t.p=h::t` by METIS_TAC [listNotNull,NULL_EQ_NIL] THEN
`(LENGTH s = 1) ∨  LENGTH s > 1` by DECIDE_TAC THENL[
`∃e.s=[e]` by METIS_TAC [list_lem1] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN
(DECIDE_TAC ORELSE (SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def]))),

`LENGTH s >= 2` by DECIDE_TAC THEN
`∃e1 e2 r.s=[e1;e2]++r` by METIS_TAC [list_lem4] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN
(DECIDE_TAC ORELSE (SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def])))],

`∃h t.s=h::t` by METIS_TAC [listNotNull,NULL_EQ_NIL] THEN
`(LENGTH p = 1) ∨  LENGTH p > 1` by DECIDE_TAC THENL[
`∃e.p=[e]` by METIS_TAC [list_lem1] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN
(DECIDE_TAC ORELSE (SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def]))),

`LENGTH p >= 2` by DECIDE_TAC THEN
`∃e1 e2 r.p=[e1;e2]++r` by METIS_TAC [list_lem4] THEN
SRW_TAC [] [ruleNonTmnlsAlt] THEN
(DECIDE_TAC ORELSE (SRW_TAC [] [FILTER_APPEND_DISTRIB] THEN SRW_TAC [] [ADD_SUC,SUC_ONE_ADD] THEN 
(DECIDE_TAC ORELSE METIS_TAC [isNonTmnlSym_def])))]])

val lemma6_b = prove(
``∀g g'.trans2NT nt nt1 nt2 g g' ⇒ (badNtmsCount g' < badNtmsCount g)``,

FULL_SIMP_TAC arith_ss [badNtmsCount,trans2NT] THEN
SRW_TAC [] [] THEN
 ASM_REWRITE_TAC [] THEN
 `~MEM (rule nt [nt1;nt2]) (rules g)` by METIS_TAC [slemma1_4] THEN
 `~MEM (rule l (p++[NTS nt]++s)) (rules g)` by METIS_TAC [slemma1_4] THEN
 `~(rule l (p++[nt1;nt2]++s) = rule nt [nt1;nt2])` by METIS_TAC [] THEN
 `~(rule l (p++[nt1;nt2]++s) = rule l (p++[NTS nt]++s))` by METIS_TAC [] THEN
 `SUM (MAP ruleNonTmnls [rule nt [nt1;nt2]]) = 0` 
 by METIS_TAC [slemma6_a_1NT] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [SUM_APPEND] THEN
 `SUM (MAP ruleNonTmnls (delete (rule l (p ++ [nt1; nt2] ++ s)) 
    (rules g))) + 
    ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))
    ≤ SUM (MAP ruleNonTmnls (rules g))` by METIS_TAC [mapSumDelLeq] THEN
 `ruleNonTmnls (rule l (p ++ [NTS nt] ++ s)) <
    ruleNonTmnls (rule l (p ++ [nt1; nt2] ++ s))`
 by (Cases_on `nt1` THEN Cases_on `nt2` THEN
 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
 SRW_TAC [][ruleNonTmnlsAlt]  THEN
 Cases_on `s` THEN Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 SRW_TAC [][FILTER_APPEND, isNonTmnlSym_def] THEN
 DECIDE_TAC) THEN
 DECIDE_TAC);
 

val lemma7_a = prove 
(``∀g g'.trans1Tmnl nt t g g' ⇒ (badTmnlsCount g > 0)``,
SRW_TAC [] [] THEN
`badTmnlsCount g' < badTmnlsCount g` by METIS_TAC [lemma6_a] THEN
FULL_SIMP_TAC arith_ss [LESS_EQ,SUC_NOT])

val lemma7_b = prove (``trans2NT nt nt1 nt2 g g' ⇒ (badNtmsCount g > 0)``,
SRW_TAC [] [] THEN
`badNtmsCount g' < badNtmsCount g` by METIS_TAC [lemma6_b] THEN
FULL_SIMP_TAC arith_ss [LESS_EQ,SUC_NOT])


val lemma15_a = prove(
``∀g g'.(badTmnlsCount g = 0) ⇒ 
(\x y.∃nt nt1 nt2.trans2NT nt nt1 nt2 x y)g g' ⇒ (badTmnlsCount g' = 0)``,

SRW_TAC [] [trans2NT] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlsCount] THEN
FULL_SIMP_TAC (srw_ss()) [SUM_IMAGE_UNION,FINITE_DIFF,f_diff,FINITE_UNION] THEN
`~MEM (rule nt [nt1;nt2]) (rules g)` by METIS_TAC [slemma1_4] THEN
`~MEM (rule l (p++[NTS nt]++s)) (rules g)` by METIS_TAC [slemma1_4] THEN
`~(rule l (p++[nt1;nt2]++s) = rule nt [nt1;nt2])` by METIS_TAC [] THEN
`~(rule l (p++[nt1;nt2]++s) = rule l (p++[NTS nt]++s))` by METIS_TAC [] THEN
ASM_REWRITE_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [SUM_APPEND] THEN
 `SUM (MAP ruleTmnls (delete (rule l (p ++ [nt1; nt2] ++ s)) 
    (rules g))) + 
    ruleTmnls (rule l (p ++ [nt1; nt2] ++ s))
    ≤ SUM (MAP ruleTmnls (rules g))` by METIS_TAC [mapSumDelLeq] THEN
(Cases_on `nt1` THEN Cases_on `nt2` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [sumMapDel] THEN
SRW_TAC [][ruleTmnlsAlt] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [SUM_APPEND, ruleTmnlsAlt] THEN
Cases_on `p` THEN 
FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND, isTmnlSym_def]));


val lemma14_b = store_thm("lemma14_b", 
``∀g g'.RTC (\x y. ∃nt nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ⇒
(badTmnlsCount g = 0) ⇒ (badTmnlsCount g' = 0)``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [lemma15_a]);

val finiteNts = prove(
``∀s.FINITE s ⇒ ∀g.(s=LIST_TO_SET (rules g)) ⇒ FINITE (nonTerminals g)``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
Cases_on `g`  THEN
SRW_TAC [] [nonTerminals_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN METIS_TAC [MEM],

Cases_on `g`  THEN
SRW_TAC [] [nonTerminals_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN
Cases_on `x` THEN
`FINITE (LIST_TO_SET l)` by METIS_TAC [finiteLists] THEN
SRW_TAC [] [rule_nonterminals_def] THEN
`{nt | isNonTmnlSym nt ∧ MEM nt l'} = {nt | isNonTmnlSym nt ∧ nt IN (LIST_TO_SET l')}` 
    by SRW_TAC [] [SET_TO_LIST_IN_MEM] THEN
ASM_REWRITE_TAC [] THEN
`{nt | isNonTmnlSym nt ∧ nt IN (LIST_TO_SET l')} SUBSET (LIST_TO_SET l')` by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]  THEN
METIS_TAC [SUBSET_FINITE, FINITE_LIST_TO_SET]]
);


val finiteNts2str = prove(
``∀s.FINITE s ⇒ ∀g.(s=(nonTerminals g)) 
           ⇒ 
       FINITE (IMAGE nts2str (nonTerminals g))``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN
SRW_TAC [] [] THENL[
METIS_TAC [FINITE_EMPTY,IMAGE_FINITE],
`FINITE (nonTerminals g)` by METIS_TAC [FINITE_INSERT] THEN
 METIS_TAC [IMAGE_FINITE]]);

val existsNewNt = prove (
``∀x.~(x IN (IMAGE nts2str (nonTerminals g))) 
             ⇒ 
         ~(NTS x IN nonTerminals g)``,
SRW_TAC [] [] THEN
`~(x = nts2str x') ∨ ~(x' IN nonTerminals g)` by METIS_TAC [] THEN
METIS_TAC [nts2str_def]);


val sumMapGt0 = store_thm
("sumMapGt0",
``∀l.SUM (MAP f l) > 0 ⇒ ∃e.MEM e l ∧ f e > 0``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `SUM (MAP f l) > 0` THEN1
METIS_TAC [] THEN
`SUM (MAP f l) = 0` by DECIDE_TAC THEN
SRW_TAC [][] THEN
`f h > 0` by DECIDE_TAC THEN
METIS_TAC []);

val lemma8_a = prove(
``INFINITE (UNIV : 'a set) ⇒ (badTmnlsCount g > 0) 
        ⇒ 
     ∃g' (nt:'a) t.trans1Tmnl nt t g g' ``,

SRW_TAC [] [badTmnlsCount] THEN
`∃e.MEM e (rules g) ∧ ruleTmnls e > 0` by METIS_TAC [sumMapGt0] THEN
`∃l p s t. (e=rule l (p ++ [TS t] ++ s)) ∧ (p ≠ [] ∨ s ≠ [])` 
 by METIS_TAC [slemma12_a_2] THEN
(FULL_SIMP_TAC (srw_ss()) [trans1Tmnl] THEN
 `FINITE (nonTerminals g)` by METIS_TAC [finiteNts, FINITE_LIST_TO_SET] THEN
`FINITE (IMAGE nts2str (nonTerminals g))` by METIS_TAC [finiteNts2str] THEN
`∃nt.nt IN UNIV ∧ ~(nt IN (IMAGE nts2str (nonTerminals g)))` 
    by METIS_TAC [IN_INFINITE_NOT_FINITE] THEN
`~(NTS nt IN nonTerminals g)` by METIS_TAC [existsNewNt] THEN
METIS_TAC [isTmnlSym_def,startSym_def,rules_def]));


val noTmnls = prove(
``∀l r.(ruleTmnls (rule l r) = 0) = ((LENGTH r <= 1) ∨ (EVERY isNonTmnlSym r))``,
SRW_TAC [] [ruleTmnlsAlt] THEN
SRW_TAC [] [EQ_IMP_THM] THENL[
`(FILTER isTmnlSym r) = []` by METIS_TAC [LENGTH_NIL] THEN
`~(∃e.MEM e r ∧ isTmnlSym e)` by METIS_TAC [filter_l2] THEN METIS_TAC [sym_r7b,rgr_r9eq],
METIS_TAC [sym_r3b,rgr_r9eq,filter_l2]]);


val lemma8_b = prove (
``INFINITE (UNIV : 'a set) ⇒
   (badTmnlsCount g = 0) 
  ⇒ ((badNtmsCount g > 0) ⇒ 
  ∃g' nt:'a nt1 nt2.trans2NT nt nt1 nt2 g g')``,

SRW_TAC [] [badNtmsCount] THEN
FULL_SIMP_TAC (srw_ss()) [badTmnlsCount] THEN
`∀r.MEM r (rules g) ⇒ (ruleTmnls r = 0)`  by METIS_TAC [lemma16_b,badTmnlsCount] THEN
`∃e.MEM e (rules g) ∧ ruleNonTmnls e > 0` by METIS_TAC [sumMapGt0] THEN
`ruleTmnls e = 0` by METIS_TAC [] THEN
` ~∃l p s t. (e = rule l (p ++ [TS t] ++ s)) ∧ (p ≠ [] ∨ s ≠ [])` 
 by METIS_TAC [slemma12_a_1] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃l r p s t1. (e=rule l (p ++ [NTS t1] ++ s)) ∧ (LENGTH (p ++ [NTS t1] ++ s) ≥ 3)` 
 by METIS_TAC [slemma12_a_2NT] THEN
`(p ≠ [] ∨ s ≠ [])` by METIS_TAC [sl, NULL_EQ_NIL] 
THENL[
` ~(e = rule l (p ++ [TS t] ++ s))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [trans2NT] THEN
`FINITE (nonTerminals g)` by METIS_TAC [finiteNts, FINITE_LIST_TO_SET] THEN
`FINITE (IMAGE nts2str (nonTerminals g))` by METIS_TAC [finiteNts2str] THEN
`∃nt.nt IN UNIV ∧ ~(nt IN (IMAGE nts2str (nonTerminals g)))` by METIS_TAC [IN_INFINITE_NOT_FINITE] THEN
`~(NTS nt IN nonTerminals g)` by METIS_TAC [existsNewNt] THEN
`~(p=[])` by METIS_TAC [NULL_DEF] THEN
`p = FRONT p ++ [LAST p]` by METIS_TAC [APPEND_FRONT_LAST] THEN
`~(LENGTH (p ++ [NTS t1] ++ s) <= 1)` by METIS_TAC [notLen1, NULL_EQ_NIL] THEN
`EVERY isNonTmnlSym (p ++ [NTS t1] ++ s)` by METIS_TAC [noTmnls] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`EVERY isNonTmnlSym (FRONT p) ∧ isNonTmnlSym (LAST p)` by METIS_TAC [EVERY_APPEND,EVERY_DEF] THEN
`∃ntx.LAST p = (NTS ntx)` by METIS_TAC [isNonTmnlSym_def] THEN

MAP_EVERY Q.EXISTS_TAC 
[`G (delete (rule l (FRONT p ++ [NTS ntx; NTS t1] ++ s)) (rules g) ++
[rule nt [NTS ntx; NTS t1]; rule l (FRONT p ++ [NTS nt] ++ s)]) (startSym g)`,
`nt`,`NTS ntx`,`NTS t1`,`l`,`FRONT p`,`s`] THEN
SRW_TAC [] []  THEN1
METIS_TAC [APPEND,CONS,APPEND_ASSOC] 
THENL[

`LENGTH (FRONT p ++ [LAST p]) + 1 + LENGTH s >= 3`  by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (FRONT p) + LENGTH s >= 1` by DECIDE_TAC THEN
Cases_on `s ≠ []` THEN1 METIS_TAC [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (FRONT p) >= 1` by DECIDE_TAC THEN
`1 <= LENGTH (FRONT p)` by DECIDE_TAC THEN
`∃a0 a1.(FRONT p=a0::a1)` by METIS_TAC [l_lemma1] THEN
SRW_TAC [] [] THEN
Cases_on `FRONT p` THEN FULL_SIMP_TAC (srw_ss()) [],

METIS_TAC [isNonTmnlSym_def],

METIS_TAC [rules_def],

METIS_TAC [startSym_def]],

` ~(e = rule l (p ++ [TS t] ++ s))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [trans2NT] THEN
`INFINITE (UNIV : string set)` by SRW_TAC [] [] THEN1 SRW_TAC [] [INFINITE_STR_UNIV] THEN
`FINITE (nonTerminals g)` by METIS_TAC [finiteNts, FINITE_LIST_TO_SET] THEN
`FINITE (IMAGE nts2str (nonTerminals g))` by METIS_TAC [finiteNts2str] THEN
`∃nt.nt IN UNIV ∧ ~(nt IN (IMAGE nts2str (nonTerminals g)))` by METIS_TAC [IN_INFINITE_NOT_FINITE] THEN
`~(NTS nt IN nonTerminals g)` by METIS_TAC [existsNewNt] THEN
`~(s=[])` by METIS_TAC [NULL_DEF] THEN
`∃h' t'.s = h'::t'` by METIS_TAC [listNotNull, NULL_EQ_NIL] THEN
`~(LENGTH (p ++ [NTS t1] ++ s) <= 1)` by METIS_TAC [notLen1, NULL_EQ_NIL] THEN
`EVERY isNonTmnlSym (p ++ [NTS t1] ++ s)` by METIS_TAC [noTmnls] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`isNonTmnlSym h' ∧ EVERY isNonTmnlSym t'` by METIS_TAC [EVERY_APPEND,EVERY_DEF,APPEND,CONS] THEN
`∃ntx.h' = (NTS ntx)` by METIS_TAC [isNonTmnlSym_def] THEN

MAP_EVERY Q.EXISTS_TAC [
`G (delete (rule l (p ++ [NTS t1; NTS ntx] ++ t')) (rules g) ++
[rule nt [NTS t1; NTS ntx]; rule l (p ++ [NTS nt] ++ t')]) (startSym g)`,
`nt`,`NTS t1`,`NTS ntx`,`l`,`p`,`t'`] THEN
SRW_TAC [] [] THENL[
METIS_TAC [APPEND,CONS,APPEND_ASSOC],

FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH p + LENGTH t' >= 1` by DECIDE_TAC THEN
Cases_on `p ≠ []` THEN1 METIS_TAC [] THEN
SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (t') >= 1` by DECIDE_TAC THEN
`1 <= LENGTH (t')` by DECIDE_TAC THEN
`∃a0 a1.(t'=a0::a1)` by METIS_TAC [l_lemma1] THEN
SRW_TAC [] [] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC [rules_def],
METIS_TAC [startSym_def]]]);


val lemma11_a = prove(
``∀g.INFINITE (UNIV:'a set) ⇒
		      ~(∃g' (nt:'a) t.trans1Tmnl nt t g g') 
      ⇒ (badTmnlsCount g = 0)``,
SRW_TAC [] [] THEN
`~(∃g' nt t.trans1Tmnl nt t g g') ⇒ ~(badTmnlsCount g > 0)` by METIS_TAC [MONO_NOT,lemma8_a] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`badTmnlsCount g <= 0` by FULL_SIMP_TAC arith_ss [] THEN
FULL_SIMP_TAC arith_ss [LE])

val lemma11_b = prove(
``∀g.INFINITE (UNIV:'a set) ⇒
(badTmnlsCount g = 0) ⇒ (~(∃g' nt:'a nt1 nt2.trans2NT nt nt1 nt2 g g') ⇒ (badNtmsCount g = 0))``,
SRW_TAC [] [] THEN
`~(∃g' nt nt1 nt2.trans2NT nt nt1 nt2 g g') ⇒ ~(badNtmsCount g > 0)` 
    by METIS_TAC [MONO_NOT,lemma8_b] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
`badNtmsCount g <= 0` by FULL_SIMP_TAC arith_ss [] THEN
FULL_SIMP_TAC arith_ss [LE]
)

val lemma9_a = store_thm("lemma9_a",
``INFINITE (UNIV:'a set) ⇒
   (∃g'.RTC (\x y.∃nt:'a t.trans1Tmnl nt t x y) g g' ∧ 
        (badTmnlsCount g' = 0))``,
completeInduct_on `badTmnlsCount g` THEN
Cases_on `v=0` THENL[
SRW_TAC [][] THEN
METIS_TAC [RTC_RULES],
SRW_TAC [] [] THEN
`∃g' nt t. trans1Tmnl nt t g g'` by  METIS_TAC [MONO_NOT,lemma11_a] THEN
`(badTmnlsCount g' < badTmnlsCount g)` by METIS_TAC [lemma6_a] THEN
`∃g''.RTC (\x y.∃nt t.trans1Tmnl nt t x y) g' g'' ∧ (badTmnlsCount g'' = 0)` by  METIS_TAC [] THEN
Q.EXISTS_TAC `g''` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.ABBREV_TAC `r=(\x y. ∃nt t. trans1Tmnl nt t x y)` THEN
`r g g'` by (SRW_TAC [] [Abbr `r`] THEN METIS_TAC []) THEN
METIS_TAC [RTC_RULES]
])


val lemma9_b = store_thm("lemma9_b",
``INFINITE (UNIV:'a set) ⇒
(badTmnlsCount g = 0) ⇒ 
      (∃g'.RTC (\x y.∃nt:'a nt1 nt2.trans2NT nt nt1 nt2 x y) g g' ∧ 
       (badNtmsCount g' = 0))``,
completeInduct_on `badNtmsCount g` THEN
Cases_on `v=0` THENL[
METIS_TAC [RTC_RULES],
SRW_TAC [] [] THEN
`∃g' nt nt1 nt2. trans2NT nt nt1 nt2 g g'` by  METIS_TAC [MONO_NOT,lemma11_b] THEN
`(badNtmsCount g' < badNtmsCount g)` by METIS_TAC [lemma6_b] THEN
`∃g''.RTC (\x y.∃nt nt1 nt2.trans2NT nt nt1 nt2 x y) g' g'' ∧ 
		     (badTmnlsCount g' = 0) ∧ (badNtmsCount g'' = 0)` 
		     by  METIS_TAC [lemma15_a] THEN
Q.EXISTS_TAC `g''` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.ABBREV_TAC `r=(\x y. ∃nt nt1 nt2. trans2NT nt nt1 nt2 x y)` THEN
`r g g'` by (SRW_TAC [] [Abbr `r`] THEN METIS_TAC []) THEN
METIS_TAC [RTC_RULES]])


val thm4_5 = store_thm
("thm4_5",
 ``∀g:('a, 'b) grammar.
 INFINITE (UNIV:'a set) ⇒
 [] ∉ language g ⇒
 ∃g'. (cnf g') ∧ (language g = language g')``,
SRW_TAC [] [cnf] THEN
METIS_TAC [cnf,lemma14_b,lemma9_a,lemma9_b,cnf_lemma]);

val isCnf_def = Define
`isCnf g = ∀l r.MEM (rule l r) (rules g) ⇒
    ((LENGTH r = 2) ∧ EVERY isNonTmnlSym r) ∨
    ((LENGTH r = 1) ∧ EVERY isTmnlSym r)`;



val cnfisCnfEq = store_thm
("cnfisCnfEq",
``∀g:('a, 'b) grammar.
 INFINITE (UNIV:'a set) ∧
 [] ∉ language g  ⇒ ∃g':(α,β) grammar.isCnf g' ∧ (language g = language g')``,

SRW_TAC [][] THEN
`∃g0:(α,β) grammar. negr g g0` by METIS_TAC [negr_exists] THEN
IMP_RES_TAC thm4_3 THEN
`∃g1:(α,β) grammar. upgr g0 g1` by METIS_TAC [upgr_exists] THEN
`language g = language g1` by METIS_TAC [thm4_4] THEN
`noeProds (rules g0)` by METIS_TAC [negrImpnoeProds] THEN
IMP_RES_TAC upgr_noeProds THEN
`[] ∉ language g0` by FULL_SIMP_TAC (srw_ss()) [] THEN
`language g0 = language g1` by METIS_TAC [thm4_4] THEN
`noUnitProds (rules g1)` by METIS_TAC [upgrImpnoUnitProds] THEN
`∃g'. (λx y. ∃nt t. trans1Tmnl nt t x y)^* g1 g' ∧
 (badTmnlsCount g' = 0)` by METIS_TAC [lemma9_a] THEN
IMP_RES_TAC trans1TmnlRtc_noeProds THEN
IMP_RES_TAC trans1TmnlRtc_noUnitProds THEN
IMP_RES_TAC lemma9_b THEN
IMP_RES_TAC trans2NTRtc_noeProds THEN
IMP_RES_TAC trans2NTRtc_noUnitProds THEN
IMP_RES_TAC lemma14_b THEN
IMP_RES_TAC cnf_lemma THEN
`cnf g''` by METIS_TAC [cnf] THEN
Q.EXISTS_TAC `g''` THEN
FULL_SIMP_TAC (srw_ss()) [isCnf_def] THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `r` THEN1
METIS_TAC [noeProds] THEN

FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, badTmnlsCount, badNtmsCount] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def, SUM_APPEND] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def,
					    ruleNonTmnls, ruleTmnls] THEN
FULL_SIMP_TAC (srw_ss()) [noUnitProds] THEN1
METIS_TAC [] THEN
Cases_on `h'` THEN FULL_SIMP_TAC (srw_ss()) [ruleNonTmnls] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [ruleNonTmnls] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def,
					    ruleNonTmnls, ruleTmnls]); 



val _ = export_theory ();
