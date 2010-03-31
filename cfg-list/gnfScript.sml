open HolKernel boolLib bossLib Parse

open stringTheory relationTheory listTheory
    rich_listTheory

open pred_setTheory symbolDefTheory grammarDefTheory listLemmasTheory
relationLemmasTheory

open containerLemmasTheory cnfTheory eProdsTheory generatingGrammarTheory
    unitProdsTheory aProdsTheory l2rTheory

val _ = new_theory "gnf";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);



val finiteaProdsRules = store_thm
("finiteaProdsRules",
``∀ru. FINITE ru ⇒ FINITE (aProdsRules A l ru)``,

HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN1
(SRW_TAC [][aProdsRules_def] THEN
 `{rule A (x ++ s) | (x,s) | F}= {}` by SRW_TAC [][EXTENSION] THEN
 SRW_TAC [][]) THEN

MAGIC);


val finiteaProdAllRules = store_thm
("finiteaProdAllRules",
``∀ru. FINITE ru ⇒ FINITE (aProdAllRules A l PP ru)``,
MAGIC);

val finitel2rRules = store_thm
("finitel2rRulese",
``FINITE ru ⇒ FINITE (l2rRules A B ru)``,

MAGIC);

val allDLenDel = store_thm
("allDLenDel",
``∀l. ALL_DISTINCT l ∧ h ∈ l ⇒ (SUC (LENGTH (delete h l)) = LENGTH l)``,

Induct_on `l` THEN SRW_TAC [][delete_def] THEN
METIS_TAC [notMem_delete_len]);

val allDistinctNewlist = store_thm
("allDistinctNewlist",
``∀l:α list. 
INFINITE (UNIV:'a set) ⇒
∃l'. LENGTH l' ≥ LENGTH l ∧ ALL_DISTINCT l' ∧ (set l ∩ set l' = {})``,

Induct_on `l` THEN SRW_TAC [][] THEN1
METIS_TAC [ALL_DISTINCT] THEN
`∃l'. LENGTH l' ≥ LENGTH l ∧ ALL_DISTINCT l' ∧
 (set l ∩ set l' = {})` by METIS_TAC [] THEN
`FINITE (set (h::l ++ l'))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
IMP_RES_TAC NOT_IN_FINITE THEN
`FINITE (set (x::h::l++l'))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`∃x'.x' ∉ set (x::h::l ++ l')` by METIS_TAC [NOT_IN_FINITE] THEN
Q.EXISTS_TAC `x'::x::delete h l'` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss())[] THEN1

(IMP_RES_TAC allDLenDel THEN
Cases_on `h ∈ l'`  THEN1
(RES_TAC THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`LENGTH (delete h l') = LENGTH l'` by METIS_TAC [notMem_delete_len] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN

FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [memdel, alld_delete, not_mem_delete]);


val listDivLen = store_thm
("listDivLen",
``∀n l. n < LENGTH l ⇒
∃l1 l2 j.(l = l1 ++ l2) ∧ (LENGTH l1 = n) ∧ (LENGTH l2 = j)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND, APPEND_NIL, LENGTH]);

val elDrop = store_thm
("elDrop",
``∀i l. e ∈ l ∧ i < LENGTH l ∧ (∀j. j ≤ i ⇒ EL j l ≠ e) ⇒
e ∈ DROP (SUC i) l``,

SRW_TAC [][] THEN
IMP_RES_TAC listDivLen THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
(IMP_RES_TAC memImpEl THEN
`i ≤ LENGTH l1` by DECIDE_TAC THEN
METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
	   ⇒ j < l``])  THEN
`SUC (LENGTH l1) ≤ LENGTH (l1 ++ l2)` by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
`SUC (LENGTH l1) = 1 + LENGTH l1`by DECIDE_TAC THEN
`¬(e ∈ DROP 1 (DROP (LENGTH l1) (l1 ++ l2)))` by METIS_TAC [BUTFIRSTN_BUTFIRSTN] THEN
FULL_SIMP_TAC (srw_ss()) [BUTFIRSTN_LENGTH_APPEND] THEN
Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
SRW_TAC [][] THEN
`LENGTH l1 ≤ LENGTH l1` by DECIDE_TAC THEN
METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
	   NOT_CONS_NIL,CONS]);


val takeSubset= store_thm
("takeSubset",
``∀l n. n ≤ LENGTH l ⇒
 set (TAKE n l) ⊆ set l``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
METIS_TAC []);

val allDNotMem = store_thm
("allDNotMem",
``∀l. ¬ALL_DISTINCT l ⇔ (∃e.e ∈ l ∧ ∃l1 l2 l3.(l = l1 ++ [e] ++ l2 ++ [e] ++ l3))``,

Induct_on `l` THEN SRW_TAC [][EQ_IMP_THM] THEN1
METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL, MEM ,MEM_APPEND, rgr_r9eq] THEN1
METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL, MEM ,MEM_APPEND, rgr_r9eq] THEN
Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL, MEM ,MEM_APPEND, rgr_r9eq]);


val TAKE_mem = store_thm
("TAKE_mem",
``∀l n. n ≤ LENGTH l ⇒ (∀e. e ∈ (TAKE n l) ⇒ e ∈ l)``,

Induct_on `l`THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);


val allDTake = store_thm
("allDTake",
``∀l n. n ≤ LENGTH l ∧ ALL_DISTINCT l ⇒
ALL_DISTINCT (TAKE n l)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
SPOSE_NOT_THEN ASSUME_TAC  THEN
METIS_TAC [TAKE_mem]);



val exists_triple = store_thm
("exists_triple",
``∃a b c.(x = (a,b,c))``,

Cases_on `x`  THEN Cases_on `r` THEN SRW_TAC [][]);

val exists_quad = store_thm
("exists_quad",
``∃a b c d.(x = (a,b,c, d))``,

Cases_on `x`  THEN Cases_on `r` THEN
Cases_on `r'` THEN
 SRW_TAC [][]);


val exists_pent = store_thm
("exists_pent",
``∃a b c d e.(x = (a,b,c, d, e))``,

Cases_on `x`  THEN Cases_on `r` THEN
Cases_on `r'` THEN
Cases_on `r` THEN
 SRW_TAC [][]);



val deleteAllD = store_thm
("deleteAllD",
``∀l.ALL_DISTINCT l ⇒ ALL_DISTINCT (delete h l)``,

Induct_on `l` THEN SRW_TAC [][delete_def, ALL_DISTINCT] THEN1
METIS_TAC [] THEN
METIS_TAC [MEM_delete]);

val rmDupesImpAllD = store_thm
("rmDupesImpAllD",
``∀l.ALL_DISTINCT (rmDupes l)``,

Induct_on `l` THEN SRW_TAC [][rmDupes, ALL_DISTINCT] THEN
METIS_TAC [rmd_del, not_mem_delete, deleteAllD]);


val isCnfImpnoeProds = store_thm
("isCnfImpnoeProds",
``isCnf g ⇒ noeProds (rules g)``,

SRW_TAC [][isCnf_def, noeProds_def] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) []);


val memImpEl = store_thm
("memImpEl",
``∀s0. MEM n s0 ⇒ ∃i. i < LENGTH s0 ∧ (EL i s0 = n)``,

Induct_on `s0` THEN SRW_TAC [][] THEN1
(Q.EXISTS_TAC `0` THEN SRW_TAC [][]) THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `SUC i` THEN
SRW_TAC [][]);

val memnonTmnls = store_thm
("memnonTmnls",
``MEM b (nonTmnls l) ⇔
(∃r.MEM (rule b r) l) ∨ (∃nt r.MEM (rule nt r) l ∧ MEM (NTS b) r)``,

Induct_on `l` THEN SRW_TAC [][nonTmnls_def] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [nonTmnls_def] THEN
SRW_TAC [][EQ_IMP_THM] THEN1
METIS_TAC [] THEN1
(FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [MEM_FILTER] THEN
 SRW_TAC [][] THEN
 Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, nts2str_def] THEN
 METIS_TAC []) THEN1
METIS_TAC [] THEN1
METIS_TAC [] THEN1
METIS_TAC [] THEN1
(FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
 SRW_TAC [][FILTER_APPEND, isNonTmnlSym_def, nts2str_def] THEN
 METIS_TAC []) THEN
METIS_TAC []);


val slemma1_4ntms = store_thm
("slemma1_4ntms",
 ``MEM nt (ntms g) =
 (∃rhs.MEM (rule nt rhs) (rules g) ∨
  ∃l p s.MEM (rule l (p++[NTS nt]++s))(rules g) ∨
  (nt=startSym g))``,

 Cases_on `g` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [ntms_def,rules_def,startSym_def, ntList_def,
			  nonTerminalsList_def, nonTmnls_def] THEN
METIS_TAC [MEM, rmd_r2, memnonTmnls, rgr_r9eq]);

val ntmsMem = store_thm
("ntmsMem",
``MEM b (ntms g) ⇔ NTS b ∈ nonTerminals g``,

METIS_TAC [slemma1_4ntms, slemma1_4]);

val listExists4SetMem = store_thm
("listExists4SetMem",
``∀s.FINITE s ⇒ ∃r.∀e.MEM e r ⇔ e ∈ s``,

HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN1
METIS_TAC [MEM,mem_in] THEN
METIS_TAC [MEM, mem_in]);


val listExists4Set = store_thm
("listExists4Set",
``∀s.FINITE s ⇒ ∃r.set r  = s``,

HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN
Q.EXISTS_TAC `e::r`  THEN
SRW_TAC [][]);


(*
Theorem 4.6
Every CFL L without can be generated by a grammar for
which every production is of the form A->aα, where A is a variable,
a is a terminal and alpha (possibly empty) is a string of variables.
*)


val r49Elem = Define
`r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) = 
∃se. (seen0 = se::seen) ∧ (sl = sl0++[se]) ∧
(set ru = aProdsRules ntk [se] (set ru0))`;


val aProdsRulesAllEq = store_thm
("aProdsRulesAllEq",
``(aProdsRules  ntk [se]  (set ru0) =
   aProdAllRules ntk se NULL (set ru0))``,

SRW_TAC [][aProdAllRules_def, aProdsRules_def] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION, NULL_EQ_NIL]);


(***********************************************************************************)
(* NTMS SUBSET *)
(***********************************************************************************)

val r49E_ntmsSubset = store_thm
("r49E_ntmsSubset",
``r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) ⇒
set (ntms (G ru s)) ⊆ set (ntms (G ru0 s))``,

SRW_TAC [][r49Elem, SUBSET_DEF] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [ntmsMem] THEN
IMP_RES_TAC slemma1_4 
THENL[
      `rule x rhs ∈  aProdAllRules ntk se NULL (set ru0)` 
      by METIS_TAC [mem_in, rules_def,aProdsRulesAllEq] THEN
      FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def] THEN SRW_TAC [][] THEN
      METIS_TAC [slemma1_4, startSym_def, rules_def],

      `rule l (p ++ [NTS x] ++ s') ∈ aProdAllRules ntk se NULL (set ru0)`
      by METIS_TAC [mem_in, rules_def, aProdsRulesAllEq] THEN
      FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def] THEN SRW_TAC [][] THEN1
      METIS_TAC [slemma1_4, symbol_11, startSym_def, rules_def] THEN
      Cases_on `p'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `x' ++ s'' = p ++ [NTS x] ++ s'` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL,rules_def,
		 startSym_def] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, rules_def,
		 startSym_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def] THEN
      Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def],

      METIS_TAC [slemma1_4, startSym_def, rules_def, startSym_def]
      ]);

val r49ERtc_ntmsSubset = store_thm
("r49ERtc_ntmsSubset",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀seen0 ru0 sl0. (x=(seen0,ru0,sl0)) ⇒ (y=(seen,ru,sl)) ⇒
set (ntms (G ru s)) ⊆ set (ntms (G ru0 s))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
`set (ntms (G ru1 s)) ⊆ set (ntms (G ru0 s))` by 
 METIS_TAC [r49E_ntmsSubset, startSym_def, rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]);



(***********************************************************************************)
(* NO EPRODS INV *)
(***********************************************************************************)



val r49E_noeProds = store_thm
("r49E_noeProds",
``noeProds ru0 ⇒
r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) ⇒
noeProds ru``,

SRW_TAC [][r49Elem, noeProds_def] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
`rule l [] ∈ aProdAllRules ntk se NULL (set ru0)` 
 by METIS_TAC [mem_in,
	       aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def] THEN
SRW_TAC [][] THEN
METIS_TAC []);

val r49ERtc_noeProds = store_thm
("r49ERtc_noeProds",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀seen0 ru0 sl0. (x=(seen0,ru0,sl0)) ⇒ (y=(seen,ru,sl)) ⇒
noeProds ru0 ⇒
noeProds ru``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
METIS_TAC [r49E_noeProds]);

(***********************************************************************************)
(* SEEN INV *)
(***********************************************************************************)


val seenInv = Define
`seenInv ru s = 
∀i. i < LENGTH s ⇒
   ∀nt rest. (rule (EL i s) (NTS nt :: rest)) ∈ ru ⇒
       ∀j. j ≤ i ⇒ EL j s ≠ nt`;


val elAppendList = store_thm
("elAppendList",
``∀i s1 s2.i < LENGTH s2 ⇒ (EL i s2 = EL (LENGTH s1 + i) (s1++s2))``,

Induct_on `s2` THEN SRW_TAC [][] THEN
Cases_on `i` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [NULL_EQ_NIL, NOT_CONS_NIL, HD, EL_LENGTH_APPEND] THEN
RES_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s1++[h]`] MP_TAC) THEN 
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`n`,`s1++[h]`] MP_TAC) THEN 
SRW_TAC [][] THEN
`s1 ++ [h]++s2 = s1++h::s2`by METIS_TAC [APPEND, APPEND_ASSOC] THEN
`LENGTH s1 + 1 + n  = LENGTH s1 + SUC n` by DECIDE_TAC THEN
METIS_TAC []);

val seenInvAppend = store_thm
("seenInvAppend",
``∀s1 s2.seenInv ru (s1++s2) ⇒ seenInv ru s1 ∧ seenInv ru s2``,

Induct_on `s1` THEN SRW_TAC [][] THEN1

SRW_TAC [][seenInv] THEN
FULL_SIMP_TAC (srw_ss()) [seenInv] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1

(`i < SUC (LENGTH s1 + LENGTH s2)`by DECIDE_TAC THEN
RES_TAC THEN
`LENGTH (h::s1) = SUC (LENGTH s1)`by SRW_TAC [][] THEN
`EL i (h::s1) = EL i (h::(s1 ++ s2))` by METIS_TAC [EL_APPEND1, APPEND, 
						    APPEND_ASSOC] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`rest`, `EL j (h::s1)`] MP_TAC) THEN SRW_TAC [][] THEN1
METIS_TAC [] THEN
`j < SUC (LENGTH s1)` by DECIDE_TAC THEN
 METIS_TAC [EL_APPEND1, APPEND, APPEND_ASSOC]) THEN

`LENGTH (h::s1) + i < SUC (LENGTH s1 + LENGTH s2)` 
 by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
RES_TAC THEN
`EL i s2 = EL (LENGTH (h::s1) + i) (h::(s1++s2))` 
 by METIS_TAC [elAppendList, APPEND,APPEND_ASSOC] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`rest`,`EL j s2`] MP_TAC) THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`j < SUC (LENGTH s1) + i` by DECIDE_TAC THEN
Q.EXISTS_TAC `LENGTH (h::s1) + j` THEN
SRW_TAC [][] THEN
`j < LENGTH s2` by DECIDE_TAC THEN
`EL j s2 = EL (LENGTH (h::s1) + j) (h::(s1++s2))` by
METIS_TAC [elAppendList, APPEND,APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) []);


val r49E_seenInv = store_thm
("r49E_seenInv",
``seenInv ru0 (sl0 ++ seen0) ⇒
noeProds ru0 ⇒
¬MEM ntk seen0 ⇒
r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) ⇒
seenInv ru (sl++seen)``,

SRW_TAC [][seenInv] THEN
FULL_SIMP_TAC (srw_ss()) [r49Elem] THEN 
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH sl0 + SUC (LENGTH seen) =  LENGTH sl0 + 1 + LENGTH seen` by DECIDE_TAC THEN
`rule (EL i (sl0 ++ [se] ++ seen)) (NTS nt::rest) ∈
 aProdAllRules ntk se  NULL (set ru0)` by METIS_TAC [mem_in,aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def, NULL_EQ_NIL,noeProds_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [APPEND, APPEND_ASSOC] THEN1
METIS_TAC [APPEND, APPEND_ASSOC] THEN1
METIS_TAC [APPEND, APPEND_ASSOC] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [] THEN
SRW_TAC [][] THEN
`∀j. j ≤ i ⇒ EL j (sl0 ++ se::seen) ≠ se` 
 by METIS_TAC [APPEND, APPEND_ASSOC] THEN
`i ≤ LENGTH sl0` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 `i > LENGTH sl0` by DECIDE_TAC THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH sl0`] MP_TAC) THEN SRW_TAC [][] THEN1
 DECIDE_TAC THEN
 METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
	    NOT_CONS_NIL,CONS]) THEN
`EL (LENGTH sl0) (sl0++se::seen) = se` by  
METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
	   NOT_CONS_NIL,CONS] THEN
`i < LENGTH sl0` by
(`(i = LENGTH sl0) ∨ i < LENGTH sl0` by DECIDE_TAC THEN
METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
	   NOT_CONS_NIL,CONS]) THEN
`LENGTH sl0 < LENGTH sl0 + 1 + LENGTH seen` by DECIDE_TAC THEN
`∀j. j ≤ LENGTH sl0 ⇒ EL j (sl0 ++ se::seen) ≠ nt` by METIS_TAC [] THEN
`j ≤ LENGTH sl0` by DECIDE_TAC THEN
METIS_TAC [APPEND, APPEND_ASSOC]);


val r49ERtc_seenInv = store_thm
("r49ERtc_seenInv",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀seen0 ru0 sl0. (x=(seen0,ru0,sl0)) ⇒ (y=(seen,ru,sl)) ⇒
seenInv ru0 (sl0 ++ seen0) ⇒
noeProds ru0 ⇒
¬MEM ntk seen0 ⇒
seenInv ru (sl++seen)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
IMP_RES_TAC r49E_seenInv THEN
METIS_TAC [r49E_seenInv, r49E_noeProds, r49Elem, MEM]);


(***********************************************************************************)
(* STEP SEEN INV *)
(***********************************************************************************)

val stepSeen = Define
`stepSeen ru sl nt = 
∀nt' rst. rule nt (NTS nt'::rst) ∈ ru ⇒ ¬MEM nt' sl`;


val r49E_stepSeen = store_thm
("r49E_stepSeen",
``stepSeen ru0 sl0 ntk ⇒
seenInv ru0 (sl0 ++ seen0) ⇒
noeProds ru0 ⇒
r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) ⇒
stepSeen ru sl ntk``,

SRW_TAC [][stepSeen] THEN
FULL_SIMP_TAC (srw_ss()) [r49Elem] THEN
SRW_TAC [][] 
THENL[      
      `rule ntk (NTS nt'::rst) ∈ aProdAllRules ntk se NULL (set ru0)`
      by METIS_TAC [mem_in, aProdsRulesAllEq] THEN
      FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def] THEN1
      METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [NULL_EQ_NIL, seenInv] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [noeProds_def] THEN1
      METIS_TAC [] THEN
      SRW_TAC [][] THEN
      `EL (LENGTH sl0) (sl0++se::seen) = se` 
      by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
		    APPEND_NIL,NOT_CONS_NIL,CONS] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH sl0 < LENGTH sl0 + SUC (LENGTH seen)` by DECIDE_TAC THEN
      `∀j. j ≤ (LENGTH sl0) ⇒ EL j (sl0 ++ se::seen) ≠ nt'`
      by METIS_TAC [symbol_11] THEN
      `LENGTH (sl0++se::seen) = LENGTH sl0 + SUC (LENGTH seen)` by
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH sl0 < LENGTH sl0 + SUC (LENGTH seen)` by DECIDE_TAC THEN
      `EL (LENGTH sl0) (sl0++se::seen) = se` 
      by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
		    APPEND_NIL,NOT_CONS_NIL,CONS] THEN
      `∀j. j ≤ (LENGTH sl0) ⇒ EL j (sl0 ++ se::seen) ≠ nt'`
      by METIS_TAC [symbol_11] THEN
      `LENGTH (sl0++se::seen) = LENGTH sl0 + SUC (LENGTH seen)` by
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `∀j. j ≤ (LENGTH sl0) ⇒ EL j (sl0 ++ se::seen) ≠ nt'`
      by METIS_TAC [symbol_11] THEN
      SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
      SRW_TAC [][] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH r1'''`] MP_TAC) THEN
      SRW_TAC [][] THEN
      `LENGTH r1''' < LENGTH (r1''' ++ [nt'] ++ r2''' ++ se::seen)` 
      by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN1
      DECIDE_TAC THEN
      METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
		    APPEND_NIL,NOT_CONS_NIL,CONS],

      `rule ntk (NTS nt'::rst) ∈ aProdAllRules ntk se NULL (set ru0)`
      by METIS_TAC [mem_in, aProdsRulesAllEq] THEN
      FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def] THEN
      FULL_SIMP_TAC (srw_ss()) [NULL_EQ_NIL] THEN1
      METIS_TAC [] THEN 
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [noeProds_def] THEN1
      METIS_TAC [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [seenInv] THEN
      `LENGTH sl0 < LENGTH sl0 + SUC (LENGTH seen)` by DECIDE_TAC THEN
      `EL (LENGTH sl0) (sl0++se::seen) = se` 
      by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, APPEND_ASSOC,
		    APPEND_NIL,NOT_CONS_NIL,CONS] THEN
      `∀j. j ≤ (LENGTH sl0) ⇒ EL j (sl0 ++ se::seen) ≠ nt'`
      by METIS_TAC [symbol_11] THEN
      `LENGTH (sl0++se::seen) = LENGTH sl0 + SUC (LENGTH seen)` by
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH sl0 ≤ LENGTH sl0` by SRW_TAC [][] THEN
      METIS_TAC []
      ]);
      

val r49ERtc_stepSeen = store_thm
("r49ERtc_stepSeen",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀seen0 ru0 sl0. (x=(seen0,ru0,sl0)) ⇒ (y=(seen,ru,sl)) ⇒
stepSeen ru0 sl0 ntk ⇒
¬MEM ntk seen0 ⇒
seenInv ru0 (sl0 ++ seen0) ⇒
noeProds ru0 ⇒
stepSeen ru sl ntk``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
IMP_RES_TAC r49E_stepSeen THEN
IMP_RES_TAC r49E_noeProds THEN
IMP_RES_TAC r49E_seenInv THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [r49Elem] THEN
SRW_TAC [][] THEN
METIS_TAC [MEM]);


(***********************************************************************************)
(* RHS TL INV *)
(***********************************************************************************)

val rhsTlNonTms = Define
`rhsTlNonTms ru ntsl bs = 
 (∀e. e ∈ (set ntsl DIFF set bs) ⇒
  (∀r.MEM (rule e r) ru ⇒ 
   ∃h t.(r = h::t) ∧ EVERY isNonTmnlSym t ∧ 
   (∀nt.(h=NTS nt) ⇒  nt ∈ (set ntsl DIFF set bs) ∧ 
    (∃nt1 t1.(t = NTS nt1::t1) ∧ nt1 ∈ (set ntsl DIFF set bs)))))`;

val r49E_rhsTlNonTms = store_thm
("r49E_rhsTlNonTms",
``rhsTlNonTms ru0 (ntms (G ru0 s)) bs ⇒
(set seen0 ∩ set bs = {}) ⇒
r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) ⇒
rhsTlNonTms ru (ntms (G ru s)) bs``,

SRW_TAC [][rhsTlNonTms] THEN
FULL_SIMP_TAC (srw_ss()) [r49Elem] THEN
SRW_TAC [][] THEN
`rule e r ∈ aProdAllRules ntk se NULL (set ru0)` by METIS_TAC [mem_in,
							       aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def, NULL_EQ_NIL] THEN
SRW_TAC [][] THEN1
(`¬MEM se bs` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		METIS_TAC []) THEN
`e ∈ ntms (G ru0 s)` by METIS_TAC [slemma1_4, ntmsMem, startSym_def,rules_def] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
METIS_TAC [slemma1_4, ntmsMem, startSym_def, rules_def, APPEND,APPEND_NIL,
	   APPEND_ASSOC]) THEN
`¬MEM se bs` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		METIS_TAC []) THEN
`e ∈ ntms (G ru0 s)` by METIS_TAC [slemma1_4, ntmsMem, startSym_def,rules_def] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
`se ∈ ntms (G ru0 s)` by METIS_TAC [slemma1_4, ntmsMem, startSym_def,rules_def] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN1
METIS_TAC [slemma1_4, ntmsMem, startSym_def, rules_def, APPEND,APPEND_NIL,
	   APPEND_ASSOC] THEN1
METIS_TAC [slemma1_4, ntmsMem, startSym_def, rules_def, APPEND,APPEND_NIL,
	   APPEND_ASSOC] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []);

val r49ERtc_rhsTlNonTms = store_thm
("r49ERtc_rhsTlNonTms",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀seen0 ru0 sl0. (x=(seen0,ru0,sl0)) ⇒ (y=(seen,ru,sl)) ⇒
rhsTlNonTms ru0 (ntms (G ru0 s)) bs ⇒
(set seen0 ∩ set bs = {}) ⇒
rhsTlNonTms ru (ntms (G ru s)) bs``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
 `∃se. (seen0 = se::seen1) ∧ (sl1 = sl0 ++ [se])` by METIS_TAC [r49Elem] THEN
`(set seen1 ∩ set bs = {})` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
				METIS_TAC []) THEN
METIS_TAC [r49E_rhsTlNonTms, startSym_def, rules_def]);

val r49E_rhsTlNonTmsGen = store_thm
("r49E_rhsTlNonTmsGen",
``rhsTlNonTms ru0 nts0 bs ⇒
MEM ntk nts0 ⇒
(set seen0 ∩ set bs = {}) ⇒
r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) ⇒
rhsTlNonTms ru nts0 bs``,

SRW_TAC [][rhsTlNonTms] THEN
FULL_SIMP_TAC (srw_ss()) [r49Elem] THEN
SRW_TAC [][] THEN
`rule e r ∈ aProdAllRules ntk se NULL (set ru0)` by METIS_TAC [mem_in,
							       aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def, NULL_EQ_NIL] THEN
SRW_TAC [][] THEN1
(`¬MEM se bs` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		METIS_TAC []) THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def]) THEN
`¬MEM se bs` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		METIS_TAC []) THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
`se ∈ ntms (G ru0 s)` by METIS_TAC [slemma1_4, ntmsMem, startSym_def,rules_def] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
METIS_TAC [slemma1_4, ntmsMem, startSym_def, rules_def, APPEND,APPEND_NIL,
	   APPEND_ASSOC]);

val r49ERtc_rhsTlNonTmsGen = store_thm
("r49ERtc_rhsTlNonTmsGen",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀seen0 ru0 sl0. (x=(seen0,ru0,sl0)) ⇒ (y=(seen,ru,sl)) ⇒
∀nts0 bs. rhsTlNonTms ru0 nts0 bs ⇒
MEM ntk nts0 ⇒
(set nts0 ∩ set bs = {}) ⇒
(set seen0 ∩ set bs = {}) ⇒
rhsTlNonTms ru nts0 bs``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
 `∃se. (seen0 = se::seen1) ∧ (sl1 = sl0 ++ [se])` by METIS_TAC [r49Elem] THEN
SRW_TAC [][] THEN
`(set seen1 ∩ set bs = {})` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
				METIS_TAC []) THEN
`rhsTlNonTms ru1 nts0 bs` by METIS_TAC [r49E_rhsTlNonTmsGen] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [r49E_rhsTlNonTmsGen, startSym_def, rules_def]);


(***********************************************************************************)
(* r49Elem membership in nonterminals *)
(***********************************************************************************)

val r49E_notMemb = store_thm
("r49E_notMemb",
`` ¬(b ∈ ntms (G ru0 s)) ⇒ 
 r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) ⇒
 NTS b ∉ nonTerminals (G ru s)``,

SRW_TAC [][r49Elem] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
IMP_RES_TAC slemma1_4 THEN
FULL_SIMP_TAC (srw_ss()) [rules_def, startSym_def] 
THENL[
      `rule b rhs ∈ aProdAllRules ntk se NULL (set ru0)` 
      by METIS_TAC [mem_in,  aProdsRulesAllEq] THEN
      FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def] THEN
      METIS_TAC [slemma1_4, ntmsMem, startSym_def, rules_def],

      `rule l (p ++ [NTS b] ++ s') ∈ aProdAllRules ntk se NULL (set ru0)`
      by METIS_TAC [mem_in,  aProdsRulesAllEq] THEN
      FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def, NULL_EQ_NIL] THEN
      SRW_TAC [][] THEN1
      METIS_TAC [slemma1_4, ntmsMem, startSym_def, rules_def, APPEND,
		 APPEND_ASSOC, APPEND_NIL, symbol_11] THEN
      `x ++ s'' = p ++ [NTS b] ++ s'` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, rules_def,
		 startSym_def] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, rules_def,
		 startSym_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def] THEN
      Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def],

      METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def]
      ]);


val r49ERtc_notMemb = store_thm
("r49ERtc_notMemb",
 ``∀x y. (r49Elem ntk)^* x y ⇒ 
∀seen0 ru0 sl0. (x=(seen0,ru0,sl0)) ⇒ (y= (seen,ru,sl)) ⇒
 ¬(b ∈ ntms (G ru0 s)) ⇒ 
 NTS b ∉ nonTerminals (G ru s)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN1
METIS_TAC [ntmsMem] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
METIS_TAC [r49E_notMemb, ntmsMem]);

(***********************************************************************************)
(* r49E RHS B NONTMS INV *)
(***********************************************************************************)

val rhsBNonTms = Define
`rhsBNonTms ru ubs = 
 (∀B. MEM B ubs ⇒ 
  ∀r. MEM (rule B r) ru ⇒ 
  EVERY isNonTmnlSym r  ∧ r ≠ [] ∧ ∃nt.(HD r = NTS nt) ∧ ¬MEM nt ubs)`;


val r49E_rhsBNonTms = store_thm
("r49E_rhsBNonTms",
``¬MEM ntk bs ⇒
 rhsBNonTms ru0 bs ⇒
 r49Elem ntk (ubs0,ru0,sl0) (ubs,ru,sl) ⇒
 rhsBNonTms ru bs``,

SRW_TAC [][rhsBNonTms] THEN
FULL_SIMP_TAC (srw_ss()) [r49Elem] THEN
SRW_TAC [][] THEN
`rule B r ∈ aProdAllRules ntk se NULL (set ru0)` 
 by METIS_TAC [mem_in,  aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def, NULL_EQ_NIL, EXTENSION] THEN
FULL_SIMP_TAC (srw_ss()) [rhsTlNonTms] THEN
SRW_TAC [][] THEN1
METIS_TAC [] THEN
METIS_TAC []);

val r49ERtc_rhsBNonTms = store_thm
("r49ERtc_rhsBNonTms",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀ubs0 ru0 sl0. (x=(ubs0,ru0,sl0)) ⇒ (y=(ubs,ru,sl)) ⇒
 ¬MEM ntk bs ⇒
 rhsBNonTms ru0 bs ⇒
 rhsBNonTms ru bs``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
 `∃se. (ubs0 = se::seen1) ∧ (sl1 = sl0 ++ [se])` by METIS_TAC [r49Elem] THEN
SRW_TAC [][] THEN
METIS_TAC [r49E_rhsBNonTms, MEM, MEM_APPEND, APPEND, APPEND_ASSOC]);

(***********************************************************************************)
(* r49E RulesSame *)
(***********************************************************************************)

val rulesSame = Define
`rulesSame ru0 ru ontms =
∀i. i < LENGTH ontms ⇒ 
∀r. rule (EL i ontms) r ∈ ru0 ⇔ rule (EL i ontms) r ∈ ru`;

val r49E_rulesSame = store_thm
("r49E_rulesSame",
 `` ¬MEM ntk ontms ⇒
 r49Elem ntk (s0,ru0,sl0) (s,ru,sl) ⇒
 rulesSame ru0 ru ontms``,

SRW_TAC [][rulesSame] THEN
FULL_SIMP_TAC (srw_ss()) [r49Elem] THEN
SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
`rule (EL i ontms) r ∈ ru0 ⇎
 rule (EL i ontms) r ∈ aProdAllRules ntk se NULL (set ru0)`
 by METIS_TAC [mem_in,  aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def, NULL_EQ_NIL] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [EL_IS_EL]);


val r49ERtc_rulesSame = store_thm
("r49ERtc_rulesSame",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀s0 ru0 sl0. 
 (x=(s0,ru0,sl0)) ⇒ (y=(s,ru,sl)) ⇒
 ¬MEM ntk ontms ⇒
rulesSame ru0 ru ontms``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [rulesSame] THEN
`∃s1 ru1 sl1. (x' = (s1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
IMP_RES_TAC r49E_rulesSame THEN
FULL_SIMP_TAC (srw_ss()) [rulesSame] THEN
SRW_TAC [][]);


(***********************************************************************************)
(* r49Elem Existence *)
(***********************************************************************************)


val r49E_exists = store_thm
("r49E_exists",
``∃u. r49Elem ntk (se::seen0,ru0,sl0) u ∧
∃ru.(u = (seen0,ru,sl0++[se])) ``,

SRW_TAC [][] THEN
Q.ABBREV_TAC `ru = aProdAllRules ntk se NULL (set ru0)` THEN
`FINITE ru` by METIS_TAC [FINITE_LIST_TO_SET, finiteaProdAllRules] THEN
`∃r.set r = ru` by METIS_TAC [listExists4Set] THEN
Q.EXISTS_TAC `(seen0,r,sl0++[se])` THEN
SRW_TAC [][r49Elem] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [aProdsRulesAllEq]);

val r49ERtc_exists = store_thm
("r49ERtc_exists",
 ``∀seen0 ru0 sl0. 
 ∃ru. (r49Elem ntk)^* (seen0,ru0,sl0) ([],ru,sl0++seen0)``,

Induct_on `seen0` THEN SRW_TAC [][] THEN1
METIS_TAC [RTC_RULES] THEN
`∃u. r49Elem ntk (h::seen0,ru0,sl0) u ∧
 ∃ru.(u = (seen0,ru,sl0++[h]))` by METIS_TAC [r49E_exists] THEN
SRW_TAC [][] THEN
SRW_TAC [][Once RTC_CASES1] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`ru`,`sl0++[h]`] MP_TAC) THEN SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`ru'`,`(seen0,ru,sl0 ++ [h])`] THEN
METIS_TAC [APPEND, APPEND_ASSOC, aProdsRulesAllEq]);

(***********************************************************************************)
(* r49Elem Language Equivalence *)
(***********************************************************************************)

val r49E_equiv = store_thm
("r49E_equiv",
``¬MEM ntk seen0 ⇒ r49Elem ntk (seen0,ru0,sl0) (seen,ru,sl) ⇒
 (language (G ru0 s) = language (G ru s))``,

SRW_TAC [][r49Elem] THEN
METIS_TAC [lemma4_3all, aProdgAll_def, rulesets_the_same, startSym_def,
	   rules_def, MEM, aProdsRulesAllEq]);


val r49ERtc_equiv = store_thm
("r49ERtc_equiv",
``∀x y.(r49Elem ntk)^* x y ⇒ 
∀seen0 ru0 sl0. (x=(seen0,ru0,sl0)) ⇒ (y=(seen,ru,sl)) ⇒
 ¬MEM ntk seen0 ⇒
 (language (G ru0 s) = language (G ru s))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃seen1 ru1 sl1. (x' = (seen1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
METIS_TAC [r49E_equiv, startSym_def, rules_def, rulesets_the_same, r49Elem,MEM,
	   aProdsRulesAllEq]);


(***********************************************************************************)
(* R49 using r49Elem *)
(***********************************************************************************)

val r49 = Define
`r49 (bs0: α list, nts0: α list, g0:(α,β) grammar, seen0: α list, ubs0)
       (bs,nts,g,seen, ubs) =

∃ntk b rules0 rules1.
(nts0 = ntk::nts) ∧ (bs0 = b::bs) ∧ (ubs = ubs0 ++ [b]) ∧
(seen = seen0 ++ [ntk]) ∧ (nts = TL nts0) ∧

(r49Elem ntk)^* (seen0,(rules g0),[]) ([],rules0,seen0) ∧

(rules1 = l2rRules ntk b (set rules0)) ∧

(startSym g = startSym g0) ∧ (set (rules g) = rules1)`;

(***********************************************************************************)
(* R49 NONTMS SUBSET *)
(***********************************************************************************)

val l2r_ntmsSubset = store_thm
("l2r_ntmsSubset",
``(set r = l2rRules ntk b (set ru)) ⇒ 
set (ntms (G r s)) ⊆ set (ntms (G ru s)) ∪ {b}``,

SRW_TAC [][SUBSET_DEF, EXTENSION, ntmsMem] THEN
IMP_RES_TAC slemma1_4 THEN
FULL_SIMP_TAC (srw_ss()) [rules_def]
THENL[
      `rule x rhs ∈ l2rRules ntk b (set ru)` by METIS_TAC [mem_in] THEN
      FULL_SIMP_TAC (srw_ss()) [l2rRules_def] THEN1
      METIS_TAC [slemma1_4, rules_def] THEN1
      (FULL_SIMP_TAC (srw_ss()) [newAprods_def] THEN
       SRW_TAC [][] THEN
       METIS_TAC [slemma1_4, rules_def]) THEN
      FULL_SIMP_TAC (srw_ss()) [bprods_def],

      `rule l (p ++ [NTS x] ++ s') ∈ l2rRules ntk b (set ru)` 
      by METIS_TAC [mem_in] THEN
      FULL_SIMP_TAC (srw_ss()) [l2rRules_def] THEN1
      METIS_TAC [slemma1_4, rules_def] THEN1
      (FULL_SIMP_TAC (srw_ss()) [newAprods_def] THEN
       SRW_TAC [][] THEN
       `y ++ [NTS b] = p ++ [NTS x] ++ s'`by METIS_TAC [] THEN
       IMP_RES_TAC twoListAppEq THEN
       SRW_TAC [][] THEN1
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,
		  symbol_11, APPEND, APPEND_ASSOC, rules_def] THEN1
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,
		  symbol_11, APPEND, APPEND_ASSOC, rules_def] THEN1
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,
		  symbol_11, APPEND, APPEND_ASSOC, rules_def] THEN1
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,
		  symbol_11, APPEND, APPEND_ASSOC, rules_def] THEN1
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,
		  symbol_11, APPEND, APPEND_ASSOC, rules_def] THEN1
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,
		  symbol_11, APPEND, APPEND_ASSOC, rules_def] THEN1
       (Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,APPEND,
		  APPEND_ASSOC, startSym_def, symbol_11]) THEN1
       (Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,APPEND,
		  APPEND_ASSOC, startSym_def, symbol_11]) THEN
       Cases_on `s1` THEN Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,APPEND,
		  APPEND_ASSOC, startSym_def, symbol_11]) THEN
      FULL_SIMP_TAC (srw_ss()) [bprods_def] THEN
      SRW_TAC [][] THEN1
      METIS_TAC [slemma1_4, startSym_def, APPEND, APPEND_ASSOC, rules_def] THEN
      `a ++ [NTS b] = p ++ [NTS x] ++ s'` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN
       SRW_TAC [][] THEN1
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, APPEND_ASSOC, APPEND,
		  startSym_def] THEN1
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, APPEND_ASSOC, APPEND,
		  startSym_def] THEN
       Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       SRW_TAC [][] THEN
       METIS_TAC [slemma1_4, rules_def, APPEND_NIL, lastElemEq,
		  symbol_11, APPEND, APPEND_ASSOC, rules_def],

      METIS_TAC [slemma1_4, startSym_def]
      ]);


val r49_ntmsSubset = store_thm
("r49_ntmsSubset",
`` (set (ntms g0) ∩ set bs0 = {}) ⇒
r49 (bs0, nts0, g0, s0,ubs0) (bs, nts, g, s, ubs) ⇒
 set (ntms g) ⊆ set (ntms g0) ∪ set ubs``,

 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [r49] THEN
 SRW_TAC [][] THEN
Cases_on `g0` THEN
`set (ntms (G rules0 n)) ⊆ set (ntms (G l n))` 
 by METIS_TAC [r49ERtc_ntmsSubset, startSym_def, rules_def] THEN
 `∃r'. set r' = l2rRules ntk b  (set rules0)` 
 by METIS_TAC [listExists4Set, finitel2rRules, FINITE_LIST_TO_SET] THEN
`set (ntms (G r' n)) ⊆ set (ntms (G rules0 n)) ∪ {b}`
 by METIS_TAC [l2r_ntmsSubset, rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, startSym_def, rules_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [ntmsMem] THEN
Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def] THEN
IMP_RES_TAC slemma1_4 THEN
METIS_TAC [slemma1_4, ntmsMem, startSym_def, mem_in, rules_def]);

val r49Rtc_ubsSubset = store_thm
("r49Rtc_ubsSubset",
``∀x y.RTC r49 x y ⇒ 
 ∀bs0 nts0 g0 seen0 ubs0.
 (x=(bs0,nts0,g0,seen0,ubs0)) ⇒
 (y = (bs,nts,g,seen,ubs)) ⇒
ALL_DISTINCT bs0 ⇒
 (set bs0 ∩ set ubs0 = {}) ⇒
 set ubs0 ⊆ set ubs``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃bs' nts' g' seen' ubs'.(x' = (bs',nts',g',seen', ubs'))` 
 by METIS_TAC [exists_pent] THEN
SRW_TAC [][] THEN
`∃ntk b.
 (nts0 = ntk::nts') ∧ (bs0 = b::bs') ∧ (ubs' = ubs0 ++ [b]) ∧
 (seen' = seen0 ++ [ntk]) ∧ (nts' = TL nts0)` by METIS_TAC [r49] THEN
SRW_TAC [][] THEN
`¬MEM b bs'` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND]) THEN
FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND] THEN
 FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC []);


val r49Rtc_ntmsSubset = store_thm
("r49Rtc_ntmsSubset",
``∀x y.RTC r49 x y ⇒ 
 ∀bs0 nts0 g0 seen0 ubs0.
 (x=(bs0,nts0,g0,seen0,ubs0)) ⇒
 (y = (bs,nts,g,seen,ubs)) ⇒
 ALL_DISTINCT bs0 ⇒
 (set (ntms g0) ∩ set bs0 = {}) ⇒
 (set bs0 ∩ set ubs0 = {}) ⇒
 set (ntms g) ⊆ set (ntms g0) ∪ set ubs``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃bs' nts' g' seen' ubs'.(x' = (bs',nts',g',seen', ubs'))` 
 by METIS_TAC [exists_pent] THEN
SRW_TAC [][] THEN
`∃ntk b.
 (nts0 = ntk::nts') ∧ (bs0 = b::bs') ∧ (ubs' = ubs0 ++ [b]) ∧
 (seen' = seen0 ++ [ntk]) ∧ (nts' = TL nts0)` by METIS_TAC [r49] THEN
SRW_TAC [][] THEN
IMP_RES_TAC r49_ntmsSubset THEN
`set ubs0 ⊆ set (ubs0 ++ [b])`
by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
    METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND] THEN
`¬MEM b bs'` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND]) THEN
`set bs' ∩ set (ubs0 ++ [b]) = {}` by 
(FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []) THEN
`set (ubs0 ++ [b]) ⊆ set ubs` by METIS_TAC [r49Rtc_ubsSubset] THEN
`(set bs' ∩ (set ubs0 ∪ {b}) = {}) ∧ (set (ntms g') ∩ set bs' = {})` by 
(FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [ALL_DISTINCT_APPEND, APPEND]) THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [PSUBSET_DEF, EXTENSION, SUBSET_DEF] THEN
METIS_TAC []);


(***********************************************************************************)
(* R49 Language equivalence *)
(***********************************************************************************)

val r49_equiv = prove
    (``∀g0 s0 nts0 b.
     ¬MEM b (ntms g0) ⇒
     (set nts0 ∩ set s0 = {}) ⇒
     ∀bs nts g s.
     r49 (b::bs0,nts0,g0,s0,ubs0) (bs,nts,g,s,ubs) ⇒
     (language g0 = language g)``,

SRW_TAC [][r49] THEN
`¬MEM ntk s0` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		METIS_TAC [MEM]) THEN
`language (G rules0 (startSym g0)) = language (G (rules g0) (startSym g0))` 
     by METIS_TAC [r49ERtc_equiv,startSym_def, rules_def] THEN
 `∃r'. set r' = l2rRules ntk b (set rules0)` 
 by METIS_TAC [listExists4Set, finitel2rRules, FINITE_LIST_TO_SET] THEN

`left2Right ntk b (G rules0 (startSym g0)) (G r' (startSym g0))`
     by (SRW_TAC [][startSym_def, rules_def, left2Right_def] THEN
	 Cases_on `g0` THEN 
	 METIS_TAC [r49ERtc_notMemb, startSym_def, rules_def]) THEN
`language (G rules0 (startSym g0)) = language (G r' (startSym g0))` by
METIS_TAC [lemma4_4] THEN
METIS_TAC [rulesets_the_same, startSym_def, rules_def]);


val r49Rtc_equiv = store_thm
("r49Rtc_equiv",
``∀s0 s.RTC r49 s0 s ⇒ 
 ∀bs0 nts0 g0 seen0 ubs0.(s0=(bs0,nts0,g0,seen0,ubs0)) ⇒
 (s = (bs,nts,g,seen,ubs)) ⇒
 LENGTH bs0 ≥ LENGTH nts0 ∧ ALL_DISTINCT bs0 ∧ 
 ALL_DISTINCT nts0 ∧
 (set (ntms g0) ∩ set bs0 = {}) ⇒
 (set bs0 ∩ set ubs0 = {}) ⇒
 (set nts0 ∩ set seen0 = {}) ⇒
 (language g0 = language g)``,
 
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
SRW_TAC [][] THEN
`∃bs' nts' g' seen' ubs'.(s0' = (bs',nts',g',seen', ubs'))` 
 by METIS_TAC [exists_pent] THEN
SRW_TAC [][] THEN
`∃ntk b.
 (nts0 = ntk::nts') ∧ (bs0 = b::bs') ∧ (ubs' = ubs0 ++ [b]) ∧
 (seen' = seen0 ++ [ntk]) ∧ (nts' = TL nts0)` by METIS_TAC [r49] THEN
SRW_TAC [][] THEN
`LENGTH bs'  ≥ LENGTH (TL nts0)` by
(Cases_on `nts0` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) []) THEN
`(set (TL nts0) ∩ set (seen0 ++ [ntk]) = {})` by
(`¬MEM ntk (TL nts0)`  by 
 (SPOSE_NOT_THEN ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
  SRW_TAC [][] THEN
  METIS_TAC [ALL_DISTINCT_APPEND, MEM, MEM_APPEND, APPEND, APPEND_ASSOC]) THEN
 FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
 METIS_TAC [MEM]) THEN
`ALL_DISTINCT (TL nts0)` by METIS_TAC [ALL_DISTINCT_APPEND, APPEND] THEN
`set (ntms g') ⊆ set (ntms g0) ∪ set (ubs0++[b])` by METIS_TAC [r49_ntmsSubset] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`¬MEM b bs'` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND]) THEN
`¬MEM b (ntms g0)` by (FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, EXTENSION] THEN
		       METIS_TAC []) THEN
`ALL_DISTINCT bs'` by METIS_TAC [APPEND, ALL_DISTINCT_APPEND] THEN
`(set bs' ∩ (set ubs0 ∪ {b}) = {})` by
(FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
    METIS_TAC []) THEN
`(set (ntms g') ∩ set bs' = {})`
by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
    METIS_TAC []) THEN
RES_TAC THEN
METIS_TAC [r49_equiv, MEM]);

val r49Rtc_equivAlt = store_thm
("r49Rtc_equivAlt",
``RTC r49 (bs0,nts0,g0,seen0,ubs0) (bs,nts,g,seen,ubs) ∧
 LENGTH bs0 ≥ LENGTH nts0 ∧ ALL_DISTINCT bs0 ∧ 
 ALL_DISTINCT nts0 ∧
 (set (ntms g0) ∩ set bs0 = {}) ∧
 (set bs0 ∩ set ubs0 = {}) ∧
 (set nts0 ∩ set seen0 = {}) ⇒
 (language g0 = language g)``,

SRW_TAC [][] THEN
METIS_TAC [r49Rtc_equiv]);
 

(***********************************************************************************)
(* R49 Existence *)
(***********************************************************************************)

val r49_exists = store_thm
("r49_exists",
``∃u.r49 (b::t',ntk::t,g0,seen0,ubs0) u ∧ 
 ∃g.(u = (t',t,g,seen0++[ntk],ubs0++[b]))``,

SRW_TAC [][] THEN
 `∃u.(r49Elem ntk)^* (seen0,rules g0,[]) u ∧
 ∃ru. u = ([],ru,seen0)` by METIS_TAC [r49ERtc_exists, APPEND_NIL] THEN
SRW_TAC [][] THEN
 `∃r'. set r' = l2rRules ntk b (set ru)` 
 by METIS_TAC [listExists4Set, finitel2rRules, FINITE_LIST_TO_SET] THEN
Q.EXISTS_TAC `(t',t,(G r' (startSym g0)),seen0++[ntk],ubs0++[b])` THEN
SRW_TAC [][r49, startSym_def, rules_def, LET_THM] THEN
Q.EXISTS_TAC `ru` THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION]);


val r49Rtc_exists = store_thm
("r49Rtc_exists",
``∀nts0 bs0.
 LENGTH bs0 ≥ LENGTH nts0 ⇒
 ALL_DISTINCT bs0 ∧ ALL_DISTINCT nts0 ⇒
 ∀seen0.(set nts0 ∩ set seen0 = {} ) ⇒
 ∀g0.(set (ntms g0) ∩ set bs0 = {}) ⇒
 ∀ubs0. (set bs0 ∩ set ubs0 = {}) ⇒
 ∃g.(r49)^* (bs0, nts0, g0, seen0,ubs0) 
 (DROP (LENGTH nts0) bs0 ,[],g,seen0++nts0,ubs0 ++ TAKE (LENGTH nts0) bs0)``,

Induct_on `LENGTH nts0` THEN SRW_TAC [][] THEN1
(`nts0 = []` by METIS_TAC [LENGTH_NIL] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
 METIS_TAC [RTC_RULES]) THEN

Cases_on `nts0` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`t`] MP_TAC) THEN SRW_TAC [][] THEN
Cases_on `bs0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
FULL_SIMP_TAC (arith_ss) [] THEN
`LENGTH t' ≥ LENGTH t` by DECIDE_TAC THEN
`ALL_DISTINCT (t' ++ [h'])` by SRW_TAC [][ALL_DISTINCT_APPEND] THEN
`∃u. r49 (h'::t',h::t,g0,seen0, ubs0) u ∧
 ∃g. u = (t',t,g,seen0++[h],ubs0++[h'])` by METIS_TAC [APPEND, r49_exists, 
						       APPEND_NIL] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`t'`] MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`seen0++[h]`] MP_TAC) THEN SRW_TAC [][] THEN
`(set t ∩ (set seen0 ∪ {h}) = {})` by
(FULL_SIMP_TAC (srw_ss()) [INTER_DEF, EXTENSION] THEN
 METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`g`] MP_TAC) THEN SRW_TAC [][] THEN
`h' INSERT set t' = set (h'::t')` by SRW_TAC [][] THEN
`set (ntms g) ⊆ set (ntms g0) ∪ set (ubs0++[h'])` by METIS_TAC [r49_ntmsSubset] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(set (ntms g) ∩ set t' = {})` 
by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
    METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][Once RTC_CASES1] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`ubs0++[h']`] MP_TAC) THEN SRW_TAC [][] THEN
`(set t' ∩ (set ubs0 ∪ {h'}) = {})`
by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
    METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
MAP_EVERY Q.EXISTS_TAC [`g'`,`(t',t,g,seen0 ++ [h],ubs0++[h'])`] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND, APPEND_ASSOC]);

val r49Rtc_existsAlt = store_thm
("r49Rtc_existsAlt",
``LENGTH bs0 ≥ LENGTH nts0 ∧
 ALL_DISTINCT bs0 ∧ ALL_DISTINCT nts0 ∧
 (set nts0 ∩ set seen0 = {} ) ∧
 (set (ntms g0) ∩ set bs0 = {}) ∧
 (set bs0 ∩ set ubs0 = {}) ⇒
 ∃g.(r49)^* (bs0, nts0, g0, seen0,ubs0) 
 (DROP (LENGTH nts0) bs0 ,[],g,seen0++nts0,ubs0 ++ TAKE (LENGTH nts0) bs0)``,

SRW_TAC [][] THEN
METIS_TAC [r49Rtc_exists]);


(***********************************************************************************)
(* R49 Invariants *)
(***********************************************************************************)

(***********************************************************************************)
(* R49 NO EPRODS *)
(***********************************************************************************)

val r49_noeProds = store_thm
("r49_noeProds",
``noeProds (rules g0) ⇒ 
 (set s0 ∩ set ubs0 = {}) ⇒
 (set nts0 ∩ set ubs0 = {}) ⇒
 rhsTlNonTms (rules g0) (ntms g0) ubs0 ⇒
 r49 (bs0, nts0, g0, s0,ubs0) (bs, nts, g, s, ubs) ⇒
 noeProds (rules g)``,

SRW_TAC [][r49] THEN
`noeProds rules0` by METIS_TAC [r49ERtc_noeProds] THEN
Cases_on `g0` THEN
`rhsTlNonTms rules0 (ntms (G rules0 n)) ubs0` 
 by METIS_TAC [r49ERtc_rhsTlNonTms, startSym_def, rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [noeProds_def] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
`rule l' [] ∈ l2rRules ntk b (set rules0)`  by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [l2rRules_def, newAprods_def, bprods_def] THEN1
METIS_TAC [] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [rhsTlNonTms, rules_def] THEN
`ntk ∈ ntms (G rules0 n)` by METIS_TAC [ntmsMem, rules_def, startSym_def,
					slemma1_4] THEN
`¬MEM ntk ubs0` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
			     METIS_TAC [MEM]) THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THEN
SRW_TAC [][]);


(***********************************************************************************)
(* r49 RHS TL NTMS *)
(***********************************************************************************)

val r49_rhsTlNonTms = store_thm
("r49_rhsTlNontms",
 ``(set s0 ∩ set ubs0 = {}) ⇒
 (set (ntms g0) ∩ set bs0 = {}) ⇒
 rhsTlNonTms (rules g0) (ntms g0) ubs0 ⇒
 r49 (bs0, nts0, g0, s0,ubs0) (bs, nts, g, s, ubs) ⇒
 rhsTlNonTms (rules g) (ntms g) ubs``,

SRW_TAC [][r49] THEN
 `∃r. set r = l2rRules ntk b (set rules0)` 
 by METIS_TAC [listExists4Set, finitel2rRules, FINITE_LIST_TO_SET] THEN
Cases_on `g0` THEN
`rhsTlNonTms rules0 (ntms (G rules0 n)) ubs0` 
 by METIS_TAC [r49ERtc_rhsTlNonTms, startSym_def, rules_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def] THEN
`¬MEM b (ntms (G l (startSym g)))` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
				       METIS_TAC []) THEN
`¬MEM b (ntms (G rules0 (startSym g)))` by METIS_TAC [r49ERtc_notMemb, startSym_def,
						      rules_def,ntmsMem] THEN
FULL_SIMP_TAC (srw_ss()) [rhsTlNonTms] THEN
SRW_TAC [][] THEN
`rule e r' ∈ l2rRules ntk b (set rules0)` by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [l2rRules_def, newAprods_def, bprods_def, rules_def,
			  startSym_def] THEN
SRW_TAC [][] THEN
`e ∈ ntms (G rules0 (startSym g))` by METIS_TAC [ntmsMem, rules_def, startSym_def,
					slemma1_4] THEN1
(
RES_TAC THEN
 SRW_TAC [][] THEN
 METIS_TAC [slemma1_4, rules_def, ntmsMem, startSym_def, APPEND, APPEND_NIL,
	    APPEND_ASSOC]) THEN
RES_TAC THEN
SRW_TAC [][isNonTmnlSym_def] THEN
METIS_TAC [slemma1_4, rules_def, ntmsMem, startSym_def, APPEND, APPEND_NIL,
	   APPEND_ASSOC]);


val r49Rtc_rhsTlNonTms = store_thm
("r49Rtc_rhsTlNonTms",
 ``∀x y. (r49)^* x y ⇒
 ∀bs0 nts0 g0 s0 ubs0. 
 (x = (bs0, nts0, g0, s0,ubs0)) ⇒ (y= (bs, nts, g, s, ubs)) ⇒
 ALL_DISTINCT bs0 ⇒
 (set bs0 ∩ set ubs0 = {}) ⇒
 (set s0 ∩ set ubs0 = {}) ⇒
 (set s0 ∩ set bs0 = {}) ⇒
 (set nts0 ∩ set ubs0 = {}) ⇒
 (set nts0 ∩ set bs0 = {}) ⇒
 (set (ntms g0) ∩ set bs0 = {}) ⇒
 rhsTlNonTms (rules g0) (ntms g0) ubs0 ⇒
 rhsTlNonTms (rules g) (ntms g) ubs``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃bs1 nts1 g1 s1 ubs1. (x' = (bs1, nts1, g1, s1,ubs1))`
 by METIS_TAC [exists_pent] THEN
SRW_TAC [][] THEN
`rhsTlNonTms (rules g1) (ntms g1) ubs1` by METIS_TAC [r49_rhsTlNonTms] THEN
SRW_TAC [][] THEN
`∃ntk b. (nts0 = ntk::nts1) ∧ (bs0 = b::bs1) ∧
 (s1 = s0 ++ [ntk]) ∧ (ubs1 = ubs0 ++ [b]) ∧ (nts1 = TL nts0)` by METIS_TAC [r49] THEN
SRW_TAC [][] THEN
`¬MEM b bs1` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND]) THEN
`set (ntms g1) ⊆ set (ntms g0) ∪ set (ubs0++[b])` by METIS_TAC [r49_ntmsSubset] THEN
`(set (s0 ++ [ntk]) ∩ set (ubs0 ++ [b]) = {})` by 
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`(set (s0 ++ [ntk]) ∩ set bs1 = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`(set (TL nts0) ∩ set (ubs0 ++ [b]) = {}) ∧ (set (TL nts0) ∩ set bs1 = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
 FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF, ALL_DISTINCT_APPEND] THEN
METIS_TAC [MEM]);


val r49Rtc_noeProds = store_thm
("r49Rtc_noeProds",
 ``∀x y. (r49)^* x y ⇒
 ∀bs0 nts0 g0 s0 ubs0. 
 (x = (bs0, nts0, g0, s0,ubs0)) ⇒ (y= (bs, nts, g, s, ubs)) ⇒
 ALL_DISTINCT bs0 ⇒
 (set bs0 ∩ set ubs0 = {}) ⇒
 (set s0 ∩ set ubs0 = {}) ⇒
 (set s0 ∩ set bs0 = {}) ⇒
 (set nts0 ∩ set bs0 = {}) ⇒
 (set (ntms g0) ∩ set bs0 = {}) ⇒
 (set nts0 ∩ set ubs0 = {}) ⇒
 rhsTlNonTms (rules g0) (ntms g0) ubs0 ⇒
 noeProds (rules g0) ⇒ 
 noeProds (rules g)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃bs1 nts1 g1 s1 ubs1. (x' = (bs1, nts1, g1, s1,ubs1))`
 by METIS_TAC [exists_pent] THEN
SRW_TAC [][] THEN
`rhsTlNonTms (rules g1) (ntms g1) ubs1` by METIS_TAC [r49_rhsTlNonTms] THEN
SRW_TAC [][] THEN
`∃ntk b. (nts0 = ntk::nts1) ∧ (bs0 = b::bs1) ∧
 (s1 = s0 ++ [ntk]) ∧ (ubs1 = ubs0 ++ [b]) ∧ (nts1 = TL nts0)` 
 by METIS_TAC [r49] THEN
 SRW_TAC [][] THEN
`¬MEM b bs1` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND]) THEN
`set (ntms g1) ⊆ set (ntms g0) ∪ set (ubs0++[b])` by METIS_TAC [r49_ntmsSubset] THEN
`(set (s0 ++ [ntk]) ∩ set (ubs0 ++ [b]) = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`(set (s0 ++ [ntk]) ∩ set bs1 = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`(set (TL nts0) ∩ set (ubs0 ++ [b]) = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`noeProds (rules g1)` by METIS_TAC [r49_noeProds] THEN
`(set (s0 ++ [ntk]) ∩ set bs1 = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`(set (TL nts0) ∩ set (ubs0 ++ [b]) = {}) ∧ (set (TL nts0) ∩ set bs1 = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
 FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF, ALL_DISTINCT_APPEND] THEN
METIS_TAC [MEM]);

(***********************************************************************************)
(* R49 RHS B NONTMS INV *)
(***********************************************************************************)

val l2r_rulesSame = store_thm
("l2r_rulesSame",
``¬MEM A ntsl ∧ ¬MEM B ntsl ∧
(set ru = l2rRules A B (set ru0)) ⇒
rulesSame ru0 ru ntsl``,

SRW_TAC [][rulesSame, l2rRules_def, EQ_IMP_THM] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN1

(`¬(rule (EL i ntsl) r ∈ set ru0 ∪ newAprods A B (set ru0) ∪
      bprods A B (set ru0) DIFF recprods A (set ru0))` by METIS_TAC [mem_in] THEN
 FULL_SIMP_TAC (srw_ss()) [newAprods_def, bprods_def, recprods_def] THEN
 SRW_TAC [][] THEN
 METIS_TAC [EL_IS_EL]) THEN

`rule (EL i ntsl) r ∈ set ru0 ∪ newAprods A B (set ru0) ∪
      bprods A B (set ru0) DIFF recprods A (set ru0)` by METIS_TAC [mem_in] THEN
 FULL_SIMP_TAC (srw_ss()) [newAprods_def, bprods_def, recprods_def] THEN
 SRW_TAC [][] THEN
 METIS_TAC [EL_IS_EL]);


val l2r_rhsBNonTms = store_thm
("l2r_rhsBNonTms",
``rhsBNonTms ru0 bs ⇒
¬MEM A bs ∧ ¬MEM B bs ⇒
¬MEM B (ntms (G ru0 s)) ⇒
rhsTlNonTms ru0 (ntms (G ru0 s)) bs ⇒
(set ru = l2rRules A B (set ru0)) ⇒
rhsBNonTms ru (bs++[B])``,

SRW_TAC [][] THEN
`rulesSame ru0 ru bs` by METIS_TAC [l2r_rulesSame] THEN
FULL_SIMP_TAC (srw_ss()) [rhsBNonTms, l2rRules_def, rulesSame] THEN
SRW_TAC [][] 
 THENL[
 `∃i. i < LENGTH bs ∧ (EL i bs = B')` by METIS_TAC [memImpEl] THEN
`rule B' r ∈ 
set ru0 ∪ newAprods A B (set ru0) ∪ bprods A B (set ru0) DIFF recprods A (set ru0)`
 by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [newAprods_def, bprods_def, recprods_def] THEN
METIS_TAC [],

 `∃i. i < LENGTH bs ∧ (EL i bs = B')` by METIS_TAC [memImpEl] THEN
`rule B' r ∈ 
set ru0 ∪ newAprods A B (set ru0) ∪ bprods A B (set ru0) DIFF recprods A (set ru0)`
 by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [newAprods_def, bprods_def, recprods_def] THEN
METIS_TAC [],

 `∃i. i < LENGTH bs ∧ (EL i bs = B')` by METIS_TAC [memImpEl] THEN
`rule B' r ∈ 
set ru0 ∪ newAprods A B (set ru0) ∪ bprods A B (set ru0) DIFF recprods A (set ru0)`
 by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [newAprods_def, bprods_def, recprods_def] THEN
`EVERY isNonTmnlSym r ∧ r ≠ [] ∧
 ∃nt. (HD r = NTS nt) ∧ ¬(nt ∈ bs)` by METIS_TAC [] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def, APPEND, APPEND_NIL,
	   APPEND_ASSOC],

`rule B r ∈ set ru0 ∪ newAprods A B (set ru0) ∪
      bprods A B (set ru0) DIFF recprods A (set ru0)` by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [rhsTlNonTms, newAprods_def, bprods_def, recprods_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN1
METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN1
METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN 
`A ∈ (ntms (G ru0 s))` by METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN
RES_TAC  THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def],

`rule B r ∈ set ru0 ∪ newAprods A B (set ru0) ∪
      bprods A B (set ru0) DIFF recprods A (set ru0)` by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [rhsTlNonTms, newAprods_def, bprods_def, recprods_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN
`A ∈ (ntms (G ru0 s))` by METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN
RES_TAC  THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
SRW_TAC [][],

`rule B r ∈ set ru0 ∪ newAprods A B (set ru0) ∪
      bprods A B (set ru0) DIFF recprods A (set ru0)` by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [rhsTlNonTms, newAprods_def, bprods_def, recprods_def] THEN
SRW_TAC [][] THEN1
METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN1
METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN
`A ∈ (ntms (G ru0 s))` by METIS_TAC [slemma1_4, ntmsMem, rules_def, 
				     startSym_def] THEN
RES_TAC  THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def]]);


val r49_rhsBNonTms = store_thm
("r49_rhsBNontms",
 ``(set nts0 ∩ set (ubs0++bs0) = {}) ⇒
 (set bs0 ∩ set ubs0 = {}) ⇒
 (set bs0 ∩ set (ntms g0) = {}) ⇒
 (set s0 ∩ set ubs0 = {}) ⇒
 rhsTlNonTms (rules g0) (ntms g0) ubs0 ⇒
 rhsBNonTms (rules g0) ubs0 ⇒
 r49 (bs0, nts0, g0, s0,ubs0) (bs, nts, g, s, ubs) ⇒
 rhsBNonTms (rules g) ubs``,

SRW_TAC [][r49] THEN
 `∃r. set r = l2rRules ntk b (set rules0)` 
 by METIS_TAC [listExists4Set, finitel2rRules, FINITE_LIST_TO_SET] THEN
`¬MEM ntk ubs0` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		    METIS_TAC [MEM]) THEN
`rhsBNonTms rules0 ubs0` by METIS_TAC [r49ERtc_rhsBNonTms] THEN
`rhsTlNonTms rules0 (ntms (G rules0 (startSym g0))) ubs0`
 by (Cases_on `g0` THEN 
     METIS_TAC [r49ERtc_rhsTlNonTms, startSym_def, rules_def]) THEN
`rhsTlNonTms rules0 (ntms (G rules0 (startSym g0))) ubs0` 
 by (Cases_on `g0` THEN
     METIS_TAC [r49ERtc_rhsTlNonTms, rules_def,startSym_def]) THEN
`¬MEM b ubs0` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		    METIS_TAC [MEM]) THEN
`¬MEM b (ntms g0)` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		    METIS_TAC [MEM]) THEN
`¬MEM b (ntms (G rules0 (startSym g0)))`
by (Cases_on `g0` THEN METIS_TAC [r49ERtc_notMemb, rules_def, startSym_def,ntmsMem,
				  symbol_11]) THEN
`rhsBNonTms r (ubs0 ++ [b])` by METIS_TAC [l2r_rhsBNonTms] THEN
FULL_SIMP_TAC (srw_ss()) [rhsBNonTms, EXTENSION] THEN SRW_TAC [][] THEN
METIS_TAC []);

val r49Rtc_rhsBNonTms = store_thm
("r49Rtc_rhsBNontms",
 ``∀x y. r49^* x y ⇒ 
 ∀bs0 nts0 g0 s0 ubs0.
 (x=(bs0, nts0, g0, s0,ubs0)) ⇒ (y=(bs, nts, g, s, ubs)) ⇒
 ALL_DISTINCT bs0 ⇒
 (set bs0 ∩ set ubs0 = {}) ⇒
 (set nts0 ∩ set (ubs0 ++ bs0) = {}) ⇒
 (set (ntms g0) ∩ set bs0 = {}) ⇒
 (set s0 ∩ set ubs0 = {}) ⇒
 (set s0 ∩ set bs0 = {}) ⇒
 rhsTlNonTms (rules g0) (ntms g0) ubs0 ⇒
 rhsBNonTms (rules g0) ubs0 ⇒
 rhsBNonTms (rules g) ubs``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃bs1 nts1 g1 s1 ubs1. (x' = (bs1, nts1, g1, s1,ubs1))`
 by METIS_TAC [exists_pent] THEN
SRW_TAC [][] THEN
`∃ntk b. (nts0 = ntk::nts1) ∧ (bs0 = b::bs1) ∧
 (s1 = s0 ++ [ntk]) ∧ (ubs1 = ubs0 ++ [b]) ∧ (nts1 = TL nts0)` 
 by METIS_TAC [r49] THEN
 SRW_TAC [][] THEN
`rhsTlNonTms (rules g1) (ntms g1) (ubs0 ++ [b])`
by METIS_TAC [r49_rhsTlNonTms] THEN
`set ubs0 ∪ set (b::bs1) = set (ubs0 ++ (b::bs1))` by SRW_TAC [][] THEN
`rhsBNonTms (rules g1) (ubs0 ++ [b])` by METIS_TAC [APPEND,INTER_COMM,
						    r49_rhsBNonTms] THEN
`¬MEM b bs1` by (SPOSE_NOT_THEN ASSUME_TAC THEN
		 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
		 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND]) THEN
 `(set (TL nts0) ∩ (set (ubs0 ++ [b]) ∪ set bs1) = {}) ∧
 (set bs1 ∩ (set ubs0 ∪ {b}) = {})` by
(FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [MEM]) THEN
`ALL_DISTINCT bs1` by FULL_SIMP_TAC (srw_ss()) [] THEN
`(set (s0 ++ [ntk]) ∩ set (ubs0 ++ [b]) = {}) ∧
(set (s0 ++ [ntk]) ∩ set bs1 = {})` by
(FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [MEM]) THEN
`(set bs1 ∩ set (ubs0 ++ [b]) = {}) ` by FULL_SIMP_TAC (srw_ss()) [] THEN
IMP_RES_TAC r49_ntmsSubset THEN
`(set (ntms g1) ∩ set bs1 = {})` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION,
							       SUBSET_DEF] THEN
				     METIS_TAC [MEM]) THEN
METIS_TAC []);


(***********************************************************************************)
(* R49 SEEN INV *)
(***********************************************************************************)

val r49_seenInv = prove
(``∀s0 g0 nts0 bs0. 
 seenInv (rules g0) s0 ∧
 rhsTlNonTms (rules g0) (ntms g0) ubs0 ⇒
 noeProds (rules g0) ∧
 (set s0 ∩ set ubs0 = {}) ∧
 (set nts0 ∩ set s0 = {}) ∧ 
 (set nts0 ∩ set ubs0 = {}) ∧
 (set nts0 ∩ set bs0 = {}) ⇒
 (set s0 ∩ set bs0 = {}) ⇒
 ∀ubs0 bs nts g s ubs.
 r49 (bs0,nts0,g0,s0,ubs0) (bs,nts,g,s,ubs) ⇒
 seenInv (rules g) s``,

SRW_TAC [][r49] THEN
`¬MEM ntk s0` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC [MEM]) THEN
`seenInv rules0 s0` by METIS_TAC [r49ERtc_seenInv, APPEND_NIL] THEN
`stepSeen (rules g0) [] ntk` by METIS_TAC [stepSeen, MEM] THEN
 `stepSeen rules0 s0 ntk` by METIS_TAC [APPEND_NIL, r49ERtc_stepSeen] THEN
 `set (ntms (G rules0 (startSym g0))) ⊆ set (ntms (G (rules g0) (startSym g0)))` 
 by METIS_TAC [r49ERtc_ntmsSubset, startSym_def, rules_def] THEN
`rhsTlNonTms rules0 (ntms (G rules0 (startSym g0))) ubs0`  
by (Cases_on `g0` THEN METIS_TAC [r49ERtc_rhsTlNonTms, startSym_def, rules_def]) THEN
 FULL_SIMP_TAC (srw_ss()) [stepSeen] THEN
`∀i. i < LENGTH s0 ⇒
 (∀nt rest. rule ntk (NTS nt::rest) ∈ rules0 ⇒ EL i s0 ≠ nt)` by 
 (`stepSeen (rules g0) [] ntk` by METIS_TAC [stepSeen, MEM] THEN
  `stepSeen rules0 s0 ntk` by METIS_TAC [APPEND_NIL, r49ERtc_stepSeen] THEN
  FULL_SIMP_TAC (srw_ss()) [stepSeen] THEN
  SRW_TAC [][] THEN
  METIS_TAC [EL_IS_EL]) THEN
 `∃r'. set r' = l2rRules ntk b (set rules0)` 
 by METIS_TAC [listExists4Set, finitel2rRules, FINITE_LIST_TO_SET] THEN

`seenInv r' (s0 ++ [ntk])` by

(FULL_SIMP_TAC (srw_ss()) [seenInv] THEN
SRW_TAC [][] THEN
`rule (EL i (s0 ++ [ntk])) (NTS nt::rest) ∈ 
 l2rRules ntk b (set rules0)` by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [seenInv, rules_def,l2rRules_def, newAprods_def, 
			   bprods_def] THEN 
 SRW_TAC [][] THEN1
(`i < LENGTH s0 ∨ (i = LENGTH s0)` by DECIDE_TAC THEN1
 (`EL j (s0++[ntk]) = EL j s0` by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
					    ⇒ j < l``] THEN
 `EL i (s0++[ntk]) = EL i s0` by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
					    ⇒ j < l``] THEN
  METIS_TAC []) THEN
`EL i (s0 ++ [ntk]) = ntk` by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,
					 NOT_CONS_NIL,CONS] THEN
SRW_TAC [][] THEN
`EL (LENGTH s0) (s0++[ntk]) = ntk` by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,
					 NOT_CONS_NIL,CONS] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`j < LENGTH s0 ∨ (j = LENGTH s0)`by DECIDE_TAC THEN1
(`EL j (s0 ++ [ntk]) = EL j s0` by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
					    ⇒ j < l``] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [recprods_def] THEN
METIS_TAC []) THEN1

(FULL_SIMP_TAC (srw_ss()) [rhsTlNonTms] THEN
`¬MEM ntk ubs0` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		   METIS_TAC [MEM]) THEN
`ntk ∈ ntms (G rules0 (startSym g0))` 
 by METIS_TAC [slemma1_4, ntmsMem, rules_def, startSym_def] THEN
`ntk ∈ ntms g0` by (Cases_on `g0` THEN 
		    FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, rules_def,
					      startSym_def]) THEN
 `y ≠ []` by METIS_TAC [NOT_CONS_NIL] THEN
Cases_on `y` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
`i < LENGTH s0 ∨ (i = LENGTH s0)` by DECIDE_TAC THEN1
(`EL j (s0++[ntk]) = EL j s0` by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
					    ⇒ j < l``] THEN
 `EL i (s0++[ntk]) = EL i s0` by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
					    ⇒ j < l``] THEN
 METIS_TAC []) THEN
`EL i (s0 ++ [ntk]) = ntk` by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,
					 NOT_CONS_NIL,CONS] THEN
SRW_TAC [][] THEN
`EL (LENGTH s0) (s0++[ntk]) = ntk` by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,
					 NOT_CONS_NIL,CONS] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`j < LENGTH s0 ∨ (j = LENGTH s0)`by DECIDE_TAC THEN1
(`EL j (s0 ++ [ntk]) = EL j s0` by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
					    ⇒ j < l``] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [recprods_def] THEN
METIS_TAC []) THEN
(`i < LENGTH s0 ∨ (i = LENGTH s0)` by DECIDE_TAC THEN1
(`EL i (s0++[ntk]) = EL i s0` by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
					    ⇒ j < l``] THEN
 FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
 METIS_TAC [EL_IS_EL]) THEN

`EL i (s0++[ntk]) = ntk` by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,
					 NOT_CONS_NIL,CONS] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [EL_IS_EL, MEM])) THEN
FULL_SIMP_TAC (srw_ss()) [seenInv, LET_THM] THEN
SRW_TAC [][] THEN
METIS_TAC [mem_in]);


val r49Rtc_seenInv = store_thm
("r49Rtc_seenInv",
 ``∀x y. (r49)^* x y ⇒ 
 ∀bs0 nts0 g0 s0 ubs0. 
 (x = (bs0,nts0,g0,s0,ubs0)) ⇒ (y= (bs,nts,g,s,ubs)) ⇒
 rhsTlNonTms (rules g0) (ntms g0) ubs0 ⇒
 seenInv (rules g0) s0 ⇒
 noeProds (rules g0) ⇒
 ALL_DISTINCT nts0 ⇒
 ALL_DISTINCT bs0 ⇒
 (set (ntms g0) ∩ set bs0 = {}) ⇒
 (set bs0 ∩ set ubs0 = {}) ⇒
 (set nts0 ∩ set s0 = {}) ⇒
 (set nts0 ∩ set bs0 = {}) ⇒
 (set nts0 ∩ set ubs0 = {}) ⇒
 (set s0 ∩ set bs0 = {}) ⇒
 (set s0 ∩ set ubs0 = {}) ⇒
 seenInv (rules g) s``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃bs1 nts1 g1 s1 ubs1. (x' = (bs1, nts1, g1, s1,ubs1))`
 by METIS_TAC [exists_pent] THEN
SRW_TAC [][] THEN
`seenInv (rules g1) s1` by METIS_TAC [r49_seenInv] THEN
`noeProds (rules g1)`by METIS_TAC [r49_noeProds] THEN
`rhsTlNonTms (rules g1) (ntms g1) ubs1` by METIS_TAC [r49_rhsTlNonTms] THEN
`∃ntk b. (nts0 = ntk::nts1) ∧ (bs0 = b::bs1) ∧
 (s1 = s0 ++ [ntk]) ∧ (ubs1 = ubs0 ++ [b]) ∧ (nts1 = TL nts0)` by METIS_TAC [r49] THEN
SRW_TAC [][] THEN
`ALL_DISTINCT (TL nts0)` by METIS_TAC [APPEND, ALL_DISTINCT_APPEND] THEN
`ALL_DISTINCT bs1` by METIS_TAC [APPEND, ALL_DISTINCT_APPEND] THEN
`¬MEM b bs1` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND]) THEN
`set (ntms g1) ⊆ set (ntms g0) ∪ set (ubs0++[b])` by METIS_TAC [r49_ntmsSubset] THEN
`(set (s0 ++ [ntk]) ∩ set (ubs0 ++ [b]) = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`(set (s0 ++ [ntk]) ∩ set bs1 = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`(set (TL nts0) ∩ set (ubs0 ++ [b]) = {})` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
 METIS_TAC [MEM]) THEN
`¬MEM ntk (TL nts0)` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 METIS_TAC [APPEND, MEM, MEM_APPEND, rgr_r9eq, ALL_DISTINCT_APPEND]) THEN
`(set (ntms g1) ∩ set bs1 = {})` by 
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, EXTENSION] THEN
 RES_TAC THEN METIS_TAC [MEM]) THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF, ALL_DISTINCT_APPEND] THEN
METIS_TAC [MEM]);


(***********************************************************************************)
(* Transforming the head ntm to a tm symbol. *)
(***********************************************************************************)

val isCnfImprhsTlNonTmnls = store_thm
("isCnfImprhsTlNonTmnls",
``isCnf g0 ⇒ (set (ntms g0) ∩ set bs0 = {}) ⇒
 rhsTlNonTms (rules g0) (ntms g0) bs0``,

SRW_TAC [][isCnf_def, rhsTlNonTms] THEN
RES_TAC 
 THENL[
       Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, 
						   isTmnlSym_def] THEN
       FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [LENGTH_NIL, isNonTmnlSym_def] THEN
       METIS_TAC [LENGTH_NIL, EVERY_DEF, DECIDE ``1 ≠ 0``, ntmsMem, slemma1_4,
		  APPEND_NIL, APPEND, APPEND_ASSOC, startSym_def, rules_def],

       Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, 
						   isTmnlSym_def] THEN
       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []
       ]);



val validGnfProd = Define 
`validGnfProd (rule l r) = 
    ∃ts ntsl.(r = ts::ntsl) ∧ isTmnlSym ts ∧ EVERY isNonTmnlSym ntsl`;

val isGnf = Define 
`isGnf g = EVERY validGnfProd (rules g)`;


val fstNtm2Tm = Define
`fstNtm2Tm (ontms0,g0,seen0) (ontms,g,seen) = 
∃ntk rules0. (ontms0 = ontms++[ntk]) ∧ (seen = ntk::seen0) ∧
(r49Elem ntk)^* (seen0,rules g0,[]) ([],rules0,seen0) ∧
(rules g = rules0) ∧
(startSym g = startSym g0)`;

val gnfInv = Define
`gnfInv ru s = 
∀i. i < LENGTH s ⇒
∀r. rule (EL i s) r ∈ ru ⇒ validGnfProd (rule (EL i s) r)`;

val gnfAlt = Define
`gnfAlt ru s = 
∀l. l ∈ s ⇒ (∀r. (rule l r) ∈ ru ⇒ validGnfProd (rule l r))`;

val gnfEqAlt = store_thm
("gnfEqAlt",
``∀ ru s.gnfInv ru s ⇔ gnfAlt ru s``,

SRW_TAC [][gnfInv, gnfAlt, EQ_IMP_THM] THEN
METIS_TAC [memImpEl, MEM_EL]);



val ruleInv = Define
`ruleInv ru ontms s =
     ∀i.
     i < LENGTH ontms ⇒
     ∀nt rst. rule (EL i ontms) (NTS nt::rst) ∈ ru ⇒ 
     nt ∈ (DROP (SUC i) ontms ++ s)`;

val ntk2Tm = Define
`ntk2Tm ru ntk s =
∀i. i < LENGTH s ⇒ ∀rst.¬MEM (rule ntk (NTS (EL i s)::rst)) ru`;

val r49E_ntk2Tm = store_thm
("r49E_ntk2Tm",
``gnfInv ru0  (sl0++s0) ∧
ntk2Tm ru0 ntk sl0 ∧
r49Elem ntk (s0,ru0,sl0) (s,ru,sl) ⇒
ntk2Tm ru ntk sl``,

SRW_TAC [][r49Elem, ntk2Tm, gnfInv] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
`rule ntk (NTS (EL i (sl0 ++ [se]))::rst) ∈ aProdAllRules ntk se NULL (set ru0)`
by METIS_TAC [mem_in,  aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def] THEN
`i < LENGTH sl0 ∨ (i = LENGTH sl0)` by DECIDE_TAC THEN1

(`EL i (sl0++[se]) = EL i sl0` by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
					    ⇒ j < l``] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH sl0 < LENGTH sl0 + 1`by DECIDE_TAC THEN
METIS_TAC []) THEN1

(`EL i (sl0++[se]) = se` by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, 
				       APPEND_ASSOC,NOT_CONS_NIL,CONS] THEN
SRW_TAC [][] THEN
METIS_TAC [APPEND, NULL_EQ_NIL, APPEND_NIL, symbol_11]) THEN

FULL_SIMP_TAC (srw_ss()) [NULL_EQ_NIL] THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH sl0 < LENGTH sl0 + SUC (LENGTH s)` by DECIDE_TAC THEN
`EL (LENGTH sl0) (sl0++se::s) = se` 
by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, 
	      APPEND_ASSOC,NOT_CONS_NIL,CONS] THEN
`validGnfProd (rule se x)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [validGnfProd] THEN
SRW_TAC [][] THEN
Cases_on `ts` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);


val r49E_gnfInv = store_thm
("r49E_gnfInv",
``gnfInv ru0 (sl0++s0) ∧
¬MEM ntk (s0++sl0) ∧
r49Elem ntk (s0,ru0,sl0) (s,ru,sl) ⇒
gnfInv ru (sl++s)``,

SRW_TAC [][r49Elem, gnfInv] THEN
FULL_SIMP_TAC (srw_ss()) [validGnfProd] THEN
`rule (EL i (sl0 ++ [se] ++ s)) r ∈ aProdAllRules ntk se NULL (set ru0)` 
 by METIS_TAC [mem_in,  aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def, NULL_EQ_NIL] THEN
SRW_TAC [][] THEN
 `LENGTH sl0 + 1 + LENGTH s = LENGTH sl0 + SUC (LENGTH s)` by DECIDE_TAC THEN1
 METIS_TAC [APPEND, APPEND_ASSOC] THEN 
`LENGTH (sl0++[se]++s) = LENGTH sl0 + 1 + LENGTH s` by
 FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
`MEM (EL i (sl0 ++ [se] ++ s)) (sl0 ++ [se] ++ s)` by
METIS_TAC [MEM, MEM_APPEND, EL_IS_EL] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);


val r49ERtc_gnfInv = store_thm
("r49ERtc_gnfInv",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀s0 ru0 sl0. 
 (x=(s0,ru0,sl0)) ⇒ (y=(s,ru,sl)) ⇒
 gnfInv ru0 (sl0++s0) ⇒
 ¬MEM ntk (s0++sl0) ⇒
 gnfInv ru (sl++s)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃s1 ru1 sl1. (x' = (s1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
 `∃se. (s0 = se::s1) ∧ (sl1 = sl0 ++ [se])` by METIS_TAC [r49Elem] THEN
SRW_TAC [][] THEN
METIS_TAC [MEM, MEM_APPEND, r49E_gnfInv]);


val r49ERtc_ntk2Tm = store_thm
("r49ERtc_ntk2Tm",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀s0 ru0 sl0. 
 (x=(s0,ru0,sl0)) ⇒ (y=(s,ru,sl)) ⇒
 gnfInv ru0  (sl0++s0) ⇒
 ¬MEM ntk (s0++sl0) ⇒
 ntk2Tm ru0 ntk sl0 ⇒
 ntk2Tm ru ntk sl``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃s1 ru1 sl1. (x' = (s1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
 `∃se. (s0 = se::s1) ∧ (sl1 = sl0 ++ [se])` by METIS_TAC [r49Elem] THEN
SRW_TAC [][] THEN
IMP_RES_TAC r49E_gnfInv THEN
METIS_TAC [r49E_gnfInv, MEM, MEM_APPEND, APPEND, APPEND_ASSOC, r49E_ntk2Tm]);


val r49E_ruleInv = store_thm
("r49E_ruleInv",
``ruleInv ru0 (ontms++[ntk]) (sl0 ++ s0) ⇒
¬MEM ntk ontms ⇒
¬MEM ntk (sl0++s0) ⇒
gnfInv ru0 (sl0++s0) ⇒
r49Elem ntk (s0,ru0,sl0) (s,ru,sl) ⇒
ruleInv ru (ontms++[ntk]) (sl ++ s)``,

SRW_TAC [][] THEN
IMP_RES_TAC r49E_rulesSame THEN
`gnfInv ru (sl++s)` by METIS_TAC [MEM, MEM_APPEND, r49E_gnfInv] THEN
 `∃se. (s0 = se::s) ∧ (sl = sl0 ++ [se])` by METIS_TAC [r49Elem] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [ruleInv] THEN
SRW_TAC [][] THEN
`i < LENGTH ontms ∨ (i = LENGTH ontms)` by DECIDE_TAC THEN1
(`EL i (ontms ++ [ntk]) = EL i ontms` 
 by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i
	       ⇒ j < l``]THEN
 FULL_SIMP_TAC (srw_ss()) [rulesSame] THEN
 `rule (EL i ontms) (NTS nt::rst) ∈ ru0` by METIS_TAC [] THEN
 METIS_TAC []) THEN

SRW_TAC [][] THEN
`EL (LENGTH ontms) (ontms++[ntk]) = ntk` 
by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, 
				       APPEND_ASSOC,NOT_CONS_NIL,CONS] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [r49Elem] THEN SRW_TAC [][] THEN
`rule ntk (NTS nt::rst) ∈ aProdAllRules ntk se NULL (set ru0)` 
 by METIS_TAC [mem_in,  aProdsRulesAllEq] THEN
FULL_SIMP_TAC (srw_ss()) [aProdAllRules_def] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [rulesSame, gnfInv, NULL_EQ_NIL] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [symbol_11, DECIDE ``LENGTH x < LENGTH x + 1``] THEN1
METIS_TAC [symbol_11, DECIDE ``LENGTH x < LENGTH x + 1``] THEN
`LENGTH sl0 < LENGTH sl0 + SUC (LENGTH s)` by DECIDE_TAC THEN
`EL (LENGTH sl0) (sl0++se::s) = se` 
by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, 
	      APPEND_ASSOC,NOT_CONS_NIL,CONS] THEN
`validGnfProd (rule se x)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [validGnfProd] THEN
SRW_TAC [][] THEN
Cases_on `ts` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);


val r49ERtc_ruleInv = store_thm
("r49ERtc_ruleInv",
``∀x y. (r49Elem ntk)^* x y ⇒ 
∀s0 ru0 sl0. 
 (x=(s0,ru0,sl0)) ⇒ (y=(s,ru,sl)) ⇒
¬MEM ntk (s0++sl0) ⇒
¬(ntk ∈ ontms) ⇒
ruleInv ru0 (ontms++[ntk]) (sl0++s0) ⇒
gnfInv ru0 (sl0++s0) ⇒
noeProds ru0 ⇒
ruleInv ru (ontms++[ntk]) (sl++s)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃s1 ru1 sl1. (x' = (s1,ru1,sl1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
 `∃se. (s0 = se::s1) ∧ (sl1 = sl0 ++ [se])` by METIS_TAC [r49Elem] THEN
SRW_TAC [][] THEN
IMP_RES_TAC r49E_ruleInv THEN
IMP_RES_TAC r49E_noeProds THEN
`gnfInv ru1 (sl0 ++ [se] ++ s1)` by METIS_TAC [MEM, MEM_APPEND,r49E_gnfInv] THEN
METIS_TAC [APPEND, APPEND_ASSOC, MEM, MEM_APPEND]);


val gnfAppend = store_thm
("gnfAppend",
``∀l1 l2. gnfInv ru (l1 ++ l2) = gnfInv ru l1 ∧ gnfInv ru l2``,

Induct_on `l1` THEN SRW_TAC [][gnfEqAlt, gnfAlt] THEN
Cases_on `l2` THEN SRW_TAC [][] THEN
SRW_TAC [][EQ_IMP_THM] THEN
METIS_TAC [MEM]);



val fstNtm2Tm_ntmsSubset = store_thm
("fstNtm2Tm_ntmsSubset",
``fstNtm2Tm (ontms0,g0,s0) (ontms,g,s) ⇒
set (ntms g) ⊆ set (ntms g0)``,

SRW_TAC [][fstNtm2Tm] THEN
IMP_RES_TAC r49ERtc_ntmsSubset THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
SRW_TAC [][] THEN
Cases_on `g` THEN Cases_on `g0` THEN FULL_SIMP_TAC (srw_ss()) [rules_def,
							       startSym_def] THEN
SRW_TAC [][]);

val fstNtm2TmRtc_ntmsSubset = store_thm
("fstNtm2TmRtc_ntmsSubset",
``∀x y.fstNtm2Tm^* x y ⇒ 
∀ontms0 g0 s0.
 (x=(ontms0,g0,s0)) ⇒ (y=(ontms,g,s)) ⇒
 set (ntms g) ⊆ set (ntms g0)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃ontms1 g1 s1. (x' = (ontms1,g1,s1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
IMP_RES_TAC fstNtm2Tm_ntmsSubset THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
SRW_TAC [][] THEN
Cases_on `g` THEN Cases_on `g0` THEN FULL_SIMP_TAC (srw_ss()) [rules_def,
							       startSym_def] THEN
SRW_TAC [][]);



val fstNtm2Tm_gnfInv = store_thm
("fstNtm2Tm_gnfInv",
``ALL_DISTINCT (ontms0 ++ s0) ⇒
 ruleInv (rules g0) ontms0 s0 ⇒
 rhsTlNonTms (rules g0) (ntms g0) bs ⇒
 (set s0 ∩ set bs = {}) ⇒
 (set ontms0 ∩ set bs = {}) ⇒
 gnfInv (rules g0) s0 ⇒
 noeProds (rules g0) ⇒
 (set ontms0 ∩ set s0 = {}) ⇒
 fstNtm2Tm (ontms0,g0,s0) (ontms,g,s) ⇒
 gnfInv (rules g) s``,

SRW_TAC [][fstNtm2Tm] THEN
`¬MEM ntk s0` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		  METIS_TAC []) THEN
`gnfInv (rules g) s0` by METIS_TAC [r49ERtc_gnfInv, APPEND_NIL] THEN
`ntk2Tm (rules g0) ntk ([]:α list)` by SRW_TAC [][ntk2Tm] THEN
`ntk2Tm (rules g) ntk s0` by METIS_TAC [r49ERtc_ntk2Tm, MEM, MEM_APPEND, 
					APPEND_NIL] THEN
`rhsTlNonTms (rules g) (ntms g) bs` by 
 (Cases_on `g0` THEN Cases_on `g` THEN
  METIS_TAC [r49ERtc_rhsTlNonTms, rules_def, startSym_def]) THEN
`¬MEM ntk ontms` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
 SRW_TAC [][] THEN
 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND, MEM, MEM_APPEND]) THEN
`noeProds (rules g)` by METIS_TAC [r49ERtc_noeProds] THEN
 `ruleInv (rules g) (ontms++[ntk]) s0` by METIS_TAC [r49ERtc_ruleInv, 
						     APPEND_NIL] THEN
 Q_TAC SUFF_TAC `gnfInv (rules g) [ntk]` THEN1 METIS_TAC [gnfAppend,APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [gnfInv] THEN
SRW_TAC [][] THEN
`i = 0` by DECIDE_TAC THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN


FULL_SIMP_TAC (srw_ss()) [ruleInv, ntk2Tm, validGnfProd, noeProds_def,
			  rhsTlNonTms] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH ontms`] MP_TAC) THEN
SRW_TAC [][] THEN
`(EL (LENGTH ontms) (ontms ++ [ntk])) = ntk` 
by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, 
	      APPEND_ASSOC,NOT_CONS_NIL,CONS] THEN
Cases_on `r`  THEN1 METIS_TAC [] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN1
(
`n ∈ DROP (SUC (LENGTH ontms)) (ontms ++ [ntk]) ∨ n ∈ s0` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
(`SUC (LENGTH ontms) = LENGTH (ontms++[ntk])` 
 by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 METIS_TAC [BUTFIRSTN_LENGTH_APPEND, MEM, APPEND_NIL, APPEND_ASSOC]) THEN
`∃i. i < LENGTH s0 ∧ (EL i s0 =  n)` by METIS_TAC [memImpEl] THEN
 METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
`ntk ∈ (ntms g)` by METIS_TAC [ntmsMem, slemma1_4] THEN
`¬MEM ntk bs` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
		  METIS_TAC []) THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) []);


val fstNtm2Tm_noeProds = store_thm
("fstNtm2Tm_noeProds",
`` noeProds (rules g0) ⇒
 fstNtm2Tm (ontms0,g0,s0) (ontms,g,s) ⇒
 noeProds (rules g)``,

SRW_TAC [][fstNtm2Tm] THEN
METIS_TAC [r49ERtc_noeProds]);


val fstNtm2Tm_ruleInv = store_thm
("fstNtm2Tm_ruleInv",
 ``ALL_DISTINCT (ontms0 ++ s0) ⇒
 gnfInv (rules g0) s0 ⇒
 noeProds (rules g0) ⇒
 ruleInv (rules g0) ontms0 s0 ⇒
 fstNtm2Tm (ontms0,g0,s0) (ontms,g,s) ⇒
 ruleInv (rules g) ontms s``,

SRW_TAC [][fstNtm2Tm] THEN
`¬MEM ntk s0 ∧ ¬MEM ntk ontms`
 by (SPOSE_NOT_THEN ASSUME_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
     SRW_TAC [][] THEN
     Cases_on `MEM ntk s0` THEN
     FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
     SRW_TAC [][] THEN
     FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND] THEN
     METIS_TAC [APPEND, APPEND_ASSOC]) THEN
 IMP_RES_TAC r49ERtc_ruleInv THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`ruleInv (rules g) (ontms ++ [ntk]) s0` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [ruleInv] THEN SRW_TAC [][] THEN
`i < LENGTH ontms + 1` by DECIDE_TAC THEN
`(EL i (ontms ++ [ntk]) = EL i ontms)`
 by METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j ≤ i ⇒ j < l``] THEN
`nt ∈ DROP (SUC i) (ontms ++ [ntk]) ∨ nt ∈ s0` by METIS_TAC [] THEN1
(`SUC i ≤ LENGTH (ontms ++ [ntk])` by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 `nt ∈ (ontms ++ [ntk])` by METIS_TAC [IS_EL_BUTFIRSTN] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [BUTFIRSTN_APPEND1, DECIDE ``i < n ⇒ SUC i ≤ n``, MEM, MEM_APPEND]) THEN
METIS_TAC []);



val fstNtm2Tm_rhsTlNonTms = store_thm
("fstNtm2Tm_rhsTlNonTms",
`` rhsTlNonTms (rules g0) (ntms g0) bs ⇒
(set s0 ∩ set bs = {}) ⇒
 fstNtm2Tm (ontms0,g0,s0) (ontms,g,s) ⇒
rhsTlNonTms (rules g) (ntms g) bs``,

SRW_TAC [][fstNtm2Tm] THEN
IMP_RES_TAC r49ERtc_rhsTlNonTms THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `g0` THEN Cases_on `g` THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def]);


val fstNtm2TmRtc_gnfInv = store_thm
("fstNtm2TmRtc_gnfInv",
 ``∀x y. (fstNtm2Tm)^* x y ⇒ 
∀ontms0 g0 s0.
 (x=(ontms0,g0,s0)) ⇒ (y=(ontms,g,s)) ⇒
 ALL_DISTINCT (ontms0 ++ s0) ⇒
 (set s0 ∩ set bs = {}) ⇒
 (set ontms0 ∩ set bs = {}) ⇒
 (set ontms0 ∩ set bs = {}) ⇒
 (set ontms0 ∩ set s0 = {}) ⇒
 ruleInv (rules g0) ontms0 s0 ⇒
 noeProds (rules g0) ⇒
 rhsTlNonTms (rules g0) (ntms g0) bs ⇒
 gnfInv (rules g0) s0 ⇒
 gnfInv (rules g) s``,


HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃ontms1 g1 s1. (x' = (ontms1,g1,s1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
IMP_RES_TAC fstNtm2Tm_ruleInv THEN
IMP_RES_TAC fstNtm2Tm_noeProds THEN
IMP_RES_TAC fstNtm2Tm_rhsTlNonTms THEN
`gnfInv (rules g1) s1` by METIS_TAC [fstNtm2Tm_gnfInv] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`∃ntk. (ontms0 = ontms1 ++ [ntk]) ∧ (s1 = ntk::s0)` by METIS_TAC [fstNtm2Tm] THEN
SRW_TAC [][] THEN
`ALL_DISTINCT (ontms1 ++ ntk::s0)` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`¬MEM ntk ontms1` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND] THEN
 METIS_TAC [APPEND, APPEND_ASSOC]) THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC [APPEND, APPEND_ASSOC]);

(*

∃g. fstNtm2Tm (ntms g0 - ubs, g0,[]) ([],g,ntms g0-ubs)

gnf (rules g) (ntms g0 - ubs)

∃g'. fstNtm2Tm (ubs, g, []) ([], g', ubs)

gnf (rules g') ubs


ntms g0 = ntms G + ubs
ntms g' = ntms g0

*)

val fstNtm2Tm_equiv = store_thm
("fstNtm2Tm_equiv",
``(set ontms0 ∩ set s0 = {}) ⇒
 fstNtm2Tm (ontms0,g0,s0) (ontms,g,s) ⇒
 (language g0 = language g)``,

SRW_TAC [][fstNtm2Tm] THEN
`¬MEM ntk s0` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN 
		  METIS_TAC []) THEN
Cases_on `g0` THEN Cases_on `g` THEN
METIS_TAC [r49ERtc_equiv, startSym_def, rules_def]);


val fstNtm2Tm_exists = store_thm
("fstNtm2Tm_exists",
 ``∃g. fstNtm2Tm (ontms++[ntk],g0,s0) (ontms,g,ntk::s0)``,

SRW_TAC [][fstNtm2Tm] THEN
Cases_on `g0` THEN
METIS_TAC [r49ERtc_exists, startSym_def, rules_def, APPEND_NIL]);


val fstNtm2TmRtc_exists = store_thm
("fstNtm2TmRtc_exists",
 ``∀ontms0 g0 s0.
 ∃g. (fstNtm2Tm)^* (ontms0,g0,s0) ([],g,ontms0++s0)``,

HO_MATCH_MP_TAC SNOC_INDUCT THEN SRW_TAC [][SNOC_APPEND] THEN1
METIS_TAC [RTC_RULES] THEN
SRW_TAC [][Once RTC_CASES1] THEN

`∃g. fstNtm2Tm (ontms0 ++ [x],g0,s0) (ontms0,g,x::s0)` 
 by METIS_TAC [fstNtm2Tm_exists] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`g`,`x::s0`] MP_TAC) THEN SRW_TAC [][] THEN
Q.EXISTS_TAC `g'` THEN
Q.EXISTS_TAC `(ontms0,g,x::s0)` THEN
METIS_TAC [APPEND_ASSOC, APPEND]);


val fstNtm2TmRtc_equiv = store_thm
("fstNtm2TmRtc_equiv",
``∀x y. (fstNtm2Tm)^* x y ⇒ 
∀ontms0 g0 s0.
 (x=(ontms0,g0,s0)) ⇒ (y=(ontms,g,s)) ⇒ 
(set ontms0 ∩ set s0 = {}) ⇒
ALL_DISTINCT (ontms0 ++ s0) ⇒
 (language g0 = language g)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃ontms1 g1 s1. (x' = (ontms1,g1,s1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
`∃ntk. (ontms0 = ontms1 ++ [ntk]) ∧ (s1 = ntk::s0)` by METIS_TAC [fstNtm2Tm] THEN
SRW_TAC [][] THEN
`¬MEM ntk ontms1` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [ALL_DISTINCT_APPEND] THEN
 METIS_TAC [APPEND, APPEND_ASSOC]) THEN
`(set ontms1 ∩ set (ntk::s0) = {})` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
					METIS_TAC []) THEN
`ALL_DISTINCT (ontms1 ++ ntk::s0)` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
METIS_TAC [fstNtm2Tm_equiv]);


val fstNtm2Tm_rhsBNonTms = store_thm
("fstNtm2Tm_rhsBNonTms",
``rhsBNonTms (rules g0) ubs ⇒
(set ontms0 ∩ set ubs = {}) ⇒
fstNtm2Tm (ontms0,g0,s0) (ontms,g,s) ⇒
rhsBNonTms (rules g) ubs``,

SRW_TAC [][fstNtm2Tm] THEN
IMP_RES_TAC r49ERtc_rhsBNonTms THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`¬MEM ntk ubs` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []) THEN
METIS_TAC []);


val fstNtm2TmRtc_rhsBNonTms = store_thm
("fstNtm2TmRtc_rhsBNonTms",
``∀x y. fstNtm2Tm^* x y ⇒ 
 ∀ontms0 g0 s0. (x=(ontms0,g0,s0)) ⇒ (y=(ontms,g,s)) ⇒
 rhsBNonTms (rules g0) ubs ⇒
 (set ontms0 ∩ set ubs = {}) ⇒
 rhsBNonTms (rules g) ubs``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃ontms1 g1 s1. (x' = (ontms1,g1,s1))` by METIS_TAC [exists_triple] THEN
SRW_TAC [][] THEN
`∃ntk. (ontms0 = ontms1 ++ [ntk]) ∧ (s1 = ntk::s0)` by METIS_TAC [fstNtm2Tm] THEN
SRW_TAC [][] THEN
IMP_RES_TAC fstNtm2Tm_rhsBNonTms THEN
 FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN METIS_TAC []);


(***********************************************************************************)
(* Transformation of B rules *)
(***********************************************************************************)

val fstNtm2TmBrules = Define
`fstNtm2TmBrules (ubs0,ontms0,g0,seen0) (ubs,ontms,g,seen) = 
∃b rules0. (ubs0 = b::ubs) ∧ (ontms0 = ontms) ∧ (seen = seen0++[b]) ∧ 
(rules0 = aProdsRules b ontms  (set (rules g0))) ∧
(set (rules g) = (rules0)) ∧
(startSym g = startSym g0)`;

val fstNtm2TmBrules_ntmsSubset = store_thm
("fstNtm2TmBrules_ntmsSubset",
``fstNtm2TmBrules (ubs0,ontms0,g0,s0) (ubs,ontms,g,s) ⇒
set (ntms g) ⊆ set (ntms g0)``,

SRW_TAC [][fstNtm2TmBrules, SUBSET_DEF] THEN
FULL_SIMP_TAC (srw_ss()) [ntmsMem] THEN
IMP_RES_TAC slemma1_4 
THENL[
      `rule x rhs ∈  aProdsRules b ontms (set (rules g0))` 
      by METIS_TAC [mem_in] THEN
      FULL_SIMP_TAC (srw_ss()) [aProdsRules_def] THEN SRW_TAC [][] THEN
      METIS_TAC [slemma1_4, startSym_def, rules_def],

      `rule l (p ++ [NTS x] ++ s) ∈ aProdsRules b ontms (set (rules g0))`
      by METIS_TAC [mem_in] THEN
      FULL_SIMP_TAC (srw_ss()) [aProdsRules_def] THEN SRW_TAC [][] THEN1
      METIS_TAC [slemma1_4, symbol_11, startSym_def, rules_def] THEN
      `x' ++ s' = p ++ [NTS x] ++ s` by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL,rules_def,
		 startSym_def] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, rules_def,
		 startSym_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      IMP_RES_TAC twoListAppEq THEN SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def] THEN1
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def] THEN
      Cases_on `s1'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [slemma1_4, ntmsMem, symbol_11, APPEND_NIL, APPEND,
		 APPEND_ASSOC, rules_def, startSym_def],

      METIS_TAC [slemma1_4, startSym_def, rules_def, startSym_def]
      ]);


val fstNtm2TmBrulesRtc_ntmsSubset = store_thm
("fstNtm2TmBrulesRtc_ntmsSubset",
``∀x y.fstNtm2TmBrules^* x y ⇒ 
∀ubs0 ontms0 g0 s0.
 (x=(ubs0,ontms0,g0,s0)) ⇒ (y=(ubs,ontms,g,s)) ⇒
 set (ntms g) ⊆ set (ntms g0)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃ubs1 ontms1 g1 s1. (x' = (ubs1,ontms1,g1,s1))` by METIS_TAC [exists_quad] THEN
SRW_TAC [][] THEN
IMP_RES_TAC fstNtm2TmBrules_ntmsSubset THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
SRW_TAC [][] THEN
Cases_on `g` THEN Cases_on `g0` THEN FULL_SIMP_TAC (srw_ss()) [rules_def,
							       startSym_def] THEN
SRW_TAC [][]);


val rhsBoldNonTms = Define
`rhsBoldNonTms ru ontms ubs = 
∀B. B ∈ ubs ⇒ 
∀r. rule B r ∈ ru ⇒
EVERY isNonTmnlSym r ∧ r ≠ [] ∧
∃nt. (HD r = NTS nt) ∧ nt ∈ ontms`;

val rhsBNonTmsImpOld = store_thm
("rhsBNonTmsImpOld",
``rhsBNonTms ru ubs ∧ (set (ntms (G ru s)) ⊆ set (ontms ++ ubs)) ∧ 
(set ontms ∩ set ubs = {}) ⇒
rhsBoldNonTms ru ontms ubs``,

SRW_TAC [][rhsBNonTms, rhsBoldNonTms] THEN
RES_TAC THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
METIS_TAC [slemma1_4, APPEND, APPEND_NIL, APPEND_ASSOC, ntmsMem, symbol_11,
	   startSym_def, rules_def]);


val aProdsRules_gnfInv = store_thm
("aProdsRules_gnfInv",
``rhsBoldNonTms ru0 ontms (b::ubs) ⇒
gnfInv (rules (G ru0 s)) (ontms ++ seen0) ⇒
(set ru = aProdsRules b ontms (set ru0)) ⇒
gnfInv (rules (G ru s)) (ontms ++ seen0 ++ [b])``,

SRW_TAC [][gnfInv, rules_def] THEN
`rule (EL i (ontms ++ seen0 ++ [b])) r ∈ aProdsRules b ontms (set ru0)`
by METIS_TAC [mem_in] THEN
`i < LENGTH ontms + LENGTH seen0 ∨ (i = LENGTH ontms + LENGTH seen0)`
by DECIDE_TAC THEN1
(`LENGTH (ontms ++ seen0 ++ [b]) = LENGTH ontms + LENGTH seen0 + 1`
 by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 `LENGTH (ontms ++ seen0) = LENGTH ontms + LENGTH seen0 `
 by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
 `LENGTH ontms + LENGTH seen0 < LENGTH ontms + LENGTH seen0 + 1` by DECIDE_TAC THEN
 `EL i (ontms ++ seen0 ++ [b]) = EL i (ontms ++ seen0)` by 
 METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j < i ⇒ j < l``, APPEND,
	    APPEND_ASSOC] THEN
 FULL_SIMP_TAC (srw_ss()) [aProdsRules_def] THEN
 SRW_TAC [][] THEN
`∃ib. ib < LENGTH ontms ∧ (EL ib ontms = B)` by METIS_TAC [memImpEl] THEN
`ib < LENGTH ontms + LENGTH seen0` by DECIDE_TAC THEN
 `EL ib (ontms ++ seen0) = EL ib ontms` by 
 METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j < i ⇒ j < l``, APPEND,
	    APPEND_ASSOC] THEN
`validGnfProd (rule (EL ib ontms) x)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [validGnfProd] THEN
SRW_TAC [][] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) []) THEN

`LENGTH (ontms ++ seen0) = LENGTH ontms + LENGTH seen0` by SRW_TAC [][] THEN
 `EL i (ontms ++ seen0 ++ [b]) = b` 
 by METIS_TAC [EL_LENGTH_APPEND, NULL_EQ_NIL, HD,APPEND, 
	       APPEND_ASSOC,NOT_CONS_NIL,CONS] THEN
 FULL_SIMP_TAC (srw_ss()) [aProdsRules_def, NULL_EQ_NIL] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [rhsBoldNonTms] THEN
RES_TAC THEN1
(`EVERY isNonTmnlSym r ∧ r ≠ [] ∧
 ∃nt. (HD r = NTS nt) ∧ nt ∈ ontms` by METIS_TAC [] THEN
 Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) []) THEN

`EVERY isNonTmnlSym (NTS B::s) ∧ (NTS B::s) ≠ [] ∧
∃nt. (HD (NTS B::s) = NTS nt) ∧ nt ∈ ontms` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
`∃ib. ib < LENGTH ontms ∧ (EL ib ontms = B)` by METIS_TAC [memImpEl] THEN
`ib < LENGTH ontms + LENGTH seen0` by DECIDE_TAC THEN
 `EL ib (ontms ++ seen0) = EL ib ontms` by 
 METIS_TAC [EL_APPEND1, DECIDE ``i < l ∧ j < i ⇒ j < l``, APPEND,
	    APPEND_ASSOC] THEN
`validGnfProd (rule (EL ib ontms) x)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [validGnfProd]);


val fstNtm2TmBrules_rulesSame = store_thm
("fstNtm2TmBrules_rulesSame",
``ALL_DISTINCT ubs0 ⇒
fstNtm2TmBrules (ubs0,ontms0,g0,seen0) (ubs,ontms,g,seen) ⇒
rulesSame (rules g0) (rules g) ubs``,

SRW_TAC [][rulesSame, fstNtm2TmBrules, EQ_IMP_THM] THEN
`¬MEM b ubs` by
(SPOSE_NOT_THEN ASSUME_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]  THEN
 METIS_TAC [APPEND, APPEND_ASSOC, ALL_DISTINCT_APPEND]) THEN1
(SPOSE_NOT_THEN ASSUME_TAC THEN
`¬(rule (EL i ubs) r ∈ aProdsRules b ontms (set (rules g0)))` 
by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [aProdsRules_def] THEN
SRW_TAC [][] THEN
METIS_TAC [EL_IS_EL]) THEN
`(rule (EL i ubs) r ∈ aProdsRules b ontms (set (rules g0)))` 
by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [aProdsRules_def] THEN
SRW_TAC [][] THEN
METIS_TAC [EL_IS_EL]);


val fstNtm2TmBrules_rhsBoldNonTms = store_thm
("fstNtm2TmBrules_rhsBoldNonTms",
`` ALL_DISTINCT ubs0 ⇒
 rhsBoldNonTms (rules g0) ontms0 ubs0 ⇒
 gnfInv (rules g0) (ontms ++ seen0) ⇒
 fstNtm2TmBrules (ubs0,ontms0,g0,seen0) (ubs,ontms,g,seen) ⇒
 rhsBoldNonTms (rules g) ontms0 ubs``,

SRW_TAC [][] THEN
IMP_RES_TAC fstNtm2TmBrules_rulesSame THEN
FULL_SIMP_TAC (srw_ss()) [fstNtm2TmBrules, rhsBoldNonTms, rulesSame] THEN
SRW_TAC [][] THEN
`rule B r ∈ aProdsRules b ontms (set (rules g0))` by METIS_TAC [mem_in] THEN
FULL_SIMP_TAC (srw_ss()) [aProdsRules_def, gnfInv] THEN
SRW_TAC [][] THEN
METIS_TAC []);


val fstNtm2TmBrules_gnfInv = store_thm
("fstNtm2TmBrules_gnfInv",
``rhsBoldNonTms (rules g0) ontms0 ubs0 ⇒
gnfInv (rules g0) (ontms0 ++ seen0) ⇒
fstNtm2TmBrules (ubs0,ontms0,g0,seen0) (ubs,ontms,g,seen) ⇒
gnfInv (rules g) (ontms ++ seen)``,

SRW_TAC [][fstNtm2TmBrules] THEN
IMP_RES_TAC aProdsRules_gnfInv THEN
FULL_SIMP_TAC (srw_ss()) [rules_def]);


val fstNtm2TmBrulesRtc_gnfInv = store_thm
("fstNtm2TmBrulesRtc_gnfInv",
``∀x y. fstNtm2TmBrules^* x y ⇒ 
∀ubs0 ontms0 g0 seen0.
 (x=(ubs0,ontms0,g0,seen0)) ⇒
 (y = (ubs,ontms,g,seen)) ⇒
 ALL_DISTINCT ubs0 ⇒
 rhsBoldNonTms (rules g0) ontms0 ubs0 ⇒
 gnfInv (rules g0) (ontms0 ++ seen0) ⇒
 gnfInv (rules g) (ontms ++ seen)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃ubs1 ontms1 g1 seen1.(x'=(ubs1, ontms1,g1,seen1))` by METIS_TAC [exists_quad] THEN
SRW_TAC [][] THEN
`∃b. (ubs0 = b::ubs1) ∧ (ontms0 = ontms1) ∧
 (seen1 = seen0 ++ [b])` by METIS_TAC [fstNtm2TmBrules] THEN
SRW_TAC [][] THEN
IMP_RES_TAC fstNtm2TmBrules_gnfInv THEN
IMP_RES_TAC fstNtm2TmBrules_rhsBoldNonTms THEN
FULL_SIMP_TAC (srw_ss()) []);


val fstNtm2TmBrules_equiv = store_thm
("fstNtm2TmBrules_equiv",
``(set ubs0 ∩ set ontms0 = {}) ⇒
fstNtm2TmBrules (ubs0,ontms0,g0,seen0) (ubs,ontms,g,seen) ⇒
(language g0 = language g)``,

SRW_TAC [][fstNtm2TmBrules] THEN
`aProds b ontms g0 g` by (SRW_TAC [][aProds_def] THEN
			       FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
			       METIS_TAC []) THEN
METIS_TAC [lemma4_3Gen]);

val fstNtm2TmBrulesRtc_equiv = store_thm
("fstNtm2TmBrulesRtc_equiv",
``∀x y. fstNtm2TmBrules^* x y ⇒
∀ubs0 ontms0 g0 seen0.
 (x=(ubs0,ontms0,g0,seen0)) ⇒ (y=(ubs,ontms,g,seen)) ⇒
(set ubs0 ∩ set ontms0 = {}) ⇒
(language g0 = language g)``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN
`∃ubs1 ontms1 g1 seen1.(x'=(ubs1, ontms1,g1,seen1))` by METIS_TAC [exists_quad] THEN
SRW_TAC [][] THEN
`∃b. (ubs0 = b::ubs1) ∧ (ontms0 = ontms1) ∧
 (seen1 = seen0 ++ [b])` by METIS_TAC [fstNtm2TmBrules] THEN
SRW_TAC [][] THEN
IMP_RES_TAC fstNtm2TmBrules_equiv THEN
FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC []);

val fstNtm2TmBrules_exists = store_thm
("fstNtm2TmBrules_exists",
``∃u. fstNtm2TmBrules (b::ubs0,ontms0,g0,seen0) u ∧
∃g.(u=(ubs0,ontms0,g,seen0++[b]))``,

SRW_TAC [][] THEN
Q.ABBREV_TAC `ru = aProdsRules b ontms0 (set (rules g0))` THEN
`FINITE ru` by METIS_TAC [FINITE_LIST_TO_SET, finiteaProdsRules] THEN
`∃r.set r = ru` by METIS_TAC [listExists4Set] THEN
Q.EXISTS_TAC `(ubs0,ontms0,G r (startSym g0), seen0++[b])` THEN
SRW_TAC [][fstNtm2TmBrules, rules_def, startSym_def]);


val fstNtm2TmBrulesRtc_exists = store_thm
("fstNtm2TmBrulesRtc_exists",
``∀ubs0 ontms0 g0 seen0.
 ∃g. fstNtm2TmBrules^* (ubs0,ontms0,g0,seen0) ([],ontms0,g,seen0++ubs0)``,

Induct_on `ubs0` THEN SRW_TAC [][] THEN1
METIS_TAC [RTC_RULES] THEN
`∃u. fstNtm2TmBrules (h::ubs0,ontms0,g0,seen0) u ∧
 ∃g. u = (ubs0,ontms0,g,seen0 ++ [h])` by METIS_TAC [fstNtm2TmBrules_exists] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`ontms0`,`g`,`seen0++[h]`] MP_TAC) THEN
 SRW_TAC [][] THEN
METIS_TAC [APPEND, APPEND_ASSOC, RTC_RULES]);

val ugImpcnf = store_thm
("ugImpcnf",
 ``usefulnts g0 g1 ∧ isCnf g0 ⇒ isCnf g1``,

Cases_on `g0` THEN
SRW_TAC [][usefulnts_def, startSym_def, rules_def] THEN
FULL_SIMP_TAC (srw_ss()) [isCnf_def, rules_def] THEN
SRW_TAC [][] THEN
METIS_TAC []);


val isGnfgnfInvEq = store_thm
("isGnfgnfInvEq",
``isGnf g ⇔ gnfInv (rules g) (ntms g)``,

SRW_TAC [][isGnf, gnfInv, EQ_IMP_THM]  THEN1
METIS_TAC [EVERY_DEF, EVERY_APPEND, rgr_r9eq] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
`∃r. r ∈ rules g ∧ ¬ validGnfProd r` by METIS_TAC [EVERY_MEM] THEN
Cases_on `r`  THEN
`n ∈ (ntms g)` by METIS_TAC [slemma1_4, ntmsMem] THEN
METIS_TAC [memImpEl]);


val isGnfgnfInvImpSub = store_thm
("isGnfgnfInvImpSub",
``(set (ntms g) ⊆ set l) ⇒ (gnfInv (rules g) l ⇒ isGnf g)``,

SRW_TAC [][isGnf, gnfInv]  THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
`∃e. e ∈ (rules g) ∧ ¬ validGnfProd e` by METIS_TAC [EVERY_MEM] THEN
Cases_on `e` THEN
METIS_TAC [slemma1_4, ntmsMem, startSym_def, rules_def, memImpEl]);


val rhsBImpoldNtms = store_thm
("rhsBImpoldNtms",
``(set (ntms (G ru1 s)) ⊆ set ontms0 ∪ set ubs) ∧
rhsBNonTms (ru1) ubs ∧
(set ontms0 ∩ set ubs = {}) ⇒
rhsBoldNonTms ru1 ontms0 ubs``,

SRW_TAC [][rhsBoldNonTms, rhsBNonTms] THEN
RES_TAC THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
METIS_TAC [slemma1_4, APPEND_NIL, APPEND, APPEND_ASSOC, ntmsMem, rules_def,
	   startSym_def]);

val rhsTlNonTmsImpRuleInv = store_thm
("rhsTlNonTmsImpRuleInv",
``rhsTlNonTms ru1 (ntms (G ru1 s)) ubs ∧ 
(set (ntms (G ru1 s)) ⊆ set ontms0 ∪ set ubs) ∧
seenInv (ru1) ontms0 ∧
(set ontms0 ∩ set ubs = {}) ⇒
ruleInv (ru1) ontms0 ([]:α list)``,

SRW_TAC [][ruleInv] THEN
FULL_SIMP_TAC (srw_ss()) [rhsTlNonTms] THEN
`EL i ontms0 ∈ ntms (G ru1 s)` by 
METIS_TAC [slemma1_4, ntmsMem, APPEND,startSym_def, rules_def,
	   APPEND_NIL, APPEND_ASSOC] THEN
`¬(EL i ontms0 ∈ ubs)` by (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
			 METIS_TAC [EL_IS_EL]) THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
`nt ∈ ontms0` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [seenInv] THEN
`∃i. i < LENGTH ontms0 ∧ (EL i ontms0 = nt)` by METIS_TAC [memImpEl] THEN
`∀j. j ≤ i ⇒ EL j ontms0 ≠ nt` by METIS_TAC [] THEN
METIS_TAC [elDrop]);


val gnfExists = store_thm
("gnfExists",
``∀g:('a, 'b) grammar. 
 INFINITE (UNIV:'a set) ∧ 
 [] ∉ language g ∧
 language g ≠ {}  ⇒ 
 ∃g'.isGnf g' ∧ (language g = language g')``,

SRW_TAC [][] THEN
`∃cg. isCnf cg ∧ (language g = language cg)` by METIS_TAC [cnfisCnfEq, thm4_5,
							    eqLang_def] THEN
 `∃ug. usefulnts cg ug ∧ (language cg = language ug)` by
METIS_TAC [use_exists, lemma4_1a] THEN
`isCnf ug` by METIS_TAC [ugImpcnf] THEN
`noeProds (rules ug)` by METIS_TAC [isCnfImpnoeProds] THEN
`ALL_DISTINCT (ntms ug)` by METIS_TAC [rmDupesImpAllD, ntms_def] THEN

 `∃bs0.ALL_DISTINCT bs0 ∧ (LENGTH bs0 ≥ LENGTH (ntms ug)) ∧
 (set (ntms ug) ∩ set bs0 = {})` by METIS_TAC [allDistinctNewlist,
					       FINITE_LIST_TO_SET] THEN

`set (ntms ug) ∩ set ([]:'a list) = {}` by SRW_TAC [][] THEN

`seenInv (rules ug) ([]:'a list)` by SRW_TAC [][seenInv] THEN

`(set bs0 ∩ set ([]:α list) = {})` by SRW_TAC [][] THEN

`∃g1.(r49)^* (bs0, ntms ug, ug, ([]:'a list), ([]:'a list)) 
 (DROP (LENGTH (ntms ug)) bs0, ([]:'a list), g1,ntms ug, 
  TAKE (LENGTH (ntms ug)) bs0) ∧
 (language ug = language g1)`
 by METIS_TAC [r49Rtc_exists, r49Rtc_equiv, APPEND_NIL] THEN


Q.ABBREV_TAC `s0 = []:α list` THEN
Q.ABBREV_TAC `ubs0 = []:α list` THEN
Q.ABBREV_TAC `nts0 = ntms ug` THEN
Q.ABBREV_TAC `ubs = TAKE (LENGTH (ntms ug)) bs0` THEN

`set (ntms g1) ⊆ set (ntms ug) ∪ set ubs` by METIS_TAC [r49Rtc_ntmsSubset] THEN

`rhsTlNonTms (rules ug) (ntms ug) ubs0` by METIS_TAC [isCnfImprhsTlNonTmnls] THEN

`set bs0 ∩ set ubs0 = {}` by SRW_TAC [][] THEN
`set s0 ∩ set ubs0 = {}` by SRW_TAC [][] THEN
`set s0 ∩ set bs0 = {}` by METIS_TAC [INTER_COMM] THEN
`set nts0 ∩ set ubs0 = {}` by SRW_TAC [][] THEN

`rhsTlNonTms (rules g1) (ntms g1) ubs` by METIS_TAC [r49Rtc_rhsTlNonTms] THEN

IMP_RES_TAC r49Rtc_rhsBNonTms THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(set (ntms ug) ∩ set bs0 = {})` by METIS_TAC [] THEN
`rhsTlNonTms (rules ug) (ntms ug) []` by METIS_TAC [] THEN
`rhsBNonTms (rules ug) []` by SRW_TAC [][rhsBNonTms] THEN
`(set nts0 ∩ (set s0 ∪ set bs0) = {})` by METIS_TAC [UNION_EMPTY,
						     LIST_TO_SET_THM] THEN

`rhsBNonTms (rules g1) ubs` by METIS_TAC [] THEN

`noeProds (rules g1)` by METIS_TAC [r49Rtc_noeProds] THEN

`seenInv (rules g1) (ntms ug)` by METIS_TAC [r49Rtc_seenInv] THEN

`∃g2. fstNtm2Tm^* (ntms ug,g1,[]:α list) ([],g2,ntms ug) ∧
 (language ug = language g2)` by METIS_TAC [fstNtm2TmRtc_exists,
					    fstNtm2TmRtc_equiv, APPEND_NIL] THEN

`set (ntms g2) ⊆ set (ntms g1)` by METIS_TAC [fstNtm2TmRtc_ntmsSubset] THEN

`gnfInv (rules g1) ([]:α list)` by SRW_TAC [][gnfInv] THEN

Q.ABBREV_TAC `ontms0 = ntms ug` THEN
Q.ABBREV_TAC `ontms = []:α list` THEN
Q.ABBREV_TAC `s = ntms ug` THEN

`set s0 ∩ set ubs = {}` by METIS_TAC [INTER_EMPTY, LIST_TO_SET_THM] THEN
`set ontms0 ∩ set s0 = {}` by SRW_TAC [][] THEN

`LENGTH nts0 ≤ LENGTH bs0` by DECIDE_TAC THEN
`set ubs ⊆ set bs0` by METIS_TAC [takeSubset] THEN
`set ontms0 ∩ set ubs = {}` by 
(FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF, EXTENSION] THEN
 METIS_TAC []) THEN
`ruleInv (rules g1) ontms0 ([]:α list)` by 
(Cases_on `g1` THEN 
 METIS_TAC [rhsTlNonTmsImpRuleInv,
	    startSym_def, rules_def]) THEN
`gnfInv (rules g1) ([]:α list)` by SRW_TAC [][gnfInv] THEN
`ALL_DISTINCT (ontms0 ++ ([]:α list))` by FULL_SIMP_TAC (srw_ss()) [] THEN

`gnfInv (rules g2) (ntms ug)` by METIS_TAC [fstNtm2TmRtc_gnfInv, INTER_EMPTY,
					    LIST_TO_SET_THM] THEN

`ALL_DISTINCT (ubs ++ [])` by METIS_TAC [allDTake, APPEND_NIL] THEN
`set ubs ∩ set [] = {}` by SRW_TAC [][] THEN

`∃g3. fstNtm2TmBrules^* (ubs,ntms ug,g2,[]) ([],ntms ug,g3,ubs)`
by METIS_TAC [fstNtm2TmBrulesRtc_exists, APPEND_NIL] THEN

`(set ubs ∩ set (ntms ug) = {})` by METIS_TAC [INTER_COMM] THEN
`language g2 = language g3` by METIS_TAC [fstNtm2TmBrulesRtc_equiv] THEN

`set (ntms g3) ⊆ set (ntms g2)` 
by METIS_TAC [fstNtm2TmBrulesRtc_ntmsSubset] THEN


`set (ntms g3) ⊆ set (ntms ug) ∪ set ubs`  
by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
    METIS_TAC []) THEN

`set (ntms g2) ⊆ set (ntms ug) ∪ set ubs`  
by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
    METIS_TAC []) THEN

`rhsBNonTms (rules g2) ubs` by METIS_TAC [fstNtm2TmRtc_rhsBNonTms] THEN

`set ubs ∩ set [] = {}` by SRW_TAC [][] THEN

`rhsBNonTms (rules g2) ubs` by METIS_TAC [fstNtm2TmRtc_rhsBNonTms] THEN

`rhsBoldNonTms (rules g2) (ntms ug) ubs` 
by (Cases_on `g2` THEN METIS_TAC [rhsBImpoldNtms, startSym_def, rules_def]) THEN

IMP_RES_TAC fstNtm2TmRtc_gnfInv THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(set (ntms ug) ∩ set ubs = {})` by METIS_TAC [] THEN


`gnfInv (rules g2) []` by SRW_TAC [][gnfInv] THEN

`gnfInv (rules g2) (ntms ug)` by METIS_TAC [fstNtm2TmRtc_gnfInv] THEN

`gnfInv (rules g3) ((ntms ug) ++ ubs)` by METIS_TAC [fstNtm2TmBrulesRtc_gnfInv,
						    APPEND_NIL] THEN

IMP_RES_TAC fstNtm2TmBrulesRtc_ntmsSubset THEN
FULL_SIMP_TAC (srw_ss()) [] THEN

`set (ntms g3) ⊆ set ((ntms ug) ++ ubs)` 
by (FULL_SIMP_TAC (srw_ss()) [EXTENSION, SUBSET_DEF] THEN
    METIS_TAC []) THEN

Q.EXISTS_TAC `g3` THEN
METIS_TAC [isGnfgnfInvImpSub]);


val _ = export_theory ();









