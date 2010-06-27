open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory arithmeticTheory


open listLemmasTheory relationLemmasTheory grammarDefTheory
     arithmeticLemmasTheory symbolDefTheory cnfTheory parseTreeTheory
     treeDerivTheory containerLemmasTheory

val _ = new_theory "pumpingLemmaTree";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1


val treeSyms_defn = Hol_defn "treeSyms_defn"
`(treeSyms (Leaf tm) =  ([TS tm]:(α,β) symbol list)) ∧
(treeSyms (Node n t) =  (NTS n) :: (FLAT (MAP treeSyms t)))`;

val (treeSyms, treeSyms_ind) = tprove (treeSyms_defn,
WF_REL_TAC (`measure ptsize`) THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ptsizel_append] THEN
DECIDE_TAC);

val distinctNtms = Define
`distinctNtms t = rmDupes (FILTER isNonTmnlSym (treeSyms t))`;

val subtree = Define
`(subtree (Leaf tm) (p::ps) = NONE) ∧
(subtree t [] = SOME t) ∧
(subtree (Node n ptl) (p::ps) = 
 if (p < LENGTH ptl) then
     subtree (EL p ptl) ps else NONE)`;

val subtPathNil = store_thm
("subtPathNil",
``(subtree t [] = SOME t1) ⇔ (t = t1)``,

Cases_on `t` THEN SRW_TAC [][subtree]);

val _ = export_rewrites ["subtPathNil"];


val isSubtree = Define
`isSubtree st t = ∃p. p ≠ [] ∧ (subtree t p = SOME st)`;

val isSubtreeEq = Define
`isSubtreeEq st t =  ∃p.(subtree t p = SOME st)`;

val allTms = Define
`allTms ptl = isWord (MAP root ptl)`;

val btree = Define
`btree B st t = (root st = B) ∧  isSubtree st t`;

val rootRep = Define
`rootRep st t = (root st = root t) ∧  isSubtree st t`;


val symRepProp = Define
`symRepProp t0 t1 t = isSubtreeEq t1 t ∧ rootRep t0 t1`;


val lastExpProp = Define
`lastExpProp t = 
∃t0 t1. symRepProp t0 t1 t ∧ 
∃n ptl.(t1 = Node n ptl) ∧ 
(∀e. e ∈ ptl ⇒ ¬∃st0 st1. symRepProp st0 st1 e)`;



val subtreeApp = store_thm
("subtreeApp",
``∀t t1 p p'.
 (subtree t p = SOME t1) ∧ (subtree t1 p' = SOME t0) ⇒
 (subtree t (p++p') = SOME t0)``,

Induct_on `p` THEN SRW_TAC [][] THEN
Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < LENGTH l` THEN FULL_SIMP_TAC (srw_ss()) []);


val subtreeTrans = store_thm 
("subtreeTrans",
``∀t0 t1 t. isSubtree t1 t ∧ isSubtree t0 t1 ⇒ isSubtree t0 t``,

FULL_SIMP_TAC (srw_ss()) [isSubtree] THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `p ++ p'` THEN
SRW_TAC [][] THEN
METIS_TAC [subtreeApp]);


val subtreeEqTrans = store_thm 
("subtreeEqTrans",
``∀t0 t1 t. isSubtreeEq t1 t ∧ isSubtreeEq t0 t1 ⇒ isSubtreeEq t0 t``,

FULL_SIMP_TAC (srw_ss()) [isSubtreeEq] THEN
SRW_TAC [][] THEN
Q.EXISTS_TAC `p ++ p'` THEN
SRW_TAC [][] THEN
METIS_TAC [subtreeApp]);

val subtImpisSubt = store_thm
("subtImpisSubt",
``∀t p t1. (subtree t p = SOME t1) ∧ p ≠ [] ⇒ isSubtree t1 t``,

Induct_on `p` THEN SRW_TAC [][subtree] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [subtree, isSubtree] THEN
Cases_on `h < LENGTH l` THEN FULL_SIMP_TAC (srw_ss())[] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN1
(Cases_on `EL h l` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
 SRW_TAC [][] THEN
 Q.EXISTS_TAC `[h]` THEN
 SRW_TAC [][subtree]) THEN

FIRST_X_ASSUM (Q.SPECL_THEN [`EL h l`, `t1`] MP_TAC) THEN SRW_TAC [][] THEN
Q.EXISTS_TAC `h::h'::t` THEN
SRW_TAC [][subtree]);


val subtreeNotSymProp = store_thm
("subtreeNotSymProp",
``(subtree t p = SOME t1) ∧ (¬∃s0 s1. symRepProp s0 s1 t) ⇒
 ¬∃s0 s1. symRepProp s0 s1 t1``,

SRW_TAC [][symRepProp] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN 
FULL_SIMP_TAC (srw_ss()) [btree] THEN
`isSubtreeEq t1 t` by METIS_TAC [isSubtreeEq, option_CLAUSES] THEN
METIS_TAC [subtreeEqTrans,root_def, isSubtree, root_def, isSubtreeEq]);


val isSubEqImpSub = store_thm
("isSubEqImpSub",
``isSubtreeEq t1 t ⇔ (t1 = t) ∨ isSubtree t1 t``,

SRW_TAC [][isSubtree, isSubtreeEq, EQ_IMP_THM] THEN1

(Cases_on `t` THEN Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < LENGTH l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
DISJ2_TAC THEN
Q.EXISTS_TAC `h::t` THEN
SRW_TAC [][subtree]) THEN1

(Cases_on `t` THEN METIS_TAC [subtree]) THEN

METIS_TAC []);

 

val subtreeLastExp = store_thm
("subtreeLastExp",
``∀t t1. lastExpProp t1 ∧ isSubtree t1 t ⇒
 lastExpProp t``,

SRW_TAC [][isSubtree, lastExpProp, isSubEqImpSub] THEN
FULL_SIMP_TAC (srw_ss()) [symRepProp, btree] THEN

FULL_SIMP_TAC (srw_ss()) [isSubEqImpSub] THEN
SRW_TAC [][] THEN

(MAP_EVERY Q.EXISTS_TAC [`t0`,`Node n ptl`] THEN
FULL_SIMP_TAC (srw_ss()) [root_def] THEN
SRW_TAC [][] THEN
METIS_TAC [isSubtree, subtreeTrans, option_CLAUSES,root_def]));


val subtreeHeight = store_thm
("subtreeHeight",
``∀t p t1. (subtree t p = SOME t1) ∧ p ≠ [] ⇒ height t1 < height t``,

Induct_on `p` THEN SRW_TAC [][] THEN
Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < LENGTH l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`EL h l`, `t1`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

(Cases_on `EL h l` THEN
FULL_SIMP_TAC (srw_ss()) [subtree, height_def] THEN
SRW_TAC [][height_def] THEN
`MEM (EL h l) l` by METIS_TAC [EL_IS_EL] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [][height_def] THEN1
DECIDE_TAC  THEN
Q.ABBREV_TAC `n = max 0 (MAP (λa. height a) l')` THEN
METIS_TAC [maxGtElem, MEM, MEM_APPEND, DECIDE ``1 + n > n``]) THEN

SRW_TAC [][height_def] THEN
`MEM (EL h l) l` by METIS_TAC [EL_IS_EL] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [][height_def] THEN
`height (EL h l) > height t1` by DECIDE_TAC THEN
METIS_TAC [maxGtElem, MEM, MEM_APPEND, DECIDE ``a < b ⇒ a < 1 + b``]);


val symPropImpLastExp = store_thm
("symPropImpLastExp",
``∀t t0 t1. symRepProp t0 t1 t ⇒ lastExpProp t``,

completeInduct_on `height t` THEN
SRW_TAC [][] THEN
Cases_on `t` THEN1
(FULL_SIMP_TAC (srw_ss()) [lastExpProp, symRepProp, isSubtreeEq] THEN
 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `t0` THEN Cases_on `t1` THEN 
FULL_SIMP_TAC (srw_ss()) [rootRep, root_def, isSubtree] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree]) THEN
 
`isSubtreeEq t1 (Node n l) ∧ rootRep t0 t1` by METIS_TAC [symRepProp] THEN
FULL_SIMP_TAC (srw_ss()) [isSubEqImpSub] THEN
SRW_TAC [][] THEN1

(`(root t0 = NTS n) ∧ isSubtree t0 (Node n l)` by METIS_TAC [rootRep, root_def] THEN
`height t0 < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree] THEN
Cases_on `∃s0 s1 t'.symRepProp s0 s1 t' ∧ isSubtree t' (Node n l)` THEN1

(FULL_SIMP_TAC (srw_ss()) [symRepProp, rootRep, isSubEqImpSub] THEN
SRW_TAC [][] THEN1
(`height s1 < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree] THEN
`lastExpProp s1` by METIS_TAC [subtreeTrans] THEN
 METIS_TAC [subtreeLastExp]) THEN
`height t' < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree] THEN
`lastExpProp t'` by METIS_TAC [subtreeTrans] THEN
 METIS_TAC [subtreeLastExp]) THEN

FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
SRW_TAC [][lastExpProp] THEN
Q.EXISTS_TAC `t0` THEN
Q.EXISTS_TAC `Node n l` THEN
SRW_TAC [][] THEN
`isSubtree e (Node n l)` by
(SRW_TAC [][isSubtree] THEN
IMP_RES_TAC memImpEl THEN
Q.EXISTS_TAC `[i]` THEN
SRW_TAC [][subtree] THEN
Cases_on `EL i l` THEN FULL_SIMP_TAC (srw_ss()) [subtree]) THEN
METIS_TAC []) THEN

(`(root t0 = root t1) ∧ isSubtree t0 t1` by METIS_TAC [rootRep, root_def] THEN
`height t1 < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree] THEN
Cases_on `∃s0 s1.symRepProp s0 s1 t1 ∧ isSubtree t1 (Node n l)` THEN1

 (FULL_SIMP_TAC (srw_ss()) [] THEN
  `lastExpProp t1` by METIS_TAC [subtreeTrans] THEN
  METIS_TAC [subtreeLastExp]) THEN

FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][lastExpProp] THEN
Q.EXISTS_TAC `t0` THEN
Q.EXISTS_TAC `t1` THEN
SRW_TAC [][] THEN
Cases_on `t1` THEN1 
 (Cases_on `t0` THEN FULL_SIMP_TAC (srw_ss()) [root_def, rootRep, isSubtree] THEN
  Cases_on `p'` THEN FULL_SIMP_TAC (srw_ss()) [subtree]) THEN
SRW_TAC [][] THEN
IMP_RES_TAC memImpEl THEN
`isSubtree e (Node n' l')` by
(SRW_TAC [][isSubtree] THEN
Q.EXISTS_TAC `[i]` THEN
SRW_TAC [][subtree] THEN
Cases_on `EL i l'` THEN SRW_TAC [][subtree]) THEN
METIS_TAC [subtreeNotSymProp, isSubtree]));


val cnfTree = store_thm
("cnfTree",
``∀g tree. validptree g tree ⇒ isCnf g ⇒ ∀n t. (tree = Node n t) ⇒
    ∃n1 t1 n2 t2.(t = [Node n1 t1; Node n2 t2]) ∨ ∃ts.(t = [Leaf ts])``,

HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [validptree, isCnf_def] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [list_lem2, list_lem1] THEN1
(Cases_on `e1` THEN Cases_on `e2` THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isNode_def] THEN1
(`∃t1 t2.ptl = [Node n' t1; Node n'' t2]` by METIS_TAC [getSymsNtm] THEN
METIS_TAC []) THEN
(RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def])) THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
`ptl = [Leaf t]` by METIS_TAC [getSymsTm] THEN
METIS_TAC []);



val treeSymsImpSubtree = store_thm
("treeSymsImpSubtree",
``∀t. e ∈ treeSyms t ⇒ ∃t1. isSubtreeEq t1 t ∧ (root t1 = e)``,

completeInduct_on `height t` THEN SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [height_def, treeSyms] THEN1
(SRW_TAC [][isSubtreeEq] THEN
Q.EXISTS_TAC `Leaf t'` THEN
SRW_TAC [][root_def] THEN
Q.EXISTS_TAC `[]` THEN SRW_TAC [][subtree]) THEN1
(SRW_TAC [][] THEN
Q.EXISTS_TAC `Node n l` THEN
SRW_TAC [][root_def, isSubtreeEq] THEN
Q.EXISTS_TAC `[]` THEN SRW_TAC [][subtree]) THEN

FULL_SIMP_TAC (srw_ss()) [MEM_FLAT, MEM_MAP] THEN
SRW_TAC [][] THEN
`isSubtree a (Node n l)` by
(IMP_RES_TAC memImpEl THEN
SRW_TAC [][isSubtree] THEN
Q.EXISTS_TAC `[i']` THEN
SRW_TAC [][subtree] THEN
Cases_on `EL i' l`THEN SRW_TAC [][subtree]) THEN
`height a < 1 + max 0 (MAP (λa. height a) l)` by
(`height a < height (Node n l)`by METIS_TAC [subtreeHeight, isSubtree] THEN
FULL_SIMP_TAC (srw_ss()) [height_def]) THEN
METIS_TAC [subtreeTrans, isSubtree, isSubEqImpSub]);



val notSymRepImpTreeSyms = store_thm
("notSymRepImpTreeSyms",
``(∀t0 t1. ¬symRepProp t0 t1 (Node n ptl)) ⇒ 
(∀e. e ∈ ptl ⇒ ¬((NTS n) ∈ treeSyms e))``,

SRW_TAC [][] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
IMP_RES_TAC treeSymsImpSubtree THEN
`isSubtree e (Node n ptl)` by
(IMP_RES_TAC memImpEl THEN
SRW_TAC [][isSubtree] THEN
Q.EXISTS_TAC `[i']` THEN
SRW_TAC [][subtree] THEN
Cases_on `EL i' ptl` THEN SRW_TAC [][subtree]) THEN

`symRepProp t1 (Node n ptl) (Node n ptl)` by
(FULL_SIMP_TAC (srw_ss()) [symRepProp, isSubEqImpSub, rootRep, root_def] THEN
METIS_TAC [isSubtree, subtreeTrans]) THEN
METIS_TAC []);


val inpLen = store_thm
("inpLen",
``∀g t. validptree g t ⇒
 isCnf g  ⇒ 
(¬∃t0 t1. symRepProp t0 t1 t) ⇒
 ∀k. (k = LENGTH (distinctNtms t)) ⇒
 (LENGTH (leaves t) ≤ 2**(k - 1))``,

completeInduct_on `height t` THEN SRW_TAC [][] THEN
 Cases_on `t` THEN1 FULL_SIMP_TAC (srw_ss()) [validptree] THEN
FULL_SIMP_TAC (srw_ss()) [validptree, height_def, isCnf_def] THEN
 Q.ABBREV_TAC `r = getSymbols l` THEN
 ` isWord r ∧ (LENGTH r = 1) ∨
 EVERY isNonTmnlSym r ∧ (LENGTH r = 2)` by METIS_TAC [] THEN1

(FULL_SIMP_TAC (srw_ss()) [list_lem1]  THEN
 SRW_TAC [][] THEN
 Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
 SRW_TAC [][leaves_def] THEN
 `l = [Leaf t]` by METIS_TAC [getSymsTm] THEN
 SRW_TAC [][leaves_def, distinctNtms, treeSyms, rmDupes, delete_def]) THEN

FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
Cases_on `e1` THEN Cases_on `e2` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
`∃t' t''.l = [Node n' t'; Node n'' t'']` by METIS_TAC [getSymsNtm] THEN
SRW_TAC [][] THEN

Q.ABBREV_TAC `t = Node n [Node n' t'; Node n'' t'']` THEN
Q.ABBREV_TAC `t1 = Node n' t'` THEN
Q.ABBREV_TAC `t2 = Node n'' t''` THEN
Q.ABBREV_TAC `d = distinctNtms t` THEN
Q.ABBREV_TAC `d1 = distinctNtms t1` THEN
Q.ABBREV_TAC `d2 = distinctNtms t2` THEN
Q.ABBREV_TAC `l = LENGTH (leaves t)` THEN
Q.ABBREV_TAC `l1 = LENGTH (leaves t1)` THEN
Q.ABBREV_TAC `l2 = LENGTH (leaves t2)` THEN

`(subtree t [0] = SOME t1)` by SRW_TAC [][subtree, Abbr `t`, Abbr `t1`] THEN
`(subtree t [1] = SOME t2)` by SRW_TAC [][subtree, Abbr `t`, Abbr `t2`] THEN
`¬∃s0 s1. symRepProp s0 s1 t1` by METIS_TAC [subtreeNotSymProp, MEM] THEN
`¬∃s0 s1. symRepProp s0 s1 t2` by METIS_TAC [subtreeNotSymProp, MEM] THEN

`height t1 < 1 + max 0 (MAP (λa. height a) [t1; t2])` by 
(SRW_TAC [][max_def] THEN FULL_SIMP_TAC (arith_ss) []) THEN
`height t2 < 1 + max 0 (MAP (λa. height a) [t1; t2])` by 
(SRW_TAC [][max_def] THEN FULL_SIMP_TAC (arith_ss) []) THEN

`l1 ≤ 2 ** (LENGTH d1 - 1)` by METIS_TAC [isNode_def, MEM] THEN
`l2 ≤ 2 ** (LENGTH d2 - 1)` by METIS_TAC [isNode_def, MEM] THEN
`leaves t = leaves t1 ++ leaves t2` by 
SRW_TAC [][Abbr `t`, Abbr `t1`, Abbr `t2`, leaves_def] THEN
`l = l1 + l2` by METIS_TAC [LENGTH_APPEND] THEN
SRW_TAC [][] THEN

`¬MEM (NTS n) (treeSyms t1) ∧ ¬MEM (NTS n) (treeSyms t2)` by
(`∀e. e ∈ [t1; t2] ⇒ ¬(NTS n ∈ treeSyms e)` by METIS_TAC [notSymRepImpTreeSyms] THEN
 FULL_SIMP_TAC (srw_ss()) []) THEN

`LENGTH d1 ≤ LENGTH d - 1` by

(SRW_TAC [][Abbr `d1`, Abbr `d`, Abbr `t1`, Abbr `t`] THEN
SRW_TAC [][distinctNtms] THEN
SRW_TAC [][rmDupes_lts_card] THEN
Q.MATCH_ABBREV_TAC `CARD (set s0) ≤ CARD (set s) - 1` THEN
Q_TAC SUFF_TAC `CARD (set s0) < CARD (set s)` THEN
FULL_SIMP_TAC (arith_ss) [] THEN
Q_TAC SUFF_TAC `set s0 ⊂ set s` THEN1
 METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [treeSyms, rmDupes, delete_def, isNonTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND, isNonTmnlSym_def] THEN
`delete (NTS n) (FILTER isNonTmnlSym (FLAT (MAP (λa. treeSyms a) t'))) =
(FILTER isNonTmnlSym (FLAT (MAP (λa. treeSyms a) t')))`
 by METIS_TAC [delete_not_mem,FILTER_APPEND,notMemFilter,
	       MEM, MEM_APPEND] THEN
ONCE_ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [PSUBSET_DEF, EXTENSION, SUBSET_DEF, EQ_IMP_THM] THEN
SRW_TAC [][] THEN1
METIS_TAC [rmd_r2, MEM, MEM_APPEND, delete_not_mem, delete_append] THEN
Q.EXISTS_TAC `NTS n` THEN
SRW_TAC [][] THEN
METIS_TAC [rmd_r2, MEM, MEM_APPEND, delete_not_mem, delete_append, 
	   delete_mem_list]) THEN

`LENGTH d2 ≤ LENGTH d - 1` by

(SRW_TAC [][Abbr `d2`, Abbr `d`, Abbr `t2`, Abbr `t`] THEN
SRW_TAC [][distinctNtms] THEN
SRW_TAC [][rmDupes_lts_card] THEN
Q.MATCH_ABBREV_TAC `CARD (set s0) ≤ CARD (set s) - 1` THEN
Q_TAC SUFF_TAC `CARD (set s0) < CARD (set s)` THEN
FULL_SIMP_TAC (arith_ss) [] THEN
Q_TAC SUFF_TAC `set s0 ⊂ set s` THEN1
 METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [treeSyms, rmDupes, delete_def] THEN
FULL_SIMP_TAC (srw_ss()) [FILTER_APPEND, isNonTmnlSym_def] THEN
`delete (NTS n) (FILTER isNonTmnlSym (FLAT (MAP (λa. treeSyms a) t''))) =
(FILTER isNonTmnlSym (FLAT (MAP (λa. treeSyms a) t'')))`
 by METIS_TAC [delete_not_mem,FILTER_APPEND,notMemFilter,
	       MEM, MEM_APPEND] THEN
ONCE_ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [PSUBSET_DEF, EXTENSION, SUBSET_DEF, EQ_IMP_THM] THEN
SRW_TAC [][] THEN1
METIS_TAC [rmd_r2, MEM, MEM_APPEND, delete_not_mem, delete_append, 
	   delete_mem_list, FILTER_APPEND] THEN
Q.EXISTS_TAC `NTS n` THEN
SRW_TAC [][rmDupes] THEN
METIS_TAC [rmd_r2, MEM, MEM_APPEND, delete_not_mem, delete_append, 
	   delete_mem_list, FILTER_APPEND]) THEN

`l1 ≤ 2 ** ((LENGTH d - 1)-1)` by METIS_TAC [powLe] THEN
`l2 ≤ 2 ** ((LENGTH d - 1)-1)` by METIS_TAC [powLe] THEN
`l1 + l2 ≤ 2*2 ** ((LENGTH d − 1) - 1)` by DECIDE_TAC THEN
`l1 + l2 ≤ 2 ** (((LENGTH d - 1) - 1) + 1)` by METIS_TAC [powMult] THEN
`LENGTH d ≥ 2` by
(SRW_TAC [][Abbr `d`, Abbr `t`, Abbr `t1`, Abbr `t2`] THEN
FULL_SIMP_TAC (srw_ss()) [treeSyms] THEN
SRW_TAC [][distinctNtms, treeSyms, rmDupes, delete_def, delete_append,
	   FILTER_APPEND, isNonTmnlSym_def] THEN
DECIDE_TAC) THEN
Cases_on `LENGTH d` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `LENGTH d` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []);


val numd = store_thm
("numd",
 ``∀t. isNode t ⇒ LENGTH (distinctNtms t) ≥ 1``,

Cases_on `t` THEN SRW_TAC [][distinctNtms, treeSyms, rmDupes, delete_def,isNode_def,
			     rmDupes, FILTER_APPEND, isNonTmnlSym_def] THEN
DECIDE_TAC);

val inpLeninv = store_thm
("inpLeninv",
 ``isCnf g ∧ validptree g t ∧
 LENGTH (leaves t) > 2**(k - 1) ∧
 (k = LENGTH (distinctNtms t))
  ⇒
  ∃t0 t1. symRepProp t0 t1 t``,

 SRW_TAC [][] THEN
Q.ABBREV_TAC `k = LENGTH (distinctNtms t)` THEN
`¬(LENGTH (leaves t) ≤ 2 ** (k − 1))` by DECIDE_TAC THEN
METIS_TAC [inpLen]);



val subtreeLevel = store_thm
("subtreeLevel",
``∀t p. (subtree t p = SOME t1) ∧ p ≠ [] ⇒
   ∃n ptl. (subtree t (FRONT p) = SOME (Node n ptl)) ∧ MEM t1 ptl``,

Induct_on `p` THEN SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < LENGTH l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

(Cases_on `EL h l` THEN
FULL_SIMP_TAC (srw_ss()) [subtree] THEN
SRW_TAC [][] THEN
METIS_TAC [EL_IS_EL]) THEN
SRW_TAC [][subtree]);


val ntmsLen = store_thm
("ntmsLen",
``LENGTH (ntms g) ≥ 1``,

Cases_on `g` THEN 
SRW_TAC [][ntms_def, ntList_def, nonTerminalsList_def, startSym_def,
	   rmDupes] THEN
DECIDE_TAC);


val distNtmsSub = store_thm
("distNtmsSub",
``∀g t. validptree g t ⇒ set (distinctNtms t) ⊆  set (MAP NTS (ntms g))``,

HO_MATCH_MP_TAC validptree_ind THEN
SRW_TAC [][validptree] THEN
`∀e. e ∈ ptl ∧ isNode e ⇒ set (distinctNtms e) ⊆ set (MAP NTS (ntms g))`
by METIS_TAC [] THEN
`∀e. e ∈ ptl ⇒ set (distinctNtms e) ⊆ set (MAP NTS (ntms g))` by
(SRW_TAC [][] THEN
Cases_on `e` THEN1
SRW_TAC [][distinctNtms, isNonTmnlSym_def, treeSyms, rmDupes, delete_def] THEN
METIS_TAC [isNode_def]) THEN
`n ∈ (ntms g)`  by METIS_TAC [ruleRhsInntms] THEN
`((NTS n):(α,β) symbol) ∈ (MAP NTS (ntms g))`  by SRW_TAC [][MEM_MAP] THEN
FULL_SIMP_TAC (srw_ss()) [distinctNtms, treeSyms, isNonTmnlSym_def,
			  SUBSET_DEF, EXTENSION] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss())[rmDupes] THEN
`x ∈ (FILTER isNonTmnlSym (FLAT (MAP (λa. treeSyms a) ptl)))`
 by METIS_TAC [memdel, rmd_r2] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_FILTER, MEM_MAP, MEM_FLAT] THEN
SRW_TAC [][] THEN
`x ∈ FILTER isNonTmnlSym (treeSyms a)` by METIS_TAC [MEM_FILTER] THEN
Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
METIS_TAC [rmd_r2, symbol_11]);


val LENGTH_distinctNtms = store_thm(
  "LENGTH_distinctNtms",
  ``LENGTH (distinctNtms t) = CARD (set (distinctNtms t))``,
  SRW_TAC [][distinctNtms, rmDupes_lts_card, rmDupes_lts_card_eq]);

val LENGTH_ntms = store_thm(
  "LENGTH_ntms",
  ``LENGTH (ntms t) = CARD (set (ntms t))``,
  SRW_TAC [][ntms_def, rmDupes_lts_card, rmDupes_lts_card_eq]);


val mapCard = store_thm
("mapCard",
``∀s. FINITE s ⇒ ∀l.(s = set l) ⇒ (∀x y.(f x = f y) ⇔ (x = y)) ⇒ 
 (CARD (set (MAP f l)) = CARD s)``,

HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [][] THEN
`∃l'. (set l' = s)` by  METIS_TAC [listExists4Set] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`l'`] MP_TAC) THEN SRW_TAC [][] THEN
`set l = e INSERT set l'` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`¬(f e ∈ (MAP f l'))`  by FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
`CARD ((f e) INSERT (set (MAP f l'))) = CARD (e INSERT set l')` by SRW_TAC [][] THEN
`set (MAP f l) = f e INSERT set (MAP f l')` by
 (FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
  METIS_TAC [MEM_MAP]) THEN
`CARD (e INSERT set l') = SUC (CARD (set l'))` 
 by FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN
METIS_TAC []);


val numdLeqNtms = store_thm
("numdLeqNtms",
``∀g t. validptree g t ⇒ LENGTH (distinctNtms t) ≤ LENGTH (ntms g)``,

SRW_TAC [][] THEN
Q_TAC SUFF_TAC ` LENGTH (distinctNtms t) ≤ 
 LENGTH ((MAP NTS (ntms g)):(α,β) symbol list)` THEN1
 METIS_TAC [LENGTH_MAP] THEN
IMP_RES_TAC distNtmsSub THEN
`FINITE (set (distinctNtms t))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
SRW_TAC [][LENGTH_ntms, LENGTH_distinctNtms] THEN
`∀x y.(NTS x = NTS y) ⇔ (x = y)` by FULL_SIMP_TAC (srw_ss()) [] THEN
`CARD (set ((MAP NTS (ntms g)):(α,β) symbol list)) =
CARD (set (ntms g))` by METIS_TAC [mapCard, FINITE_LIST_TO_SET] THEN
METIS_TAC [CARD_SUBSET, FINITE_LIST_TO_SET, DECIDE ``a ≤ b ∧b ≤ c ⇒ a ≤ c``]);

val cleavesApp = store_thm
("cleavesApp",
``∀a b. cleaves (a ++ b) = cleaves a ++ cleaves b``,

Induct_on `a` THEN SRW_TAC [][leaves_def]);


val subtreePfxSfxLeaves = store_thm
("subtreePfxSfxLeaves",
``∀t t1 p.(subtree t p = SOME t1) ⇒ 
∃pfx sfx.(leaves t = pfx ++ leaves t1 ++ sfx)``,

Induct_on `p` THEN SRW_TAC [][] THEN1

(Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
 METIS_TAC [APPEND_NIL]) THEN

Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
FULL_SIMP_TAC (srw_ss()) [subtree] THEN
FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < LENGTH l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`EL h l`,`t1`] MP_TAC) THEN SRW_TAC [][] THEN

(Cases_on `EL h l` THEN
FULL_SIMP_TAC (srw_ss()) [subtree, leaves_def] THEN
SRW_TAC [][leaves_def] THEN
`MEM (EL h l) l` by METIS_TAC [EL_IS_EL] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [][cleavesApp, leaves_def] THEN
METIS_TAC [APPEND_ASSOC]));

val cnfTreeLeaves = store_thm
("cnfTreeLeaves",
``∀g t. validptree g t ⇒ isCnf g ⇒ LENGTH (leaves t) ≥ 1``,

HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [validptree, isCnf_def] THEN
Q.ABBREV_TAC `r = getSymbols ptl` THEN
`EVERY isNonTmnlSym r ∧ (LENGTH r = 2) ∨
isWord r ∧ (LENGTH r = 1)` by METIS_TAC [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [list_lem2, list_lem1] THEN1
(Cases_on `e1` THEN Cases_on `e2` THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isNode_def] THEN
`∃t1 t2.ptl = [Node n' t1; Node n'' t2]` by METIS_TAC [getSymsNtm] THEN
SRW_TAC [][leaves_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (leaves (Node n' t1)) ≥ 1`by METIS_TAC [isNode_def] THEN
`LENGTH (leaves (Node n'' t2)) ≥ 1`by METIS_TAC [isNode_def] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [leaves_def]) THEN
Cases_on `e` THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
`(ptl = [Leaf t])` by METIS_TAC [getSymsTm] THEN
SRW_TAC [][leaves_def]);



val vptSubtree = store_thm
("vptSubtree",
``∀g t. validptree g t ⇒ 
 (∀t1. isSubtreeEq t1 t ∧ isNode t1 ⇒ validptree g t1)``,

completeInduct_on `height t` THEN SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
FULL_SIMP_TAC (srw_ss()) [validptree] THEN
FULL_SIMP_TAC (srw_ss()) [isSubEqImpSub, isSubtree] THEN

Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < LENGTH l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`isSubtreeEq t1 (EL h l)` by
(SRW_TAC [][isSubEqImpSub, isSubtree] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
METIS_TAC [MEM]) THEN
`isSubtree (EL h l) (Node n l)` by
(SRW_TAC [][isSubtree] THEN
Q.EXISTS_TAC `[h]` THEN SRW_TAC [][subtree] THEN
Cases_on `EL h l` THEN SRW_TAC [][subtree]) THEN
Cases_on `EL h l` THEN1
(Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [validptree, subtree] THEN
Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [isNode_def]) THEN
`height (EL h l) < height (Node n l)` by METIS_TAC [isSubtree, subtreeHeight] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`height (EL h l)`] MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`EL h l`] MP_TAC) THEN SRW_TAC [][] THEN
`validptree g (Node n' l')` by
(FULL_SIMP_TAC (srw_ss()) [validptree] THEN
METIS_TAC [isNode_def, EL_IS_EL, validptree]) THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`g`] MP_TAC) THEN SRW_TAC [][] THEN

FULL_SIMP_TAC (srw_ss()) [isSubEqImpSub, isSubtree] THEN
METIS_TAC []);



val leafSubt = store_thm
("leafSubt",
``isSubtree t0 (Node n [Leaf ts]) ⇒ (t0 = Leaf ts)``,

SRW_TAC [][isSubtree] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < 1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`h = 0` by DECIDE_TAC THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [subtree]);


val subtDistNtms = store_thm
("subtDistNtms",
``∀t t1 p. (subtree t p = SOME t1) ⇒ 
LENGTH (distinctNtms t1) ≤ LENGTH (distinctNtms t)``,

Induct_on `p` THEN SRW_TAC [][] THEN
Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < LENGTH l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`EL h l`,`t1`] MP_TAC) THEN SRW_TAC [][] THEN

`LENGTH (distinctNtms (EL h l)) ≤ LENGTH (distinctNtms (Node n l))`
by (SRW_TAC [][distinctNtms, treeSyms] THEN
`(EL h l) ∈ l`by METIS_TAC [EL_IS_EL] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, isNonTmnlSym_def] THEN
SRW_TAC [][] THEN
Q_TAC SUFF_TAC `LENGTH (rmDupes (FILTER isNonTmnlSym (treeSyms (EL h l)))) ≤
LENGTH
  (rmDupes
     (NTS n::
          FILTER isNonTmnlSym
            (FLAT (MAP (λa. treeSyms a) (r1 ++ [EL h l] ++ r2)))))` THEN1
METIS_TAC [] THEN
SRW_TAC [][FILTER_APPEND, FLAT_APPEND] THEN
METIS_TAC [rmdLenLe, APPEND, APPEND_ASSOC]) THEN
DECIDE_TAC);



val distSymsLenSub = store_thm
("distSymsLenSub",
``∀t1 t. isSubtreeEq t1 t ⇒ LENGTH (distinctNtms t1) ≤ LENGTH (distinctNtms t)``,

SRW_TAC [][isSubtreeEq] THEN
METIS_TAC [subtDistNtms]);


val getSymsCleaves = store_thm
("getSymsCleaves",
``∀g t. (∀e. e ∈ t ∧ isNode e ⇒ validptree g e) ⇒
(derives g)^* (getSymbols t) (MAP TS (cleaves t))``,

Induct_on `t` THEN SRW_TAC [][] THEN1
SRW_TAC [][getSymbols_def, leaves_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [getSymbols_def] THEN
FULL_SIMP_TAC (srw_ss()) [cleavesApp, leaves_def] THEN1
METIS_TAC [APPEND, rtc_derives_same_append_left, APPEND] THEN

`(derives g)^* [NTS n] (MAP TS (leaves (Node n l)))`
 by METIS_TAC [vptRtcd, fringeEqLeaves, isNode_def, root_def] THEN
FULL_SIMP_TAC (srw_ss()) [leaves_def] THEN
METIS_TAC [APPEND, derives_append, APPEND]);


val vptSubtD = store_thm
("vptSubtD",
``∀g t. validptree g t ⇒ ∀p t0. (subtree t p = SOME t0) ⇒
∃pfx sfx. (derives g)^* [root t] (MAP TS pfx ++ [root t0] ++ MAP TS sfx) ∧
(leaves t = pfx ++ leaves t0 ++ sfx)``,

HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][validptree] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
SRW_TAC [][] THEN1
(MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
SRW_TAC [][]) THEN

Cases_on `h < LENGTH ptl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `EL h ptl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

(Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [subtree] THEN
SRW_TAC [][] THEN
IMP_RES_TAC EL_IS_EL THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, getSyms_append] THEN
SRW_TAC [][] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [][root_def, leaves_def, cleavesApp] THEN
`rule n (getSymbols (r1' ++ [Leaf t'] ++ r2')) ∈ rules g`
by METIS_TAC [MEM, MEM_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [getSyms_append, getSymbols_def] THEN
MAP_EVERY Q.EXISTS_TAC [`cleaves r1'`,`cleaves r2'`]  THEN
SRW_TAC [][] THEN
`(derives g)^* (getSymbols r1') (MAP TS (cleaves r1'))`
by METIS_TAC [getSymsCleaves, MEM, MEM_APPEND, validptree, rgr_r9eq] THEN
`(derives g)^* (getSymbols r2') (MAP TS (cleaves r2'))`
by METIS_TAC [getSymsCleaves, MEM, MEM_APPEND, validptree, rgr_r9eq] THEN

`(derives g)^* ((getSymbols r1')++[TS t']) (MAP TS (cleaves r1') ++ [TS t'])`
by METIS_TAC [rtc_derives_same_append_right] THEN
`(derives g)^* ((getSymbols r1')++[TS t']++(getSymbols r1' ++ [TS t'])) 
(MAP TS (cleaves r1') ++ [TS t']++(getSymbols r1' ++ [TS t']))`
by METIS_TAC [rtc_derives_same_append_right] THEN
`derives g [NTS n] (getSymbols r1' ++ [TS t'] ++ getSymbols r2')`
by METIS_TAC [res1] THEN
METIS_TAC [rtc_derives_same_append_left, rtc_derives_same_append_right,
	   RTC_RULES, RTC_RTC]) THEN


`isNode (EL h ptl)`by METIS_TAC [isNode_def] THEN
Q.PAT_ASSUM `∀e. P e`MP_TAC THEN
`Node n' l ∈ ptl` by METIS_TAC [EL_IS_EL] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`EL h ptl`] MP_TAC) THEN SRW_TAC [][] THEN
`∃pfx sfx. (derives g)^* [root (Node n' l)] 
(MAP TS pfx ++ [root t0] ++ MAP TS sfx) ∧
(leaves (Node n' l) = pfx ++ leaves t0 ++ sfx)`  by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [leaves_def] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
SRW_TAC [][cleavesApp, leaves_def] THEN
FULL_SIMP_TAC (srw_ss()) [root_def] THEN
`rule n (getSymbols (r1' ++ [Node n' l] ++ r2'))∈ rules g`
by METIS_TAC [MEM, MEM_APPEND] THEN
MAP_EVERY Q.EXISTS_TAC [`cleaves r1'++pfx`,`sfx ++ cleaves r2'`] THEN
SRW_TAC [][] THEN
`(derives g)^* (getSymbols r1') (MAP TS (cleaves r1'))`
by METIS_TAC [getSymsCleaves, MEM, MEM_APPEND, validptree, rgr_r9eq] THEN
`(derives g)^* (getSymbols r2') (MAP TS (cleaves r2'))`
by METIS_TAC [getSymsCleaves, MEM, MEM_APPEND, validptree, rgr_r9eq] THEN
`derives g [NTS n] (getSymbols (r1' ++ [Node n' l] ++ r2'))`
by METIS_TAC [res1] THEN
FULL_SIMP_TAC (srw_ss()) [getSyms_append, getSymbols_def] THEN
`(derives g)^* (getSymbols [Node n' l]) (MAP TS (cleaves [Node n' l]))`
by METIS_TAC [getSymsCleaves, MEM, MEM_APPEND, validptree, rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [getSymbols_def, leaves_def] THEN
`(derives g)^* ((getSymbols r1')++[NTS n']) (MAP TS (cleaves r1') ++ [NTS n'])`
by METIS_TAC [rtc_derives_same_append_right] THEN
`(derives g)^* (MAP TS (cleaves r1')++[NTS n']++getSymbols r2') 
(MAP TS (cleaves r1') ++ [NTS n'] ++ getSymbols r2')`
by METIS_TAC [rtc_derives_same_append_right, APPEND_ASSOC,RTC_RULES] THEN
`(derives g)^* (MAP TS (cleaves r1') ++ [NTS n'] ++getSymbols r2') 
(MAP TS (cleaves r1') ++ [NTS n'] ++MAP TS (cleaves r2'))`
by METIS_TAC [rtc_derives_same_append_left, APPEND_ASSOC] THEN
`(derives g)^* (MAP TS (cleaves r1') ++[NTS n'] ++ MAP TS (cleaves r2'))
(MAP TS (cleaves r1') ++MAP TS pfx ++ [root t0] ++ MAP TS sfx ++ MAP TS (cleaves r2'))`
by METIS_TAC [rtc_derives_same_append_left, rtc_derives_same_append_right,
	      APPEND_ASSOC] THEN
`(derives g)^* (getSymbols r1' ++ [NTS n'] ++ getSymbols r2')
         (MAP TS (cleaves r1') ++ [NTS n'] ++ getSymbols r2')`
by METIS_TAC [APPEND_ASSOC, rtc_derives_same_append_right] THEN
METIS_TAC [APPEND_ASSOC, RTC_RTC, RTC_RULES]);

val rtcDReplEnd = store_thm
("rtcDReplEnd",
 ``∀i.(derives g)^* [NTS B] (p ++ [NTS B] ++ s) ∧
 (derives g)^*  [NTS B] z ∧ EVERY isTmnlSym z ∧
 (derives g)^* s z' ∧ EVERY isTmnlSym z'
  ⇒
  (derives g)^* [NTS B] (FLAT (lpow p i) ++ z ++ FLAT (lpow z' i))``,

Induct_on `i` THEN SRW_TAC [][] THEN1
(SRW_TAC [][lpow_def,REPLICATE] THEN
 METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left,
	    APPEND_ASSOC,RTC_RTC]) THEN
RES_TAC THEN
SRW_TAC [][flatRepSuc] THEN
Q_TAC SUFF_TAC
`(derives g)^* [NTS B] (p ++ FLAT (lpow p i) ++ z ++  FLAT (lpow z' i) ++z')` THEN1
METIS_TAC [flatRepComm,APPEND_ASSOC] THEN
`(derives g)^* (p++[NTS B]++s) (p++FLAT (lpow p i) ++ z ++ FLAT (lpow z' i)++s)` by
METIS_TAC [rtc_derives_same_append_right,rtc_derives_same_append_left,
	   APPEND_ASSOC] THEN
METIS_TAC [RTC_RTC,rtc_derives_same_append_left]);
      

val pumpCfg = store_thm
("pumpCfg",
``∀g.
   isCnf (g:('a,'b) grammar)  ⇒
   ∃n. n > 0 ∧
       ∀z. z ∈ language g ∧ LENGTH z ≥ n ⇒
           ∃u v w x y.
	     (z = u ++ v ++ w ++ x ++ y) ∧
             LENGTH v + LENGTH x ≥ 1 ∧
             LENGTH v + LENGTH w + LENGTH x ≤ n ∧
             ∀i. u++FLAT (lpow v i)++w++FLAT (lpow x i)++y ∈ language g``,

SRW_TAC [][] THEN
 Q.ABBREV_TAC `k=LENGTH (ntms g)` THEN
Q.EXISTS_TAC `2**k` THEN
SRW_TAC [][] THEN1 SRW_TAC [][Abbr`k`, GREATER_DEF] THEN
`∃t. validptree g t ∧ (root t = NTS (startSym g)) ∧ (z = MAP TS (leaves t))` 
 by METIS_TAC [ptLangThm, fringeEqLeaves] THEN
SRW_TAC [][] THEN
Q.ABBREV_TAC `z:(α,β) symbol list = MAP TS (leaves t)` THEN
Q.ABBREV_TAC `k0 = LENGTH (distinctNtms t)` THEN
`isNode t` by (Cases_on `t` THEN FULL_SIMP_TAC (srw_ss())[validptree, 
							  isNode_def]) THEN
`k0 ≥ 1` by METIS_TAC [numd] THEN
`k0 ≤ k` by METIS_TAC [numdLeqNtms] THEN
`1 ≤ k0`by DECIDE_TAC THEN
`k ≠ 0`by DECIDE_TAC THEN
 `LENGTH z ≥ 2 ** k0` by METIS_TAC [powGtTrans] THEN
 `LENGTH z > 2**(k0-1)` by METIS_TAC [powGt] THEN
`∃t0' t1'. symRepProp  t0' t1' t` by METIS_TAC [inpLeninv, LENGTH_MAP] THEN
IMP_RES_TAC symPropImpLastExp THEN
FULL_SIMP_TAC (srw_ss()) [lastExpProp] THEN
SRW_TAC [][] THEN
`validptree g (Node n ptl)` by METIS_TAC [symRepProp, vptSubtree, isNode_def] THEN
`isNode t0` by
(Cases_on `t0` THEN FULL_SIMP_TAC (srw_ss()) [symRepProp, rootRep, root_def,
					     isNode_def]) THEN
`validptree g (Node n ptl)` by METIS_TAC [symRepProp, vptSubtree, isNode_def] THEN
`validptree g t0` by 
(FULL_SIMP_TAC (srw_ss()) [symRepProp, rootRep] THEN
 METIS_TAC [vptSubtree, isSubEqImpSub]) THEN

`∃n1 n2 ptl1 ptl2. (ptl = [Node n1 ptl1; Node n2 ptl2])` by 
(`∃n1 t1 n2 t2. (ptl = [Node n1 t1; Node n2 t2]) ∨ ∃ts. ptl = [Leaf ts]` 
by METIS_TAC [isNode_def, cnfTree] THEN1
METIS_TAC [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [symRepProp, rootRep] THEN
`t0 = Leaf ts` by METIS_TAC [leafSubt] THEN
SRW_TAC [][] THEN
METIS_TAC [isNode_def]) THEN

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.ABBREV_TAC `t1 = Node n1 ptl1` THEN
Q.ABBREV_TAC `t2 = Node n2 ptl2` THEN
Q.ABBREV_TAC `l1 = distinctNtms (Node n1 ptl1)` THEN
Q.ABBREV_TAC `l2 = distinctNtms (Node n2 ptl2)` THEN
`validptree g t1` by METIS_TAC [validptree, MEM, isNode_def] THEN
`LENGTH (leaves t1) ≤ 2 ** (LENGTH l1 - 1)` by METIS_TAC [inpLen] THEN
`validptree g t2` by METIS_TAC [validptree, MEM, isNode_def] THEN
`LENGTH (leaves t2) ≤ 2 ** (LENGTH l2 - 1)` by METIS_TAC [inpLen] THEN
`∃p.(subtree (Node n [t1; t2]) p = SOME t0) ∧ p ≠ []`
by  METIS_TAC [symRepProp, isSubtree, rootRep] THEN
`∃p'. (subtree t p' = SOME (Node n [t1; t2]))` by  
(FULL_SIMP_TAC (srw_ss()) [symRepProp] THEN
 `((Node n [t1; t2]) = t) ∨ isSubtree (Node n [t1; t2]) t` 
 by METIS_TAC [isSubEqImpSub] THEN
 SRW_TAC [][] THEN
 METIS_TAC [subtree, isSubtree]) THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [subtree] THEN
Cases_on `h < 2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`(h = 0) ∨ (h = 1)` by DECIDE_TAC THEN SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `∃pfx sfx. (derives g)^* [root t] (((MAP TS pfx):(α,β) symbol list) ++ 
					 [NTS n] ++ 
					 (MAP TS sfx):(α,β) symbol list) ∧ 
	   (leaves t = pfx ++ leaves (Node n [t1; t2]) ++ sfx)`
      by METIS_TAC [vptSubtD, root_def] THEN
      `∃pfx' sfx'.(derives g)^* [NTS n1] (((MAP TS pfx'):(α,β) symbol list)
					  ++ [root t0] ++ 
					  MAP TS sfx':(α,β) symbol list) ∧
	   (leaves t1 = pfx' ++ leaves t0 ++ sfx')` 
      by METIS_TAC [vptSubtD, root_def] THEN
      `LENGTH (leaves t2) ≥ 1` by METIS_TAC [cnfTreeLeaves] THEN
      FULL_SIMP_TAC (srw_ss()) [leaves_def] THEN
      MAP_EVERY Q.EXISTS_TAC [`MAP TS pfx`,`MAP TS pfx'`,`MAP TS (leaves t0)`,
			      `MAP TS sfx'++ MAP TS (leaves t2)`,`MAP TS sfx`] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (arith_ss) [] THEN1      
      (`isSubtreeEq t1 t` by 
      (FULL_SIMP_TAC (srw_ss())[isSubEqImpSub, symRepProp, isNode_def] THEN
       SRW_TAC [][isSubtree] THEN
       `(subtree (Node n [t1; t2]) [0] = SOME t1)` by SRW_TAC [][subtree] THEN
       METIS_TAC [MEM, subtreeTrans, isSubtree]) THEN      
      `LENGTH l1 ≤ k0` by METIS_TAC [isSubEqImpSub, distSymsLenSub] THEN
      `LENGTH l1 ≤ k` by DECIDE_TAC THEN
      `isSubtreeEq t2 t` by 
      (FULL_SIMP_TAC (srw_ss())[isSubEqImpSub, symRepProp, isNode_def] THEN
       SRW_TAC [][isSubtree] THEN
       `(subtree (Node n [t1; t2]) [1] = SOME t2)` by SRW_TAC [][subtree] THEN
       METIS_TAC [MEM, subtreeTrans, isSubtree]) THEN      
      `LENGTH l2 ≤ k0` by METIS_TAC [isSubEqImpSub, distSymsLenSub] THEN
      `LENGTH l2 ≤ k` by DECIDE_TAC THEN       
      `LENGTH pfx' + (LENGTH sfx' + LENGTH (leaves t0)) ≤ 2 ** (k − 1)` 
       by METIS_TAC [powLe] THEN
       `LENGTH (leaves t2) ≤ 2 ** (k − 1)` by METIS_TAC [powLe] THEN      
      `LENGTH pfx' + (LENGTH sfx' + LENGTH (leaves t0)) + 
      LENGTH (leaves t2) ≤ 2*2 ** (k − 1)` by DECIDE_TAC THEN
      `LENGTH pfx' + (LENGTH sfx' + LENGTH (leaves t0)) + 
      LENGTH (leaves t2) ≤ 2 ** (k − 1 + 1)` 
      by METIS_TAC [powMult] THEN
      `k - 1 + 1 = k` by DECIDE_TAC THEN
      `LENGTH pfx' + (LENGTH sfx' + LENGTH (leaves t0)) + 
      LENGTH (leaves t2) ≤ 2 ** k` 
      by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [leaves_def] THEN
      METIS_TAC [LENGTH_APPEND, APPEND_ASSOC, ADD_SYM]) THEN

      `(derives g)^* [root t1] ((MAP TS (leaves t1)):(α,β) symbol list)` by 
      METIS_TAC [vptRtcd,fringeEqLeaves] THEN
      `(derives g)^* [root t2] ((MAP TS (leaves t2)):(α,β) symbol list)` by
      METIS_TAC [vptRtcd,fringeEqLeaves] THEN
      `root t0 = NTS n` by METIS_TAC [symRepProp, rootRep, root_def] THEN
      `(derives g)^* [root t0] ((MAP TS (leaves t0)):(α,β) symbol list)` by
      METIS_TAC [vptRtcd,fringeEqLeaves] THEN
      Cases_on `t0` THEN FULL_SIMP_TAC (srw_ss()) [root_def] THEN
      SRW_TAC [][] THEN
      `root t1 = NTS n1` by METIS_TAC [root_def] THEN
      `root t2 = NTS n2` by METIS_TAC [root_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      
      `derives g [NTS n] [NTS n1;NTS n2]` by 
      (`isSubtreeEq (Node n [t1; t2]) t` by
      (SRW_TAC [][isSubEqImpSub, isSubtree] THEN
      Cases_on `p'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [MEM]) THEN
      `validptree g (Node n [t1;t2])` by METIS_TAC [isNode_def,vptSubtree] THEN
      FULL_SIMP_TAC (srw_ss()) [validptree, Abbr `t1`, Abbr `t2`,
				getSymbols_def] THEN
      METIS_TAC [res1]) THEN
      `(derives g)^* [NTS n1;NTS n2]
	 (MAP TS pfx' ++ [NTS n] ++ MAP TS sfx'++[NTS n2])`
      by METIS_TAC [rtc_derives_same_append_right, APPEND] THEN
      `(derives g)^* [NTS n] (MAP TS pfx' ++ [NTS n] ++ MAP TS sfx'++[NTS n2])`
      by METIS_TAC [APPEND,RTC_RULES,APPEND_ASSOC] THEN
      `isWord ((MAP TS (leaves (Node n l))):(α,β) symbol list)` 
      by METIS_TAC [everyTmMapTs] THEN
      `(derives g)^* (MAP TS sfx' ++ [NTS n2])  (MAP TS sfx' ++ MAP TS (leaves t2))`
      by METIS_TAC [rtc_derives_same_append_left] THEN
      `isWord ((MAP TS sfx' ++ MAP TS (leaves t2)):(α,β) symbol list)`
      by METIS_TAC [everyTmMapTs, EVERY_APPEND] THEN
      Q.ABBREV_TAC `p = MAP TS pfx'` THEN
      Q.ABBREV_TAC `s = MAP TS sfx' ++ [NTS n2]` THEN
     `(derives g)^* [NTS n] (p ++ [NTS n] ++ s)` by METIS_TAC [APPEND_ASSOC] THEN				      
     Q.ABBREV_TAC `x:(α,β) symbol list = (MAP TS (leaves (Node n l)))` THEN
     Q.ABBREV_TAC `x':(α,β) symbol list = (MAP TS sfx' ++ MAP TS (leaves t2))` THEN
      `(derives g)^* [NTS n] (FLAT (lpow p i) ++ x ++ FLAT (lpow x' i))`
				      by METIS_TAC [rtcDReplEnd] THEN
    SRW_TAC [][language_def, EXTENSION] THEN
    `(derives g)^* (MAP TS pfx ++ [NTS n] ++ MAP TS sfx)
         (MAP TS pfx ++ (FLAT (lpow p i) ++ x ++ FLAT (lpow x' i)) ++
	  MAP TS sfx)` by METIS_TAC [rtc_derives_same_append_left,
				     rtc_derives_same_append_right] THEN
    METIS_TAC [APPEND_ASSOC,RTC_RTC,everyTmMapTs,islpowTmnl,EVERY_APPEND],

    
    (* t0 is in the second subtree *)
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `∃pfx sfx. (derives g)^* [root t] (((MAP TS pfx):(α,β) symbol list) ++ 
					 [NTS n] ++ 
					 (MAP TS sfx):(α,β) symbol list) ∧ 
	   (leaves t = pfx ++ leaves (Node n [t1; t2]) ++ sfx)`
      by METIS_TAC [vptSubtD, root_def] THEN
      `∃pfx' sfx'.(derives g)^* [NTS n2] (((MAP TS pfx'):(α,β) symbol list)
					  ++ [root t0] ++ 
					  MAP TS sfx':(α,β) symbol list) ∧
	   (leaves t2 = pfx' ++ leaves t0 ++ sfx')` 
      by METIS_TAC [vptSubtD, root_def] THEN
      `LENGTH (leaves t1) ≥ 1` by METIS_TAC [cnfTreeLeaves] THEN
      FULL_SIMP_TAC (srw_ss()) [leaves_def] THEN
      MAP_EVERY Q.EXISTS_TAC [`MAP TS pfx`,`MAP TS (leaves t1)++MAP TS pfx'`,
			      `MAP TS (leaves t0)`,`MAP TS sfx'`,`MAP TS sfx`] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (arith_ss) [] THEN1      
      (`isSubtreeEq t2 t` by 
      (FULL_SIMP_TAC (srw_ss())[isSubEqImpSub, symRepProp, isNode_def] THEN
       SRW_TAC [][isSubtree] THEN
       `(subtree (Node n [t1; t2]) [1] = SOME t2)` by SRW_TAC [][subtree] THEN
       METIS_TAC [MEM, subtreeTrans, isSubtree]) THEN      
       `LENGTH l2 ≤ k0` by METIS_TAC [isSubEqImpSub, distSymsLenSub] THEN
      `LENGTH l2 ≤ k` by DECIDE_TAC THEN
      `isSubtreeEq t1 t` by 
      (FULL_SIMP_TAC (srw_ss())[isSubEqImpSub, symRepProp, isNode_def] THEN
       SRW_TAC [][isSubtree] THEN
       `(subtree (Node n [t1; t2]) [0] = SOME t1)` by SRW_TAC [][subtree] THEN
       METIS_TAC [MEM, subtreeTrans, isSubtree]) THEN      
      `LENGTH l1 ≤ k0` by METIS_TAC [isSubEqImpSub, distSymsLenSub] THEN
      `LENGTH l1 ≤ k` by DECIDE_TAC THEN       
      `LENGTH pfx' + (LENGTH sfx' + LENGTH (leaves t0)) ≤ 2 ** (k − 1)` 
       by METIS_TAC [powLe] THEN
       `LENGTH (leaves t1) ≤ 2 ** (k − 1)` by METIS_TAC [powLe] THEN      
      `LENGTH pfx' + (LENGTH sfx' + LENGTH (leaves t0)) + 
      LENGTH (leaves t1) ≤ 2*2 ** (k − 1)` by DECIDE_TAC THEN
      `LENGTH pfx' + (LENGTH sfx' + LENGTH (leaves t0)) + 
      LENGTH (leaves t1) ≤ 2 ** (k − 1 + 1)` 
      by METIS_TAC [powMult] THEN
      `k - 1 + 1 = k` by DECIDE_TAC THEN
      `LENGTH pfx' + (LENGTH sfx' + LENGTH (leaves t0)) + 
      LENGTH (leaves t1) ≤ 2 ** k` 
      by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [leaves_def] THEN
      METIS_TAC [LENGTH_APPEND, APPEND_ASSOC, ADD_SYM]) THEN

      `(derives g)^* [root t1] ((MAP TS (leaves t1)):(α,β) symbol list)` by 
      METIS_TAC [vptRtcd,fringeEqLeaves] THEN
      `(derives g)^* [root t2] ((MAP TS (leaves t2)):(α,β) symbol list)` by
      METIS_TAC [vptRtcd,fringeEqLeaves] THEN
      `root t0 = NTS n` by METIS_TAC [symRepProp, rootRep, root_def] THEN
      `(derives g)^* [root t0] ((MAP TS (leaves t0)):(α,β) symbol list)` by
      METIS_TAC [vptRtcd,fringeEqLeaves] THEN
      Cases_on `t0` THEN FULL_SIMP_TAC (srw_ss()) [root_def] THEN
      SRW_TAC [][] THEN
      `root t1 = NTS n1` by METIS_TAC [root_def] THEN
      `root t2 = NTS n2` by METIS_TAC [root_def] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      
      `derives g [NTS n] [NTS n1;NTS n2]` by 
      (`isSubtreeEq (Node n [t1; t2]) t` by
      (SRW_TAC [][isSubEqImpSub, isSubtree] THEN
      Cases_on `p'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [MEM]) THEN
      `validptree g (Node n [t1;t2])` by METIS_TAC [isNode_def,vptSubtree] THEN
      FULL_SIMP_TAC (srw_ss()) [validptree, Abbr `t1`, Abbr `t2`,
				getSymbols_def] THEN
      METIS_TAC [res1]) THEN
      `(derives g)^* [NTS n1;NTS n2]
	 ([NTS n1] ++ MAP TS pfx' ++ [NTS n] ++ MAP TS sfx')`
      by METIS_TAC [rtc_derives_same_append_left, APPEND] THEN
      `(derives g)^* [NTS n] ([NTS n1]++MAP TS pfx' ++ [NTS n] ++ MAP TS sfx')`
      by METIS_TAC [APPEND,RTC_RULES,APPEND_ASSOC] THEN
      `isWord ((MAP TS (leaves (Node n l))):(α,β) symbol list)` 
      by METIS_TAC [everyTmMapTs] THEN
      `(derives g)^* [NTS n] 
	 (((MAP TS (leaves t1)):(α,β) symbol list) ++ 
	 MAP TS pfx' ++ [NTS n] ++ MAP TS sfx')` 
      by METIS_TAC [rtc_derives_same_append_right, APPEND_ASSOC,RTC_RTC] THEN

      Q.ABBREV_TAC `p = ((MAP TS (leaves t1)):(α,β) symbol list) ++MAP TS pfx'` THEN
      Q.ABBREV_TAC `s = MAP TS sfx'` THEN
     Q.ABBREV_TAC `x:(α,β) symbol list = (MAP TS (leaves (Node n l)))` THEN
     Q.ABBREV_TAC `x':(α,β) symbol list = MAP TS sfx'` THEN
     `(derives g)^* x' x'`by METIS_TAC [RTC_RULES] THEN
      `(derives g)^* [NTS n] (FLAT (lpow p i) ++ x ++ FLAT (lpow x' i))`
				      by METIS_TAC [rtcDReplEnd, everyTmMapTs,
						    EVERY_APPEND] THEN
    SRW_TAC [][language_def, EXTENSION] THEN
    `(derives g)^* (MAP TS pfx ++ [NTS n] ++ MAP TS sfx)
         (MAP TS pfx ++ (FLAT (lpow p i) ++ x ++ FLAT (lpow x' i)) ++
	  MAP TS sfx)` by METIS_TAC [rtc_derives_same_append_left,
				     rtc_derives_same_append_right] THEN
    METIS_TAC [APPEND_ASSOC,RTC_RTC,everyTmMapTs,islpowTmnl,EVERY_APPEND]]);


val _ = export_theory ();