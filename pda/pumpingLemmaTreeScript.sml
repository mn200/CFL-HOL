open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory arithmeticTheory


open listLemmasTheory relationLemmasTheory grammarDefTheory
     arithmeticLemmasTheory symbolDefTheory cnfTheory parseTreeTheory
     treeDerivTheory containerLemmasTheory

val _ = new_theory "pumpingLemmaTree";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1




val lastExpProp = Define
`lastExpProp t = 
∃t0 t1. symRepProp t0 t1 t ∧ 
∃n ptl.(t1 = Node n ptl) ∧ 
(∀e. e ∈ ptl ⇒ ¬∃st0 st1. symRepProp st0 st1 e)`;



val subtreeLastExp = store_thm
("subtreeLastExp",
``∀t t1. lastExpProp t1 ∧ isSubtree t1 t ⇒
 lastExpProp t``,

SRW_TAC [][isSubtree_def, lastExpProp, isSubEqImpSub] THEN
FULL_SIMP_TAC (srw_ss()) [symRepProp_def, btree_def] THEN

FULL_SIMP_TAC (srw_ss()) [isSubEqImpSub] THEN
SRW_TAC [][] THEN

(MAP_EVERY Q.EXISTS_TAC [`t0`,`Node n ptl`] THEN
FULL_SIMP_TAC (srw_ss()) [root_def] THEN
SRW_TAC [][] THEN
METIS_TAC [isSubtree_def, subtreeTrans, option_CLAUSES,root_def]));


val symPropImpLastExp = store_thm
("symPropImpLastExp",
``∀t t0 t1. symRepProp t0 t1 t ⇒ lastExpProp t``,

completeInduct_on `height t` THEN
SRW_TAC [][] THEN
Cases_on `t` THEN1
(FULL_SIMP_TAC (srw_ss()) [lastExpProp, symRepProp_def, isSubtreeEq_def] THEN
 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree_def] THEN
Cases_on `t0` THEN Cases_on `t1` THEN 
FULL_SIMP_TAC (srw_ss()) [rootRep_def, root_def, isSubtree_def] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree_def]) THEN
 
`isSubtreeEq t1 (Node n l) ∧ rootRep t0 t1` by METIS_TAC [symRepProp_def] THEN
FULL_SIMP_TAC (srw_ss()) [isSubEqImpSub] THEN
SRW_TAC [][] THEN1

(`(root t0 = NTS n) ∧ isSubtree t0 (Node n l)` by METIS_TAC [rootRep_def, root_def] THEN
`height t0 < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree_def] THEN
Cases_on `∃s0 s1 t'.symRepProp s0 s1 t' ∧ isSubtree t' (Node n l)` THEN1

(FULL_SIMP_TAC (srw_ss()) [symRepProp_def, rootRep_def, isSubEqImpSub] THEN
SRW_TAC [][] THEN1
(`height s1 < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree_def] THEN
`lastExpProp s1` by METIS_TAC [subtreeTrans] THEN
 METIS_TAC [subtreeLastExp]) THEN
`height t' < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree_def] THEN
`lastExpProp t'` by METIS_TAC [subtreeTrans] THEN
 METIS_TAC [subtreeLastExp]) THEN

FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
SRW_TAC [][lastExpProp] THEN
Q.EXISTS_TAC `t0` THEN
Q.EXISTS_TAC `Node n l` THEN
SRW_TAC [][] THEN
`isSubtree e (Node n l)` by
(SRW_TAC [][isSubtree_def] THEN
IMP_RES_TAC memImpEl THEN
Q.EXISTS_TAC `[i]` THEN
SRW_TAC [][subtree_def] THEN
Cases_on `EL i l` THEN FULL_SIMP_TAC (srw_ss()) [subtree_def]) THEN
METIS_TAC []) THEN

(`(root t0 = root t1) ∧ isSubtree t0 t1` by METIS_TAC [rootRep_def, root_def] THEN
`height t1 < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree_def] THEN
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
 (Cases_on `t0` THEN FULL_SIMP_TAC (srw_ss()) [root_def, rootRep_def, isSubtree_def] THEN
  Cases_on `p'` THEN FULL_SIMP_TAC (srw_ss()) [subtree_def]) THEN
SRW_TAC [][] THEN
IMP_RES_TAC memImpEl THEN
`isSubtree e (Node n' l')` by
(SRW_TAC [][isSubtree_def] THEN
Q.EXISTS_TAC `[i]` THEN
SRW_TAC [][subtree_def] THEN
Cases_on `EL i l'` THEN SRW_TAC [][subtree_def]) THEN
METIS_TAC [subtreeNotSymProp, isSubtree_def]));



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
 SRW_TAC [][leaves_def, distinctNtms_def, treeSyms_def, rmDupes, delete_def]) THEN

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

`(subtree t [0] = SOME t1)` by SRW_TAC [][subtree_def, Abbr `t`, Abbr `t1`] THEN
`(subtree t [1] = SOME t2)` by SRW_TAC [][subtree_def, Abbr `t`, Abbr `t2`] THEN
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
SRW_TAC [][distinctNtms_def] THEN
SRW_TAC [][rmDupes_lts_card] THEN
Q.MATCH_ABBREV_TAC `CARD (set s0) ≤ CARD (set s) - 1` THEN
Q_TAC SUFF_TAC `CARD (set s0) < CARD (set s)` THEN
FULL_SIMP_TAC (arith_ss) [] THEN
Q_TAC SUFF_TAC `set s0 ⊂ set s` THEN1
 METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [treeSyms_def, rmDupes, delete_def, isNonTmnlSym_def] THEN
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
SRW_TAC [][distinctNtms_def] THEN
SRW_TAC [][rmDupes_lts_card] THEN
Q.MATCH_ABBREV_TAC `CARD (set s0) ≤ CARD (set s) - 1` THEN
Q_TAC SUFF_TAC `CARD (set s0) < CARD (set s)` THEN
FULL_SIMP_TAC (arith_ss) [] THEN
Q_TAC SUFF_TAC `set s0 ⊂ set s` THEN1
 METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [treeSyms_def, rmDupes, delete_def] THEN
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
FULL_SIMP_TAC (srw_ss()) [treeSyms_def] THEN
SRW_TAC [][distinctNtms_def, treeSyms_def, rmDupes, delete_def, delete_append,
	   FILTER_APPEND, isNonTmnlSym_def] THEN
DECIDE_TAC) THEN
Cases_on `LENGTH d` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `LENGTH d` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) []);




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
`validptree g (Node n ptl)` by METIS_TAC [symRepProp_def, vptSubtree, isNode_def] THEN
`isNode t0` by
(Cases_on `t0` THEN FULL_SIMP_TAC (srw_ss()) [symRepProp_def, rootRep_def, root_def,
					     isNode_def]) THEN
`validptree g (Node n ptl)` by METIS_TAC [symRepProp_def, vptSubtree, isNode_def] THEN
`validptree g t0` by 
(FULL_SIMP_TAC (srw_ss()) [symRepProp_def, rootRep_def] THEN
 METIS_TAC [vptSubtree, isSubEqImpSub]) THEN

`∃n1 n2 ptl1 ptl2. (ptl = [Node n1 ptl1; Node n2 ptl2])` by 
(`∃n1 t1 n2 t2. (ptl = [Node n1 t1; Node n2 t2]) ∨ ∃ts. ptl = [Leaf ts]` 
by METIS_TAC [isNode_def, cnfTree] THEN1
METIS_TAC [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [symRepProp_def, rootRep_def] THEN
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
by  METIS_TAC [symRepProp_def, isSubtree_def, rootRep_def] THEN
`∃p'. (subtree t p' = SOME (Node n [t1; t2]))` by  
(FULL_SIMP_TAC (srw_ss()) [symRepProp_def] THEN
 `((Node n [t1; t2]) = t) ∨ isSubtree (Node n [t1; t2]) t` 
 by METIS_TAC [isSubEqImpSub] THEN
 SRW_TAC [][] THEN
 METIS_TAC [subtree_def, isSubtree_def]) THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [subtree_def] THEN
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
      (FULL_SIMP_TAC (srw_ss())[isSubEqImpSub, symRepProp_def, isNode_def] THEN
       SRW_TAC [][isSubtree_def] THEN
       `(subtree (Node n [t1; t2]) [0] = SOME t1)` by SRW_TAC [][subtree_def] THEN
       METIS_TAC [MEM, subtreeTrans, isSubtree_def]) THEN      
      `LENGTH l1 ≤ k0` by METIS_TAC [isSubEqImpSub, distSymsLenSub] THEN
      `LENGTH l1 ≤ k` by DECIDE_TAC THEN
      `isSubtreeEq t2 t` by 
      (FULL_SIMP_TAC (srw_ss())[isSubEqImpSub, symRepProp_def, isNode_def] THEN
       SRW_TAC [][isSubtree_def] THEN
       `(subtree (Node n [t1; t2]) [1] = SOME t2)` by SRW_TAC [][subtree_def] THEN
       METIS_TAC [MEM, subtreeTrans, isSubtree_def]) THEN      
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
      `root t0 = NTS n` by METIS_TAC [symRepProp_def, rootRep_def, root_def] THEN
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
      (SRW_TAC [][isSubEqImpSub, isSubtree_def] THEN
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
      (FULL_SIMP_TAC (srw_ss())[isSubEqImpSub, symRepProp_def, isNode_def] THEN
       SRW_TAC [][isSubtree_def] THEN
       `(subtree (Node n [t1; t2]) [1] = SOME t2)` by SRW_TAC [][subtree_def] THEN
       METIS_TAC [MEM, subtreeTrans, isSubtree_def]) THEN      
       `LENGTH l2 ≤ k0` by METIS_TAC [isSubEqImpSub, distSymsLenSub] THEN
      `LENGTH l2 ≤ k` by DECIDE_TAC THEN
      `isSubtreeEq t1 t` by 
      (FULL_SIMP_TAC (srw_ss())[isSubEqImpSub, symRepProp_def, isNode_def] THEN
       SRW_TAC [][isSubtree_def] THEN
       `(subtree (Node n [t1; t2]) [0] = SOME t1)` by SRW_TAC [][subtree_def] THEN
       METIS_TAC [MEM, subtreeTrans, isSubtree_def]) THEN      
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
      `root t0 = NTS n` by METIS_TAC [symRepProp_def, rootRep_def, root_def] THEN
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
      (SRW_TAC [][isSubEqImpSub, isSubtree_def] THEN
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