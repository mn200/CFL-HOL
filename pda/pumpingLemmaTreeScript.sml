open HolKernel boolLib bossLib Parse BasicProvers Defn

open pred_setTheory stringTheory containerTheory relationTheory
listTheory rich_listTheory optionTheory arithmeticTheory


open listLemmasTheory relationLemmasTheory grammarDefTheory
     arithmeticLemmasTheory symbolDefTheory cnfTheory parseTreeTheory
     treeDerivTheory

val _ = new_theory "pumpingLemmaTree";

fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w);

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

val distinctSyms = Define
`distinctSyms t = rmDupes (treeSyms t)`;

val subtree = Define
`(subtree t [] = SOME t) ∧
(subtree (Node n ptl) (p::ps) = 
 if (p < LENGTH ptl) then
     subtree (EL p ptl) ps else NONE)`;

val isSubtree = Define
`isSubtree st t = ∃p. p ≠ [] ∧ (subtree t p = SOME st)`;

val allTms = Define
`allTms ptl = isWord (MAP ptree2Sym ptl)`;

val btree = Define
`btree B st t = (ptree2Sym st = NTS B) ∧  isSubtree st t`;

val symRepProp = Define
`symRepProp t0 t1 t =
∃B. btree B t1 t ∧ btree B t0 t1`;

val lastExpProp = Define
`lastExpProp t = ∃t0 t1. symRepProp t0 t1 t ∧ 
∃B n1 n2.(t1 = Node B y1 y2) ∧ (root y1 = n1) ∧ (root y2 = n2) ∧
(¬∃st0 st1. symRepProp st0 st1 y1) ∧ (¬∃st0 st1. symRepProp st0 st1 y2)`;


val max = Define
`(max n [] = n) ∧
(max n (x::xs) = if (n > x) then max n xs else max x xs)`;

val height_defn = Hol_defn "height_defn"
`(height (Leaf tm) = 0) ∧
 (height (Node n l) = 1 + max 0 (MAP height l))`;


val (height_def, height_ind) = tprove (height_defn,
WF_REL_TAC (`measure ptsize`) THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ptsizel_append] THEN
DECIDE_TAC);


val subtreeApp = store_thm
("subtreeApp",
``∀t t1 p p'.
 (subtree t p = SOME t1) ∧ (subtree t1 p' = SOME t0) ⇒
 (subtree t (p++p') = SOME t0)``,

Induct_on `p` THEN SRW_TAC [][] THEN1
(Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [subtree]) THEN

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
``(subtree t p = SOME t1) ∧ p ≠ [] ∧ (¬∃s0 s1. symRepProp s0 s1 t) ⇒
 ¬∃s0 s1. symRepProp s0 s1 t1``,

SRW_TAC [][symRepProp] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN 
FULL_SIMP_TAC (srw_ss()) [btree] THEN
`isSubtree t1 t` by METIS_TAC [isSubtree] THEN
METIS_TAC [subtreeTrans]);


val subtreeLastExp = store_thm
("subtreeLastExp",
``∀t t1. lastExpProp t1 ∧ isSubtree t1 t ⇒
 lastExpProp t``,

SRW_TAC [][isSubtree, lastExpProp] THEN
FULL_SIMP_TAC (srw_ss()) [symRepProp, btree] THEN
Q.EXISTS_TAC `t0` THEN
Q.EXISTS_TAC `t1'` THEN
SRW_TAC [][] THEN1
METIS_TAC [subtreeTrans, isSubtree]);

val maxMapElem = store_thm
("maxMapElem",
``∀l n. (max n (MAP f l) = n') ⇒ 
(∃e. MEM e l ∧ (f e = n')) ∨ (n = n')``,

Induct_on `l` THEN SRW_TAC [][max] THEN
FULL_SIMP_TAC (srw_ss()) [max] THEN
METIS_TAC []);

val subtreeHeight = store_thm
("subtreeHeight",
``∀t p t1. (subtree t p = SOME t1) ∧ p ≠ [] ⇒ height t1 < height t``,

Induct_on `height t` THEN SRW_TAC [][] THEN1
(Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [height_def] THEN
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree]) THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [height_def] THEN
`v = max 0 (MAP (λa. height a) l)` by DECIDE_TAC THEN
SRW_TAC [][] THEN
MAGIC);


val symPropImpLastExp = store_thm
("symPropImpLastExp",
``∀t t0 t1. symRepProp t0 t1 t ⇒ lastExpProp t``,

completeInduct_on `height t` THEN
SRW_TAC [][] THEN
Cases_on `t` THEN1
(FULL_SIMP_TAC (srw_ss()) [lastExpProp, symRepProp, btree, isSubtree] THEN
 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree]) THEN

FULL_SIMP_TAC (srw_ss()) [symRepProp] THEN
`(ptree2Sym t1 = NTS B) ∧ isSubtree t1 (Node n l)` by METIS_TAC [btree] THEN
`height t1 < height (Node n l)` by METIS_TAC [subtreeHeight, isSubtree] THEN
Cases_on `∃s0 s1.symRepProp s0 s1 t1` THEN1

(FULL_SIMP_TAC (srw_ss()) [symRepProp] THEN
`lastExpProp t1` by METIS_TAC [] THEN
METIS_TAC [subtreeLastExp]) THEN

FULL_SIMP_TAC (srw_ss()) [symRepProp] THEN
SRW_TAC [][lastExpProp] THEN
Q.EXISTS_TAC `t0` THEN
Q.EXISTS_TAC `t1` THEN
SRW_TAC [][] THEN1
(FULL_SIMP_TAC (srw_ss()) [symRepProp] THEN
 METIS_TAC []) THEN

FULL_SIMP_TAC (srw_ss()) [symRepProp] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
FULL_SIMP_TAC (srw_ss()) [btree] THEN
METIS_TAC [subtreeTrans]);



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
 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isNode_def] THEN
 MAGIC) THEN
MAGIC);



val inpLen = store_thm
("inpLen",
``∀g t. validptree g t ⇒
 isCnf g  ⇒ 
 (¬∃t0 t1. symRepProp t0 t1 t) ⇒
 ∀k. (k = LENGTH (distinctSyms t)) ⇒
 (LENGTH (leaves t) ≤ 2**(k - 1))``,

HO_MATCH_MP_TAC validptree_ind THEN
SRW_TAC [][] THEN
IMP_RES_TAC cnfTree THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
MAGIC);


val inpLeninv = store_thm
("inpLeninv",
 ``isCnf g ∧ validptree g t ∧
 LENGTH (leaves t) > 2**(k - 1) ∧
 (k = LENGTH (distinctSyms t))
  ⇒
  ∃t0 t1. symRepProp t0 t1 t``,

 SRW_TAC [][] THEN
Q.ABBREV_TAC `k = LENGTH (distinctSyms t)` THEN
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


val numd = store_thm
("numd",
``∀t.LENGTH (distinctSyms t) ≥ 1``,

Cases_on `t` THEN SRW_TAC [][distinctSyms, treeSyms, rmDupes, delete_def,
			     rmDupes] THEN
DECIDE_TAC);

val numdLeqNtms = store_thm
("numdLeqNtms",
``∀g t. validptre g t ⇒ LENGTH (distinctSyms t) ≤ LENGTH (ntms g)``,

HO_MATCH_MP_TAC validptree_ind THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [validptree, distinctSyms, treeSyms, rmDupes] THEN
MAGIC);


val vptTreeLevel = store_thm
("vptTreeLevel",
``∀g t.validptree g t ⇒ 
∀t p t1. (subtree t p = SOME t1) ⇒
∃pfx sfx. (fringe t = fringe pfx ++ fringe t1 ++ fringe sfx) ∧
RTC (derives g) [root t] 
(MAP TS (fringe pfx) ++ getSymbols [t1] ++ MAP TS (fringe sfx))``,


HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [validptree] THEN
MAGIC);


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
`∃t. validptree g t ∧ (ptree2Sym t = NTS (startSym g)) ∧ (z = leaves t)` 
 by MAGIC THEN
SRW_TAC [][] THEN
Q.ABBREV_TAC `z:(α,β) symbol list = leaves t` THEN
Q.ABBREV_TAC `k0 = LENGTH (distinctSyms t)` THEN
`k0 ≥ 1` by METIS_TAC [numd] THEN
`k0 ≤ k` by METIS_TAC [numdLeqNtms] THEN
`1 ≤ k0`by DECIDE_TAC THEN
`k ≠ 0`by DECIDE_TAC THEN
 `LENGTH z ≥ 2 ** k0` by METIS_TAC [powGtTrans] THEN
 `LENGTH z > 2**(k0-1)` by METIS_TAC [powGt] THEN
`∃t0 t1. symRepProp t0 t1 t` by METIS_TAC [inpLeninv] THEN
IMP_RES_TAC symPropImpLastExp THEN
`∃s0 s1. symRepProp s0 s1 t ∧ ¬∃st0 st1. symRepProp st0 st1 s0` 
 by METIS_TAC [lastExpProp] THEN
`∃B. btree B s1 t ∧ btree B s0 s1` by METIS_TAC [symRepProp] THEN
FULL_SIMP_TAC (srw_ss()) [btree, isSubtree] THEN
`∃n1 ptl1. (subtree t (FRONT p) = SOME (Node n1 ptl1)) ∧ s1 ∈ ptl1` 
by METIS_TAC [subtreeLevel] THEN
`RTC (derives g) [root t] (getSymbols ptl1)` by MAGIC THEN
`∃pfx1 sfx1. (derives g)^* [root t] (getSymbols (pfx1++[s1]++sfx1)) ∧
	     (ptl1 = pfx1 ++ [s1] ++ sfx1)` by METIS_TAC [rgr_r9eq] THEN
SRW_TAC [][] THEN

`∃n0 ptl0. (subtree s1 (FRONT p') = SOME (Node n0 ptl0)) ∧ s0 ∈ ptl0` 
by METIS_TAC [subtreeLevel] THEN
`RTC (derives g) [root s1] (getSymbols ptl0)` by MAGIC THEN
`∃pfx0 sfx0. (derives g)^* [root s1] (getSymbols (pfx0++[s0]++sfx0)) ∧
	     (ptl0 = pfx0 ++ [s0] ++ sfx0)` by METIS_TAC [rgr_r9eq] THEN
SRW_TAC [][] THEN





`validptree g s0` by MAGIC THEN
`LENGTH (leaves s0) ≤ 2 ** (LENGTH (distinctSyms s0) - 1)`
by METIS_TAC [inpLen] THEN


FULL_SIMP_TAC (srw_ss()) [btree, isSubtree] THEN

`∃n ptl. (subtree s1 (FRONT p') = SOME (Node n ptl)) ∧ s0 ∈ ptl` 
by METIS_TAC [subtreeLevel] THEN

`∃n1 ptl1. (subtree t (FRONT p) = SOME (Node n1 ptl1)) ∧ s1 ∈ ptl1` 
by METIS_TAC [subtreeLevel] THEN




∃v0 x0. s1 -> getSyms (v0 ++ s0 ++ x0)




Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [subtree]
	     
  ∃pfx sfx. RTC (derives g) [root t] (getSymbols (pfx ++ t1 ++ sfx))``


 `symRepProp t` by MAGIC THEN
FULL_SIMP_TAC (srw_ss()) [symRepProp] THEN
SRW_TAC [][] THEN

u = leaves pfx

v = leaves pfx1

w = leaves bst1

x = leaves sfx1

y = leaves sfx



`z ∈ llanguage g` by METIS_TAC [drd_ld_langeq] THEN
`(lderives g)^* [NTS (startSym g)] z ∧ EVERY isTmnlSym z`
  by FULL_SIMP_TAC (srw_ss()) [llanguage_def] THEN
`∃dl.(lderives g) ⊢ dl ◁ [NTS (startSym g)] → z`
  by METIS_TAC [rtc2list_exists'] THEN
Q.ABBREV_TAC `k0=LENGTH (distinctldNts dl)` THEN
`LENGTH (distinctldNts dl) ≥ 1` by METIS_TAC [numdlds] THEN
`k0 ≥ 1 ⇒ 1 ≤ k0` by DECIDE_TAC THEN
`isNonTmnlSym (NTS (startSym g))` by METIS_TAC [isNonTmnlSym_def] THEN
IMP_RES_TAC dldntsLeg THEN
FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
`MEM (startSym g) (ntms g)` by
(SRW_TAC [][ntms_def, ntList_def, nonTerminalsList_def] THEN
 METIS_TAC [rmd_r2, MEM, APPEND]) THEN
`k0 ≤ k` by METIS_TAC [dldntsLeg] THEN
 `1 ≤ k0` by METIS_TAC [] THEN
`k ≠ 0` by DECIDE_TAC THEN
 `LENGTH z ≥ 2 ** k0` by METIS_TAC [powGtTrans] THEN
 `LENGTH z > 2**(k0-1)` by METIS_TAC [powGt] THEN
 `symRepProp dl` by METIS_TAC [inpLeninv,symRepProp_def] THEN
`EVERY isNonTmnlSym ([NTS (startSym g)]:('a,'b) symbol list)`
by METIS_TAC [APPEND_ASSOC,APPEND_11,symbol_11,isNonTmnlSym_def,EVERY_DEF] THEN
 `∃pz0:('a,'b) symbol list sz0:('a,'b) symbol list.([NTS (startSym g)]=pz0++sz0) ∧
	 EVERY isTmnlSym pz0 ∧ EVERY isNonTmnlSym sz0`
 by METIS_TAC [EVERY_DEF,APPEND_NIL] THEN
`lastExpProp (g,dl,z)`
by METIS_TAC [lastExp,symbol_11] THEN
FULL_SIMP_TAC (srw_ss()) [lastExpProp] THEN
SRW_TAC [][] THEN
`lderives g ⊢ (dl1++TL dl2) ◁ [NTS n1]++[NTS n2] → (v++rst)` by
METIS_TAC [listderivTrans, APPEND] THEN
`∃pfx sfx.([NTS n1]++[NTS n2]=pfx++sfx) ∧ EVERY isTmnlSym pfx ∧
	 EVERY isNonTmnlSym sfx` by
(MAP_EVERY Q.EXISTS_TAC [`[]`,`[NTS n1]++[NTS n2]`] THEN
 SRW_TAC [][isNonTmnlSym_def]) THEN
`∃dl1' dl2' zb zy.
   splitDerivProp (g,dl1++TL dl2,v++rst)
   (dl1',[NTS n1],zb) (dl2',[NTS n2],zy)` by METIS_TAC [ldSplitDeriv,EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
`LENGTH zb ≤ 2**(LENGTH (distinctldNts dl1') -1)`
by METIS_TAC [symRepProp_def, inpLen,EVERY_APPEND] THEN
`LENGTH zy ≤ 2**(LENGTH (distinctldNts dl2') -1)`
by METIS_TAC [symRepProp_def, inpLen,EVERY_APPEND] THEN
SRW_TAC [][] THEN
`∃v''.zb++zy=v++v''`by
(IMP_RES_TAC twoListAppEq THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
 METIS_TAC [APPEND_ASSOC]) THEN
SRW_TAC [][] THEN
`lderives g ⊢ MAP (listsec v []) dl2 ◁
   listsec v [] (v ++ ([NTS B]++w)) → listsec v [] (v ++ v'')`
by METIS_TAC [listsecldSfxNil,APPEND_ASSOC,EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [listsecDropNilSfx] THEN
`¬symRepProp (MAP (listsec v []) dl2)` by METIS_TAC [notspropLsTmnls,
						    APPEND_ASSOC,
						    EVERY_APPEND] THEN
`MEM (v++[NTS B]++w) dl1` by
(Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
 METIS_TAC [MEM, MEM_APPEND, APPEND_FRONT_LAST]) THEN
`v ++ [NTS B] ++ w = v ++ ([NTS B]++w)` by SRW_TAC [][] THEN
`∃p1 p2.([NTS B]++w = p1++p2) ∧ EVERY isTmnlSym p1 ∧ EVERY isNonTmnlSym p2`
by METIS_TAC [ldMemlderivesSfx] THEN
`∃dl1' dl2' zb' zy'.
   splitDerivProp (g,(MAP (listsec v []) dl2),v'') (dl1',[NTS B],zb')
   (dl2',w,zy')`
by METIS_TAC [APPEND,ldSplitDeriv] THEN
FULL_SIMP_TAC (srw_ss()) [splitDerivProp] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
MAP_EVERY Q.EXISTS_TAC [`tsl`,`v`,`zb'`,`zy'`,`rst'`] THEN
SRW_TAC [][] THEN1
(FULL_SIMP_TAC (srw_ss()) [ntProp] THEN SRW_TAC [][]
 THENL[
       `LENGTH ([NTS B;NTS n2]) > 1` by
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
       `v ≠ [] ∨ w ≠ []` by METIS_TAC [cnfvwNotNil] THEN1
       (`LENGTH v ≠ 0` by METIS_TAC [LENGTH_NIL] THEN DECIDE_TAC) THEN
       `p1 = []` by (Cases_on `p1` THEN SRW_TAC [][] THEN
		     Cases_on `h` THEN SRW_TAC [][] THEN
		     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,
					       isNonTmnlSym_def]) THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `zy' ≠ []` by METIS_TAC [cnfNotLderivesNilAllntms,
				EVERY_DEF, APPEND_NIL] THEN
       `LENGTH zy' ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
       DECIDE_TAC,

       `LENGTH ([NTS n1;NTS n2]) > 1` by
       FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
       `v ≠ [] ∨ w ≠ []` by METIS_TAC [cnfvwNotNil] THEN1
       (`LENGTH v ≠ 0` by METIS_TAC [LENGTH_NIL] THEN DECIDE_TAC) THEN
       `p1 = []` by (Cases_on `p1` THEN SRW_TAC [][] THEN
		     Cases_on `h` THEN SRW_TAC [][] THEN
		     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,
					       isNonTmnlSym_def]) THEN
       SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       `zy' ≠ []` by METIS_TAC [cnfNotLderivesNilAllntms,
				EVERY_DEF, APPEND_NIL] THEN
       `LENGTH zy' ≠ 0` by METIS_TAC [LENGTH_NIL] THEN
       DECIDE_TAC])
THENL[
      `LENGTH (distinctldNts dl1') ≤
      LENGTH (distinctldNts (dl1 ++ TL dl2))` by METIS_TAC [distElemLen_def] THEN
      `LENGTH (distinctldNts dl2') ≤
      LENGTH (distinctldNts (dl1 ++ TL dl2))` by METIS_TAC [distElemLen_def] THEN
      `LENGTH (zb ++ zy) = LENGTH (v ++ zb' ++ zy')`
      by METIS_TAC [APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `dl2 ≠ []` by (Cases_on `dl2` THEN
		     FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
      `∀e. (MEM e dl1 ⇒ MEM (tsl ++ e ++ sfx) dl)
      ∧ (∀e. MEM e dl2 ⇒ MEM (tsl ++ e ++ sfx) dl) ⇒
      LENGTH (distinctldNts (dl1++TL dl2)) ≤ LENGTH (distinctldNts dl)` by
      METIS_TAC [dldntsLenLe, APPEND_NIL] THEN
      `∀e. (MEM e dl1 ⇒ MEM (tsl ++ e ++ sfx) dl)
      ∧ (∀e. MEM e dl2 ⇒ MEM (tsl ++ e ++ sfx) dl) ⇒
      LENGTH (distinctldNts (dl1++TL dl2)) ≤ k` by
      METIS_TAC [DECIDE ``a ≤ b ∧ b ≤ c ⇒ a ≤ c``] THEN
      FULL_SIMP_TAC (srw_ss()) [distElemLen_def] THEN
      `LENGTH (distinctldNts dl1') ≤ k`
      by METIS_TAC [DECIDE ``a ≤ b ∧ b ≤ c ⇒ a ≤ c``] THEN
      `LENGTH (distinctldNts dl2') ≤ k`
      by METIS_TAC [DECIDE ``a ≤ b ∧ b ≤ c ⇒ a ≤ c``] THEN
      `LENGTH zb ≤ 2 ** (k-1)` by METIS_TAC [powLe] THEN
      `LENGTH zy ≤ 2 ** (k-1)` by METIS_TAC [powLe] THEN
      `LENGTH zb + LENGTH zy ≤ 2**(k-1) + 2**(k-1)`by DECIDE_TAC THEN
       `LENGTH zb + LENGTH zy ≤ 2*2**(k-1)`by DECIDE_TAC THEN
       `LENGTH zb + LENGTH zy ≤ 2**(k-1+1)`by METIS_TAC [powMult] THEN
       `LENGTH dl > 1` by
       (SPOSE_NOT_THEN ASSUME_TAC THEN
	Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()++ARITH_ss) [] THEN
	SRW_TAC [][] THEN
	`EVERY isTmnlSym (pz0++sz0)` by METIS_TAC [EVERY_APPEND] THEN
	Cases_on `pz0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	SRW_TAC [][] THEN
	FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN
       `k0 ≥ 1` by METIS_TAC [dldntsGe1] THEN
       `k - 1 + 1 = k` by DECIDE_TAC THEN
       METIS_TAC [],

       FULL_SIMP_TAC (srw_ss()) [language_def,llanguage_def, EXTENSION] THEN
       SRW_TAC [][]
       THENL[
	     (* 3 subgoals *)

	     (* 1 *)
	     FULL_SIMP_TAC (srw_ss()) [ntProp] THEN
	     (Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
	      (`(tsl ++ [NTS B] ++ sfx) = pz0++sz0`
	      by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	      `(tsl ++ [NTS B] ++ sfx = [NTS (startSym g)])`
	      by METIS_TAC [] THEN
	      FULL_SIMP_TAC (srw_ss()) [lreseq] THEN SRW_TAC [][] THEN

	      `(lderives g)^* [NTS (startSym g)] (pfx++sfx')`
	      by METIS_TAC [ldMemRel, APPEND, APPEND_NIL, APPEND_ASSOC] THEN

	      `dl1 ≠ []` by (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* (pfx++sfx') (v ++ [NTS (startSym g)] ++ w)`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN

	      `dl1'' ≠ []` by (Cases_on `dl1''` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* [NTS (startSym g)] zb'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN

	      `dl2'' ≠ []` by (Cases_on `dl2''` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* w zy'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN
	      `(lderives g)^* [NTS (startSym g)] (v ++ [NTS (startSym g)] ++ w)`
	      by METIS_TAC [RTC_RTC] THEN
	      `(lderives g)^* v v` by SRW_TAC [][] THEN
	      `(lderives g)^* [NTS (startSym g)]
	     (FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i))`
	      by METIS_TAC [rtcDerivesReplEnd] THEN
	      `rst' = []` by
	      (Cases_on `dl3`  THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	       SRW_TAC [][] THEN
	       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [lderives_def]) THEN
	      SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	      `llanguage g = language g` by METIS_TAC [drd_ld_langeq] THEN
	      FULL_SIMP_TAC (srw_ss()) [language_def, llanguage_def, EXTENSION] THEN
	      METIS_TAC [EVERY_APPEND, islpowTmnl]) THEN

	     `h = pz0++sz0` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
	     SRW_TAC [][] THEN

	      `(lderives g)^* [NTS (startSym g)] (tsl ++ pfx++sfx'++sfx)`
	      by METIS_TAC [ldMemRel, APPEND, APPEND_ASSOC] THEN

	      `dl1 ≠ []` by (Cases_on `dl1` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* (pfx++sfx') (v ++ [NTS B] ++ w)`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN

	      `dl1'' ≠ []` by (Cases_on `dl1''` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* [NTS B] zb'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN


	      `dl3 ≠ []` by (Cases_on `dl3` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* sfx rst'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN

	      `dl2'' ≠ []` by (Cases_on `dl2''` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def]) THEN
	      `(lderives g)^* w zy'`
	      by METIS_TAC [rtc2listRtcHdLast, listderiv_def, APPEND_ASSOC] THEN
	      `(lderives g)^* [NTS (startSym g)] (tsl ++ v ++ [NTS B] ++ w ++sfx)`
	      by METIS_TAC [RTC_RTC, rtc_lderives_same_append_left,
			    rtc_lderives_same_append_right, APPEND_ASSOC] THEN
	      `(lderives g)^* [NTS B] (pfx++sfx')` by
	      (`lderives g (tsl ++ [NTS B] ++ sfx)
	       (tsl ++ pfx ++ sfx' ++ sfx)`
	       by METIS_TAC [ldMemRel', APPEND, APPEND_ASSOC] THEN
	       FULL_SIMP_TAC (srw_ss()) [lderives_def] THEN
	       SRW_TAC [][] THEN
	      `EVERY isNonTmnlSym [NTS lhs]` by SRW_TAC [][isNonTmnlSym_def] THEN
	       `(s1=tsl) ∧ ([NTS lhs] ++ s2 = [NTS B]++sfx)`
	       by METIS_TAC [symlistdiv3, NOT_CONS_NIL] THEN
	       FULL_SIMP_TAC (srw_ss()) [] THEN
	       SRW_TAC [][] THEN
	       `rhs = pfx++sfx'` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	       METIS_TAC [ldres1, RTC_RULES]) THEN
	      `(lderives g)^* [NTS B] (v ++ [NTS B] ++ w)`
	      by METIS_TAC [RTC_RTC] THEN
	      `(lderives g)^* v v` by SRW_TAC [][] THEN
	      `(lderives g)^* [NTS B]
                 (FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i))`
	      by METIS_TAC [rtcDerivesReplEnd] THEN
	      `llanguage g = language g` by METIS_TAC [drd_ld_langeq] THEN
	      FULL_SIMP_TAC (srw_ss()) [language_def, llanguage_def, EXTENSION] THEN
	      `(lderives g)^* (pz0++sz0) (tsl ++ [NTS B] ++sfx)`
	      by METIS_TAC [ldMemRel, APPEND, APPEND_ASSOC] THEN
	      `(lderives g)^* (pz0++sz0)
		 (tsl ++ (FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i)) ++ sfx)`
	      by METIS_TAC [EVERY_APPEND, islpowTmnl, RTC_RTC,
			    rtc_lderives_same_append_right,
			    rtc_lderives_same_append_left] THEN
	      `(lderives g)^*
		 (tsl ++ FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i) ++ sfx)
		 (tsl ++ FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i) ++ rst')`
	      by METIS_TAC [APPEND_ASSOC, EVERY_APPEND, islpowTmnl,
			    rtc_lderives_same_append_left] THEN
	      `(lderives g)^* (pz0++sz0)
		 (tsl ++ FLAT (lpow v i) ++ zb' ++ FLAT (lpow zy' i) ++ rst')`
	      by METIS_TAC [RTC_RTC, APPEND_ASSOC] THEN
	      METIS_TAC [EVERY_APPEND, islpowTmnl]),

	      METIS_TAC [islpowTmnl],

	      METIS_TAC [islpowTmnl]
	      ]]


MAGIC);

val _ = export_theory ();