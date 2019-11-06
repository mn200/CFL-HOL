(* A theory about parse trees *)
open HolKernel boolLib bossLib Parse Defn BasicProvers

open stringTheory grammarDefTheory symbolDefTheory listTheory pairTheory
optionTheory rich_listTheory pred_setTheory

open listLemmasTheory containerLemmasTheory

val _ = new_theory "parseTree";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1

val _ = Hol_datatype 
`ptree = Leaf of 'ts | Node of 'nts => ptree list`;

val ptree2Sym = Define 
`(ptree2Sym (Node nt ptl) = NTS nt) ∧
(ptree2Sym (Leaf tm) = TS tm)`;

val isNode = Define 
`(isNode (Node _ _) = T) ∧
(isNode (Leaf _) = F)`;

val isLeaf = Define 
`(isLeaf (Node _ _) = F) ∧
(isLeaf (Leaf _) = T)`;

val ptsize_def = Define`  (ptsize (Leaf tmnl) = 1) ∧  
(ptsize (Node nt ptlist) = 1 + ptsizel ptlist) ∧  
(ptsizel [] = 0) ∧     
(ptsizel (h::t) = ptsize h + ptsizel t) `
val _ = export_rewrites ["ptsize_def"];

val ptheight_def = Define`  (ptheight (Leaf tmnl) = 0) ∧  
(ptheight (Node nt ptlist) = 1 + ptheightl ptlist) ∧  
(ptheightl [] = 0) ∧     
(ptheightl (h::t) = ptheight h + ptheightl t) `;
val _ = export_rewrites ["ptheight_def"];

val root = Define
`(root (Leaf tm) = TS tm) ∧
 (root (Node x ptl) =  NTS x)`;

val fringe_defn = Hol_defn "fringe_defn"
    `(fringe (Leaf tm) = [tm]) ∧
(fringe (Node x ptl) = FLAT (MAP fringe ptl))`;

val ptsize_better = prove(
  ``ptsize (Node nt ptlist) = 1 + SUM (MAP ptsize ptlist)``,
  SRW_TAC [][] THEN Induct_on `ptlist` THEN
  SRW_TAC [][]);

val ptheight_better = store_thm("ptheight_better",
  ``ptheight (Node nt ptlist) = 1 + SUM (MAP ptheight ptlist)``,
  SRW_TAC [][] THEN Induct_on `ptlist` THEN
  SRW_TAC [][]);

val ptsizel_append = store_thm ("ptsizel_append",
``ptsizel (l1++l2) = ptsizel l1 + ptsizel l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [ptsize_def] THEN
DECIDE_TAC);

val (fringe_def, fringe_ind) = tprove (fringe_defn,
WF_REL_TAC (`measure ptsize`) THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ptsizel_append] THEN
DECIDE_TAC);

val _ = save_thm ("fringe_def",fringe_def)
val _ = save_thm ("fringe_ind",fringe_ind)


val size_nonzero = prove(
  ``∀pt. ptsize pt > 0``,
  Cases_on `pt` THENL [
    SRW_TAC [][ptsize_def],
    SRW_TAC [numSimps.ARITH_ss][ptsize_def]
  ]);


val getSymbols = Define `(getSymbols [] = []) ∧  
(getSymbols ((Leaf tmnl)::t) =  (TS tmnl) :: (getSymbols t)) ∧
(getSymbols ((Node nt ptlist)::t) =  (NTS nt) :: (getSymbols t))`;

val ptreeToRules = Define 
`(ptreeToRules (Leaf tm) = []) ∧
(ptreeToRules (Node nt ptl) = 
(rule nt (getSymbols ptl)) :: (ptreeToRules2 ptl)) ∧
(ptreeToRules2 [] = []) ∧
(ptreeToRules2 (h::t) = (ptreeToRules h) ++ (ptreeToRules2 t))`;

val checkRules = Define 
 `(checkRules [] rls = T) ∧
  (checkRules (h::t) rls <=> MEM h rls ∧ checkRules t rls)`;

val ptreeSubtSyms = Define 
`(ptreeSubtSyms (Node nt tl) = MAP ptree2Sym tl) ∧
 (ptreeSubtSyms (Leaf  tm) = [])`;

val ptreeSubtree = Define 
`(ptreeSubtree (Node x l) = l) ∧
(ptreeSubtree (Leaf tm) = [])`;

val validptree_defn = Hol_defn "validptree_defn" 
 `(validptree g (Node n ptl) <=>  
      MEM (rule n (getSymbols ptl)) (rules g) ∧
      (∀e. MEM e ptl ⇒ isNode e ⇒ validptree g e)) ∧
  (validptree g (Leaf tm) <=> F)`;

val (validptree, validptree_ind) = tprove (validptree_defn,
WF_REL_TAC (`measure (\(g,e).ptsize e)`) THEN
SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ptsizel_append] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [ptsize_def] THEN
DECIDE_TAC);

val _ = save_thm ("validptree",validptree)
val _ = save_thm ("validptree_ind",validptree_ind)

val leaves_def = Define 
`(leaves (Leaf tm) = [tm]) ∧
 (leaves (Node nt ptlist) = cleaves ptlist) ∧
 (cleaves [] = []) /\ (cleaves (h::t) = leaves h ++ cleaves t)`;

val flat_leaves = store_thm("flat_leaves", 
``∀l.(leaves (Node n l)) = FLAT (MAP leaves l)``,
Induct_on `l` THEN SRW_TAC [] [leaves_def, MAP, FLAT] THEN
METIS_TAC [leaves_def]);

val getSyms_append = store_thm ("getSyms_append", 
``getSymbols (l1++l2) = getSymbols l1 ++ getSymbols l2``,
Induct_on `l1` THEN SRW_TAC [] [getSymbols] THEN
Cases_on `h` THEN SRW_TAC [] [getSymbols] THEN
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [getSymbols]
);

val getSymsEqptree2sym = store_thm ("getSymsEqptree2Sym", 
``getSymbols l = MAP (ptree2Sym) l``,
Induct_on `l` THEN SRW_TAC [] [getSymbols] THEN
`getSymbols (h::l) = getSymbols [h] ++ getSymbols l` 
by METIS_TAC [getSyms_append, APPEND] THEN
Cases_on `h` THEN Cases_on `l` THEN 
METIS_TAC [ptree2Sym, getSymbols]
);

val mapSymsptree = store_thm ("mapSymsptree",
``MAP (ptree2Sym o SND) p = getSymbols (MAP SND p)``,
Induct_on `p` THEN SRW_TAC [] [getSymbols] THEN
Cases_on `h` THEN Cases_on `r` THEN 
FULL_SIMP_TAC (srw_ss()) [getSymbols, ptree2Sym, SND] THEN
Induct_on `MAP SND p` THEN 
METIS_TAC [getSyms_append, getSymsEqptree2sym, getSymbols]);


val getSyms_len = store_thm ("getSyms_len",
``∀l.LENGTH l = LENGTH (getSymbols l)``,
Induct_on `l` THEN SRW_TAC [] [getSymbols, LENGTH] THEN
Cases_on `h` THEN Induct_on `l` THEN 
SRW_TAC [] [getSymbols, LENGTH]);
    
val take1_getSyms = store_thm ("take1_getSyms",
``∀l n.(LENGTH l >= n) ⇒ 
(take1 n (getSymbols l) = getSymbols (take1 n l))``,
Induct_on `n` THEN Induct_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [take1, getSymbols] THENL[

FULL_SIMP_TAC (arith_ss) [],

`LENGTH l >= n` by FULL_SIMP_TAC (arith_ss) [] THEN
RES_TAC THEN
`getSymbols (h::l) = getSymbols [h] ++ getSymbols l` by METIS_TAC [APPEND, getSyms_append] THEN
SRW_TAC [] [] THEN

Cases_on `h` THEN
FULL_SIMP_TAC (arith_ss) [take1, getSymbols] THENL[

`take1 (SUC n) ([(TS (tmnlToStr t))]++ getSymbols l) = 
take1 (SUC n) (TS (tmnlToStr t) :: getSymbols l)` by METIS_TAC [APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [take1],

`take1 (SUC n) ([(NTS (nonTmnlToStr n'))]++ getSymbols l) = 
take1 (SUC n) (NTS (nonTmnlToStr n') :: getSymbols l)` by METIS_TAC [APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [take1]
]]);

val take_getSyms = store_thm ("take_getSyms",
``∀n l.(take n (MAP SND l) = SOME x) ⇒ 
(THE (take n  (getSymbols (MAP SND l))) = getSymbols (THE (take n (MAP SND l))))``,
Induct_on `l` THEN SRW_TAC [] [] THENL[
Induct_on `n` THEN FULL_SIMP_TAC (srw_ss()) [take_def, getSymbols] THENL[
METIS_TAC [getSymbols, take10],
SRW_TAC [] [] THEN FULL_SIMP_TAC (arith_ss) [take10]],
`LENGTH (SND h::MAP SND l) >= n` by METIS_TAC [take_len, NOT_SOME_NONE] THEN
Cases_on `n` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (arith_ss) [] THEN METIS_TAC [take0, THE_DEF, take10],
FULL_SIMP_TAC (srw_ss()) [take_def] THEN
`LENGTH (getSymbols (SND h::MAP SND l)) = LENGTH (SND h::MAP SND l)` by 
METIS_TAC [getSyms_len] THEN
`LENGTH l = LENGTH (MAP SND l)` by METIS_TAC [LENGTH_MAP] THEN
`SUC (LENGTH l) = LENGTH (SND h::MAP SND l)` by METIS_TAC [LENGTH] THEN
`LENGTH (getSymbols (SND h::MAP SND l)) >= SUC n'` by METIS_TAC [] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [take1_getSyms]]]);


val checkRules_append = store_thm
("checkRules_append", 
 ``checkRules (l1++l2) rs <=> checkRules l1 rs ∧ checkRules l2 rs``,
 SRW_TAC [] [EQ_IMP_THM] THENL[
 Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [checkRules],
 Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [checkRules],
 Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [checkRules]]
);

val ptreeToRules_append = store_thm ("ptreeToRules_append", 
``ptreeToRules2 (l1++l2) = ptreeToRules2 l1 ++ ptreeToRules2 l2``,
Induct_on `l1` THEN SRW_TAC [] [ptreeToRules]
);

val getSyms_nil = store_thm ("getSyms_nil", 
``(getSymbols l = []) ⇒ (l=[])``,
Induct_on `l` THEN SRW_TAC [] [getSymbols] THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [getSymbols] THEN
Induct_on `l` THEN
METIS_TAC [NULL, getSymbols]);

val getSyms_rev = store_thm ("getSyms_rev",
``getSymbols (REVERSE x) = REVERSE (getSymbols x)``,
Induct_on `x` THEN SRW_TAC [] [REVERSE_DEF, getSymbols] THEN
FULL_SIMP_TAC (srw_ss()) [getSyms_append] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [getSymbols] THEN
Induct_on `x` THEN FULL_SIMP_TAC (srw_ss()) [getSymbols]);


val getSymsEqRoot = store_thm
("getSymsEqRoot",
``∀ptl.getSymbols ptl = MAP root ptl``,

Induct_on `ptl` THEN SRW_TAC [][root, getSymbols] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [root, getSymbols]);


val sym2ptree = Define
`(sym2ptree (TS s) = Leaf s) ∧
 (sym2ptree (NTS n) = Node n [])`;

val getSymsTmsEq = store_thm
("getSymsTmsEq",
``EVERY isTmnlSym x ⇒ 
(getSymbols (MAP Leaf (MAP ts2str x)) = x)``,

Induct_on `x` THEN SRW_TAC [][isTmnlSym_def, getSymbols, ts2str_def]);

val fringeTmsEq = store_thm
("fringeTmsEq",
``EVERY isTmnlSym x ⇒ 
(MAP TS (FLAT (MAP fringe (MAP Leaf (MAP ts2str x)))) = x)``,

Induct_on `x` THEN SRW_TAC [][ts2str_def, isTmnlSym_def, fringe_def]);


val height_defn = Hol_defn "height_defn"
`(height (Leaf tm) = 0) ∧
 (height (Node n l) = 1 + max 0 (MAP height l))`;


val (height_def, height_ind) = tprove (height_defn,
WF_REL_TAC (`measure ptsize`) THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ptsizel_append] THEN
DECIDE_TAC);

val _ = save_thm ("height_def",height_def)
val _ = save_thm ("height_ind",height_ind)

val getSymsNtm = store_thm
("getSymsNtm",
``(getSymbols l = [NTS n1; NTS n2]) ⇒ ∃t1 t2. (l = [Node n1 t1; Node n2 t2])``,

SRW_TAC [][] THEN
`LENGTH l = 2` by METIS_TAC [getSyms_len, list_lem2] THEN
FULL_SIMP_TAC (srw_ss()) [list_lem2] THEN
SRW_TAC [][] THEN
Cases_on `e1` THEN Cases_on `e2` THEN 
FULL_SIMP_TAC (srw_ss()) [getSymbols]);

val getSymsTm = store_thm
("getSymsTm",
``(getSymbols l = [TS t]) ⇒  (l = [Leaf t])``,

SRW_TAC [][] THEN
`LENGTH l = 1` by METIS_TAC [getSyms_len, list_lem1] THEN
FULL_SIMP_TAC (srw_ss()) [list_lem1] THEN
SRW_TAC [][] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [getSymbols]);


val mapFringeLeaves = store_thm
("mapFringeLeaves",
``∀ptl. (∀t.t ∈ ptl ⇒ (fringe t = leaves t)) ⇒ 
 (FLAT (MAP (λa. fringe a) ptl) = cleaves ptl)``,

Induct_on `ptl` THEN SRW_TAC [][leaves_def]);

val fringeEqLeaves = store_thm
("fringeEqLeaves",
``∀t. (fringe t = leaves t)``,

HO_MATCH_MP_TAC fringe_ind THEN SRW_TAC [][] THEN
SRW_TAC [][fringe_def, leaves_def] THEN
METIS_TAC [mapFringeLeaves]);

val treeSyms_defn = Hol_defn "treeSyms_defn"
`(treeSyms (Leaf tm) =  ([TS tm]:(α,β) symbol list)) ∧
(treeSyms (Node n t) =  (NTS n) :: (FLAT (MAP treeSyms t)))`;

val (treeSyms, treeSyms_ind) = tprove (treeSyms_defn,
WF_REL_TAC (`measure ptsize`) THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ptsizel_append] THEN
DECIDE_TAC);

val _ = save_thm ("treeSyms_def",treeSyms)
val _ = save_thm ("treeSyms_ind",treeSyms_ind)


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
`btree B st t <=> (root st = B) ∧  isSubtree st t`;

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

val treeSymsImpSubtree = store_thm
("treeSymsImpSubtree",
``∀t. e ∈ treeSyms t ⇒ ∃t1. isSubtreeEq t1 t ∧ (root t1 = e)``,

completeInduct_on `height t` THEN SRW_TAC [][] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [height_def, treeSyms] THEN1
(SRW_TAC [][isSubtreeEq] THEN
Q.EXISTS_TAC `Leaf t'` THEN
SRW_TAC [][root] THEN
Q.EXISTS_TAC `[]` THEN SRW_TAC [][subtree]) THEN1
(SRW_TAC [][] THEN
Q.EXISTS_TAC `Node n l` THEN
SRW_TAC [][root, isSubtreeEq] THEN
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

val numd = store_thm
("numd",
 ``∀t. isNode t ⇒ LENGTH (distinctNtms t) ≥ 1``,

Cases_on `t` THEN SRW_TAC [][distinctNtms, treeSyms, rmDupes, delete_def,isNode,
			     rmDupes, FILTER_APPEND, isNonTmnlSym_def] THEN
DECIDE_TAC);

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
METIS_TAC [isNode]) THEN
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
Cases_on `t1` THEN FULL_SIMP_TAC (srw_ss()) [isNode]) THEN
`height (EL h l) < height (Node n l)` by METIS_TAC [isSubtree, subtreeHeight] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`height (EL h l)`] MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`EL h l`] MP_TAC) THEN SRW_TAC [][] THEN
`validptree g (Node n' l')` by
(FULL_SIMP_TAC (srw_ss()) [validptree] THEN
METIS_TAC [isNode, EL_IS_EL, validptree]) THEN
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

val cnfTree = store_thm
("cnfTree",
``∀g tree. 
     validptree g tree ⇒ 
     isCnf g ⇒ 
     ∀n t. (tree = Node n t) ⇒
           ∃n1 t1 n2 t2. 
              (t = [Node n1 t1; Node n2 t2]) ∨ ∃ts.(t = [Leaf ts])``,

HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [validptree, isCnf_def] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [list_lem2, list_lem1] THEN1
(Cases_on `e1` THEN Cases_on `e2` THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isNode] THEN1
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
 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isNode] THEN
`∃t1 t2.ptl = [Node n' t1; Node n'' t2]` by METIS_TAC [getSymsNtm] THEN
SRW_TAC [][leaves_def] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (leaves (Node n' t1)) ≥ 1`by METIS_TAC [isNode] THEN
`LENGTH (leaves (Node n'' t2)) ≥ 1`by METIS_TAC [isNode] THEN
FULL_SIMP_TAC (srw_ss()++ARITH_ss) [leaves_def]) THEN
Cases_on `e` THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
`(ptl = [Leaf t])` by METIS_TAC [getSymsTm] THEN
SRW_TAC [][leaves_def]);


val rootRep = Define
`rootRep st t <=> (root st = root t) ∧  isSubtree st t`;


val symRepProp = Define
`symRepProp t0 t1 t <=> isSubtreeEq t1 t ∧ rootRep t0 t1`;

val subtreeNotSymProp = store_thm
("subtreeNotSymProp",
``(subtree t p = SOME t1) ∧ (¬∃s0 s1. symRepProp s0 s1 t) ⇒
 ¬∃s0 s1. symRepProp s0 s1 t1``,

SRW_TAC [][symRepProp] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN 
FULL_SIMP_TAC (srw_ss()) [btree] THEN
`isSubtreeEq t1 t` by METIS_TAC [isSubtreeEq, option_CLAUSES] THEN
METIS_TAC [subtreeEqTrans,root, isSubtree, root, isSubtreeEq]);

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
(FULL_SIMP_TAC (srw_ss()) [symRepProp, isSubEqImpSub, rootRep, root] THEN
METIS_TAC [isSubtree, subtreeTrans]) THEN
METIS_TAC []);




val mlDir = ref ("./theoryML/");
(*
val _ =
 let open EmitML
 in emitML (!mlDir)
   ("parseTree",
OPEN ["num", "regexp"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: DATATYPE `ptree = Leaf of string | Node of string => ptree list`
    :: DEFN ptree2Sym
    :: [])
 end;
*)
val _ = export_theory ();

