(* A theory about parse trees *)
open HolKernel boolLib bossLib Parse Defn BasicProvers

open stringTheory grammarDefTheory symbolDefTheory listTheory pairTheory
optionTheory

open listLemmasTheory

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

val checkRules = Define `(checkRules [] rls = T) ∧
(checkRules (h::t) rls = (MEM h rls) ∧ checkRules t rls)`;



val ptreeSubtSyms = Define 
`(ptreeSubtSyms (Node nt tl) = MAP ptree2Sym tl) ∧
(ptreeSubtSyms (Leaf  tm) = [])`;

val ptreeSubtree = Define 
`(ptreeSubtree (Node x l) = l) ∧
(ptreeSubtree (Leaf tm) = [])`;

val validptree_defn = Hol_defn "validptree_defn" 
    `(validptree g (Node n ptl) =
      MEM (rule n (getSymbols ptl)) (rules g) ∧
      (∀e.MEM e ptl ⇒ isNode e ⇒ validptree g e)) ∧
(validptree g (Leaf tm) = F)`;

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


val checkRules_append = store_thm("checkRules_append", 
``checkRules (l1++l2) rs = checkRules l1 rs ∧ checkRules l2 rs``,
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

