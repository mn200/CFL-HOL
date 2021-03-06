(* A theory about parse trees *)
open HolKernel boolLib bossLib Parse Defn BasicProvers

open stringTheory grammarDefTheory symbolDefTheory listTheory pairTheory
    optionTheory relationTheory boolSimps rich_listTheory pred_setTheory

open listLemmasTheory parseTreeTheory grammarDefTheory relationLemmasTheory    

val _ = new_theory "treeDeriv";

val _ = Globals.linewidth := 60
val _ = set_trace "Unicode" 1


(* used to be lem1 in slr-parsing *)
val treeRtc = store_thm("treeRtc",
``(∀t. MEM t ptl ∧ isNode t ⇒ RTC (derives g) [ptree2Sym t] (MAP TS (leaves t))) 
  ⇒ 
  RTC (derives g) (MAP ptree2Sym ptl) (MAP TS (cleaves ptl))``,

Induct_on `ptl` THEN  SRW_TAC [] [ptree2Sym_def, leaves_def, RTC_RULES] THEN
Cases_on `h` THEN SRW_TAC [] [ptree2Sym_def, leaves_def] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [isNode_def, ptree2Sym_def, leaves_def] 
THENL[
`RTC (derives g) [(TS t)] [(TS t)]` by METIS_TAC [RTC_RULES] THEN
METIS_TAC [derives_append, APPEND],
METIS_TAC [derives_append, APPEND]]);

val vpt_rtcd = store_thm ("vpt_rtcd",
``∀g t. validptree g t ⇒ 
         RTC (derives g) [ptree2Sym t] (MAP TS (leaves t))``,
HO_MATCH_MP_TAC validptree_ind THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [validptree] THEN
`derives g [NTS n] (MAP ptree2Sym ptl)` by METIS_TAC [res1, getSymsEqptree2Sym] THEN
Q_TAC SUFF_TAC `RTC (derives g) (MAP ptree2Sym ptl) (MAP TS (leaves (Node n ptl)))` 
THENL[
SRW_TAC [] [ptree2Sym_def] THEN METIS_TAC [RTC_RULES, getSymsEqptree2Sym],
METIS_TAC [treeRtc, leaves_def]]);


val leafRtcd = store_thm
("leafRtcd",
``∀t.isLeaf t ⇒ (derives g)^* [root t] (MAP TS (fringe t))``,

Cases_on `t` THEN
SRW_TAC [][isLeaf_def, root_def, fringe_def]);

val ptlRtcd = store_thm
("ptlRtcd",
``∀ptl.(∀e.MEM e ptl ⇒ (derives g)^* [root e] (MAP TS (fringe e))) 
 ⇒
(derives g)^* (MAP root ptl) (MAP TS (FLAT  (MAP fringe ptl)))``,

Induct_on `ptl` THEN SRW_TAC [][] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [root_def, fringe_def] THEN1
METIS_TAC [rtc_derives_same_append_left, APPEND] THEN
`(derives g)^* [NTS n] (MAP TS (fringe (Node n l)))` by METIS_TAC [root_def] THEN
FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss) [fringe_def] THEN
METIS_TAC [derives_append, APPEND]);

val vptRtcd = store_thm
("vptRtcd",
``∀g t.validptree g t ⇒ (derives g)^* [root t] (MAP TS (fringe t))``,

HO_MATCH_MP_TAC validptree_ind THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [root_def, validptree] THEN
 `(∀e.MEM e ptl ⇒ (derives g)^* [root e] (MAP TS (fringe e)))` 
 by (SRW_TAC [][] THEN
     Cases_on `e` THEN 
     FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss) [root_def, fringe_def] THEN
     FULL_SIMP_TAC (srw_ss()) [validptree] THEN
     `isNode (Node n' l)` by SRW_TAC [][isNode_def] THEN
     RES_TAC THEN
     FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss) [root_def, fringe_def]) THEN
FULL_SIMP_TAC (srw_ss()) [validptree] THEN
`(derives g)^* [NTS n] (MAP TS (FLAT (MAP fringe ptl)))` 
by METIS_TAC [getSymsEqRoot, ptlRtcd, res1, RTC_RULES] THEN
Cases_on `ptl=[]` THEN 
FULL_SIMP_TAC (srw_ss()++boolSimps.ETA_ss) [getSymbols_def, fringe_def]);


val lpexImpvpt = store_thm
("lpexImpvpt",
``∀l.(∀a b.MEM (a,b) l ⇒  
   (isNonTmnlSym a ⇒ 
    ∃t.validptree g t ∧ (MAP TS (fringe t) = b) ∧ (root t = a)) ∧
      (isTmnlSym a ⇒ ([a]=b))) ⇒
∃ts.(MAP root ts = MAP FST l) ∧ 
(MAP TS (FLAT (MAP fringe ts)) = FLAT (MAP SND l)) ∧
(∀e.MEM e ts ∧ isNode e ⇒ validptree g e)``,

Induct_on `l` THEN SRW_TAC [][] THEN
Cases_on `h` THEN
Cases_on `q` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
(`∃t.validptree g t ∧ (MAP TS (fringe t) = r) ∧ (root t = NTS n)`
by METIS_TAC [isNonTmnlSym_def, symbol_11] THEN
Q.EXISTS_TAC `t::ts` THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []) THEN
Q.EXISTS_TAC `Leaf t::ts` THEN
SRW_TAC [][root_def,fringe_def] THEN
`[TS t]=r` by METIS_TAC [isTmnlSym_def] THEN
METIS_TAC [APPEND, isNode_def]);


val rtcdImpVpt = store_thm
("rtcdImpVpt",
``∀A y.(derives g) ⊢ dl ◁ [NTS A] → y ⇒ 
 EVERY isTmnlSym y ⇒
 ∃t.validptree g t ∧ (MAP TS (fringe t) = y) ∧ (root t = NTS A)``,

completeInduct_on `LENGTH dl` THEN
SRW_TAC [][] THEN
Cases_on `dl` THEN1 
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

(FULL_SIMP_TAC (srw_ss()) [derives_def, listderiv_def, lreseq] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN

`derives g h h' ∧ derives g ⊢ h'::t' ◁ h' → y` by METIS_TAC [listDerivHdBrk] THEN
`h = [NTS A]` by FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
`∃l.(h' = MAP FST l) ∧ (y = FLAT (MAP SND l)) ∧
 ∀a b. MEM (a,b) l ⇒  ∃dl'. LENGTH dl' ≤ LENGTH (h'::t') ∧ 
 derives g ⊢ dl' ◁ [a] → b` by METIS_TAC [listPairExistsLd] THEN
SRW_TAC [][] THEN
`∀a b.MEM (a,b) l ⇒
 (isNonTmnlSym a ⇒ ∃t.validptree g t ∧ (MAP TS (fringe t) = b) ∧ 
 (root t = a)) ∧ (isTmnlSym a ⇒ ([a]=b))` by
(SRW_TAC [][] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH dl' < SUC (SUC (LENGTH t'))` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH dl'`] MP_TAC) THEN SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`dl'`] MP_TAC) THEN SRW_TAC [][] THEN1
(Cases_on `a` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`n`,`b`] MP_TAC) THEN SRW_TAC [][] THEN
`EVERY isTmnlSym b` by 
 (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
 SRW_TAC [][] THEN
 FULL_SIMP_TAC (srw_ss()) [FLAT_APPEND]) THEN
METIS_TAC []) THEN 
Cases_on `a` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
Cases_on `dl'` THEN FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq]) THEN
`∃ts.(MAP root ts = MAP FST l) ∧ (MAP TS (FLAT (MAP fringe ts)) = FLAT (MAP SND l)) ∧
(∀e.MEM e ts ∧ isNode e ⇒ validptree g e)`
by METIS_TAC [lpexImpvpt] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq] THEN
Q.EXISTS_TAC `Node A ts` THEN
SRW_TAC [boolSimps.ETA_ss][validptree, fringe_def, root_def] THEN
METIS_TAC [getSymsEqRoot]);


val ptLangThm = store_thm
("ptLangThm",
``∀w. w ∈ language g <=> 
 ∃t.validptree g t ∧ (MAP TS (fringe t) = w) ∧
 (root t = NTS (startSym g))``,

SRW_TAC [][language_def, EXTENSION, EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[

IMP_RES_TAC rtc2list_exists' THEN
METIS_TAC [rtcdImpVpt],

METIS_TAC [vptRtcd, root_def],

SRW_TAC [][EVERY_MEM] THEN
Cases_on `e` THEN 
FULL_SIMP_TAC (srw_ss()) [MEM_MAP, isTmnlSym_def]]);

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
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [subtree_def] THEN
SRW_TAC [][] THEN1
(MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
SRW_TAC [][]) THEN

Cases_on `h < LENGTH ptl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `EL h ptl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

(Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [subtree_def] THEN
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


val _ = export_theory();
