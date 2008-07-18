open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory

open regexpTheory grammarDefTheory boolLemmasTheory listLemmasTheory
parseTreeTheory parserDefTheory yaccDefTheory


val _ = new_theory "parseProp2Def";

(* 2. All the trees associated with nonterminal symbols on the stack
correspond to a rule in the grammar*)

val stacktreeleaves = Define `(stacktreeleaves [] = []) /\
(stacktreeleaves (((sym, itl),tree)::rst) = (leaves tree)++stacktreeleaves rst )`

val prop2 = Define `prop2 orig sl stl = (stacktreeleaves stl ++ sl = orig)`


val addrule_stkl = store_thm ("revTakeMap",
``!p l r nt ptl.(addRule p (rule l r) = SOME (Node nt ptl)) ==> 
(ptl = REVERSE (MAP SND (THE (take (LENGTH r) p))))``,
SRW_TAC [] [addRule_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [buildTree_def, LET_THM] THEN
Cases_on `take (LENGTH (REVERSE r)) (MAP (ptree2Sym o SND) p)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `REVERSE r = x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH r = LENGTH x` by METIS_TAC [rev_len] THEN
`(LENGTH p) = LENGTH (MAP (ptree2Sym o SND) p)` by METIS_TAC [LENGTH_MAP] THEN
`~( take (LENGTH x) (MAP (ptree2Sym o SND) p) = NONE)` by FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH p) >= LENGTH x ` by METIS_TAC [take_len] THEN
SRW_TAC [] [] THEN
METIS_TAC [revTakeMap, takeCoMap])

val addrule_ntLf = store_thm ("addrule_ntLf",
``(addRule p (rule l r) = SOME x) ==> ~(isLeaf x)``,
SRW_TAC [] [addRule_def, LET_THM] THEN
SRW_TAC [] [isLeaf_def]
)

val stl_append = store_thm ("stl_append", 
``!l1 l2.stacktreeleaves (l1++l2) = stacktreeleaves l1 ++ stacktreeleaves l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [stacktreeleaves] THEN
Cases_on `h'` THEN Cases_on `q` THEN 
METIS_TAC [stacktreeleaves, APPEND, APPEND_ASSOC]
)


val stl_map = store_thm ("stl_map",
``!l.stacktreeleaves l = leaves (Node n (MAP SND l))``,
Induct_on `l` THEN SRW_TAC  [] [stacktreeleaves, leaves_def] THEN
Cases_on `h` THEN 
Cases_on `q` THEN Cases_on `r` THEN 
SRW_TAC [] [stl_append, stacktreeleaves, leaves_def]
)


val addrule_len = store_thm("addrule_len", 
``(addRule sl (rule l r) = SOME x) ==> ((LENGTH sl) >= LENGTH r)``,
SRW_TAC [] [addRule_def, LET_THM, buildTree_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(LENGTH sl) >= (LENGTH (REVERSE r))` by METIS_TAC [take_len, NOT_SOME_NONE, LENGTH_MAP] THEN
METIS_TAC [rev_len])


val addrule_leaves = store_thm ("addrule_leaves",
``(addRule stl (rule l r) = SOME (Node nt ptl)) ==> 
((MAP SND stl) = ((REVERSE ptl) ++ (pop (MAP SND stl) (LENGTH r))))``,
SRW_TAC [] [] THEN
`(LENGTH stl) >= LENGTH  r` by METIS_TAC [addrule_len] THEN
`ptl = REVERSE (MAP SND (THE (take (LENGTH r) stl)))` by METIS_TAC [addrule_stkl] THEN
`(REVERSE ptl) = (MAP SND (THE (take (LENGTH r) stl)))` by METIS_TAC [REVERSE_REVERSE] THEN
`?x.((take (LENGTH r) stl) = SOME x)` by METIS_TAC [take_valid] THEN
`((MAP SND (THE (take (LENGTH r) stl)) = 
(THE (take (LENGTH r) (MAP SND stl)))))` by METIS_TAC [take_map] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH stl = LENGTH (MAP SND stl)` by METIS_TAC [LENGTH_MAP] THEN
`(take (LENGTH r) (MAP SND stl)) = SOME (REVERSE ptl)` by METIS_TAC [option_r1, option_CLAUSES,
valid_take_map] THEN


`(LENGTH stl) = LENGTH (MAP SND stl)` by METIS_TAC [LENGTH_MAP] THEN
`(LENGTH (MAP SND stl)) >= LENGTH r` by METIS_TAC [] THEN

Cases_on `~(LENGTH r = 0)` THENL[
`?sfx.((MAP SND stl) = (REVERSE ptl) ++ sfx) /\ (sfx = pop (MAP SND stl) (LENGTH r))` by
METIS_TAC [take_pop] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(REVERSE (MAP SND stl)) = REVERSE (REVERSE ptl ++ pop (MAP SND stl) (LENGTH r))`
by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND, REVERSE_REVERSE],

FULL_SIMP_TAC (arith_ss) [pop0] THEN
`r=[]` by METIS_TAC [LENGTH_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [addRule_def, LET_THM] THEN
Cases_on `buildTree stl []` THEN
FULL_SIMP_TAC (srw_ss()) [take0, buildTree_def, take_def, LET_THM] THEN
Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [REVERSE_DEF, APPEND_NIL, APPEND]])




val stlEq = store_thm ("stlEq",
``!stl.(stacktreeleaves stl) = FLAT (MAP leaves (MAP SND stl))``,
Induct_on `stl` THEN SRW_TAC [] [stacktreeleaves, MAP, FLAT] THEN
Cases_on `h` THEN Cases_on `q` THEN 
FULL_SIMP_TAC (srw_ss()) [stacktreeleaves, leaves_def]
)


val red_stkleaves = store_thm ("red_stkleaves", 
``(doReduce m (sym::rst,stl,(s, itl)::csl) r = 
SOME (sl',stl',csl')) ==> ((stacktreeleaves (REVERSE stl)) = stacktreeleaves (REVERSE stl'))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, Abbrev_def] THEN
Cases_on `isNonTmnlSym sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `r` THEN 
Cases_on `x` THENL[
METIS_TAC [addrule_ntLf, isLeaf_def],
SRW_TAC [] [ruleRhs_def, ruleLhs_def, stl_append, stacktreeleaves] THEN
`(LENGTH stl) >= LENGTH l` by METIS_TAC [addrule_len] THEN
`(MAP SND stl) = (REVERSE l') ++ (pop (MAP SND stl) (LENGTH l))` by 
METIS_TAC [addrule_leaves] THEN
FULL_SIMP_TAC (srw_ss()) [stlEq] THEN
FULL_SIMP_TAC (srw_ss()) [map_rev] THEN
ONCE_ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [MAP_APPEND, FLAT_APPEND_DISTRIB, REVERSE_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [map_pop] THEN
SRW_TAC [] [map_rev] THEN
SRW_TAC [] [flat_leaves]])

val red_sym = store_thm ("red_sym", 
``(doReduce m (sym::rst,stl,(s, itl)::csl) r = SOME (sl',stl',csl')) 
==> (sl'=sym::rst)``,
SRW_TAC [] [doReduce_def, LET_THM] THEN
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r))` THEN FULL_SIMP_TAC (srw_ss()) [])


(* 3. Leaves of all the ptrees on the stack + the remaining input symbols = original symbol list *)
val prop2thm = store_thm ("prop2thm",
``!m g.(m=slr g) ==> prop2 orig sl (REVERSE stl) ==> ((parse m (sl, stl, ((s, itl)::csl)) = SOME (sl',stl',csl'))) 
==> prop2 orig sl' (REVERSE stl')``,
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM, prop2] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `getState m itl e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `v1` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
(* 4 subgoals *)

METIS_TAC [red_stkleaves, red_sym, APPEND],

METIS_TAC [red_stkleaves, red_sym, APPEND],

Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`stl' = (((e,l),Leaf (TM (tmnlSym e)))::stl)` by SRW_TAC [] [] THEN
`sl'=h::t` by SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [stacktreeleaves, leaves_def,tmnlToStr_def, tmnlSym_def] THENL[
FULL_SIMP_TAC (srw_ss()) [stacktreeleaves, leaves_def, stl_append, tmnlToStr_def] THEN
METIS_TAC [APPEND, CONS, APPEND_ASSOC],
METIS_TAC [isNonTmnlSym_def]]])


val _ = export_theory ();