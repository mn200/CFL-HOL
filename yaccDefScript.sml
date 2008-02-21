open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory containerTheory pairTheory

open regexpTheory grammarDefTheory listLemmasTheory parserDefTheory
firstSetDefTheory followSetDefTheory containerLemmasTheory
setLemmasTheory boolLemmasTheory

val _ = new_theory "yaccDef"

val getItems = Define `
(getItems [] s = [])
/\ (getItems ((rule l r)::rs) s = if (l=s) then (item l ([],r)::getItems rs s) 
				  else getItems rs s)`

(* iclosure :: grammar -> item list -> item list *)
val iclosure1 = Define `(iclosure1 g [] = []) /\
(iclosure1 g ((item s (l1,[]))::il) = ((item s (l1,[]))::iclosure1 g il)) /\
(iclosure1 g ((item s (l1,TS ts::l2))::il) = 
 (((item s (l1,TS ts::l2)))::iclosure1 g il)) /\
(iclosure1 g ((item s (l1,NTS nt::l2))::il) = 
(getItems (rules g) nt ++ [(item s (l1,NTS nt::l2))] ++ iclosure1 g il))`



val iclosure_defn = Hol_defn "iclosure_defn" `(iclosure g [] = []) /\
(iclosure g il = 
	let
	    ril = rmDupes il
	    in
		let
		    al = rmDupes (iclosure1 g ril)
		in 
		    if ~(LIST_TO_SET ril = LIST_TO_SET al) then iclosure g al
		    else al)`


val rules2Items = Define `(rules2Items [] = []) /\
(rules2Items (rule l r::rst) = item l ([], r)::rules2Items rst)`

val iclosure1_mem = store_thm ("iclosure1_mem", 
``!e l.MEM e l ==> (MEM e (iclosure1 g l))``,
Induct_on `l` THEN SRW_TAC [] [] THENL[
Cases_on `e`  THEN Cases_on `p` THEN Cases_on `r` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
METIS_TAC [rmd_r2_1, MEM],
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
METIS_TAC [rmd_r2_1, MEM, APPEND, CONS, rgr_r9eq, MEM_APPEND]],
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN 
FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
METIS_TAC [rmd_r2_1, MEM, APPEND, CONS, rgr_r9eq, MEM_APPEND]])


val iclosure1_not_nil = store_thm ("iclosure1_not_nil", 
``!g x xs.~(iclosure1 g (x::xs) = [])``,
Cases_on `x` THEN Cases_on `p` THEN Cases_on `r` THENL[
SRW_TAC [] [iclosure1, rmDupes_not_nil],
Cases_on `h` THEN SRW_TAC [] [iclosure1, rmDupes_not_nil] THEN
Cases_on `getItems (rules g) s'` THEN SRW_TAC [] [iclosure1, rmDupes_not_nil]])

val iclosure1_len = store_thm ("iclosure1_len", 
``!g l.LENGTH (iclosure1 g l) >= LENGTH (rmDupes l)``,
Induct_on `iclosure1 g l` THEN SRW_TAC [] [] THEN
Induct_on `l` THEN SRW_TAC [] [iclosure1, rmDupes] THENL[
METIS_TAC [iclosure1_not_nil],
`~(iclosure1 g (h'::l) = [])` by METIS_TAC [iclosure1_not_nil] THEN
`!e.MEM e (h'::l) ==> MEM e (iclosure1 g (h'::l))` by METIS_TAC [iclosure1_mem] THEN
`LENGTH (h'::l) >= SUC (LENGTH l)` by FULL_SIMP_TAC (arith_ss) [LENGTH] THEN
`LENGTH (iclosure1 g (h'::l)) >= LENGTH (rmDupes (h'::l))` 
by METIS_TAC [mem_subset_len, rmd_r2] THEN
FULL_SIMP_TAC (arith_ss) [rmDupes, MEM, APPEND, LENGTH]])



val rules2items_sub = store_thm ("rules2items_sub",
``!e lhs rs.MEM e (getItems rs lhs) ==> MEM e (rules2Items rs)``,
Induct_on `rs` THEN SRW_TAC [] [getItems, rules2Items] THEN
Cases_on `h` THEN  FULL_SIMP_TAC (srw_ss()) [rules2Items, getItems] THEN
Cases_on `s=lhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [MEM, rules2Items, getItems, APPEND])

val iclosure1_outmem = store_thm ("iclosure1_outmem", 
``!e l.MEM e (iclosure1 g l) ==> ~(MEM e l) ==> (MEM e (rules2Items (rules g)))``,
Induct_on `l` THEN SRW_TAC [] [iclosure1] THEN
Cases_on `h` THEN  Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
Cases_on `h` THEN 
FULL_SIMP_TAC (srw_ss()) [iclosure1] THEN
METIS_TAC [rmd_r2_2, MEM, MEM_APPEND, rules2items_sub])


val iclosure1_before_after_len = store_thm ("iclosure1_before_after_len",
``!l.(CARD (set (iclosure1 g l)) > CARD (set l)) ==> 
((CARD (set (rules2Items (rules g)) INTER set (iclosure1 g l)) -
CARD (set (rules2Items (rules g)) INTER (set l))) > 0)``,
SRW_TAC [] [] THEN
`(set l) SUBSET (set (iclosure1 g l))` by METIS_TAC [mem_subset, iclosure1_mem] THEN
`?e.~(e IN set l) /\ (e IN set (iclosure1  g l))` by METIS_TAC [set_neq, FINITE_LIST_TO_SET] THEN
`MEM e (iclosure1 g l)` by METIS_TAC [IN_LIST_TO_SET] THEN
`~(MEM e l)` by METIS_TAC [IN_LIST_TO_SET] THEN
`MEM e (rules2Items (rules g))` by METIS_TAC [iclosure1_outmem] THEN
`e IN set (rules2Items (rules g))` by METIS_TAC [IN_LIST_TO_SET] THEN
`~(set l= set (iclosure1 g l))` by METIS_TAC [LIST_TO_SET_THM, IN_LIST_TO_SET] THEN
`(set l) PSUBSET set (iclosure1 g l)` by METIS_TAC [PSUBSET_DEF] THEN
`CARD (set l) < CARD (set (iclosure1 g l))` by METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET] THEN
`CARD (set l) < CARD (set (iclosure1 g l))` by METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET] THEN
`CARD (set l INTER (set (rules2Items (rules g)))) 
< CARD (set (iclosure1 g l) INTER (set (rules2Items (rules g))))` 
by METIS_TAC [card_same_inter, FINITE_LIST_TO_SET] THEN
FULL_SIMP_TAC (arith_ss) [INTER_COMM])


val (iclosure, iclosure_ind) = tprove(iclosure_defn,
WF_REL_TAC `measure (\(g,al).CARD (set (rules2Items (rules g)) DIFF (set al)))` THEN
SRW_TAC [] [] THENL[
(*1*)
`!e.MEM e (rmDupes (v2::v3)) ==> MEM e (iclosure1 g (rmDupes (v2::v3)))` by 
METIS_TAC [iclosure1_mem] THEN
`!e.MEM e (iclosure1 g (rmDupes (v2::v3))) ==> MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` 
by  METIS_TAC [rmd_r2] THEN
`!e.MEM e (rmDupes (v2::v3)) ==> MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` by METIS_TAC []
THEN
`LENGTH (rmDupes (iclosure1 g (rmDupes (v2::v3)))) >= LENGTH (rmDupes (v2::v3))` by
METIS_TAC [mem_subset_len] THEN
`CARD (set (rmDupes (iclosure1 g (rmDupes (v2::v3))))) >= CARD (set (rmDupes (v2::v3)))`  by 
METIS_TAC [list_set_len, rmDupes_twice] THEN
`!e.MEM e (rmDupes (v2::v3)) ==> MEM e (iclosure1 g (rmDupes (v2::v3)))` by 
METIS_TAC [iclosure1_mem] THEN
`(set (v2::v3)) SUBSET (set (iclosure1 g (rmDupes (v2::v3))))` by  
METIS_TAC [mem_subset, rmDupes_lts] THEN
`CARD (set (iclosure1 g (rmDupes (v2::v3)))) > CARD (v2 INSERT set v3)` by 
METIS_TAC [set_neq_len, iclosure1_mem, FINITE_LIST_TO_SET, mem_subset, LIST_TO_SET_THM, rmDupes_lts] THEN
`?e.e IN (set (iclosure1 g (rmDupes (v2::v3)))) /\ ~(e IN (v2 INSERT set v3))` by
METIS_TAC [set_neq, FINITE_LIST_TO_SET, rmDupes_lts, LIST_TO_SET_THM] THEN
`MEM e (iclosure1 g (rmDupes (v2::v3)))` by FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST] THEN
`~(MEM e (v2::v3))` by FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST] THEN
`MEM e (rules2Items (rules g))` by METIS_TAC [iclosure1_outmem, rmd_r2] THEN
`e IN (set (rules2Items (rules g)))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`~(e IN (v2 INSERT set v3))`  by FULL_SIMP_TAC (srw_ss()) [] THEN
`CARD (set (rules2Items (rules g))) - CARD (set (rules2Items (rules g)) INTER (v2 INSERT set v3)) > 0` by METIS_TAC [inter_card_less, FINITE_LIST_TO_SET] THEN
`CARD (set (rules2Items (rules g)) INTER set (rmDupes (iclosure1 g (rmDupes (v2::v3))))) -
CARD (set (rules2Items (rules g)) INTER (v2 INSERT set v3)) > 0` by 
METIS_TAC [iclosure1_before_after_len, LIST_TO_SET_THM, rmDupes_lts] THEN
FULL_SIMP_TAC (arith_ss) [],

(*2*)
`!e.MEM e (rmDupes (v2::v3)) ==> MEM e (iclosure1 g (rmDupes (v2::v3)))` by 
METIS_TAC [iclosure1_mem] THEN
`!e.MEM e (iclosure1 g (rmDupes (v2::v3))) ==> MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` 
by  METIS_TAC [rmd_r2] THEN
`!e.MEM e (rmDupes (v2::v3)) ==> MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` by METIS_TAC []
THEN
`LENGTH (rmDupes (iclosure1 g (rmDupes (v2::v3)))) >= LENGTH (rmDupes (v2::v3))` by
METIS_TAC [mem_subset_len] THEN
`CARD (set (rmDupes (iclosure1 g (rmDupes (v2::v3))))) >= CARD (set (rmDupes (v2::v3)))`  by 
METIS_TAC [list_set_len, rmDupes_twice] THEN
`!e.MEM e (rmDupes (v2::v3)) ==> MEM e (iclosure1 g (rmDupes (v2::v3)))` 
by METIS_TAC [iclosure1_mem] THEN
`(set (v2::v3)) SUBSET (set (iclosure1 g (rmDupes (v2::v3))))` by  
METIS_TAC [mem_subset, rmDupes_twice, LIST_TO_SET_THM, FINITE_LIST_TO_SET, rmDupes_lts] THEN
`CARD (set (iclosure1 g (rmDupes (v2::v3)))) > CARD (v2 INSERT set v3)` by 
METIS_TAC [set_neq_len, iclosure1_mem, FINITE_LIST_TO_SET, LIST_TO_SET_THM, rmDupes_lts] THEN
`?e.e IN (set (iclosure1 g (rmDupes (v2::v3)))) /\ ~(e IN (v2 INSERT set v3))` by
METIS_TAC [set_neq, FINITE_LIST_TO_SET, rmDupes_lts, LIST_TO_SET_THM] THEN
`MEM e (iclosure1 g (rmDupes (v2::v3)))` by FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST] THEN
`~(MEM e (v2::v3))` by FULL_SIMP_TAC (srw_ss()) [MEM_SET_TO_LIST, rmd_r2_1] THEN
`MEM e (rules2Items (rules g))` by METIS_TAC [iclosure1_outmem, rmd_r2] THEN
`e IN (set (rules2Items (rules g)))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`~(e IN (v2 INSERT set v3))`  by FULL_SIMP_TAC (srw_ss()) [] THEN
`CARD (set (rules2Items (rules g))) - CARD (set (rules2Items (rules g)) INTER (v2 INSERT set v3)) > 0` by METIS_TAC [inter_card_less, FINITE_LIST_TO_SET] THEN
FULL_SIMP_TAC (arith_ss) []])

val _ = save_thm ("iclosure", iclosure)
val _ = save_thm ("iclosure_ind", iclosure_ind)


val iclosure_nil = store_thm ("iclosure_nil", 
``!g l.~(l=[]) ==> ~(iclosure g l = [])``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [] THEN
SRW_TAC [] [iclosure, LET_THM] THEN
METIS_TAC [iclosure1_not_nil, rmDupes_not_nil, len_not_0, LENGTH_NIL])




val auggr = Define `(auggr g s eof = 	
         if ((~((NTS s) IN (nonTerminalsML g)) /\ (~ ((TS eof) IN (nonTerminalsML g))))) then 
         SOME (G ([(rule s [NTS (startSym g); TS eof])]++(rules g)) s) 
         else NONE)`


val ag_new_rule = store_thm("ag_new_rule", 
``!g s eof.(auggr g s eof = SOME ag)
==> (MEM (rule s [NTS (startSym g);TS eof]) (rules ag) /\ (s=startSym ag))``,
SRW_TAC [] [auggr, rules_def, MEM, startSym_def, APPEND, MEM_APPEND] THEN
SRW_TAC [] [auggr, rules_def, MEM, startSym_def, APPEND, MEM_APPEND])


val initProds2Items = Define `(initProds2Items s [] = []) /\
(initProds2Items s ((rule l r)::rs) = if (s=l) then (((item l ([],r)))::initProds2Items s rs) else initProds2Items s rs)`

val initItems = Define
(`(initItems g r = iclosure g (initProds2Items (startSym g) r))`)
(*
Induct_on `r` THEN SRW_TAC [] [initItems, initProds2Items, iclosure] THEN
Cases_on `h` THEN SRW_TAC [] [initItems, initProds2Items, iclosure] THEN

*)


(* Given an itemset and a symbol, move the dot to the right of the symbol *)
(*val moveDot = Define `moveDot its sym = {item s (pfx++[sym],sfx) | item s (pfx,[sym]++sfx) IN its}`*)


 val moveDot = Define `(moveDot [] sym = []) /\
 (moveDot ((item str (a,(s::ss)))::it) sym =  
if (s=sym) then (item str (a++[s],ss))::moveDot it sym else moveDot it sym) /\
 (moveDot (_::it) sym = moveDot it sym)`


(* nextState :: grammar -> item list -> symbol -> item list option *)

val nextState = Define `nextState g itl sym = iclosure g (moveDot itl sym)`

val validItl = Define `(validItl g [] = T) /\
(validItl g (item l (r1,r2) :: rst) = MEM (rule l (r1++r2)) (rules g) /\ validItl g rst)`

val validStates = Define `(validStates g [] = T) /\
(validStates g ((state sym itl)::rst) = validItl g itl /\ validStates g rst)`

val validItl_append = store_thm ("validItl_append",
``validItl g (l1++l2) = validItl g l1 /\ validItl g l2``,
SRW_TAC [] [EQ_IMP_THM] THENL [
Induct_on `l1` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [validItl] THEN 
Cases_on `h` THEN Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [validItl],
Induct_on `l2` THEN SRW_TAC [] [] THEN Induct_on `l1` THEN 
FULL_SIMP_TAC (srw_ss()) [validItl] THEN 
SRW_TAC [] [] THEN Cases_on `h'` THEN Cases_on `p` THEN 
FULL_SIMP_TAC (srw_ss()) [validItl],
Induct_on `l2` THEN SRW_TAC [] [] THEN Induct_on `l1` THEN 
FULL_SIMP_TAC (srw_ss()) [validItl] THEN 
SRW_TAC [] [] THEN Cases_on `h'` THEN 
Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [validItl]]
)


val validStates_append = store_thm ("validStates_append", 
``!l1 l2.validStates g (l1 ++ l2) = validStates g l1 /\ validStates g l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [validStates] THEN
Cases_on `h'` THEN METIS_TAC [validStates, APPEND])


val validStates_pop = store_thm ("validStates_pop", 
``!g l n.validStates g l ==> validStates g (pop l n)``,
METIS_TAC [popl, validStates_append])

val validItl_md = store_thm ("validItl_md",
``!itl sym.validItl g itl ==> validItl g (moveDot itl sym)``,
Induct_on `itl` THEN SRW_TAC [] [validItl, moveDot] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [validItl, moveDot] THEN
Cases_on `h=sym` THEN SRW_TAC [] [validItl] THEN 
METIS_TAC [APPEND, APPEND_ASSOC])


val validItl_rules_cons = store_thm ("validItl_rules_cons",
``!r s l e.validItl (G r s) l ==> validItl (G (e::r) s) l``,
SRW_TAC [] [] THEN
Induct_on `l` THEN SRW_TAC [] [validItl] THEN
Cases_on `h` THEN Cases_on `p`  THEN FULL_SIMP_TAC (srw_ss()) [validItl, rules_def])


val rules2items_sub2 = store_thm ("rules2items_sub2",
``!g.validItl g  (rules2Items (rules g))``,
Cases_on `g` THEN SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [validItl, rules2Items] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [validItl, rules_def, rules2Items] THEN
METIS_TAC [validItl_rules_cons])


val validItl_mem = store_thm ("validItl_mem",
``!l.validItl g l = (!e.MEM e l ==> validItl g [e])``,
Induct_on `l` THEN SRW_TAC [] [validItl, EQ_IMP_THM] THEN
METIS_TAC [validItl_append, APPEND])



val validItl_getItems = store_thm ("validItl_getItems",
``! g sym.validItl g (getItems (rules g) sym)``,
Induct_on `rules g` THEN SRW_TAC [] [validItl, getItems] THENL[
METIS_TAC [validItl, getItems],
`rules g = h::v` by METIS_TAC [] THEN 
Cases_on `h` THEN ONCE_ASM_REWRITE_TAC [] THEN
`!e.MEM e (getItems (rule s l::v) sym) ==> MEM e (rules2Items (rule s l::v))` by METIS_TAC [rules2items_sub] THEN
`validItl g (rules2Items (rule s l ::v))` by METIS_TAC [rules2items_sub2, rules_def] THEN
`!e.MEM e (rules2Items (rule s l::v)) ==> validItl g [e]` by METIS_TAC [validItl_mem] THEN
METIS_TAC [validItl_mem, APPEND, validItl_append]])

val validItl_iclosure1 = store_thm ("validItl_iclosure1", 
``!g itl.validItl g itl ==> validItl g (iclosure1 g itl)``,
Induct_on `itl` THEN SRW_TAC [] [validItl, iclosure1] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1, validItl] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1, validItl] THEN
METIS_TAC [validItl, validItl_append, APPEND, APPEND_ASSOC, validItl_getItems])


val validItl_delete = store_thm ("validItl_delete",
``!g t h.validItl g t ==> validItl g (delete h t)``,
Induct_on `t` THEN SRW_TAC [] [delete_def, validItl] THEN
METIS_TAC [validItl_append, APPEND])


val validItl_rmDupes = store_thm ("validItl_rmDupes", 
``!itl.validItl g itl ==> validItl g (rmDupes itl)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes, validItl] THEN
METIS_TAC [validItl_append, APPEND, validItl_delete])


val validItl_iclosure = store_thm ("validItl_iclosure",
``!g itl.validItl g itl ==> validItl g (iclosure g itl)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, validItl, LET_THM] THEN
METIS_TAC [validItl_rmDupes, validItl_iclosure1])

val sgoto = Define `sgoto g itl sym = nextState g itl sym`


val validItl_sgoto = store_thm ("validItl_sgoto", 
``!g itl sym.validItl g itl ==> validItl g (sgoto g itl sym)``,
SRW_TAC [] [sgoto, nextState] THEN
`validItl g (moveDot itl sym)` by METIS_TAC [validItl_md] THEN
METIS_TAC [validItl_iclosure])



val reduce = Define `
(reduce g [] s = []) /\ 
(reduce g (item l (r, [])::it) s  = 
if ((TS s) IN (followSetML g (NTS l))) then 
    ((rule l r)::reduce g it s) else reduce g it s) /\
(reduce g ((item l (r, _))::it) s = reduce g it s)`



val buildTree = Define `(buildTree p r = 
			 let s = take (LENGTH r) ((MAP (ptree2Sym o SND) p))
			 in
			     if (s=NONE) then NONE
				 else
				     if (r=THE s) then take (LENGTH r) (MAP SND p)
					 else NONE)`



val addRule = Define `(addRule p (rule l r) = 
         let x =  buildTree p (REVERSE r) in 
              if (x = NONE) then NONE else SOME  (Node (NT l) (REVERSE (THE x))))`

(* stack top is the first element *)
(* ptree is a stack of parsetrees *)

(*
Parsing procedure
If terminal symbol -> shift goto or reduce -> both then conflict
nonterminal symbol -> goto or reduce -> both then conflict
accept when all symbols read and only one parse tree exists
*)

val machine = Define `machine g = (sgoto g, reduce g)`

(* slr :: grammar -> machine option *)
(* 
if reduce returns more than 1 rule -> NONE
if reduce and goto are null -> NONE
if both are not null and return different states -> NONE
----------------
if ?itl1 itl2, sym IN grammar : sgoto g itl1 sym [] = itl2 /\ 
iclosure (reduce)
*)

val slr = Define `slr g =
let
sg = sgoto g and
red = reduce g
in
if (?itl sym.
let
(s = sg itl sym) and
 (r = red itl (sym2Str sym))
in
case (s,r) of (* ([],[]) dealt in the parser *)
 ((x::xs),(y::ys)) -> T
|| (_,(y::y'::ys)) -> T
|| otherwise -> F)
then NONE else SOME (sg,red)`


(*
1. get init closure
2. get all symbols in the grammar
3. build the graph

#of symbols after the dot decreases in the common rules between the
 old and the new state
*)

val ruleItems_defn = Hol_defn "ruleItems_defn" 
`(ruleItems (item l (r,[])) = [item l (r,[])]) /\
(ruleItems (item l ([],x::xs)) = item l ([],x::xs) :: ruleItems (item l ([x],xs))) /\
(ruleItems (item l (r1,x::xs))  = item l (r1,x::xs) :: ruleItems (item l (r1++[x],xs)))`

val itemPair = Define `itemPair (item l x) = x`


val (ruleItems, ruleItems_ind) = tprove (ruleItems_defn,
WF_REL_TAC `measure (\x.(LENGTH (SND (itemPair x))))` THEN SRW_TAC [] [itemPair, SND])

val allItems = Define `(allItems [] = []) /\
(allItems (rule l r::rs) = ruleItems (item l ([], r)) ++ allItems rs)`

val symNeighbour = Define `(symNeighbour g itl sym = rmDupes (iclosure g (moveDot itl sym)))`

val asNeighbours = Define `(asNeighbours g itl [] = []) /\
(asNeighbours g itl (x::xs) =  (symNeighbour g itl x::asNeighbours g itl xs))`


val visit_defn = Hol_defn "visit_defn" 
`(visit g sn itl = 
if ~(ALL_DISTINCT itl) \/ ~(validItl g itl) then [] else
let 
s = asNeighbours g itl (SET_TO_LIST (allSyms g)) 
in
		     let
			 rem = diff s sn
		     in
			 rem++(FLAT (MAP (visit g (sn++rem)) rem)))`

val validItem = Define `validItem g (item l (r1,r2)) = MEM (rule l (r1++r2)) (rules g)`

val isGrammarItl = Define `(isGrammarItl g itl = EVERY (validItem g) itl)`

val allGrammarItls = Define `allGrammarItls g = {itl | isGrammarItl g itl /\ ALL_DISTINCT itl}`

val finite_allItems = store_thm ("finite_allItems",
``!g.FINITE {i|MEM i (allItems (rules g))}``,
`!g.{i|MEM i (allItems (rules g))} = {i|i IN LIST_TO_SET (allItems (rules g))}` by METIS_TAC [setc_mem_in] THEN
SRW_TAC [] [EXTENSION])

val validItemRulesEqGrRules = store_thm ("validItemRulesEqGrRules",
``!g.{rule l (r1++r2) | validItem g (item l (r1,r2))} = (LIST_TO_SET (rules g))``,
SRW_TAC [] [validItem, SUBSET_DEF, EQ_IMP_THM, EXTENSION] THENL[
METIS_TAC [],
Cases_on `x` THEN Induct_on `l` THEN SRW_TAC [] [] THEN
 METIS_TAC [APPEND]])

val allItems_append = store_thm ("allItems_append",
``!l1 l2.allItems (l1++l2) = allItems l1 ++ allItems l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [allItems] THEN
Cases_on `h` THEN Cases_on `h'` THEN METIS_TAC [APPEND, APPEND_ASSOC, allItems]
)
    

val itemLhs = Define `itemLhs (item l r) = l`
val itemFstRhs = Define `itemFstRhs (item l r) = FST r`
val itemSndRhs = Define `itemSndRhs (item l r) = SND r`

val ruleItems_mem = store_thm ("ruleItems_mem",
``!it.MEM (item (itemLhs it) (itemFstRhs it++itemSndRhs it,[])) (ruleItems it)``,
HO_MATCH_MP_TAC ruleItems_ind THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [ruleItems, itemLhs, itemFstRhs, itemSndRhs] THEN
METIS_TAC [APPEND, APPEND_ASSOC])

val allMemRuleItems = store_thm ("allMemRuleItems",
``!it r1 r2.(itemSndRhs it = r1++r2) ==> MEM (item (itemLhs it) (itemFstRhs it++r1,r2)) (ruleItems it)``,
HO_MATCH_MP_TAC ruleItems_ind THEN SRW_TAC [] [ruleItems, itemFstRhs, itemSndRhs, itemLhs] THEN
Induct_on `r1` THEN SRW_TAC [] [] THEN METIS_TAC [APPEND, APPEND_NIL, APPEND_ASSOC])


val memRuleAllItems = store_thm ("memRuleAllItems",
``!l r rs.MEM (rule l r) rs ==> !r1 r2.(r=r1++r2) ==> MEM (item l (r1,r2)) (allItems rs)``,
Induct_on `rs` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [allItems] THENL[
`MEM (item (itemLhs (item l ([],r1++r2))) (itemFstRhs (item l ([],r1++r2)) ++r1,r2)) (ruleItems (item l ([],r1++r2)))`
by FULL_SIMP_TAC (srw_ss()) [allMemRuleItems, itemSndRhs] THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs, itemLhs, itemSndRhs],
Cases_on `h` THEN SRW_TAC [] [allItems]])


val itemEqRule = store_thm ("itemEqRule",
 ``!it.!s q r.MEM (item s (q,r)) (ruleItems it) ==> (s=itemLhs it) /\ (q++r = itemFstRhs it ++ itemSndRhs it)``,
HO_MATCH_MP_TAC ruleItems_ind THEN SRW_TAC [] [ruleItems, itemSndRhs, itemFstRhs, itemLhs] THEN
METIS_TAC [APPEND, APPEND_NIL, APPEND_ASSOC])

val memAllItemsRules = store_thm ("memAllItemsRules",
 ``!rs s q r.MEM (item s (q,r)) (allItems rs) ==> MEM (rule s (q++r)) rs``,
Induct_on `rs` THEN SRW_TAC [] [allItems] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [allItems] THEN
`(s = itemLhs (item s' ([], l))) /\ (q ++ r = itemFstRhs(item s' ([], l)) ++ itemSndRhs  (item s' ([], l)))` by METIS_TAC [itemEqRule] THEN
FULL_SIMP_TAC (srw_ss()) [itemLhs, itemFstRhs, itemSndRhs])


val validItemEqAllItems = store_thm ("validItemEqAllItems",
``!g.{x | validItem g x} = (LIST_TO_SET (allItems (rules g)))``,
Induct_on `rules g` THEN SRW_TAC [] [EXTENSION, EQ_IMP_THM] THEN
Cases_on `x` THEN Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [allItems, validItem] THEN
METIS_TAC [MEM, allItems, validItem, memRuleAllItems, memAllItemsRules])


val finite_validItem = store_thm ("finite_validItem",
``FINITE  (validItem g)``,
ASSUME_TAC lemma THEN
`{x|P x} = P` by SRW_TAC [] [EXTENSION, IN_DEF] THEN
`validItem g = {x | validItem g x}` by SRW_TAC [] [EXTENSION, IN_DEF] THEN
ONCE_ASM_REWRITE_TAC [] THEN
METIS_TAC [validItemEqAllItems, SUBSET_FINITE, FINITE_LIST_TO_SET])


val finite_allGrItls = store_thm ("finiteAllGrItls",
``!g.FINITE (allGrammarItls g)``,
SRW_TAC [] [allGrammarItls, isGrammarItl, setc_flem, finite_validItem])


val prop_mem = store_thm ("prop_mem", 
``!P l.MEM e (asNeighbours g itl l) ==> ?e'.MEM e' l /\ MEM e (asNeighbours g itl [e'])``,
Induct_on `l` THEN SRW_TAC [] [asNeighbours] THENL[
METIS_TAC [asNeighbours],
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e'`  THEN FULL_SIMP_TAC (srw_ss()) [asNeighbours] THEN METIS_TAC []])




val validItl_evmem = store_thm ("validItl_evmem", 
``!l.validItl g l = EVERY (validItem g) l``,
Induct_on `l` THEN SRW_TAC [] [validItl] THEN
Cases_on `h` THEN Cases_on `p` THEN METIS_TAC [validItl, validItem])


val validItl_symNeighbour = store_thm ("validItl_symNeighbour", 
``!itl.validItl g itl ==> EVERY (validItem g) (symNeighbour g itl sym)``,
SRW_TAC [] [symNeighbour] THEN
`validItl g (iclosure g (moveDot itl sym))` by METIS_TAC [validItl_iclosure, validItl_md] THEN
METIS_TAC [validItl_evmem, rmDupes_prop])


val symNeighbour_allDistinct = store_thm ("symNeighbour_allDistinct", 
``!g itl sym.ALL_DISTINCT (symNeighbour g itl sym)``,
METIS_TAC [symNeighbour, alld_rmd])



val ar1 = store_thm ("ar1", 
``!a b c.a >=c ==> (a < b + (a-c) = 0 < b-c)``,
SRW_TAC [] [EQ_IMP_THM] THEN
DECIDE_TAC)




val (visit, visit_ind) = tprove (visit_defn,
WF_REL_TAC (`measure (\(g,sn,itl).CARD ((allGrammarItls g )DIFF (LIST_TO_SET sn)))`) THEN
SRW_TAC [] [] THEN
`MEM a (asNeighbours g itl (SET_TO_LIST (allSyms g)))` by METIS_TAC [diff_mem] THEN
`?e'.MEM e' (SET_TO_LIST (allSyms g)) /\ MEM a (asNeighbours g itl [e'])` by METIS_TAC [prop_mem] THEN
FULL_SIMP_TAC (srw_ss()) [asNeighbours] THEN
`EVERY (validItem g) a` by METIS_TAC [validItl_symNeighbour] THEN
`ALL_DISTINCT a` by METIS_TAC [symNeighbour_allDistinct] THEN
`isGrammarItl g a` by METIS_TAC [isGrammarItl] THEN
`a IN (allGrammarItls g)` by SRW_TAC [] [allGrammarItls, EXTENSION] THEN
`~ (a IN LIST_TO_SET sn)` by METIS_TAC [diff_mem, mem_in] THEN
SRW_TAC [] [diff_DIFF] THEN
`FINITE (allSyms g)` by METIS_TAC [FINITE_LIST_TO_SET, finiteAllSyms] THEN
`FINITE (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF set sn)` by METIS_TAC [FINITE_LIST_TO_SET, FINITE_DIFF] THEN
`FINITE ((set sn) UNION (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF set sn))` by METIS_TAC [FINITE_LIST_TO_SET, FINITE_DIFF,
FINITE_UNION] THEN
`FINITE (allGrammarItls g)` by METIS_TAC [finite_allGrItls] THEN
FULL_SIMP_TAC (srw_ss()) [CARD_DIFF, FINITE_LIST_TO_SET, FINITE_DIFF, finite_allGrItls, FINITE_UNION] THEN SRW_TAC [] [] THENL[
`(symNeighbour g itl e') IN (allGrammarItls g INTER
       (set sn UNION
        (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF set sn)))` by FULL_SIMP_TAC (srw_ss()) [INTER_DEF] THEN
`~((symNeighbour g itl e') IN (allGrammarItls g INTER set sn))` by METIS_TAC [not_in_inter, mem_in, finite_allGrItls] THEN
`symNeighbour g itl e' IN (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`~(symNeighbour g itl e' IN (set sn))` by METIS_TAC [mem_in] THEN
`~((set sn) = (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn)))` by METIS_TAC [] THEN
`(CARD (allGrammarItls g) - CARD (allGrammarItls g INTER set sn)) > 0` by METIS_TAC [inter_card_less, INTER_COMM, finite_allGrItls] THEN
`(CARD (allGrammarItls g)) >= CARD (allGrammarItls g INTER set sn)` by DECIDE_TAC THEN
SRW_TAC [] [ar1] THEN
`(set sn) SUBSET (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`(set sn) PSUBSET (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn))` by METIS_TAC [PSUBSET_DEF] THEN
`CARD (set sn) < CARD (set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
             set sn))` by METIS_TAC [CARD_PSUBSET, FINITE_LIST_TO_SET, FINITE_UNION, FINITE_DIFF] THEN
`CARD (set sn INTER (allGrammarItls g)) < CARD (((set sn UNION
            (set (asNeighbours g itl (SET_TO_LIST (allSyms g))) DIFF
            set sn)) INTER (allGrammarItls g)))` by METIS_TAC [mem_in, card_same_inter, FINITE_UNION, FINITE_DIFF, FINITE_LIST_TO_SET] THEN
FULL_SIMP_TAC (arith_ss) [INTER_COMM],

`CARD (allGrammarItls g) - CARD ((allGrammarItls g) INTER (LIST_TO_SET sn)) > 0` by METIS_TAC [inter_card_less, finite_allGrItls, mem_in] 
THEN
DECIDE_TAC])


val slrML4Sym = Define `
(slrML4Sym g [] sym = SOME (sgoto g, reduce g)) /\
(slrML4Sym g (i::itl) sym = 
let
s = sgoto g i sym 
in
let
r = reduce g i (sym2Str sym)
in
case (s,r) of 
                     ([],[]) -> slrML4Sym g itl sym
                    || ([],[v12]) -> slrML4Sym g itl sym
                    || ([],v12::v16::v17) -> NONE
                    || (v8::v9,[]) -> slrML4Sym g itl sym
                    || (v8::v9,[v20]) -> NONE
                    || (v8::v9,v20::v26::v27) -> NONE)`


val slrML = Define `
(slrML g itl [] = SOME (sgoto g, reduce g)) /\
(slrML g itl (sym::rst) = 
if (slrML4Sym g itl sym = NONE) then NONE else slrML g itl rst)` 



val findItemInRules = Define `(findItemInRules (item l1 (r1,[])) [] = F) /\
(findItemInRules (item l1 (r1,[])) ((rule l2 r2)::rst) = T) /\
(findItemInRules (item l1 (r1,[])) (_::rst) = findItemInRules (item l1 (r1,[])) rst) /\
(findItemInRules _ _ = F)`

val itemEqRuleList_defn = Hol_defn "itemEqRuleList_defn"
`(itemEqRuleList [] [] = T) /\
(itemEqRuleList [] _ = T) /\
(itemEqRuleList _ [] = F) /\
(itemEqRuleList l1 l2 = if ~(LENGTH l1 = LENGTH l2) then F
		     else
			   if (findItemInRules (HD l1) l2) then itemEqRuleList (TL l1) l2
			   else F)`


val (itemEqRuleList,itemEqRuleList_ind) = tprove (itemEqRuleList_defn,
WF_REL_TAC (`measure (\(l1,l2).LENGTH l1)`) THEN	
SRW_TAC [] [])

		

val getState = Define `(getState (sg,red) (itl:item list) sym = 
             let 
                newitl = sg itl sym and
                rl =  (red itl (sym2Str sym))
	     in
			case (newitl,rl) of ([],[]) -> NA 
			|| ([],(y::ys)) -> if (LENGTH rl = 1) then REDUCE  (HD rl) 
					   else NA 
			|| ((x::xs),[]) -> GOTO (state sym newitl)
			|| ((x::xs),(y::ys)) -> if (itemEqRuleList (x::xs) (y::ys))
						    then REDUCE (HD rl) else NA)`





(* three output options:
    NONE : failed to terminate
    SOME NONE : failed, but terminated (i.e., parse error)
    SOME (SOME s) : succeeded, and result is s
*)

(* parse :: machine -> (symbol list, (state,ptree) list) -> (symbol list, (state, ptree) list) option *)

val doReduce = Define `doReduce m ((sym::rst), os, ((state s itl)::rem)) ru =
                   if (isNonTmnlSym sym) then NONE 
                   else 
                       let 
                           l = ruleLhs ru and
                           r = ruleRhs ru 
                       in 
                           let 
                                 ptree = addRule os ru 
                           in 
                                case ptree of NONE -> NONE 
                                || (SOME p) -> 
                                   let 
                                       newStk = pop os (LENGTH r) 
                                    in 
					let 
					newStateStk = pop  ((state s itl)::rem) (LENGTH r)
					in
					if (newStateStk = []) then NONE else
                                      let 
                                           topitl = stateItl (HD newStateStk)
                                        in 
                                          let 
                                              ns = state (NTS l) ((FST m) topitl (NTS l))
                                          in 
                                              SOME ((sym::rst),([(ns,p)] ++ newStk), push newStateStk ns)`


val parse = Define `
(parse mac (inp, os, ((state s itl)::rem)) = 
  case mac of NONE -> NONE 
  || (SOME m) ->
	case inp of [] -> NONE
	    || [e] -> 
	    (let      
		 newState = getState m itl e
	     in 
		 case newState of NA -> NONE 
		   || (GOTO st) -> NONE		     
		   || (REDUCE ru) -> doReduce m ([e], os, ((state s itl)::rem)) ru)

	    || (sym::rst) -> 
		 (let      
		     newState = getState m itl sym 
		 in 
		     case newState of NA -> NONE 
		       || (GOTO st) -> 
			 if (isNonTmnlSym sym) then NONE 
			 else (* shift goto *) 
			     SOME (rst,(st,Leaf (TM (tmnlSym sym)))::os, push ((state s itl)::rem) st)
			   || (REDUCE ru) -> doReduce m ((sym::rst), os, ((state s itl)::rem)) ru))`
    


(* parser :: machine -> symbol list -> ((state,ptree) list -> ptree option *)

val parser = Define `parser g m sl stl curStatel eof oldsym = 
let 
out = (mwhile (\(sli,stli,csli).~(sli = [eof]) \/ ~(stateSym (FST (HD stli)) = oldsym)) 
(\(sli,stli,csli).parse m (sli,stli, csli)) 
(SOME (sl,stl,curStatel)))
in
    case out of NONE -> NONE
              || (SOME (SOME (slo,[(st1,pt)],cs))) -> 
	SOME (SOME (Node (NT (startSym g)) ([pt]++[Leaf (TM (tmnlSym eof))])))
					    || SOME (NONE) -> SOME (NONE)
	|| SOME _ -> SOME NONE`



(* Is [] symbol list parseable wrt a grammar????? *)
(* yacc :: grammar -> symbol list -> ptree opion*)
val yacc = Define `yacc g s' eof sl = 
let 
    g' = auggr g s' eof
in
    case g' of NONE -> NONE
    || (SOME ag) ->
       (let
	    mac = slr ag (* slrML g [(initItems ag (rules ag))] (SET_TO_LIST (allSyms g))  -- FOR ML version*)
	in 
	    case mac of NONE -> NONE
            || (SOME m) -> (
			    let
				initState = state (NTS s') (initItems ag (rules ag))
			    in
				case (parser ag (SOME m) sl [] [initState] (TS eof) (NTS (startSym g))) 
				    of NONE -> NONE
		|| SOME (NONE) -> NONE
		|| SOME (SOME out) -> SOME out))`




val mlDir = ref ("./theoryML/");

(*
val list_size_def =
  REWRITE_RULE [arithmeticTheory.ADD_ASSOC]
               (#2 (TypeBase.size_of ``:'a list``));*)


val _ =
 let open EmitML
 in emitML (!mlDir)
   ("yacc",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "whileLemmas", "set","num", "parseTree","firstSet", "followSet", "parser"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: MLSIG "type rule = grammarDefML.rule"
    :: MLSIG "type grammar = grammarDefML.grammar"
    :: MLSIG "type ptree = parseTreeML.ptree"
    :: MLSIG "type item = parserML.item"
    :: MLSIG "type state = parserML.state"
    :: DATATYPE `action = REDUCE of rule | GOTO of state | NA`
    :: DEFN getItems
    :: DEFN iclosure1
    :: DEFN iclosure
    :: DEFN auggr
    :: DEFN initProds2Items
    :: DEFN initItems
    :: DEFN moveDot
    :: DEFN nextState
    :: DEFN sgoto
    :: DEFN reduce
    :: DEFN buildTree
    :: DEFN addRule
    :: DEFN machine
    :: DEFN findItemInRules
    :: DEFN itemEqRuleList
    :: DEFN getState
    :: DEFN doReduce
    :: DEFN parse
    :: DEFN parser
    :: [])
 end;


(*
Theorems
1. ?g.~(yacc g = NONE)

2. s IN language (g) /\ (yacc (g) = SOME lrm) ==> ?t.(parse lrm s = SOME (t))

3. (yacc g = SOME lrm) ==> unambiguous (g)

4. (yacc g sl = SOME tree) ==> (validptree tree g /\ (leaves tree = sl))

*)

val _ = export_theory();
