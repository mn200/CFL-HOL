open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory rich_listTheory

open symbolDefTheory grammarDefTheory boolLemmasTheory listLemmasTheory
setLemmasTheory whileLemmasTheory parseTreeTheory followSetDefTheory
yaccDefTheory parseProp1DefTheory parseProp2DefTheory uselessSymbolsTheory

val _ = new_theory "lrGrammarDef";
val _ = diminish_srw_ss ["list EQ"];

val handleg = Define 
`handleg g sf rhs (pfx,lhs,sfx) = 
∃sf'.RTC (rderives g) [NTS (startSym g)] sf' ∧
(sf'=pfx++[NTS lhs]++sfx) ∧ (MEM (rule lhs rhs) (rules g)) ∧
(sf = pfx++rhs++sfx) ∧ EVERY isTmnlSym sfx`;


val viablePfx = Define 
`viablePfx g (N,h) sf p = ∃pfx sfx.handleg g sf h (pfx,N,sfx) ∧
IS_PREFIX (pfx++h) p`;


val validItem = Define 
`validItem g vp (item l (r1,r2)) = 
   ∃pfx sfx.
     RTC (rderives g) [NTS (startSym g)] (pfx++[NTS l]++sfx) ∧
     rderives g (pfx++[NTS l]++sfx) (pfx++r1++r2++sfx) ∧
     MEM (rule l (r1 ++ r2)) (rules g) ∧
     (pfx++r1=vp)`;

val itemlist_def = Define`
 itemlist (stl : ((('nts,'ts)symbol # ('nts,'ts)item list)  list)) 
 = SND ((HD stl))`;

val completeItem = Define `(completeItem (item l (r1, [])) = T) ∧
(completeItem (item l (r1, r2)) = F)`;


val shiftReduce = store_thm ("shiftReduce",
``(slrmac ag = SOME m) ⇒ validItl ag itl 
⇒ (getState m itl sym = REDUCE (rule l r)) ⇒
(trans ag (initItems ag (rules ag), vp)  = SOME itl) ⇒ isTmnlSym sym ⇒
∀e.MEM e itl ⇒ 
(e=item l (r,[])) ∨ ~(∃l' r2 r1.e = item l' (r1,sym::r2))``,

SRW_TAC [] [] THEN
`m = (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
SRW_TAC [] [] THEN
`MEM (item l (r,[])) itl` by METIS_TAC [getState_mem_itl, sgoto_exp, 
					validStates_def] THEN
Cases_on `e` THEN Cases_on `p` THEN Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [slrmac_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto ag itl sym` THEN
Cases_on `reduce ag itl (ts2str sym)` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1

(Cases_on `LENGTH t' = 0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [][] THEN
 SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
 `MEM (item n (q++[h],t)) (sgoto ag itl h)` by METIS_TAC [sgoto_mem] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`vp`,`itl`,`h`] MP_TAC) THEN SRW_TAC [][] THEN
 Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 METIS_TAC [MEM, rgr_r9eq]) THEN

Cases_on `itemEqRuleList (h'::t') (h''::t'')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
SRW_TAC [][] THEN
 SPOSE_NOT_THEN ASSUME_TAC THEN SRW_TAC [][] THEN
 FIRST_X_ASSUM (Q.SPECL_THEN [`vp`,`itl`,`h`] MP_TAC) THEN SRW_TAC [][] THEN
 Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) []);


val followSetEq = 
    mk_thm ([], ``∀g sym.s IN (followSetML g sym) = s IN (followSet g sym)``);

val _ = save_thm ("followSetEq", followSetEq);

val reduce_not_mem = store_thm ("reduce_not_mem",
``isTmnlSym sym ⇒ (reduce ag itl (ts2str sym) = []) ⇒ 
(∀e.MEM e itl ⇒ (~∃N r.(e=(item N (r,[]))) ∧ (sym IN (followSet ag (NTS N)))))``,

Cases_on `itl` THEN SRW_TAC [] [] THENL[
`(reduce ag [e] (ts2str sym) ++ (reduce ag t (ts2str sym)) = [])` 
					by METIS_TAC [reduce_append, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e` THEN  
Cases_on `p` THEN 
Cases_on `item n (q,r') = item N (r,[])` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
Cases_on `sym` THEN FULL_SIMP_TAC (srw_ss()) [ts2str_def, isTmnlSym_def] THEN
Cases_on `TS t' IN followSet ag (NTS N)` THEN FULL_SIMP_TAC (srw_ss()) [],

FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, reduce_append] THEN
SRW_TAC [] [] THEN
`(reduce ag [h] (ts2str sym) ++ reduce ag r1 (ts2str sym) ++
reduce ag [e] (ts2str sym) ++ (reduce ag r2 (ts2str sym)) = [])` by METIS_TAC [reduce_append, APPEND] THEN
`reduce ag [e] (ts2str sym) = []` by FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e` THEN  
Cases_on `p` THEN 
Cases_on `item n (q,r') = item N (r,[])` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
Cases_on `sym` THEN FULL_SIMP_TAC (srw_ss()) [ts2str_def, isTmnlSym_def] THEN
Cases_on `TS t IN followSet ag (NTS N)` THEN FULL_SIMP_TAC (srw_ss()) []]);

val shiftReduceGoto = store_thm ("shiftReduceGoto",
``(slrmac ag = SOME m) ⇒ isTmnlSym sym ⇒ validItl ag itl ⇒
				 (getState m itl sym = GOTO s') ⇒
~∃N r.MEM (item N (r,[])) itl ∧ (sym IN (followSet ag (NTS N)))``,

SRW_TAC [] [] THEN
`m = (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [slrmac_def, LET_THM] THEN
Cases_on `∃pfx itl' sym'. isTmnlSym sym' ∧
               (trans ag (initItems ag (rules ag),pfx) = SOME itl') ∧
               case sgoto ag itl' sym' of
                  [] ->
                    (case reduce ag itl' (ts2str sym') of
                        [] -> F
                     || [v12] -> F
                     || v12::v16::v17 -> T)
               || v8::v9 ->
                    case reduce ag itl' (ts2str sym') of
                       [] -> F
                    || [v20] -> T
                    || v20::v26::v27 -> T` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN

`SOME (sgoto ag,reduce ag)=SOME (sgoto ag,reduce ag)` by 
				 METIS_TAC [NOT_SOME_NONE] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
(Cases_on `sgoto ag itl sym` THEN
Cases_on `reduce ag itl (ts2str sym)` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `LENGTH t = 0` THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC [reduce_not_mem],
Cases_on `itemEqRuleList (h::t) (h'::t')` THEN FULL_SIMP_TAC (srw_ss()) []]));



val auggr_neqStartSym = store_thm ("auggr_neqStartSym", 
``(auggr g st eof = SOME ag) ⇒ ∀n.MEM (rule n []) (rules ag) ⇒ ~(n=st)``,
SRW_TAC [] [auggr_def] THEN
SRW_TAC [] [rules_def] THEN
METIS_TAC [slemma1_4, nonTerminalsEq]);


val stackSyms_stl = store_thm ("stackSyms_stl", 
``(doReduce m (e::t,stl,(s, itl)::csl) r = SOME (sl',stl',csl')) ⇒
(getState m itl e = REDUCE r) ⇒
(stackSyms stl' = stackSyms (pop stl (LENGTH (ruleRhs r))) ++  [NTS (ruleLhs r)])``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, 
				    pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl r` THEN
Cases_on `FST m (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
               (NTS (ruleLhs r)) =
             []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def] THEN
`stl'=((NTS n,
            FST m (SND (HD (pop ((s,itl)::csl) (LENGTH l)))) (NTS n)),x)::
              pop stl (LENGTH l)` by METIS_TAC [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [] [stackSyms_def, ruleRhs_def]);


val validStlItems = Define `(validStlItems stl [] = T) ∧
(validStlItems stl (e::t) =  
(isSuffix (itemFstRhs e) (stackSyms stl)) ∧ validStlItems stl t)`;

val validStlItemsStack = Define 
`(validStlItemsStack [] [e] = 
  validStlItems ([]:((('nts,'ts)symbol # ('nts,'ts)state) # ('nts,'ts)ptree) list) (SND e)) ∧
(validStlItemsStack (h::stl) (e::csl) =  
 validStlItems (h::stl) (SND e) ∧ validStlItemsStack stl csl) ∧
(validStlItemsStack _ _ = F)`;

val validItemStack = Define `(validItemStack g [] = T) ∧
(validItemStack g (e::rst) =  
                       EVERY (validItem g (stackSyms (e::rst))) (SND (FST e)) ∧ 
                       validItemStack g rst )`;


val validStlItems_append = store_thm ("validStlItems_append", 
``∀l1 l2.validStlItems stl (l1++l2) = validStlItems stl l1 ∧ validStlItems stl l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [] THENL[
METIS_TAC [APPEND, validStlItems],
METIS_TAC [APPEND, validStlItems],
Cases_on `h'` THEN Cases_on `p`  THEN 
METIS_TAC [APPEND, validStlItems, APPEND_ASSOC, APPEND_NIL]]);


val stackSyms_len = store_thm ("stackSyms_len", 
``∀stl.LENGTH stl = LENGTH (stackSyms stl)``,

Induct_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [stackSyms_def, ADD1]);


val auggr_notStartRule = store_thm ("auggr_notStartRule",
``(slrmac ag = SOME m) ⇒ (validStates ag ((s, itl)::csl)) ⇒
(auggr g st eof = SOME ag) ⇒ ~(FST (FST (HD stl)) = TS eof) ⇒ 
(∃pfx.stackSyms stl = pfx++l) ⇒ 
(getState m itl e = REDUCE (rule N l)) ⇒ ~(N=st)``,
SRW_TAC [] [] THEN 
`MEM (rule N l) (rules ag)` by METIS_TAC [getstate_red, APPEND, validStates_def, sgoto_exp] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
Cases_on `stl` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
SRW_TAC [] [] THEN METIS_TAC [auggr_neqStartSym],

Cases_on `h` THEN Cases_on `q` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l` THENL[
SRW_TAC [] [] THEN METIS_TAC [auggr_neqStartSym],
`LAST (REVERSE (MAP FST (MAP FST t)) ++ [q']) = LAST (pfx ++ h::t')` 
		   by METIS_TAC [] THEN
METIS_TAC [auggr_neqStartSym2, last_elem, last_append, NOT_CONS_NIL]]]);



val getState_nil = store_thm ("getState_nil", 
``~(getState (sgoto g, reduce g) [] h = REDUCE (rule s'' l'))``,
SRW_TAC [] [getState_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `sgoto g [] h` THEN 
Cases_on `reduce g [] (ts2str h)` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def]);


val reduce_mem_followSet = store_thm ("reduce_mem_followSet", 
``∀N r1 itl.MEM (item N (r1,[])) itl ⇒ isTmnlSym h ⇒
h IN followSet ag (NTS N) ⇒ ~(reduce ag itl (ts2str h) =[])``,

Induct_on `itl` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def, LET_THM] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [ts2str_def, followSetEq, 
					     isTmnlSym_def] THEN
RES_TAC THEN
`~(reduce ag itl t = [])` by METIS_TAC [ts2str_def] THEN
`reduce ag (h'::itl) t = reduce ag [h'] t ++ reduce ag itl t` 
by METIS_TAC [reduce_append, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) []);



val reduce_followSet = store_thm ("reduce_followSet",
``∀l s out.(reduce g l s = out) ⇒ 
(∀e.MEM e out ⇒ (TS s) IN followSet g (NTS (ruleLhs e)))``,

Induct_on `l` THEN SRW_TAC [] [reduce_def] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
Cases_on `TS s IN followSet g (NTS n)` THEN 
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def]);


val getState_reduce_followSet = store_thm ("getState_reduce_followSet", 
``(m=(sgoto g, reduce g)) ⇒ validItl g itl ⇒
isTmnlSym sym ⇒ (getState m itl sym = REDUCE (rule s' l)) ⇒ 
					   sym IN (followSet g (NTS s'))``,

Cases_on `itl` THEN SRW_TAC [] [getState_def, LET_THM] THEN Cases_on `sym` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, ts2str_def] 
THENL[

Cases_on `sgoto g [] (TS s)` THEN Cases_on `reduce g [] s` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def],

Cases_on `sgoto g [] (TS t)` THEN Cases_on `reduce g [] t` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def],


Cases_on `sgoto g (h::t) (TS t')` THEN Cases_on `reduce g (h::t) t'` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
SRW_TAC [] [] THEN
METIS_TAC [ruleLhs_def, reduce_followSet, MEM],
Cases_on `itemEqRuleList (h'::t'') (h''::t''')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [ruleLhs_def, reduce_followSet, MEM]],

Cases_on `sgoto g (h::t) (TS t')` THEN Cases_on `reduce g (h::t) t'` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `itemEqRuleList (h'::t'') (h''::t''')` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [ruleLhs_def, reduce_followSet, MEM]]);


val validItls = Define `
validItls ((s, itl)) topitl = 
(∀N r1 r2.(MEM (item N (r1,r2)) itl) ⇒ (r1=[]) ∨
(LAST r1 = s)) ∧
(∀N' r1' r2'.(MEM (item N' (r1',r2')) topitl) ⇒ (r1'=[]) ∨ (∃l1 l2.(r1'=l1++[s]++l2) ∧ 
MEM (item N' (l1++[s],l2++r2')) itl))`

val stateValidItls = Define `
(stateValidItls [] topitl = T) ∧
(stateValidItls (st::rst) topitl = validItls st topitl ∧ stateValidItls rst topitl)`;

val symsAfterDot = Define `(symsAfterDot [] = []) ∧
(symsAfterDot (item l (r1,[])::t) = symsAfterDot t) ∧
(symsAfterDot (item l (r1,s::ss)::t) = s::symsAfterDot t)`;


val rhsEqItems = Define 
`rhsEqItems e1 e2 = 
(itemFstRhs e1 ++ itemSndRhs e1 = itemFstRhs e2 ++ itemSndRhs e2)`;


val isNewItem = Define `(isNewItem [] = T) ∧
(isNewItem ((item l (r1,r2))::rst) = if (r1=[]) then (isNewItem rst) else F)`;

val isNewItem_rules2items = store_thm ("newItem_rules2items",
``∀g.isNewItem  (rules2Items (rules g))``,
Cases_on `g` THEN SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [isNewItem, rules2Items_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isNewItem,rules2Items_def]);


val isNewItem_append = store_thm ("isNewItem_append",
``∀l1 l2.isNewItem (l1++l2) = isNewItem l1 ∧ isNewItem l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [isNewItem, EQ_IMP_THM] THEN
Cases_on `h'` THEN Cases_on `p` THEN
METIS_TAC [APPEND, isNewItem]);


val isNewItem_mem = store_thm ("isNewItem_mem",
``∀l. isNewItem l = (∀e.MEM e l ⇒ isNewItem [e])``,
Induct_on `l` THEN SRW_TAC [] [isNewItem, EQ_IMP_THM] THEN
METIS_TAC [isNewItem_append, APPEND]);


val isNewItem_getItems = store_thm ("isNewItem_getItems",
``∀ g sym.isNewItem (getItems (rules g) sym)``,

Induct_on `rules g` THEN SRW_TAC [] [isNewItem, getItems_def] THEN1
METIS_TAC [isNewItem, getItems_def] THEN
`rules g = h::v` by METIS_TAC [] THEN 
Cases_on `h` THEN ONCE_ASM_REWRITE_TAC [] THEN
`∀e.MEM e (getItems (rule n l::v) sym) ⇒ MEM e (rules2Items (rule n l::v))` by METIS_TAC [rules2items_sub] THEN
`isNewItem (rules2Items (rule n l ::v))` by METIS_TAC [isNewItem_rules2items, rules_def] THEN
`∀e.MEM e (rules2Items (rule n l::v)) ⇒ isNewItem [e]` by METIS_TAC [isNewItem_mem] THEN
METIS_TAC [isNewItem_mem, APPEND, isNewItem_append, getItems_def]);


val isNewItem_iclosure1 = store_thm ("isNewItem_iclosure1", 
``∀g itl.isNewItem itl ⇒ isNewItem (iclosure1 g itl)``,
Induct_on `itl` THEN SRW_TAC [] [isNewItem, iclosure1_def] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1_def, isNewItem] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1_def, isNewItem] THEN
METIS_TAC [isNewItem, isNewItem_append, APPEND, APPEND_ASSOC, isNewItem_getItems]);


val isNewItem_delete = store_thm ("isNewItem_delete",
``∀t h.isNewItem  t ⇒ isNewItem  (delete h t)``,
Induct_on `t` THEN SRW_TAC [] [delete_def, isNewItem] THEN
METIS_TAC [isNewItem_append, APPEND]);


val isNewItem_rmDupes = store_thm ("isNewItem_rmDupes", 
``∀itl.isNewItem  itl ⇒ isNewItem (rmDupes itl)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes, isNewItem] THEN
METIS_TAC [isNewItem_append, APPEND, isNewItem_delete]);


val isNewItem_iclosure = store_thm ("isNewItem_iclosure",
``∀g itl.isNewItem  itl ⇒ isNewItem  (iclosure g itl)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, isNewItem, LET_THM] THEN
METIS_TAC [isNewItem_rmDupes, isNewItem_iclosure1]);


val isNewItem_initProds2Items = store_thm ("isNewItem_initProds2Items",
``∀s l.isNewItem (initProds2Items s l)``,
Induct_on `l` THEN SRW_TAC [] [initProds2Items_def, isNewItem] THEN
Cases_on `h` THEN SRW_TAC [] [initProds2Items_def, isNewItem]);

val isNewItem_everyNullFstRhs = store_thm ("isNewItem_everyNullFstRhs",
``∀l.isNewItem l = EVERY NULL (MAP itemFstRhs l)``,
Induct_on `l` THEN SRW_TAC [] [isNewItem] THEN
Cases_on `h` THEN  Cases_on `p` THEN
FULL_SIMP_TAC (srw_ss()) [isNewItem, itemFstRhs_def] THEN
METIS_TAC [NULL_EQ_NIL]);



val b4DotEmpty = store_thm ("b4DotEmpty",
``∀g.(EVERY NULL (MAP itemFstRhs (initItems g (rules g))))``,
Cases_on `g` THEN
SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [initItems_def, startSym_def, initProds2Items_def, 
			       iclosure] THEN
METIS_TAC [isNewItem_everyNullFstRhs, isNewItem_initProds2Items, 
	   isNewItem_iclosure]);

val nullFstRhs_validStlItems = store_thm ("nullFstRhs_validStlItems",
``∀l.(EVERY NULL (MAP itemFstRhs l)) ⇒ (validStlItems [] l)``,
Induct_on `l` THEN SRW_TAC [] [validStlItems] THEN
Cases_on `h` THEN Cases_on `p` THEN 
FULL_SIMP_TAC (srw_ss()) [NULL_EQ_NIL, itemFstRhs_def, validStlItems,
			  stackSyms_def, isSuffix_def, IS_PREFIX_REFL]);

val validItl_initProds2Items = store_thm ("validItl_initProds2Items", 
``∀g l.validItl g (initProds2Items sym (rules g))``,
Cases_on `g` THEN SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [initProds2Items_def, validItl_def, rules_def] THEN
Cases_on `h` THEN
SRW_TAC [] [initProds2Items_def, validItl_def, rules_def] THEN
METIS_TAC [validItl_rules_cons]);


val rderives_rules_cons = store_thm ("rderives_rules_cons", 
``∀s1 s2 r e.rderives (G r s) s1 s2 ⇒ rderives (G (e::r) s) s1 s2``,
SRW_TAC [] [rderives_def, rules_def] THEN
METIS_TAC [rules_def]);


val rtc_rderives_rules_cons = store_thm ("rtc_rderives_rules_cons", 
``∀s1 s2.RTC (rderives (G r s)) s1 s2 ⇒ RTC (rderives (G (e::r) s)) s1 s2``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
METIS_TAC  [RTC_RULES, rderives_rules_cons]);

val validItem_rules_cons = store_thm ("validItem_rules_cons",
``∀r s l e.validItem (G r s) [] l ⇒ validItem (G (e::r) s) [] l``,
SRW_TAC [] [] THEN
Induct_on `l` THEN SRW_TAC [] [validItem] THEN 
Cases_on `p` THEN SRW_TAC [] [validItem, startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [validItem, startSym_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `sfx` THEN
SRW_TAC [] [rules_def] THEN
METIS_TAC [rderives_rules_cons, rtc_rderives_rules_cons, rules_def]);



val validItem_initProds2Items = store_thm ("validItem_initProds2Items",
``∀g.EVERY (validItem g []) (initProds2Items (startSym g) (rules g))``,

Cases_on `g` THEN 
SRW_TAC [] [startSym_def, validItem, rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [initProds2Items_def] THEN
Cases_on `h` THEN SRW_TAC [] [initProds2Items_def, validItem, startSym_def] THEN
SRW_TAC [] [rderives_def] 
THENL[
      Q.EXISTS_TAC `[]`  THEN
      SRW_TAC [] [RTC_RULES] 
      THENL[
	    MAP_EVERY Q.EXISTS_TAC [`[]`, `[]`, `l'`, `n`] THEN
	    SRW_TAC [] [rules_def],
	    
	    METIS_TAC [rules_def, MEM]
	    ],

      METIS_TAC [validItem_rules_cons, EVERY_MEM],
      METIS_TAC [validItem_rules_cons, EVERY_MEM]]);


val pfx_lem1 = prove(
``∀r1 e h t pfx t' sfx.
(r1 ++ e :: h :: t = pfx ++ r1 ++ e :: t' ++ sfx) ∧
IS_PREFIX (pfx ++ r1 ++ e::t') r1 ∧
~(r1 = pfx ++ r1) ⇒
IS_PREFIX (pfx ++ r1 ++ e::t') (r1 ++ [e])``,

Induct THEN SRW_TAC [][] THENL [
Cases_on `pfx` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX],

Cases_on `pfx` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
(SRW_TAC [][IS_PREFIX] THEN
Q.MATCH_ABBREV_TAC `IS_PREFIX BIG SMALL` THEN
`BIG = (t'' ++ [h]) ++ r1 ++ e::t'`
by (SRW_TAC [][Abbr`BIG`] THEN
METIS_TAC [APPEND_ASSOC, APPEND]) THEN
Q.UNABBREV_TAC `SMALL` THEN
POP_ASSUM SUBST1_TAC THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
METIS_TAC [APPEND_ASSOC, APPEND]) ]);



val stateSym_stl_len1 = store_thm ("stateSym_stl_len1",
``∀stl.(MAP FST (MAP FST stl) = [NTS nt]) ⇒
(FST (FST (HD stl)) = NTS nt)``,
Induct_on `stl` THEN SRW_TAC [] []);


val slrmacNotValid = store_thm ("slrmacNotValid",
``MEM (item N (h,[])) itl ⇒ 
(e IN (followSet ag (NTS N))) ⇒ (isTmnlSym e) ⇒
MEM (item N' (pfx,e::sfx)) itl ⇒ 
(trans ag (initItems ag (rules ag),vp) = SOME itl) ⇒
~(slrmac ag = SOME (sgoto ag,reduce ag))``,

SRW_TAC [] [slrmac_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
MAP_EVERY Q.EXISTS_TAC [`vp`,`itl`,`e`] THEN SRW_TAC [][] THEN
Cases_on `sgoto ag itl e` THEN
Cases_on `reduce ag itl (ts2str e)` THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
      METIS_TAC [reduce_not_mem],

      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [sgoto_mem,MEM],

      METIS_TAC [reduce_not_mem],      

      Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) []
      ]);



val stackTopSym = Define `stackTopSym stl = FST (FST (HD stl))`;


val validItemNts = store_thm ("validItemNts",
``∀g p r.validItem g p (item l (r1,NTS nt::r2)) ⇒ 
(∀nt.nt IN (nonTerminals g) ⇒ gaw g nt) ⇒
MEM (rule nt r) (rules g) ⇒ validItem g p (item nt ([],r))``,

SRW_TAC [] [validItem] THEN
`(NTS nt)  IN (nonTerminals ( g))` by METIS_TAC [slemma1_4] THEN
`~(language g = {})` by METIS_TAC [language_not_empty, slemma1_4] THEN
`gaw g (NTS nt)` by METIS_TAC [language_def, gaw_def, slemma1_4] THEN
FULL_SIMP_TAC (srw_ss()) [gaw_def] THEN
`RTC (rderives g) [NTS nt] w` by METIS_TAC [derivesImpRderives] THEN
Cases_on `([NTS nt] = w)` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
`∃sf.RTC (rderives g) [NTS nt] sf ∧ rderives g sf w` by METIS_TAC [RTC_CASES2] THEN

Cases_on `EVERY isTmnlSym (r2++sfx)` THENL[
Q.EXISTS_TAC `r2++sfx` THEN SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES_RIGHT1, RTC_RULES, rdres1, APPEND, APPEND_ASSOC],
`rderives g [NTS nt] r` by METIS_TAC [rdres1] THEN
METIS_TAC [rderives_append, APPEND_ASSOC]],

(* ~EVERY isTmnlSym (r2 ++ sfx) *)
`gaw g (NTS (startSym ( g))) ` by METIS_TAC [gaw_def, slemma1_4] THEN
`RTC (rderives ( g)) [NTS (startSym ( g))] (pfx ++ r1 ++ [NTS nt]++r2 ++ sfx)` by METIS_TAC [RTC_RULES_RIGHT1, APPEND, APPEND_ASSOC] THEN
`gaw ( g) (NTS (startSym g))` by METIS_TAC [] THEN

`∃w.RTC (rderives g) (r2++sfx) w ∧ EVERY isTmnlSym w` by 
METIS_TAC [APPEND_ASSOC, APPEND,  gaw_def, rderivesImpDerives,gaw_l1] THEN

`RTC (rderives ( g)) (pfx++r1++[NTS nt]++r2++sfx) (pfx++r1++[NTS nt]++w')` by 
METIS_TAC [rtc_rderives_same_append_left, APPEND_ASSOC] THEN
 Cases_on `((pfx ++ r1 ++ [NTS nt] ++ r2 ++ sfx) = (pfx ++ r1 ++ [NTS nt] ++ w'))` THEN 
FULL_SIMP_TAC (srw_ss()) [] THENL[
SRW_TAC [] [] THEN
Q.EXISTS_TAC `w'` THEN SRW_TAC [] [] THEN
METIS_TAC [rderives_append, APPEND_ASSOC, rdres1],
SRW_TAC [] [] THEN
Q.EXISTS_TAC `w'` THEN SRW_TAC [] [] THEN
METIS_TAC [rderives_append, APPEND_ASSOC, rdres1],

Q.EXISTS_TAC `w'` THEN SRW_TAC [] [] THEN
`RTC (rderives g) (pfx ++ [NTS l] ++ sfx) (pfx ++ r1 ++ [NTS nt] ++ w')` by 
METIS_TAC [RTC_SUBSET, RTC_RTC, APPEND, APPEND_ASSOC] THEN
METIS_TAC [RTC_RTC, rderives_append, rdres1, APPEND_ASSOC],

Q.EXISTS_TAC `w'` THEN SRW_TAC [] [] THEN
`RTC (rderives g) (pfx ++ [NTS l] ++ sfx) (pfx ++ r1 ++ [NTS nt] ++ w')` by 
METIS_TAC [RTC_SUBSET, RTC_RTC, APPEND, APPEND_ASSOC] THEN
METIS_TAC [RTC_RTC, rderives_append, rdres1, APPEND_ASSOC]]]);



val getItems_mem = store_thm ("getItems_mem",
``∀e l s'.MEM e (getItems l s') ⇒ ∃r.(e=item s' ([],r)) ∧ MEM (rule s' r) l``,
Induct_on `l` THEN SRW_TAC [] [getItems_def] THEN
Cases_on `h` THEN METIS_TAC [getItems_def, MEM]);

val validItem_getItems = store_thm ("validItem_getItems",
``∀g p s' t.validItem g p (item s (q,NTS s'::t)) ⇒ 
(∀nt.nt IN (nonTerminals g) ⇒ gaw g nt) ⇒
EVERY (validItem g p) (getItems (rules g) s')``,
Induct_on `rules g` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [getItems_def, validItem] THEN METIS_TAC [EVERY_DEF, getItems_def],
`∀e.MEM e (getItems (rules g) s') ⇒ ∃r.(e=item s' ([],r)) ∧ MEM (rule s' r) (rules g)` by METIS_TAC [getItems_mem] THEN
SRW_TAC [] [EVERY_MEM] THEN
RES_TAC  THEN
SRW_TAC [] [] THEN
METIS_TAC [validItemNts]]);


val validItem_iclosure1 = store_thm ("validItem_iclosure1", 
``∀g itl l.EVERY (validItem g l) itl ⇒ 
(∀nt.nt IN (nonTerminals g) ⇒ gaw g nt) ⇒
EVERY (validItem g l) (iclosure1 g itl)``,

Induct_on `itl` THEN SRW_TAC [] [iclosure1_def, validItem] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1_def, validItem] THEN1
METIS_TAC [RTC_RULES] THEN
Cases_on `h` THEN SRW_TAC [] [iclosure1_def] 
THENL[
      `validItem g (pfx++q) (item n (q,NTS n'::t))` by METIS_TAC [validItem, APPEND_ASSOC] THEN
      METIS_TAC [validItem_getItems],
      SRW_TAC [] [validItem] THEN METIS_TAC [],
      SRW_TAC [] [validItem] THEN METIS_TAC []]);



val validItem_delete = store_thm ("validItem_delete",
``∀t h.EVERY (validItem g l) t ⇒ EVERY (validItem g l) (delete h t)``,
Induct_on `t` THEN SRW_TAC [] [delete_def, validItem]);


val validItem_rmDupes = store_thm ("validItem_rmDupes", 
``∀itl g l.EVERY (validItem g l)  itl ⇒ EVERY (validItem g l) (rmDupes itl)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes, validItem] THEN
METIS_TAC [validItem_delete]);


val validItem_iclosure = store_thm ("validItem_iclosure",
``∀g itl l.EVERY (validItem g l)  itl ⇒ 
(∀nt.nt IN (nonTerminals g) ⇒ gaw g nt) ⇒
EVERY (validItem g l)  (iclosure g itl)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, validItem, LET_THM] THEN
`EVERY (validItem g l) (v2::v3)` by FULL_SIMP_TAC (srw_ss()) [] THEN
`EVERY (validItem g l) (rmDupes (v2::v3))` by METIS_TAC [validItem_rmDupes, validItem_iclosure1, APPEND, EVERY_APPEND] THEN
`EVERY (validItem g l) (iclosure1 g (rmDupes (v2::v3)))` 
by METIS_TAC [validItem_rmDupes, validItem_iclosure1, APPEND, EVERY_APPEND] THEN
`EVERY (validItem g l) (rmDupes (iclosure1 g (rmDupes (v2::v3))))` 
by METIS_TAC [validItem_rmDupes, validItem_iclosure1, APPEND, EVERY_APPEND] THEN
METIS_TAC []);



val fstRhsNil_delete = store_thm ("fstRhsNil_delete",
``∀t h.EVERY NULL (MAP itemFstRhs t) ⇒ EVERY NULL (MAP itemFstRhs (delete h t))``,
Induct_on `t` THEN SRW_TAC [] [delete_def]);


val fstRhsNil_rmDupes = store_thm ("fstRhsNil_rmDupes", 
``∀itl.EVERY NULL (MAP itemFstRhs itl) ⇒ EVERY NULL (MAP itemFstRhs (rmDupes itl))``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
METIS_TAC [APPEND, fstRhsNil_delete]);

val every_map_itemFstRhs = store_thm ("every_map_itemFstRhs",
``∀l.EVERY NULL (MAP itemFstRhs l) = (∀e.MEM e l ⇒ (itemFstRhs e = []))``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e` THEN Cases_on `p` THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def, NULL_EQ_NIL]);


val fstRhsNil_getItems = store_thm ("fstRhsNil_getItems",
``∀l.EVERY NULL (MAP itemFstRhs (getItems l s'))``,

Induct_on `l` THEN SRW_TAC [] [getItems_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [getItems_def] THEN
Cases_on `n=s'` THEN FULL_SIMP_TAC (srw_ss()) [getItems_def, itemFstRhs_def]);


val fstRhsNil_iclosure1 = store_thm ("fstRhsNil_iclosure1",
``∀g l.EVERY NULL (MAP itemFstRhs l) ⇒ EVERY NULL (MAP itemFstRhs (iclosure1 g l))``,
Induct_on `l` THEN SRW_TAC [] [iclosure1_def] THEN
Cases_on `h` THEN Cases_on `p` THEN 
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def] THEN
`q=[]` by METIS_TAC [NULL_EQ_NIL] THEN
SRW_TAC [] [] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1_def, itemFstRhs_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1_def, itemFstRhs_def] THEN
METIS_TAC [fstRhsNil_getItems]);

val fstRhsNil_iclosure = store_thm ("fstRhsNil_iclosure",
``∀g l.EVERY NULL (MAP itemFstRhs l) ⇒ MEM e (iclosure g l) ⇒ (itemFstRhs e=[])``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, iclosure1_def] THEN
Cases_on `e` THEN Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def, LET_THM] THEN
Cases_on `~(set (rmDupes (v2::v3)) =
                 set (rmDupes (iclosure1 g (rmDupes (v2::v3)))))` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
`EVERY NULL (MAP itemFstRhs (v2::v3))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`EVERY NULL (MAP itemFstRhs (rmDupes (v2::v3)))` by METIS_TAC [fstRhsNil_rmDupes] THEN
`EVERY NULL (MAP itemFstRhs (iclosure1 g (rmDupes (v2::v3))))` by METIS_TAC [fstRhsNil_iclosure1] THEN
METIS_TAC [fstRhsNil_iclosure1, fstRhsNil_rmDupes],
`EVERY NULL (MAP itemFstRhs (v2::v3))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`EVERY NULL (MAP itemFstRhs (rmDupes (v2::v3)))` by METIS_TAC [fstRhsNil_rmDupes] THEN
`EVERY NULL (MAP itemFstRhs (iclosure1 g (rmDupes (v2::v3))))` by METIS_TAC [fstRhsNil_iclosure1] THEN
`EVERY NULL (MAP itemFstRhs (rmDupes (iclosure1 g (rmDupes (v2::v3)))))` by METIS_TAC [fstRhsNil_rmDupes] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
POP_ASSUM MP_TAC THEN
SRW_TAC [] [itemFstRhs_def] THEN
METIS_TAC [NULL_EQ_NIL, NOT_CONS_NIL]]);

val fstRhsNil_initProds2Items = store_thm ("fstRhsNil_initProds2Items",
``∀l r1 r2. MEM (item l (r1,r2)) (initProds2Items s x) ⇒ (r1=[])``,

Induct_on `x` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [initProds2Items_def] THEN
Cases_on `h` THEN Cases_on `r2` THEN 
FULL_SIMP_TAC (srw_ss()) [initProds2Items_def] THEN
Cases_on `n=s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC []);


val initItems_fstRhs_nil = store_thm ("initItems_fstRhs_nil", 
``∀l r1 r2.MEM (item l (r1,r2)) (initItems ag (rules ag)) ⇒ (r1=[])``,
SRW_TAC [] [initItems_def, initProds2Items_def] THEN
`∀l r1 r2.MEM (item l (r1,r2)) (initProds2Items (startSym ag) (rules ag)) ⇒ (r1 = [])` by 
METIS_TAC [fstRhsNil_initProds2Items] THEN
`EVERY NULL (MAP itemFstRhs (initProds2Items (startSym ag) (rules ag)))` by (FULL_SIMP_TAC (srw_ss()) [every_map_itemFstRhs] THEN
SRW_TAC [] [] THEN Cases_on `e` THEN Cases_on `p` THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def] THEN METIS_TAC []) THEN
`itemFstRhs (item l (r1,r2)) = []` by METIS_TAC [fstRhsNil_iclosure] THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def]);


val completeItem_sndRhs_nil = store_thm ("completeItem_sndRhs_nil",
``∀l r1 r2.MEM (item l (r1,r2)) (FILTER completeItem x) ⇒ (r2=[]) ``,
Induct_on `x` THEN SRW_TAC [] [completeItem] THENL[
Cases_on `r2` THEN FULL_SIMP_TAC (srw_ss()) [completeItem],
METIS_TAC [],
METIS_TAC []]);


val initProds_compItem_nil = store_thm ("initProds_compItem_nil", 
``∀l r1 r2.MEM (item l (r1, r2)) (FILTER completeItem (initItems ag (rules ag))) ⇒ 
					((r1=[]) ∧ (r2=[]))``,
SRW_TAC [] [] THENL[
METIS_TAC [MEM_FILTER, initItems_fstRhs_nil],
METIS_TAC [completeItem_sndRhs_nil]]);


val mem_reduce = store_thm ("mem_reduce",
``∀e itl N.e IN followSet ag (NTS N) ⇒ MEM (item N (h,[])) itl ⇒ isTmnlSym e ⇒
    MEM (rule N h) (reduce ag itl (ts2str e))``,

Induct_on `itl` THEN SRW_TAC [] [] THEN
SRW_TAC [] [reduce_def] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [ts2str_def, isTmnlSym_def, followSetEq] THEN
`reduce ag (h'::itl) t = reduce ag [h'] t ++ reduce ag itl t` by METIS_TAC [reduce_append, APPEND] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [] [] THEN
RES_TAC THEN
METIS_TAC [ts2str_def]);


val isTmnlMemFollowSet = store_thm
("isTmnlMemFollowSet",
``e ∈ followSet ag (NTS N) ⇒ isTmnlSym e``,

SRW_TAC [][followSet_def, isTmnlSym_def]);


val slrmacCompItemsEq = 
store_thm ("slrmacCompItemsEq",
``∀m ag N h itl.(SOME m = slrmac ag) ⇒ 
(trans ag (initItems ag (rules ag),vp) = SOME itl) ⇒
                   MEM (item N (h,[])) itl 
                ⇒ (e IN followSet ag (NTS N)) ⇒
                (∀j.
                MEM j itl ∧ completeItem j ∧
                e IN followSet ag (NTS (itemLhs j)) ⇒
                (j = item N (h,[])))``,

SRW_TAC [] [slrmac_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`isTmnlSym e` by METIS_TAC [isTmnlMemFollowSet] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`vp`,`itl`, `e`] ASSUME_TAC) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
Cases_on `j=item N (h,[])` THEN
SRW_TAC [] [] THEN
`MEM (rule N h) (reduce ag itl (ts2str e))` by METIS_TAC [mem_reduce] THEN
Cases_on `j` THEN 
Cases_on `p` THEN Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [completeItem, itemLhs_def] THEN
`MEM (rule N h) (reduce ag itl (ts2str e))` by METIS_TAC [mem_reduce] THEN
Cases_on `sgoto ag itl e` THEN Cases_on `reduce ag itl (ts2str e)` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN 
REPEAT 
(FULL_SIMP_TAC (srw_ss()) [] THEN 
Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`rule N h = rule s q` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) []) THEN
REPEAT 
(Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
(Cases_on `t'` THEN
FULL_SIMP_TAC (srw_ss()) [])) THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][] THEN
METIS_TAC [rule_11, mem_reduce, MEM]);



val getItems_append = store_thm ("getItems_append",
``∀l1 l2.getItems (l1++l2) N  = getItems l1 N ++ getItems l2 N``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [getItems_def] THEN
Cases_on `h'` THEN SRW_TAC [] [getItems_def]);


val iclosureNt = store_thm ("iclosureNt",
``∀ag l.MEM (item lhs ([],NTS N::r2)) (iclosure ag l) ⇒ 
 ∀rhs.MEM (rule N rhs) (rules ag) ⇒
MEM (item N ([],rhs)) (iclosure ag l)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, LET_THM] THEN
`(item lhs ([],NTS N::r2)) IN set (rmDupes (iclosure1 ag (rmDupes (v2::v3))))` by 
FULL_SIMP_TAC (srw_ss()) [] THEN
`(item lhs ([],NTS N::r2)) IN set (rmDupes (v2::v3))` 
    by (FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item lhs ([],NTS N::r2))
            ((iclosure1 ag (rmDupes (v2::v3))))`
    by METIS_TAC [rmd_mem_list] THEN
`v2 INSERT set v3 = set (v2::v3)` by SRW_TAC [][] THEN
METIS_TAC [rmd_mem_list,containerLemmasTheory.mem_in]) THEN
`MEM (item lhs ([],NTS N::r2)) (SET_TO_LIST (set (rmDupes (v2::v3))))` by 
METIS_TAC [FINITE_LIST_TO_SET, MEM_SET_TO_LIST, SET_TO_LIST_IN_MEM] THEN
`MEM (item lhs ([],NTS N::r2)) (rmDupes (v2::v3))` by METIS_TAC [stl_mem, FINITE_LIST_TO_SET] THEN
`∃p s.(rmDupes (v2::v3))=p++[item lhs ([],NTS N::r2)]++s`
    by METIS_TAC [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1_append,iclosure1_def] THEN
`∃r1 r2.rules ag=r1++[rule N rhs]++r2`
    by METIS_TAC [rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [getItems_append,getItems_def] THEN
METIS_TAC [rmd_mem_list,MEM,MEM_APPEND]);


val initClosure = store_thm ("initClosure",
``∀l lhs r2.MEM (item lhs ([],NTS N::r2)) l ⇒ (l=(initItems ag (rules ag))) ⇒ 
 ∀rhs.MEM (rule N rhs) (rules ag) ⇒
MEM (item N ([],rhs)) l``,
SRW_TAC [] [initItems_def] THEN
FULL_SIMP_TAC (srw_ss()) [initItems_def] THEN
METIS_TAC [iclosureNt]);


val rtcImpInClosure = store_thm ("rtcImpInClosure",
``∀u u'.RTC (rderives ag) u u' ⇒ (u=[NTS (startSym ag)]) ⇒ ∀v.derives ag u' v ⇒
       (auggr g s eof = SOME ag) ⇒ (LENGTH v < LENGTH u' ⇒ isTmnlSym (HD u')) ⇒
        (∃lhs r2.
      MEM (item lhs ([],HD v::r2))
        (initItems ag (rules ag)))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] 
THENL[

FULL_SIMP_TAC (srw_ss()) [lreseq, derives_def] THEN
SRW_TAC [] [] THEN
METIS_TAC [auggrStartRule, HD, auggrExistsMemInit, initItems_def, iclosure_mem],

Cases_on `isTmnlSym (HD u')` THENL[

`HD u'' = HD u'` by METIS_TAC [rderivesHdTmnl] THEN
`HD v = HD u''` by METIS_TAC [derivesHdTmnl] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, derives_def] THEN
SRW_TAC [] [] THEN
METIS_TAC [rderivesImpDerives],

Cases_on `isTmnlSym (HD u'')` THENL[
`HD v = HD u''` by METIS_TAC [derivesHdTmnl] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`rhs++s2`] MP_TAC) THEN
SRW_TAC [] [] THEN
`derives ag (NTS lhs::s2) (rhs ++ s2)` by METIS_TAC [res1, APPEND, derives_same_append_right] THEN
RES_TAC THEN
Cases_on `rhs` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`EVERY isTmnlSym (s1 ++ [NTS lhs'] ++ s2')` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

` ~(SUC (LENGTH t) < 1)` by DECIDE_TAC THEN
METIS_TAC []],

Cases_on `isTmnlSym (HD v)` THENL[

`~(LENGTH v < LENGTH u'')` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `rhs` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] 
THENL[
(* 4 subgoals *)
Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def],

Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS lhs'::t++s2`] MP_TAC) THEN
SRW_TAC [] [] THEN
`~(SUC (LENGTH t) < 1)` by DECIDE_TAC THEN
RES_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s2`, `[]`] MP_TAC) THEN
SRW_TAC [] [] THEN
METIS_TAC [initClosure],

Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`derives ag (NTS lhs'::(t ++ [NTS lhs] ++ s2))  ((TS s'::t')++(t ++ [NTS lhs] ++ s2))` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`LENGTH (s1 ++ rhs ++ s2') = LENGTH (TS s'::(t' ++ t ++ [NTS lhs] ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t' + LENGTH t + 1 + LENGTH s2) < SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`(TS s'::(t' ++ t ++ [NTS lhs] ++ s2))`] MP_TAC) THEN
SRW_TAC [] [] THEN
METIS_TAC [],

Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`derives ag (NTS lhs'::(t ++ [NTS lhs] ++ s2)) (TS s'::t''++(t ++ [NTS lhs] ++ s2))` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`LENGTH (s1 ++ rhs ++ s2') = LENGTH (TS s'::(t'' ++ t ++ [NTS lhs] ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~( SUC (LENGTH t'' + LENGTH t + 1 + LENGTH s2) < SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`TS s'::(t'' ++ t ++ [NTS lhs] ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
METIS_TAC []],

`~(LENGTH v < LENGTH u'')` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `rhs` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] 
THENL[
(* 4 subgoals *)
Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def],

Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[

FIRST_X_ASSUM (Q.SPECL_THEN [`(NTS lhs'::t)++s2`] MP_TAC) THEN
SRW_TAC [] [] THEN
`~(SUC (LENGTH t) < 1)` by DECIDE_TAC THEN
RES_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s2`, `[]`] MP_TAC) THEN
SRW_TAC [] [] THEN
METIS_TAC [initClosure],

`derives ag (NTS lhs::s2) ((NTS n::t)++s2)` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS n::(t ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t + LENGTH s2) < 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS n::(t ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
METIS_TAC [],

`derives ag (NTS lhs::s2) ((NTS n::t)++s2)` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS n::(t ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t + LENGTH s2) < 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS n::(t ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
METIS_TAC []],

Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THENL[

`derives ag (NTS lhs'::(t ++ [NTS lhs] ++ s2))  ((h::t')++(t ++ [NTS lhs] ++ s2))` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`LENGTH (s1 ++ rhs ++ s2') = LENGTH (h::(t' ++ t ++ [NTS lhs] ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [ADD1] THEN
`~(SUC (LENGTH t' + LENGTH t + 1 + LENGTH s2) < SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`([h]++t' ++ t ++ [NTS lhs] ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`~(1 + LENGTH t' < 1)` by DECIDE_TAC THEN
METIS_TAC [],

`derives ag  (NTS n::(t ++ [NTS lhs] ++ s2)) (NTS n::(t++s2))` by METIS_TAC [res1, derives_same_append_right, derives_same_append_left, APPEND_NIL, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS n::(t' ++ [NTS lhs'] ++ s2')`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS n::(t' ++ [NTS lhs'] ++ s2'))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t' + 1 + LENGTH s2') <
             SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC [],

`MEM (NTS lhs')  (t ++ s2)` by METIS_TAC [MEM_APPEND, rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[

`∃pfx sfx.t=pfx++[NTS lhs']++sfx` by METIS_TAC [rgr_r9eq] THEN
SRW_TAC [] [] THEN
`derives ag (NTS n::(pfx ++ [NTS lhs'] ++ sfx ++ [NTS lhs] ++ s2)) (NTS n::(pfx ++ h::t'' ++ sfx)++ [NTS lhs] ++ s2)` by 
METIS_TAC [res1, derives_same_append_left, derives_same_append_right, APPEND, APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [` NTS n::(pfx ++ h::t'' ++ sfx ++ [NTS lhs] ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS n::(pfx ++ h::t'' ++ sfx ++ [NTS lhs] ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
` ~(SUC
 (LENGTH pfx + SUC (LENGTH t'') + LENGTH sfx + 1 +
                LENGTH s2) <
             SUC (LENGTH pfx + 1 + LENGTH sfx) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC [],

`∃pfx sfx.s2=pfx++[NTS lhs']++sfx` by METIS_TAC [rgr_r9eq] THEN
SRW_TAC [] [] THEN
`derives ag (NTS n::(t ++ [NTS lhs] ++ (pfx ++ [NTS lhs'] ++ sfx))) (NTS n::(t ++ [NTS lhs] ++ (pfx ++ h::t'' ++ sfx)))` by 
METIS_TAC [res1, derives_same_append_left, derives_same_append_right, APPEND, APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS n::(t ++ [NTS lhs] ++ pfx ++ h::t'' ++ sfx)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2) = LENGTH (NTS n::(t ++ [NTS lhs] ++ pfx ++ h::t'' ++ sfx))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC
               (LENGTH t + 1 + LENGTH pfx + SUC (LENGTH t'') + LENGTH sfx) <
             SUC (LENGTH t) + 1 + (LENGTH pfx + 1 + LENGTH sfx))` by DECIDE_TAC THEN
METIS_TAC []]],


Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THENL[

`derives ag (NTS lhs'::(t ++ [NTS lhs] ++ s2)) (h::t''++(t ++ [NTS lhs] ++ s2))` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`h::(t'' ++ t ++ [NTS lhs] ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2') = LENGTH (h::(t'' ++ t ++ [NTS lhs] ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t'' + LENGTH t + 1 + LENGTH s2) <
             SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC [],


`derives ag (NTS n::(t ++ [NTS lhs] ++ s2)) (NTS n::(t ++ (h'::t') ++ s2))` by METIS_TAC [res1, derives_same_append_right, derives_same_append_left, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS n::(t ++ h'::t' ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS n::(t ++ h'::t' ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t + SUC (LENGTH t') + LENGTH s2) <
             SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC [],

`derives ag (NTS n::(t ++ [NTS lhs] ++ s2)) (NTS n::(t ++ (h'::t') ++ s2))` by METIS_TAC [res1, derives_same_append_right, derives_same_append_left, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS n::(t ++ h'::t' ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS n::(t ++ h'::t' ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t + SUC (LENGTH t') + LENGTH s2) <
             SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC []]]]]]]);



val auggrLastEof = store_thm ("auggrLastEof",
``(auggr g st eof = SOME ag) ⇒ 
RTC (rderives ag) [NTS (startSym ag)] (h::pfx++[NTS N]++sfx) ⇒ ∃pfx'. sfx = pfx' ++ [TS eof]``,
SRW_TAC [] [Once RTC_CASES2, derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `lhs=(startSym ag)` THEN SRW_TAC [] []
THENL[

 `(s1=[]) ∧ (s2=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 `rhs=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
 SRW_TAC [] [] THEN
 Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) []
 THENL[
 `LAST [TS eof] = LAST [NTS N]` by METIS_TAC [last_append, NOT_CONS_NIL] THEN
 FULL_SIMP_TAC (srw_ss()) [],

 Cases_on `pfx` THEN FULL_SIMP_TAC (srw_ss()) []
 ],
 
 `∃pfx'.s2=pfx'++[TS eof]` by METIS_TAC [lastEof] THEN
 Cases_on `sfx` THEN SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [] 
 THENL[
 `TS eof = NTS N` by METIS_TAC [last_elem, APPEND] THEN
 FULL_SIMP_TAC (srw_ss()) [],

 `LAST [TS eof] = LAST (h'::t)` by METIS_TAC [last_append, NOT_CONS_NIL, APPEND_ASSOC, APPEND] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 METIS_TAC [APPEND_NIL, APPEND_FRONT_LAST, NOT_CONS_NIL]
 ]]);




val initItemsHdNt = store_thm ("initItemsHdNt",
``∀u v.RTC (rderives ag) u v ⇒ (u=[NTS (startSym ag)]) ⇒ 
   ∀N rst.(v=(NTS N::rst)) ⇒
   ∀rhs.MEM (rule N rhs) (rules ag) ⇒ (auggr g st eof = SOME ag) ⇒
    MEM (item N ([],rhs)) (initItems ag (rules ag))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES]
THENL[
      SRW_TAC [] [initItems_def] THEN
      `rhs=[NTS (startSym g);TS eof]` by METIS_TAC [auggrStartRule] THEN
      SRW_TAC [] [] THEN
      METIS_TAC [auggrExistsMemInit, iclosure_mem],

      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [] [] THEN
      Cases_on `s1` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `rhs'` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
      SRW_TAC [] [] THEN
      METIS_TAC [initClosure]]);


val initItemsNtInBtwn = store_thm ("initItemsNtInBtwn",
``∀u v.RTC (rderives ag) u v ⇒ (u=[NTS (startSym ag)]) ⇒ ∀sl N rst.(v=sl++[NTS N]++rst) ⇒ ~(sl=[]) ⇒ EVERY isTmnlSym sl ⇒ 
(auggr g st eof = SOME ag)
 ⇒ ∃lhs rhs.MEM (item lhs ([],HD (sl)::rhs)) (initItems ag (rules ag))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
Cases_on `sl` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `rhs` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] [] 
THENL[
      METIS_TAC [initItemsHdNt],

      SRW_TAC [] [] THEN
      `(t'=t) ∨ (∃pfx sfx.(t'=t++[NTS N]++pfx) ∧ (rst=pfx++sfx)) ∨ (∃pfx sfx.(t=pfx++sfx) ∧ (t'=pfx))` by METIS_TAC [listCompLens]
      THENL[
	    SRW_TAC [] [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`TS s::t`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [isTmnlSym_def, EVERY_DEF, APPEND_ASSOC, APPEND, NOT_CONS_NIL, HD, EVERY_APPEND],

	    SRW_TAC [] [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`TS s::t`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [isTmnlSym_def, EVERY_DEF, APPEND_ASSOC, APPEND, NOT_CONS_NIL, HD, EVERY_APPEND],

	    SRW_TAC [] [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`TS s::pfx`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [isTmnlSym_def, EVERY_DEF, APPEND_ASSOC, APPEND, NOT_CONS_NIL, HD, EVERY_APPEND]
	    ],

      SRW_TAC [] [] THEN
      `(t'=t) ∨ (∃pfx sfx.(t'=t++[NTS N]++pfx) ∧ (rst=pfx++sfx)) ∨ (∃pfx sfx.(t=pfx++sfx) ∧ (t'=pfx))` by METIS_TAC [listCompLens, APPEND, APPEND_ASSOC, APPEND_NIL]
      THENL[

	    SRW_TAC [] [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`TS s::t`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [isTmnlSym_def, EVERY_DEF, APPEND_ASSOC, APPEND, NOT_CONS_NIL, HD, EVERY_APPEND],

	    SRW_TAC [] [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`TS s::t`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [isTmnlSym_def, EVERY_DEF, APPEND_ASSOC, APPEND, NOT_CONS_NIL, HD, EVERY_APPEND],

	    SRW_TAC [] [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`TS s::pfx`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [isTmnlSym_def, EVERY_DEF, APPEND_ASSOC, APPEND, NOT_CONS_NIL, HD, EVERY_APPEND]
	    ]
      ]);



val vsisLen = store_thm ("vsisLen",
``∀l1 l2.validStlItemsStack l1 l2 ⇒ (LENGTH l2 = LENGTH l1 + 1)``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems] THEN
Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems] THEN
Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems] THEN
DECIDE_TAC);


val validStlItems_pop_lemma = store_thm ("validStlItems_pop_lemma",
``∀h' t' h t n.validStlItemsStack (h'::t') (h::t) ⇒ validStlItemsStack (pop t' (n - 1)) (pop t (n - 1)) ⇒ 
validStlItemsStack (pop (h'::t') n) (pop (h::t) n)``,
Induct_on `n` THEN SRW_TAC [] [validStlItemsStack] THEN
SRW_TAC [] [pop_def] THEN
METIS_TAC [validStlItemsStack]);

val validStlItems_pop = store_thm("validStlItems_pop",
``∀l1 l2 n.validStlItemsStack l1 l2 ⇒ (n <= LENGTH l1) ⇒
validStlItemsStack (pop l1 n) (pop l2 n)``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [validStlItemsStack] THEN
Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack] THENL[
SRW_TAC [] [pop_def, validStlItemsStack],

SRW_TAC [] [pop_def, validStlItemsStack] THEN
Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack],

Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack] 
THENL[

 Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack] THEN
 `(n=0) ∨ (n=1)` by DECIDE_TAC THEN
 FULL_SIMP_TAC (srw_ss()) [pop_def, validStlItemsStack],

 `validStlItemsStack (h'''::t') (h''::t)` by METIS_TAC [validStlItemsStack] THEN
 `n-1<=SUC (LENGTH t')` by DECIDE_TAC THEN
 RES_TAC THEN
 `validStlItemsStack (h'::h'''::t') (h::h''::t)` by METIS_TAC [validStlItemsStack] THEN
METIS_TAC [validStlItems_pop_lemma]
]]);


val rules2ItemsMemType = store_thm ("rules2ItemsMemType",
``∀l.MEM e (rules2Items l) ⇒ ∃lhs r. e = item lhs ([],r)``,
Induct_on `l` THEN SRW_TAC [] [rules2Items_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [rules2Items_def]);


val iclosureMemNotMemList = store_thm ("iclosureMemNotMemList",
``∀g l.MEM e (iclosure g l) ⇒ ~MEM e l ⇒  ∃lhs r. (e = item lhs ([],r))``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
Cases_on ` ~(set (rmDupes (v2::v3)) =
                 set (rmDupes (iclosure1 g (rmDupes (v2::v3)))))` THEN FULL_SIMP_TAC (srw_ss()) []
THENL[
 Cases_on `~MEM e (rmDupes (iclosure1 g (rmDupes (v2::v3))))` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [] [] THEN
 `~MEM e (rmDupes (v2::v3))` by METIS_TAC [rmd_r2, MEM] THEN
 `MEM e  (iclosure1 g (rmDupes (v2::v3)))` by METIS_TAC [rmd_r2] THEN
 `MEM e (rules2Items (rules g))` by METIS_TAC [iclosure1_outmem] THEN
 METIS_TAC [rules2ItemsMemType],

 `MEM e (rules2Items (rules g))` by METIS_TAC [iclosure1_outmem, rmd_r2, MEM] THEN
 METIS_TAC [rules2ItemsMemType]
 ]);



val sgotoMemType = store_thm ("sgotoMemType",
``∀e l itl.MEM e l ⇒ (l=(sgoto g itl h)) ⇒ (∃lhs r.(e=item lhs ([],r)) ∨ ∃lhs r1 r2.(e=item lhs (r1++[h],r2)))``,
Induct_on `itl` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, moveDot_def, iclosure] THEN
Cases_on `MEM e (moveDot (h'::itl) h)` THEN
METIS_TAC [mdMem, iclosureMemNotMemList]);


val iclosureMemRhsFstNil = store_thm ("iclosureMemRhsFstNil",
  ``∀g l.~MEM (item lhs (r1 ++ [h],r2)) l ⇒ ~(MEM (item lhs (r1 ++ [h],r2)) (iclosure g l))``,
    SRW_TAC [] [] THEN
    Cases_on `~MEM (item lhs (r1 ++ [h],r2)) (iclosure g l)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    `∃lhs' r. (item lhs (r1 ++ [h],r2)) = item lhs' ([],r)` by METIS_TAC [iclosureMemNotMemList] THEN
    FULL_SIMP_TAC (srw_ss()) []);
	      

val sgotoMemItlType = store_thm ("sgotoMemItlType",
``∀itl l.MEM (item lhs (r1++[h],r2)) l ⇒  (l=(sgoto g itl h)) ⇒ MEM (item lhs (r1,[h]++r2)) itl``,
Induct_on `itl` THEN SRW_TAC [] [] 
THENL[
      Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, iclosure, moveDot_def],

      FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, iclosure, moveDot_def] THEN
      Cases_on ` MEM (item lhs (r1 ++ [h],r2)) (moveDot (h'::itl) h)`
      THENL[
	    Cases_on `h'` THEN Cases_on `p` THEN Cases_on `r` THEN
	    FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, iclosure, moveDot_def] THEN
	    Cases_on `h=h'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] [] THEN
	    `∃l r1' r2'.
	    ((item lhs (r1 ++ [h],r2)) = item l (r1' ++ [h],r2')) ∧ MEM (item l (r1',h::r2')) itl` by METIS_TAC [mdMem] THEN
	    FULL_SIMP_TAC (srw_ss()) [],
	    
	    METIS_TAC [iclosureMemRhsFstNil]
	    ]
      ]);


val vsis_cons = store_thm ("vsi_cons",
``∀h itl l el.validStlItemsStack l ((s,h::itl)::el) ⇒ validStlItemsStack l ((s,itl)::el)``,

Induct_on `l` THEN SRW_TAC [] [validStlItemsStack] 
 THENL[

 Cases_on `el` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems],

 FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems]
 ]);

val vsiAlt = store_thm ("vsiAlt",
``∀stl l.validStlItems stl l = (∀e.MEM e l ⇒ isSuffix (itemFstRhs e) (stackSyms stl))``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM, validStlItems] THEN
FULL_SIMP_TAC (srw_ss()) []);

val validStlItems_sgoto_gen = store_thm("validStlItems_sgoto_gen",
``∀l itl sym el l'.validStlItemsStack l ((s, itl)::el) ⇒ (l'=(sgoto g itl sym)) ⇒
validStlItems  (((sym, (sgoto g itl sym)),tr)::l) l'``,

Induct_on `itl` THEN SRW_TAC [] [] 
 THENL[
  FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, sgoto_def, nextState_def, moveDot_def, iclosure, validStlItems],

 FULL_SIMP_TAC (srw_ss()) [] THEN
`validStlItems (((sym,sgoto g itl sym),tr)::l)
                   (sgoto g itl sym)`  by METIS_TAC [vsis_cons] THEN
FULL_SIMP_TAC (srw_ss()) [vsiAlt] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
`∃lhs r. 
           (e = item lhs ([],r)) ∨ ∃lhs r1 r2. e = item lhs (r1 ++ [sym],r2)` by METIS_TAC [sgotoMemType] 
 THENL[

 SRW_TAC [] [isSuffix_def, IS_PREFIX, itemFstRhs_def],

`MEM (item lhs' (r1,[sym] ++ r2)) (h::itl)` by METIS_TAC [sgotoMemItlType] THEN
Cases_on `l` THEN Cases_on `el` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack] THEN
 SRW_TAC [] [] 
 THENL[

 FULL_SIMP_TAC (srw_ss()) [isSuffix_def, itemFstRhs_def, IS_PREFIX, REVERSE_APPEND, validStlItems, stackSyms_def],

 FULL_SIMP_TAC (srw_ss()) [validStlItems, rgr_r9eq] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [validStlItems_append, validStlItems, stackSyms_def, isSuffix_def, itemFstRhs_def] THEN
 Cases_on `r1` THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND, IS_PREFIX],

 FULL_SIMP_TAC (srw_ss()) [isSuffix_def, itemFstRhs_def, IS_PREFIX, REVERSE_APPEND, validStlItems, stackSyms_def],

 FULL_SIMP_TAC (srw_ss()) [validStlItems, rgr_r9eq] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [validStlItems_append, validStlItems, stackSyms_def, isSuffix_def, itemFstRhs_def] THEN
 Cases_on `r1` THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND, IS_PREFIX],

  FULL_SIMP_TAC (srw_ss()) [isSuffix_def, itemFstRhs_def, IS_PREFIX, REVERSE_APPEND, validStlItems, stackSyms_def],


 FULL_SIMP_TAC (srw_ss()) [validStlItems, rgr_r9eq] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [validStlItems_append, validStlItems, stackSyms_def, isSuffix_def, itemFstRhs_def] THEN
 Cases_on `r1` THEN FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND, IS_PREFIX]
 ]]]);


val vsi_goto_lemma = store_thm ("vsi_goto_lemma",
``∀t itl l.validStlItems t itl ⇒
(∀e.
            MEM e l ⇒
            ∃lhs r'.
              (e = item lhs ([],r')) ∨
              ∃lhs r1 r2. e = item lhs (r1 ++ [sym],r2)) ⇒
(∀lhs r1 r2.
            MEM (item lhs (r1 ++ [sym],r2)) l ⇒
            MEM (item lhs (r1,[sym] ++ r2)) itl) ⇒
validStlItems (((sym,l),tr)::t) l``,

Induct_on `l` THEN SRW_TAC [] []  THENL[

SRW_TAC [] [validStlItems],

SRW_TAC [] [validStlItems] THENL[

`∃lhs r'.
              (h = item lhs ([],r')) ∨
              ∃lhs r1 r2. h = item lhs (r1 ++ [sym],r2)` by METIS_TAC [] 
THENL[

SRW_TAC [] [isSuffix_def, stackSyms_def, itemFstRhs_def, IS_PREFIX],

SRW_TAC [] [] THEN
`MEM (item lhs' (r1,sym::r2)) itl` by METIS_TAC [] THEN
`validStlItems t [item lhs' (r1,sym::r2)]` by METIS_TAC [rgr_r9eq, validStlItems_append] THEN
FULL_SIMP_TAC (srw_ss()) [validStlItems, isSuffix_def, itemFstRhs_def, IS_PREFIX, REVERSE_APPEND, stackSyms_def]
],


Cases_on `~∃e.MEM e l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[

Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [validStlItems] THEN
METIS_TAC [],

Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [validStlItems] THEN
METIS_TAC [],

FULL_SIMP_TAC (srw_ss()) [] THEN
`validStlItems (((sym,l),tr)::t) l` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [vsiAlt] THEN
SRW_TAC [] [] THEN
`isSuffix (itemFstRhs e') (stackSyms (((sym,l),tr)::t))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms_def]]]]);


val validStlItems_goto = store_thm ("validStlItems_goto",
``∀g itl itl' sym t.(getState (sgoto g, reduce g) itl sym = GOTO itl') ⇒
 validStlItems t itl ⇒
validStlItems (((sym,itl'), Leaf (ts2str sym))::t) itl'``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto g itl sym` THEN Cases_on `reduce g itl (ts2str sym)` THEN FULL_SIMP_TAC (srw_ss()) [] 
 THENL[
 Cases_on `LENGTH t'=0` THEN FULL_SIMP_TAC (srw_ss()) [],
 
`∀e.MEM e (h::t') ⇒ ∃lhs r'.(e = item lhs ([],r')) ∨ ∃lhs r1 r2. e = item lhs (r1 ++ [sym],r2)` by METIS_TAC [sgotoMemType, MEM] THEN
`∀lhs r1 r2.MEM (item lhs (r1 ++ [sym],r2)) (h::t') ⇒ MEM (item lhs (r1,[sym]++r2)) itl` by METIS_TAC [sgotoMemItlType, MEM] THEN
METIS_TAC [vsi_goto_lemma],

 Cases_on `itemEqRuleList (h::t') (h'::t'')` THEN FULL_SIMP_TAC (srw_ss()) []
 ]);



(*
lr1 components hold after one parse step
validStates ag (state s itl::csl) = parse_csl_validStates
*)

val parse_validStlItemsStack = store_thm("parse_validStlItemsStack",
``∀m g.validStlItemsStack stl csl ⇒ (m=slrmac g) ⇒
~NULL csl ⇒ (* preserved by parse_csl_not_nil *)
(LENGTH csl = LENGTH stl + 1) ⇒ (* another invariant *)
EVERY (\x.~(x=[])) (MAP SND csl) ⇒ (* prove this as an invariant∀∀∀∀∀ *)
~(stl=[]) ⇒
(parse m (sl, stl, csl) = SOME (sl',stl',csl')) ⇒ validStlItems stl' (SND (HD csl'))``,

SRW_TAC [] [] THEN
`∃x y.csl = x::y` by METIS_TAC [list_mem2, NULL_EQ_NIL] THEN
SRW_TAC [] [] THEN
Cases_on `x` THEN
`~NULL csl'` by METIS_TAC [parse_csl_not_nil] THEN
`∃x' y'.csl' = x'::y'` by (Induct_on `csl'` THEN SRW_TAC [] []) THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN 
Cases_on `slrmac g ` THEN  Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN Cases_on `getState x r h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[

(* doReduce x ([h],h'::t,state s l::y) r = SOME (sl',stl',x'::y') *)

FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym h` THEN Cases_on `addRule (h'::t) r'` THEN 
Cases_on `FST x (SND (HD (pop ((q,r)::y) (LENGTH (ruleRhs r')))))
				  (NTS (ruleLhs r')) = []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((q, r)::y) (LENGTH (ruleRhs r')) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `r'` THEN 
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [ADD1] THEN
`x=(sgoto g, reduce g)` by METIS_TAC [sgoto_exp] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`∃e el.(pop ((q, (h''::t'))::y) (LENGTH l)) = e::el` by METIS_TAC [list_nchotomy] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (h'::t) >= LENGTH l` by METIS_TAC [addrule_len] THEN
`LENGTH l <= LENGTH (h'::t)` by DECIDE_TAC THEN
`validStlItemsStack (pop (h'::t) (LENGTH l)) (e::el)` by METIS_TAC [validStlItems_pop, NOT_CONS_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [push_def, validStlItemsStack] THEN
Cases_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [pop_def, LENGTH] THENL[
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN METIS_TAC [validStlItems_sgoto_gen],

SRW_TAC [] [] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN METIS_TAC [validStlItems_sgoto_gen]],

(* doReduce x (h::h'::t',h''::t,state s l::y) r = SOME (sl',stl',x'::y') *)
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym h` THEN Cases_on `addRule (h''::t) r'` THEN 
Cases_on `FST x (SND (HD (pop ((q,r)::y) (LENGTH (ruleRhs r')))))
				  (NTS (ruleLhs r')) = []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((q, r)::y) (LENGTH (ruleRhs r')) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `r'` THEN 
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [ADD1] THEN
`x=(sgoto g, reduce g)` by METIS_TAC [sgoto_exp] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`∃e el.(pop ((q, (h'::t'))::y) (LENGTH l)) = e::el` by METIS_TAC [list_nchotomy] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (h''::t) >= LENGTH l` by METIS_TAC [addrule_len] THEN
`LENGTH l <= LENGTH (h''::t)` by DECIDE_TAC THEN
`validStlItemsStack (pop (h''::t) (LENGTH l)) (e::el)` by METIS_TAC [validStlItems_pop, NOT_CONS_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [push_def, validStlItemsStack] THEN
Cases_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [pop_def, LENGTH] THENL[
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN METIS_TAC [validStlItems_sgoto_gen],

SRW_TAC [] [] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN METIS_TAC [validStlItems_sgoto_gen]],


(* getState x l h = GOTO s' *)
Cases_on `isNonTmnlSym h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `x'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Induct_on `l` THEN 
FULL_SIMP_TAC (srw_ss()) [validStlItems, isSuffix_def, stackSyms_def, REVERSE_APPEND] THEN
Cases_on `q'` THEN Cases_on `h''` THEN
Cases_on `r'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [push_def] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems] THEN
FULL_SIMP_TAC (srw_ss()) [push_def,validStlItemsStack] THEN
SRW_TAC [] [] THEN
`x=(sgoto g, reduce g)` by METIS_TAC [sgoto_exp] THEN
SRW_TAC [] [] THEN
METIS_TAC [sgoto_exp, validStlItems_goto, APPEND, APPEND_ASSOC, validStlItems]]);


val validItem_moveDot = store_thm ("validItem_moveDot",
``∀itl.EVERY (validItem ag p) itl ⇒
EVERY (validItem ag (p++[h])) (moveDot itl h)``,
Induct_on `itl` THEN SRW_TAC [] [moveDot_def] THEN
Cases_on `h'` THEN Cases_on `p'` THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [moveDot_def]  THEN
Cases_on `h'=h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
SRW_TAC [] [] THEN
METIS_TAC [APPEND, APPEND_ASSOC]);



val getState_reduce_not_NA = store_thm ("getState_reduce_not_NA", 
``∀N r1 itl h ag. 
(slrmac ag = SOME (sgoto ag, reduce ag)) ⇒ 
(trans ag (initItems ag (rules ag),vp) = SOME itl) ⇒
MEM (item N (r1,[])) itl ⇒
 h IN followSet ag (NTS N) ⇒ isTmnlSym h ⇒
(∀j.
             MEM j itl ∧ completeItem j ∧
             h IN followSet ag (NTS (itemLhs j)) ⇒
             (j = item N (r1,[])))
⇒ ~(getState (sgoto ag,reduce ag) itl h = NA)``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [slrmac_def, LET_THM] THEN
Cases_on `∃pfx itl' sym. isTmnlSym sym ∧
               (trans ag (initItems ag (rules ag),pfx) = SOME itl') ∧
               case sgoto ag itl' sym of
                  [] ->
                    (case reduce ag itl' (ts2str sym) of
                        [] -> F
                     || [v12] -> F
                     || v12::v16::v17 -> T)
               || v8::v9 ->
                    case reduce ag itl' (ts2str sym) of
                       [] -> F
                    || [v20] -> T
                    || v20::v26::v27 -> T` THEN 
(FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`vp`,`itl`,`h`] MP_TAC) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto ag itl h` THEN 
Cases_on `reduce ag itl (ts2str h)` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [reduce_mem_followSet, NOT_CONS_NIL],

Cases_on `LENGTH t = 0` THEN SRW_TAC [] [] THEN
Cases_on `t` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [],

Cases_on `itemEqRuleList (h'::t) (h''::t')` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) []]));



val getState_shift_not_NA = store_thm 
("getState_shift_not_NA",
``∀g N r1 h' t itl.(SOME (sgoto g, reduce g) = slrmac g) ⇒
MEM (item N (r1,h'::t)) itl ⇒ isTmnlSym h' ⇒
(trans g (initItems g (rules g),vp) = SOME itl) ⇒
~(getState (sgoto g, reduce g) itl h' = NA)``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto g itl h'` THEN 
Cases_on `reduce g itl (ts2str h')` THEN FULL_SIMP_TAC (srw_ss()) [] 
THENL[
      METIS_TAC [sgoto_mem, NOT_CONS_NIL, APPEND, MEM, rgr_r9eq],

      METIS_TAC [sgoto_mem, NOT_CONS_NIL, APPEND, MEM, rgr_r9eq],

      Cases_on `itemEqRuleList (h::t') (h''::t'')` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [slrmac_def, LET_THM] THEN
      Cases_on `∃pfx itl' sym. isTmnlSym sym ∧
               (trans g (initItems g (rules g),pfx) = SOME itl') ∧
               case sgoto g itl' sym of
                  [] ->
                    (case reduce g itl' (ts2str sym) of
                        [] -> F
                     || [v12] -> F
                     || v12::v16::v17 -> T)
               || v8::v9 ->
                    case reduce g itl' (ts2str sym) of
                       [] -> F
                    || [v20] -> T
                    || v20::v26::v27 -> T` THEN 
      FULL_SIMP_TAC (srw_ss()) [] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`vp`,`itl`, `h'`] MP_TAC) THEN
      SRW_TAC [][] THEN
      Cases_on `t''` THEN SRW_TAC [][]]);

val validStkSymTree_stateSym_eq_ptree2Sym = store_thm 
("validStkSymTree_stateSym_eq_ptree2Sym", 
``∀stl.validStkSymTree stl ⇒ ((MAP FST (MAP FST stl)) = (MAP (ptree2Sym o SND) stl))``,
Induct_on `stl` THEN SRW_TAC [] [] THEN
Cases_on `h` THEN Cases_on `q` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [ptree2Sym_def, validStkSymTree_def]);


val addRule_SOME = store_thm ("addRule_SOME",
``∀pfx l stl.(stackSyms stl = pfx++l) ⇒ validStkSymTree stl 
			      ⇒ ∃x.(addRule stl (rule N l) = SOME x)``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [buildTree_def, LET_THM, stackSyms_def, addRule_def] THEN
`((MAP FST (MAP FST stl)) = (MAP (ptree2Sym o SND) stl))` by METIS_TAC [validStkSymTree_stateSym_eq_ptree2Sym] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(MAP (ptree2Sym o SND) stl) = REVERSE l ++ REVERSE pfx` by METIS_TAC [REVERSE_APPEND, REVERSE_REVERSE] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH l + LENGTH pfx >= LENGTH l` by DECIDE_TAC THEN
`LENGTH (REVERSE l) + LENGTH (REVERSE pfx) >= LENGTH (REVERSE l)` by DECIDE_TAC THEN
`LENGTH (REVERSE l ++ REVERSE pfx) >= (LENGTH (REVERSE l))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`∃x.((take (LENGTH (REVERSE l)) (REVERSE l ++ REVERSE pfx)) = SOME x)` by METIS_TAC [take_valid] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] 
THENL[
      FULL_SIMP_TAC (srw_ss()) [take_def, take10] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH stl = LENGTH (REVERSE t ++ [h] ++ REVERSE pfx)`
      by METIS_TAC [LENGTH_MAP] THEN
      FULL_SIMP_TAC (srw_ss()) [],

      SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (arith_ss) [] THEN
      `~((LENGTH (REVERSE t) + 1) = 0)` by DECIDE_TAC THEN
      `LENGTH (REVERSE t ++ [h]) = (LENGTH (REVERSE t) + 1)` by FULL_SIMP_TAC (arith_ss) [rev_nil, LENGTH, LENGTH_APPEND] THEN
      `take (LENGTH (REVERSE t) + 1) (REVERSE t ++ [h] ++ REVERSE pfx) = SOME (REVERSE t ++ [h])` by METIS_TAC [takenthm] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN

      `LENGTH (REVERSE t ++ [h]) = SUC (LENGTH t)` 
      by FULL_SIMP_TAC (srw_ss()++ARITH_ss) [LENGTH_REVERSE] THEN
      METIS_TAC [takenthm, APPEND_ASSOC, option_CASES, SOME_11]]);


val validStatesAuggrRule = store_thm ("validStatesAuggrRule", 
``(auggr g st eof = SOME ag) ⇒ MEM (item l' (r1,TS eof::r2)) itl
⇒ validStates ag ((s,itl)::csl) ⇒ 
(l'=startSym ag) ∧ (r1=[NTS (startSym g)]) ∧ (r2=[])``,
SRW_TAC [] [] THEN
`validItl ag [item l' (r1,TS eof::r2)]` by METIS_TAC [validStates_def, validStates_append, rgr_r9eq, validItl_append] THEN
FULL_SIMP_TAC (srw_ss()) [validItl_def, auggr_def, startSym_def, LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g) ∧ ~(TS eof IN terminalsML g)` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`ag = G (rule st [NTS (startSym g); TS eof]::rules g) st` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def, startSym_def] THENL[

METIS_TAC [APPEND, slemma1_4Tmnls, terminalsEq, APPEND_NIL, APPEND_ASSOC],
SRW_TAC [] [] THEN
Cases_on `r1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC [APPEND, slemma1_4Tmnls, terminalsEq, APPEND_NIL, APPEND_ASSOC],
SRW_TAC [] [] THEN
Cases_on `r1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC [APPEND, slemma1_4Tmnls, terminalsEq, APPEND_NIL, APPEND_ASSOC]]);

val mapFstHd = store_thm ("mapFstHd",
``∀l.~(l=[]) ⇒ (FST (FST (HD l)) = HD (MAP FST (MAP FST l)))``,
Induct_on `l` THEN SRW_TAC [] []);

val funcCompNegEq = store_thm ("funcCompNegEq",
``∀l.EVERY ($~ o $~ o isTmnlSym) l ⇒ EVERY isTmnlSym l``,
Induct_on `l` THEN SRW_TAC [] []);

val listEndNt = store_thm ("listEndNt",
``∀l l' sfx.(l ++ [NTS N] = l' ++ sfx) ⇒ EVERY isTmnlSym sfx ⇒ (sfx=[])``,

Induct_on `sfx` THEN SRW_TAC [][] THEN
`LAST (l ++ [NTS N]) = LAST (l' ++ h::sfx)` by METIS_TAC [] THEN
`LAST ([NTS N]) = LAST (h::sfx)` by METIS_TAC [last_append, NOT_CONS_NIL, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`[]`, `[LAST (h::sfx)]`] MP_TAC) THEN
SRW_TAC [] [] THEN
Cases_on `EXISTS ($~ o isTmnlSym) sfx` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`EVERY isTmnlSym sfx` by METIS_TAC [funcCompNegEq] THEN
Cases_on `sfx` THEN Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] [] THEN
`(FRONT (TS s::t) ++ [LAST (TS s::t)]) = (TS s::t)` by  METIS_TAC [APPEND_FRONT_LAST, NOT_CONS_NIL] THEN
`EVERY isTmnlSym  (FRONT (TS s::t) ++ [NTS N])` by METIS_TAC [EVERY_DEF, EVERY_APPEND, isTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]);


val transImpValidItem = store_thm ("transImpValidItem",
``∀s. (slrmac ag = SOME m) ∧ (auggr g st eof = SOME ag) ∧
      (trans ag ((initItems ag (rules ag)), vp) = SOME s) ⇒
      ∀i. validItem ag vp i ⇒ MEM i s``,

Induct_on `LENGTH vp` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] 
THENL[
      `vp=[]` by METIS_TAC [LENGTH_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
      Cases_on `i` THEN Cases_on `p` THEN
      FULL_SIMP_TAC (srw_ss()) [validItem] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      METIS_TAC [initItemsHdNt],
	 

      FULL_SIMP_TAC (srw_ss()) [len_snoc] THEN SRW_TAC [][] THEN 
      Cases_on `i` THEN Cases_on `p` THEN
      FULL_SIMP_TAC (srw_ss()) [validItem] THEN 
      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [trans_snoc] THEN 
      Cases_on `trans ag (initItems ag (rules ag), pfx)` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN 
      Cases_on `moveDot x t` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `((pfx'=pfx) ∧ (q=[t])) ∨
       (∃q1 q2.(q=q1++q2) ∧ (pfx=pfx'++q1) ∧ ([t]=q2)) ∨
       (∃t1 t2.([t]=t1++t2) ∧ (pfx'=pfx++t1) ∧ (q=t2))` by METIS_TAC [twoListAppEq] THEN
      SRW_TAC [] [] 
      THENL[
	    `∃s.(trans ag (initItems ag (rules ag),pfx) = SOME s) 
                ∧ MEM (item n ([],[t]++r)) s` 
		by METIS_TAC [lemma, RTC_NRC] THEN
	    `x=s` by METIS_TAC [transOutEq] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [md_append, moveDot_def] THEN
	    METIS_TAC [iclosure_mem, MEM, MEM_APPEND, rgr_r9eq],

	    `∃s.(trans ag (initItems ag (rules ag),pfx') = SOME s) 
               ∧ MEM (item n ([],q1++[t]++r)) s` 
		by METIS_TAC [lemma, RTC_NRC] THEN
	    `∃st.(trans ag (s,q1) = SOME st) 
                  ∧ MEM (item n ([]++q1,[t]++r)) st` 
		by METIS_TAC [transExists, APPEND_ASSOC] THEN
	    FULL_SIMP_TAC (srw_ss()) []THEN
	    `trans ag (initItems ag (rules ag),pfx'++q1) = SOME st'` 
		by METIS_TAC [transSeq, initItems_def] THEN
	    `x=st'` by METIS_TAC [transOutEq] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [md_append, moveDot_def] THEN
	    METIS_TAC [iclosure_mem, MEM, MEM_APPEND, rgr_r9eq],


	    SRW_TAC [] [] THEN
	    `∃s.(trans ag (initItems ag (rules ag),pfx++t1) = SOME s) 
               ∧ MEM (item n ([],q++r)) s` 
		by METIS_TAC [lemma, RTC_NRC] THEN
	    Cases_on `t1` THEN Cases_on `q` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] []
            THENL[
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [md_append, moveDot_def] THEN
		  METIS_TAC [iclosure_mem, MEM, MEM_APPEND, rgr_r9eq],

		  FULL_SIMP_TAC (srw_ss()) [trans_snoc] THEN
		  Cases_on `trans ag (initItems ag (rules ag),pfx)` THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  Cases_on `moveDot x' h'`THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC []
		  ]]]);

val _ = export_theory()