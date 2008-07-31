open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory

open regexpTheory grammarDefTheory boolLemmasTheory listLemmasTheory
whileLemmasTheory parseTreeTheory followSetDefTheory parserDefTheory
yaccDefTheory parseProp1DefTheory parseProp2DefTheory rich_listTheory



val rsf = Define `rsf g sf = RTC (rderives g) [NTS (startSym g)] sf`

val handleg = Define 
`handleg g sf rhs (pfx,lhs,sfx) = 
?sf'.RTC (rderives g) [NTS (startSym g)] sf' /\
(sf'=pfx++[NTS lhs]++sfx) /\ (MEM (rule lhs rhs) (rules g)) /\
(sf = pfx++rhs++sfx) /\ EVERY isTmnlSym sfx`


val viablePfx = Define 
`viablePfx g (N,h) sf p = ?pfx sfx.handleg g sf h (pfx,N,sfx) /\
IS_PREFIX (pfx++h) p`


val validItem = Define 
`validItem g vp (item l (r1,r2)) = 
?pfx sfx.RTC (rderives g) [NTS (startSym g)] (pfx++[NTS l]++sfx) /\
rderives g (pfx++[NTS l]++sfx) (pfx++r1++r2++sfx) /\
(pfx++r1=vp)`


(*
val incompItem = Define `(incompItem (item l (r1,[])) = F) /\
(incompItem (item l (r1,(TS ts)::r2)) = F) /\
(incompItem (item l (r1,(NTS ts)::r2)) = T)`
*)

val rsforms = Define `rsforms g = {tsl | RTC (rderives g) [NTS (startSym g)] tsl}`


val sgoto_exp = store_thm ("sgoto_exp", 
``!g.(slr g = SOME m) ==> (m= (sgoto g, reduce g))``,
SRW_TAC [] [slr_def, LET_THM])


val stackSyms = Define `stackSyms stl = (REVERSE (MAP FST (MAP FST stl)))`


val completeItem = Define `(completeItem (item l (r1, [])) = T) /\
(completeItem (item l (r1, r2)) = F)`


val list_mem1 = store_thm ("list_mem1", 
``!l.~(l=[]) = ?e.MEM e l``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM, list_exists_mem])

val list_mem2 = store_thm ("list_mem2", 
``!l.~(l=[]) = ?h t.(l=h::t)``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM])

val md_append = store_thm ("md_append", 
``!l1 l2.moveDot (l1++l2) sym = moveDot l1 sym ++ moveDot l2 sym``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [moveDot_def] THEN
Cases_on `h'` THEN Cases_on `p` THEN Cases_on `r` THEN Cases_on `h'=sym` THEN
FULL_SIMP_TAC (srw_ss()) [moveDot_def])


val iclosure_mem = store_thm ("iclosure_mem",
``!g l.MEM e l ==> MEM e (iclosure g l)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, LET_THM] THEN
METIS_TAC [rmd_r2, iclosure1_mem, MEM])

val sgoto_mem = store_thm ("sgoto_mem", 
``MEM (item s (q,sym::t)) itl ==> (MEM (item s (q++[sym],t)) (sgoto ag itl sym))``,
SRW_TAC [] [sgoto_def, nextState_def] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, md_append, moveDot_def] THEN
METIS_TAC [rgr_r9eq, iclosure_mem])

val getState_mem_itl = store_thm ("getState_mem_itl", 
``validItl g itl ==> (m = (sgoto g, reduce g)) ==> 
(getState m itl e = REDUCE (rule s' l)) ==> (MEM (item s' (l,[])) itl)``,
SRW_TAC [] [] THEN
`MEM (rule s' l) (rules g)` by METIS_TAC [getstate_red] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto g itl e` THEN Cases_on `reduce g itl (sym2Str e)` THEN FULL_SIMP_TAC (srw_ss()) []  THENL[
Cases_on `LENGTH t = 0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`MEM (rule s' l) (rule s' l::t)` by METIS_TAC [MEM] THEN
`?l' r1. (rule s' l = rule l' r1) /\ MEM (item l' (r1,[])) itl` by METIS_TAC [reduce_mem] THEN
FULL_SIMP_TAC (srw_ss()) [],

Cases_on `itemEqRuleList (h::t) (h'::t')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
`MEM (rule s' l) (rule s' l::t')` by METIS_TAC [MEM] THEN
`?l' r1. (rule s' l = rule l' r1) /\ MEM (item l' (r1,[])) itl` by METIS_TAC [reduce_mem] THEN
FULL_SIMP_TAC (srw_ss()) []])




val shiftReduce = store_thm ("shiftReduce",
``(slr ag = SOME m) ==> validItl ag itl ==> (getState m itl sym = REDUCE (rule l r)) ==>
!e.MEM e itl ==> (e=item l (r,[])) \/ ~(?l' r2 r1.e = item l' (r1,sym::r2))``,
SRW_TAC [] [] THEN
`m = (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
SRW_TAC [] [] THEN
`MEM (item l (r,[])) itl` by METIS_TAC [getState_mem_itl, sgoto_exp, validStates_def] THEN
Cases_on `e` THEN Cases_on `p` THEN Cases_on `r'` THEN
FULL_SIMP_TAC (srw_ss()) [slr_def, LET_THM] THEN
Cases_on `q=r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `h=sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s (q++[sym],t)) (sgoto ag itl sym)` by METIS_TAC [sgoto_mem] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
`?h t.(sgoto ag itl sym) = h::t` by METIS_TAC [list_mem1, list_mem2] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `reduce ag itl (sym2Str sym)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `itemEqRuleList (h'::t') (h''::t'')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
`?h t.reduce ag itl (sym2Str sym) = h::t` by METIS_TAC [list_mem1, list_mem2, NOT_CONS_NIL, APPEND] THEN
FULL_SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`itl`, `h`] MP_TAC) THEN
Cases_on `t''` THEN SRW_TAC [][])

val followSetEq = mk_thm ([], ``!g sym.s IN (followSetML g sym) = s IN (followSet g sym)``)


val reduce_not_mem = store_thm ("reduce_not_mem",
``isTmnlSym sym ==> (reduce ag itl (sym2Str sym) = []) ==> 
(!e.MEM e itl ==> (~?N r.(e=(item N (r,[]))) /\ (sym IN (followSet ag (NTS N)))))``,
Cases_on `itl` THEN SRW_TAC [] [] THENL[
`(reduce ag [e] (sym2Str sym) ++ (reduce ag t (sym2Str sym)) = [])` by METIS_TAC [reduce_append, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e` THEN  
Cases_on `p` THEN 
Cases_on `item s (q,r') = item N (r,[])` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
Cases_on `sym` THEN FULL_SIMP_TAC (srw_ss()) [sym2Str_def, isTmnlSym_def] THEN
Cases_on `TS s' IN followSetML ag (NTS N)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [followSetEq],

FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, reduce_append] THEN
SRW_TAC [] [] THEN
`(reduce ag [h] (sym2Str sym) ++ reduce ag r1 (sym2Str sym) ++
reduce ag [e] (sym2Str sym) ++ (reduce ag r2 (sym2Str sym)) = [])` by METIS_TAC [reduce_append, APPEND] THEN
`reduce ag [e] (sym2Str sym) = []` by FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e` THEN  
Cases_on `p` THEN 
Cases_on `item s (q,r') = item N (r,[])` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
Cases_on `sym` THEN FULL_SIMP_TAC (srw_ss()) [sym2Str_def, isTmnlSym_def] THEN
Cases_on `TS s' IN followSetML ag (NTS N)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [followSetEq]])



val shiftReduceGoto = store_thm ("shiftReduceGoto",
``(slr ag = SOME m) ==> isTmnlSym sym ==> validItl ag itl ==> (getState m itl sym = GOTO s') ==>
~?N r.MEM (item N (r,[])) itl /\ (sym IN (followSet ag (NTS N)))``,
SRW_TAC [] [] THEN
`m = (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [slr_def, LET_THM] THEN
Cases_on `?itl' sym'.
               case sgoto ag itl' sym' of
                  [] ->
                    (case reduce ag itl' (sym2Str sym') of
                        [] -> F
                     || [v12] -> F
                     || v12::v16::v17 -> T)
               || v8::v9 ->
                    case reduce ag itl' (sym2Str sym') of
                       [] -> F
                    || [v20] -> T
                    || v20::v26::v27 -> T` THEN FULL_SIMP_TAC (srw_ss()) [] THEN

FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto ag itl sym` THEN
Cases_on `reduce ag itl (sym2Str sym)` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `LENGTH t = 0` THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC [reduce_not_mem],
Cases_on `itemEqRuleList (h::t) (h'::t')` THEN FULL_SIMP_TAC (srw_ss()) []])



val auggr_neqStartSym = store_thm ("auggr_neqStartSym", 
``(auggr g st eof = SOME ag) ==> !n.MEM (rule n []) (rules ag) ==> ~(n=st)``,
SRW_TAC [] [auggr_def] THEN
SRW_TAC [] [rules_def] THEN
METIS_TAC [slemma1_4, nonTerminalsEq])

val last_elem = store_thm ("last_elem", 
``!l pfx e. (l = pfx ++ [e]) ==> (LAST l = e)``,
Induct_on `pfx` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [LAST_DEF])


val auggr_neqStartSym2 = store_thm ("auggr_neqStartSym2", 
``(auggr g st eof = SOME ag) ==> MEM (rule n l) (rules ag) ==> ~(LAST l = TS eof) ==> ~(n=st)``,
SRW_TAC [] [auggr_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THENL[
METIS_TAC [last_elem, APPEND],
Cases_on `n=st` THEN
METIS_TAC [slemma1_4, nonTerminalsEq]])


val list_neq = store_thm ("list_neq", 
``!st n.~(st=n) ==> ~?pfx sfx.[NTS st] = pfx++[NTS n]++sfx``,
SRW_TAC [] [] THEN
Induct_on `pfx` THEN SRW_TAC [] [])

val auggr_startSym = store_thm ("auggr_startSym", 
``(auggr g st eof = SOME ag) ==> (startSym ag = st)``,
SRW_TAC [] [auggr_def] THEN SRW_TAC [] [startSym_def])

val stackSyms_stl = store_thm ("stackSyms_stl", 
``(doReduce m (e::t,stl,(s, itl)::csl) r = SOME (sl',stl',csl')) ==>
(getState m itl e = REDUCE r) ==>
(stackSyms stl' = stackSyms (pop stl (LENGTH (ruleRhs r))) ++  [NTS (ruleLhs r)])``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl r` THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def] THEN
`stl' = ((NTS s',
            FST m
              (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs (rule s' l))))))
              (NTS s')),x)::pop stl (LENGTH (ruleRhs (rule s' l)))` by METIS_TAC [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [] [stackSyms, ruleRhs_def])

val isSuffix = Define `isSuffix x l = IS_PREFIX  (REVERSE l)  (REVERSE x)`

val validStlItems = Define `(validStlItems stl [] = T) /\
(validStlItems stl (e::t) =  (isSuffix (itemFstRhs e) (stackSyms stl)) /\ validStlItems stl t)`

val validStlItemsStack = Define 
`(validStlItemsStack [] [e] = validStlItems ([]:((symbol # state) # ptree) list) (SND e)) /\
(validStlItemsStack (h::stl) (e::csl) =  
 validStlItems (h::stl) (SND e) /\ validStlItemsStack stl csl) /\
(validStlItemsStack _ _ = F)`

val validItemStack = Define `(validItemStack g [] = T) /\
(validItemStack g (e::rst) =  
                       EVERY (validItem g (stackSyms (e::rst))) (SND (FST e)) /\ 
                       validItemStack g rst )`


val validStlItems_append = store_thm ("validStlItems_append", 
``!l1 l2.validStlItems stl (l1++l2) = validStlItems stl l1 /\ validStlItems stl l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [] THENL[
METIS_TAC [APPEND, validStlItems],
METIS_TAC [APPEND, validStlItems],
Cases_on `h'` THEN Cases_on `p`  THEN METIS_TAC [APPEND, validStlItems, APPEND_ASSOC, APPEND_NIL]])

val cx = store_thm ("cx",
``!stl pfx h e t sfx.~(h=e) ==> ~(stl ++ [e] = pfx ++ stl ++ h::t ++ sfx)``,
Cases_on `pfx` THEN SRW_TAC [] [] THENL[
Cases_on `t` THEN SRW_TAC [] [] THEN
Cases_on `sfx` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `(stl ++ [e] = stl ++ [h] ++ h'::t)` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (stl ++ [e]) = LENGTH (stl ++ [h] ++ h'::t)` by METIS_TAC [] THEN
FULL_SIMP_TAC (arith_ss) [ADD1, LENGTH_APPEND, LENGTH],

Cases_on `~(stl ++ [e] = stl ++ h::h'::t' ++ h''::t)` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (stl ++ [e]) = LENGTH (stl ++ h::h'::t'++h''::t)` by METIS_TAC [] THEN
FULL_SIMP_TAC (arith_ss) [ADD1, LENGTH_APPEND, LENGTH]],

Cases_on ` ~(stl ++ [e] = h::(t ++ stl ++ h'::t' ++ sfx))` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (stl ++ [e]) = LENGTH (h::(t ++ stl ++ h'::t' ++ sfx))` by METIS_TAC [] THEN
FULL_SIMP_TAC (arith_ss) [ADD1, LENGTH_APPEND, LENGTH]])

val pop_eq = store_thm ("pop_eq", 
``!l n.(LENGTH l = n) ==> (pop l n = [])``,
Induct_on `l` THEN SRW_TAC [] [pop_def] THEN
FULL_SIMP_TAC (arith_ss) [])

val stackSyms_len = store_thm ("stackSyms_len", 
``!stl.LENGTH stl = LENGTH (stackSyms stl)``,
Induct_on `stl` THEN SRW_TAC [] [stackSyms] THEN
FULL_SIMP_TAC (srw_ss()) [ADD1])


val c0 = store_thm ("c0",
``!pfx stl l.(pfx ++ l = REVERSE (MAP FST (MAP FST stl)))  ==>
(REVERSE (MAP FST (MAP FST (pop stl (LENGTH l)))) = pfx)``,
SRW_TAC [] [] THEN
`(MAP FST (MAP FST (pop stl (LENGTH l)))) = pop (MAP FST (MAP FST stl)) (LENGTH l)` by METIS_TAC [map_pop] THEN
ONCE_ASM_REWRITE_TAC [] THEN
`(MAP FST (MAP FST stl)) = REVERSE (pfx++l)` by METIS_TAC [REVERSE_REVERSE] THEN
FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
METIS_TAC [popnthm, REVERSE_REVERSE, rev_len])



val last_append = store_thm ("last_append", 
``!l1 l2.~(l2=[]) ==> (LAST (l1++l2) = LAST l2)``,
SRW_TAC [] [] THEN
`?h t.l2=h::t` by METIS_TAC [list_mem2] THEN
SRW_TAC [] [LAST_DEF] THEN
Induct_on `l1` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [LAST_DEF])



val auggr_notStartRule = store_thm ("auggr_notStartRule",
``(slr ag = SOME m) ==> (validStates ag ((s, itl)::csl)) ==>
(auggr g st eof = SOME ag) ==> ~(FST (FST (HD stl)) = TS eof) ==> 
(?pfx.stackSyms stl = pfx++l) ==> 
(getState m itl e = REDUCE (rule N l)) ==> ~(N=st)``,
SRW_TAC [] [] THEN 
`MEM (rule N l) (rules ag)` by METIS_TAC [getstate_red, APPEND, validStates_def, sgoto_exp] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
Cases_on `stl` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
SRW_TAC [] [] THEN METIS_TAC [auggr_neqStartSym],

Cases_on `h` THEN Cases_on `q` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l` THENL[
SRW_TAC [] [] THEN METIS_TAC [auggr_neqStartSym],
`LAST (REVERSE (MAP FST (MAP FST t)) ++ [q']) = LAST (pfx ++ h::t')` by METIS_TAC [] THEN
METIS_TAC [auggr_neqStartSym2, last_elem, last_append, NOT_CONS_NIL]]])

(*
val getstate_r2 = store_thm ("getstate_r2", 
``!m itl sym.(getState m itl sym = GOTO (state s l)) ==> (s=sym)``,
SRW_TAC [] [] THEN
Cases_on `m` THEN 
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `q itl sym` THEN Cases_on `r itl (sym2Str sym)` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `LENGTH t` THEN FULL_SIMP_TAC (srw_ss()) [],
Cases_on `itemEqRuleList (h::t) (h'::t')`  THEN FULL_SIMP_TAC (srw_ss()) []])
*)

val list_isp = store_thm ("list_isp",
``!s1' s2' N l.(s1' ++ s2' = pfx ++ [NTS N] ++ l) ==> 
EVERY isTmnlSym s2' ==> EVERY isTmnlSym l ==> 
IS_PREFIX s1' (pfx ++ [NTS N])``,
Induct_on `pfx` THEN SRW_TAC [] [] THENL[
Cases_on `s1'` THEN SRW_TAC [] [] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, IS_PREFIX],
Cases_on `s1'` THEN SRW_TAC [] [] THENL[
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN METIS_TAC [IS_PREFIX, IS_PREFIX_REFL]]])

val pfxthm2 = store_thm ("pfxthm2",
``!r1 sfx.(IS_PREFIX r1 (r1 ++ sfx) ==> (sfx=[]))``,
Induct_on `r1` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
Induct_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [IS_PREFIX])


val getState_nil = store_thm ("getState_nil", 
``~(getState (sgoto g, reduce g) [] h = REDUCE (rule s'' l'))``,
SRW_TAC [] [getState_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `sgoto g [] h` THEN 
Cases_on `reduce g [] (sym2Str h)` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def])


val reduce_mem_followSet = store_thm ("reduce_mem_followSet", 
``!N r1 itl h.MEM (item N (r1,[])) itl ==> isTmnlSym h ==>
h IN followSet ag (NTS N) ==> ~(reduce ag itl (sym2Str h) =[])``,
Induct_on `itl` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def, LET_THM] THEN
Cases_on `h'` THEN FULL_SIMP_TAC (srw_ss()) [sym2Str_def, followSetEq, isTmnlSym_def] THEN
RES_TAC THEN
`~(reduce ag itl s = [])` by METIS_TAC [sym2Str_def] THEN
Cases_on `h` THEN Cases_on `p` THEN 
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [reduce_def, LET_THM , isTmnlSym_def, followSetEq] THEN
Cases_on ` TS s IN followSet ag (NTS s')` THEN FULL_SIMP_TAC (srw_ss()) [])



val reduce_followSet = store_thm ("reduce_followSet",
``!l s out.(reduce g l s = out) ==> (!e.MEM e out ==> (TS s) IN followSet g (NTS (ruleLhs e)))``,
Induct_on `l` THEN SRW_TAC [] [reduce_def] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
Cases_on `TS s IN followSetML g (NTS s')` THEN 
FULL_SIMP_TAC (srw_ss()) [followSetEq, ruleLhs_def])


val getState_reduce_followSet = store_thm ("getState_reduce_followSet", 
``(m=(sgoto g, reduce g)) ==> validItl g itl ==>
isTmnlSym sym ==> (getState m itl sym = REDUCE (rule s' l)) ==> sym IN (followSet g (NTS s'))``,
Cases_on `itl` THEN SRW_TAC [] [getState_def, LET_THM] THEN Cases_on `sym` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, sym2Str_def] THENL[

Cases_on `sgoto g [] (TS s)` THEN Cases_on `reduce g [] s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def],

Cases_on `sgoto g [] (TS s)` THEN Cases_on `reduce g [] s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def],


Cases_on `sgoto g (h::t) (TS s)` THEN Cases_on `reduce g (h::t) s` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
SRW_TAC [] [] THEN
METIS_TAC [ruleLhs_def, reduce_followSet, MEM],
Cases_on `itemEqRuleList (h'::t') (h''::t'')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [ruleLhs_def, reduce_followSet, MEM]],

Cases_on `sgoto g (h::t) (TS s)` THEN Cases_on `reduce g (h::t) s` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `itemEqRuleList (h'::t') (h''::t'')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [ruleLhs_def, reduce_followSet, MEM]])


val validItls = Define `
validItls ((s, itl)) topitl = 
(!N r1 r2.(MEM (item N (r1,r2)) itl) ==> (r1=[]) \/
(LAST r1 = s)) /\
(!N' r1' r2'.(MEM (item N' (r1',r2')) topitl) ==> (r1'=[]) \/ (?l1 l2.(r1'=l1++[s]++l2) /\ 
MEM (item N' (l1++[s],l2++r2')) itl))`

val stateValidItls = Define `
(stateValidItls [] topitl = T) /\
(stateValidItls (st::rst) topitl = validItls st topitl /\ stateValidItls rst topitl)`

val symsAfterDot = Define `(symsAfterDot [] = []) /\
(symsAfterDot (item l (r1,[])::t) = symsAfterDot t) /\
(symsAfterDot (item l (r1,s::ss)::t) = s::symsAfterDot t)`

val str2nts = Define `(str2nts s = NTS s)`

val rhsEqItems = Define `rhsEqItems e1 e2 = (itemFstRhs e1 ++ itemSndRhs e1 = itemFstRhs e2 ++ itemSndRhs e2)`

val reduce_reduce_cond = Define 
`reduce_reduce_cond ag itl = ~?e1 e2.MEM e1 itl /\ MEM e2 itl /\ ~(e1=e2) /\ completeItem e1 /\ completeItem e2 /\ rhsEqItems e1 e2 /\ 
~?s.(TS s) IN ((followSet ag (NTS (itemLhs e1))) INTER (followSet ag (NTS (itemLhs e2))))`

val shift_reduce_cond = Define 
`(shift_reduce_cond ag itl = ~?e1 e2.MEM e1 itl /\ MEM e2 itl /\ completeItem e1 /\
~?s. (TS s) IN ((followSet ag (NTS (itemLhs e1))) INTER (LIST_TO_SET ((symsAfterDot [e2])))))`

val disjoint = Define `(disjoint ag itl = 
reduce_reduce_cond ag itl /\ shift_reduce_cond ag itl)`


val noRepeatRulesInItl = Define `noRepeatRulesInItl itl =
(!l r1 r2.MEM (item l (r1, r2)) itl ==> 
          (~?r1' r2'.MEM (item l (r1',r2')) itl /\ (r1'++r2'=r1++r2) /\ ~((r1',r2')=(r1,r2))))`

val lr1_inv = Define `lr1_inv (ag, stl, ((s, itl)::csl), inp) = 
(* stateValidItls csl itl /\ *)
EVERY (validItem ag (stackSyms stl)) itl /\
validStlItems stl itl /\
validStates ag ((s, itl)::csl) /\
(?pfx h N sfx.
        handleg ag (stackSyms stl++inp) h (pfx,N,sfx) /\ IS_PREFIX (pfx ++ h) (stackSyms stl) /\
        (
	 if (isSuffix h (stackSyms stl) /\ (MEM (item N (h,[])) itl) /\ (sfx=inp)) then
	     ( ((HD inp) IN (followSet ag (NTS N))) /\ 
	     (!j. MEM j itl /\ completeItem j /\ (HD inp) IN (followSet ag (NTS (itemLhs j))) ==> 
                          (j=item N (h,[])))) 
	else	    
	    ?l r1 r2 e.(MEM (item l (r1,e::r2)) itl /\ ((isSuffix r1 (stackSyms stl)) /\ (HD inp = e)))))`
(*

/\
	    ?pfx0 sfx0 pfx1 sfx1.RTC (rderives ag) (pfx0++[NTS l]++sfx0) (pfx1++[NTS N]++sfx1)

pfx'++[l]++sfx' can lead to pfx + [handle] + sfx

either l itself is the handle or l can rderive all terminals which is a part of the prefix+handle??

*)


val isNewItem = Define `(isNewItem [] = T) /\
(isNewItem ((item l (r1,r2))::rst) = if (r1=[]) then (isNewItem rst) else F)`

val isNewItem_rules2items = store_thm ("newItem_rules2items",
``!g.isNewItem  (rules2Items (rules g))``,
Cases_on `g` THEN SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [isNewItem, rules2Items_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isNewItem,rules2Items_def])


val isNewItem_append = store_thm ("isNewItem_append",
``!l1 l2.isNewItem (l1++l2) = isNewItem l1 /\ isNewItem l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [isNewItem, EQ_IMP_THM] THEN
Cases_on `h'` THEN Cases_on `p` THEN
METIS_TAC [APPEND, isNewItem])


val isNewItem_mem = store_thm ("isNewItem_mem",
``!l. isNewItem l = (!e.MEM e l ==> isNewItem [e])``,
Induct_on `l` THEN SRW_TAC [] [isNewItem, EQ_IMP_THM] THEN
METIS_TAC [isNewItem_append, APPEND])

val isNewItem_getItems = store_thm ("isNewItem_getItems",
``! g sym.isNewItem (getItems (rules g) sym)``,
Induct_on `rules g` THEN SRW_TAC [] [isNewItem, getItems_def] THENL[
METIS_TAC [isNewItem, getItems_def],
`rules g = h::v` by METIS_TAC [] THEN 
Cases_on `h` THEN ONCE_ASM_REWRITE_TAC [] THEN
`!e.MEM e (getItems (rule s l::v) sym) ==> MEM e (rules2Items (rule s l::v))` by METIS_TAC [rules2items_sub] THEN
`isNewItem (rules2Items (rule s l ::v))` by METIS_TAC [isNewItem_rules2items, rules_def] THEN
`!e.MEM e (rules2Items (rule s l::v)) ==> isNewItem [e]` by METIS_TAC [isNewItem_mem] THEN
METIS_TAC [isNewItem_mem, APPEND, isNewItem_append, getItems_def]]) 


val isNewItem_iclosure1 = store_thm ("isNewItem_iclosure1", 
``!g itl.isNewItem itl ==> isNewItem (iclosure1 g itl)``,
Induct_on `itl` THEN SRW_TAC [] [isNewItem, iclosure1_def] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1_def, isNewItem] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1_def, isNewItem] THEN
METIS_TAC [isNewItem, isNewItem_append, APPEND, APPEND_ASSOC, isNewItem_getItems])


val isNewItem_delete = store_thm ("isNewItem_delete",
``!t h.isNewItem  t ==> isNewItem  (delete h t)``,
Induct_on `t` THEN SRW_TAC [] [delete_def, isNewItem] THEN
METIS_TAC [isNewItem_append, APPEND])


val isNewItem_rmDupes = store_thm ("isNewItem_rmDupes", 
``!itl.isNewItem  itl ==> isNewItem (rmDupes itl)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes, isNewItem] THEN
METIS_TAC [isNewItem_append, APPEND, isNewItem_delete])


val isNewItem_iclosure = store_thm ("isNewItem_iclosure",
``!g itl.isNewItem  itl ==> isNewItem  (iclosure g itl)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, isNewItem, LET_THM] THEN
METIS_TAC [isNewItem_rmDupes, isNewItem_iclosure1])


val isNewItem_initProds2Items = store_thm ("isNewItem_initProds2Items",
``!s l.isNewItem (initProds2Items s l)``,
Induct_on `l` THEN SRW_TAC [] [initProds2Items_def, isNewItem] THEN
Cases_on `h` THEN SRW_TAC [] [initProds2Items_def, isNewItem])

val isNewItem_everyNullFstRhs = store_thm ("isNewItem_everyNullFstRhs",
``!l.isNewItem l = EVERY NULL (MAP itemFstRhs l)``,
Induct_on `l` THEN SRW_TAC [] [isNewItem] THEN
Cases_on `h` THEN  Cases_on `p` THEN
FULL_SIMP_TAC (srw_ss()) [isNewItem, itemFstRhs_def] THEN
METIS_TAC [NULL_EQ_NIL])



val b4DotEmpty = store_thm ("b4DotEmpty",
``!g.(EVERY NULL (MAP itemFstRhs (initItems g (rules g))))``,
Cases_on `g` THEN
SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [initItems_def, startSym_def, initProds2Items_def, iclosure] THEN
METIS_TAC [isNewItem_everyNullFstRhs, isNewItem_initProds2Items, isNewItem_iclosure])




val nullFstRhs_validStlItems = store_thm ("nullFstRhs_validStlItems",
``!l.(EVERY NULL (MAP itemFstRhs l)) ==> (validStlItems [] l)``,
Induct_on `l` THEN SRW_TAC [] [validStlItems] THEN
Cases_on `h` THEN Cases_on `p` THEN 
FULL_SIMP_TAC (srw_ss()) [NULL_EQ_NIL, itemFstRhs_def, validStlItems, stackSyms, isSuffix, IS_PREFIX_REFL])

val validItl_initProds2Items = store_thm ("validItl_initProds2Items", 
``!g l.validItl g (initProds2Items sym (rules g))``,
Cases_on `g` THEN SRW_TAC [] [rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [initProds2Items_def, validItl_def, rules_def] THEN
Cases_on `h` THEN
SRW_TAC [] [initProds2Items_def, validItl_def, rules_def] THEN
METIS_TAC [validItl_rules_cons])


val rderives_rules_cons = store_thm ("rderives_rules_cons", 
``!s1 s2 r e.rderives (G r s) s1 s2 ==> rderives (G (e::r) s) s1 s2``,
SRW_TAC [] [rderives_def, rules_def] THEN
METIS_TAC [rules_def])


val rtc_rderives_rules_cons = store_thm ("rtc_rderives_rules_cons", 
``!s1 s2.RTC (rderives (G r s)) s1 s2 ==> RTC (rderives (G (e::r) s)) s1 s2``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
METIS_TAC  [RTC_RULES, rderives_rules_cons])

val validItem_rules_cons = store_thm ("validItem_rules_cons",
``!r s l e.validItem (G r s) [] l ==> validItem (G (e::r) s) [] l``,
SRW_TAC [] [] THEN
Induct_on `l` THEN SRW_TAC [] [validItem] THEN 
Cases_on `p` THEN SRW_TAC [] [validItem, startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [validItem, startSym_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Q.EXISTS_TAC `sfx` THEN
METIS_TAC [rderives_rules_cons, rtc_rderives_rules_cons])



val validItem_initProds2Items = store_thm ("validItem_initProds2Items",
``!g.EVERY (validItem g []) (initProds2Items (startSym g) (rules g))``,
Cases_on `g` THEN 
SRW_TAC [] [startSym_def, validItem, rules_def] THEN
Induct_on `l` THEN SRW_TAC [] [initProds2Items_def] THEN
Cases_on `h` THEN SRW_TAC [] [initProds2Items_def, validItem, startSym_def] THEN
SRW_TAC [] [rderives_def] THENL[
Q.EXISTS_TAC `[]`  THEN
SRW_TAC [] [RTC_RULES] THEN
MAP_EVERY Q.EXISTS_TAC [`[]`, `[]`, `l'`, `s`] THEN
SRW_TAC [] [rules_def],
METIS_TAC [validItem_rules_cons, EVERY_MEM],
METIS_TAC [validItem_rules_cons, EVERY_MEM]])


val pfx_lem1 = prove(
``!r1 e h t pfx t' sfx.
(r1 ++ e :: h :: t = pfx ++ r1 ++ e :: t' ++ sfx) /\
IS_PREFIX (pfx ++ r1 ++ e::t') r1 /\
~(r1 = pfx ++ r1) ==>
IS_PREFIX (pfx ++ r1 ++ e::t') (r1 ++ [e])``,
Induct THEN SRW_TAC [][] THENL [
Cases_on `pfx` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX],

Cases_on `pfx` THEN SRW_TAC [][] THENL [
FULL_SIMP_TAC (srw_ss()) [],
FULL_SIMP_TAC (srw_ss()) [] THENL [
FULL_SIMP_TAC (srw_ss()) [],
SRW_TAC [][IS_PREFIX] THEN
Q.MATCH_ABBREV_TAC `IS_PREFIX BIG SMALL` THEN
`BIG = (t'' ++ [h]) ++ r1 ++ e::t'`
by (SRW_TAC [][Abbr`BIG`] THEN
METIS_TAC [APPEND_ASSOC, APPEND]) THEN
Q.UNABBREV_TAC `SMALL` THEN
POP_ASSUM SUBST1_TAC THEN
FIRST_X_ASSUM MATCH_MP_TAC THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
METIS_TAC [APPEND_ASSOC, APPEND]]]]);

val elem_eq = store_thm ("elem_eq", 
``!l1 l2 l3 e h.(l1++[e]++l2 = l1++[h]++l3) ==> (e=h)``,
Induct_on `l1` THEN SRW_TAC [] [] THEN
METIS_TAC [])

(*
val vpPropThm = store_thm ("vpPropThm",
``!m g.(auggr g st eof = SOME ag) ==>
(m=slr ag) ==> 
~(stateSym (FST (HD stl)) = NTS (startSym g)) ==> 
~(stateSym (FST (HD stl)) = TS eof) ==>
lr1_inv (ag, stl, (state s itl::csl), sl) ==>
((parse m (sl, stl, (state s itl::csl)) = SOME (sl',stl',csl'))) ==>
?N' h'.viablePfx ag (N',h') (stackSyms stl'++sl') (stackSyms stl')``,

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM, viablePfx, handleg, sforms_def, lr1_inv] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isSuffix h (stackSyms stl)` THEN FULL_SIMP_TAC (srw_ss()) [isSuffix] THEN
SRW_TAC [] [] THEN
Cases_on `MEM (item N (h,[])) itl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `getState m itl e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN 
Cases_on `v1` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[

(* 1 Last input symbol & reduction *)
`validItem ag (stackSyms stl) (item N (h,[]))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
`MEM r (rules ag)` by METIS_TAC [getstate_red, validStates_def, sgoto_exp] THEN
Cases_on `r` THEN
`(stackSyms stl' = stackSyms (pop stl (LENGTH l)) ++  [NTS s'])` by METIS_TAC [stackSyms_stl, ruleLhs_def, ruleRhs_def] THEN
`MEM (item s' (l,[])) itl` by METIS_TAC [getState_mem_itl, sgoto_exp, validStates_def] THEN
`completeItem (item s' (l,[]))` by METIS_TAC [completeItem] THEN
`(item s' (l,[])) = item N (h,[])` by  
METIS_TAC [completeItem, getState_reduce_followSet, itemLhs_def, sgoto_exp, validStates_def, EVERY_DEF] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN 
SRW_TAC [] [] THEN
`sl'=[e]` by METIS_TAC [red_sym] THEN
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl (rule N h)` THEN
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs (rule N h)))=[]` THEN
FULL_SIMP_TAC (srw_ss()) [stateItl_def, ruleLhs_def] THEN
`~(N=st)` by METIS_TAC [auggr_notStartRule] THEN
`~([NTS (startSym ag)] = pfx++[NTS N]++[e])` by METIS_TAC [list_neq, startSym_def, auggr_startSym] THEN
`?sf.RTC (rderives ag) [NTS (startSym ag)] sf /\ rderives ag sf (pfx++[NTS N]++[e])` by METIS_TAC [RTC_CASES2] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, ruleRhs_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms, stateSym_def] THEN
MAP_EVERY Q.EXISTS_TAC [`lhs'`, `rhs'`, `s1'`, `s2'`] THEN
SRW_TAC [] [] THENL[
METIS_TAC [c0],
`EVERY isTmnlSym [e]` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [list_isp, c0, IS_PREFIX_REFL]],

(* 2 reduction | more than input symbols *)
`MEM r (rules ag)` by METIS_TAC [getstate_red, validStates_def, sgoto_exp] THEN
Cases_on `r` THEN
`(stackSyms stl' = stackSyms (pop stl (LENGTH l)) ++  [NTS s'])` by METIS_TAC [stackSyms_stl, ruleLhs_def, ruleRhs_def] THEN
`MEM (item s' (l,[])) itl` by METIS_TAC [getState_mem_itl, sgoto_exp, validStates_def] THEN
`completeItem (item s' (l,[]))` by METIS_TAC [completeItem] THEN
(* (r=[])*)
`(item s' (l,[])) = item N (h,[])` by  
METIS_TAC [completeItem, getState_reduce_followSet, itemLhs_def, sgoto_exp, validStates_def, EVERY_DEF] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN 
SRW_TAC [] [] THEN
`sl'=e::h'::t` by METIS_TAC [red_sym] THEN
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl (rule N h)` THEN
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs (rule N h)))=[]` THEN
FULL_SIMP_TAC (srw_ss()) [stateItl_def, ruleLhs_def] THEN
`~(N=st)` by METIS_TAC [auggr_notStartRule] THEN
`~([NTS (startSym ag)] = pfx++[NTS N]++e::h'::t)` by METIS_TAC [list_neq, startSym_def, auggr_startSym] THEN
`?sf.RTC (rderives ag) [NTS (startSym ag)] sf /\ rderives ag sf (pfx++[NTS N]++e::h'::t)` by METIS_TAC [RTC_CASES2] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, ruleRhs_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms, stateSym_def]  THEN
MAP_EVERY Q.EXISTS_TAC [`lhs`, `rhs`, `s1`, `s2`] THEN
SRW_TAC [] [] THENL[
METIS_TAC [c0],
`EVERY isTmnlSym (e::h'::t)` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [list_isp, c0]],

(* 3 *)
Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`stl' = (s',Leaf (TM (tmnlSym e)))::stl` by METIS_TAC [] THEN
`sl'=h'::t` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
SRW_TAC [] [] THEN
METIS_TAC [shiftReduceGoto, validStates_def],

(* 4 *)
Cases_on `r` THEN
`validItl ag itl` by METIS_TAC [validStates_def] THEN
`!e'.MEM e' itl ==>
         (e' = item s' (l',[])) \/ ~ ?l r2 r1. e' = item l (r1,e::r2)` by METIS_TAC [shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [],

(* 5 *)
Cases_on `r` THEN
`validItl ag itl` by METIS_TAC [validStates_def] THEN
`!e'.MEM e' itl ==>
         (e' = item s' (l',[])) \/ ~ ?l r2 r1. e' = item l (r1,e::r2)` by METIS_TAC [shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [],

(* 6 *)
Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`stl' = (s',Leaf (TM (tmnlSym e)))::stl` by METIS_TAC [] THEN
`sl'=h'::t` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
SRW_TAC [] [] THEN
`validItem ag (REVERSE (MAP stateSym (MAP FST stl))) (item l (r1,e::r2))` by METIS_TAC [rgr_r9eq, EVERY_DEF, EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
Cases_on `s'` THEN
`s'' = e` by METIS_TAC [getstate_r2, sgoto_exp] THEN
SRW_TAC [] [] THEN
`REVERSE (MAP stateSym (MAP FST stl)) = pfx'++r1` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`isSuffix r1 (stackSyms stl)` by METIS_TAC [MEM ,validStlItems, validStlItems_append, rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [isSuffix, stackSyms] THEN
`(MAP stateSym (MAP FST stl)) = REVERSE (pfx' ++ r1)` by METIS_TAC [REVERSE_REVERSE] THEN
FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
SRW_TAC [] [stateSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `EVERY isTmnlSym (pfx' ++ r1 ++ e::r2 ++ sfx')` THEN SRW_TAC [] [] THEN

MAP_EVERY Q.EXISTS_TAC [`l`, `r1++[e]++r2`, `pfx'`, `e::h'::t`] THEN SRW_TAC [] [] THENL[



Cases_on `pfx++h=pfx'++r1` THEN SRW_TAC [] [] THENL[
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN

METIS_TAC [APPEND, APPEND_ASSOC],
FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN








METIS_TAC [APPEND_ASSOC, APPEND],

Cases_on `pfx++h=pfx'++r1` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [] THEN 
`REVERSE r1 ++ REVERSE pfx' = REVERSE h ++ REVERSE pfx` by METIS_TAC [REVERSE_APPEND, REVERSE_REVERSE] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN





Cases_on `l''` THEN SRW_TAC [] [] THEN Cases_on `sfx` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [APPEND, APPEND_ASSOC],
METIS_TAC [APPEND, APPEND_ASSOC, elem_eq]]]]




(* 7 *)

Cases_on `r` THEN
`validItl ag itl` by METIS_TAC [validStates_def] THEN
`!e'.MEM e' itl ==>
         (e' = item s' (l',[])) \/ ~ ?l r2 r1. e' = item l (r1,e::r2)` by METIS_TAC [shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [],

(* 8 *)
Cases_on `r` THEN
`validItl ag itl` by METIS_TAC [validStates_def] THEN
`!e'.MEM e' itl ==>
         (e' = item s' (l',[])) \/ ~ ?l r2 r1. e' = item l (r1,e::r2)` by METIS_TAC [shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [],

(* 9 *)





(* 10 *)
Cases_on `r` THEN
`validItl ag itl` by METIS_TAC [validStates_def] THEN
`!e'.MEM e' itl ==>
         (e' = item s' (l',[])) \/ ~ ?l r2 r1. e' = item l (r1,e::r2)` by METIS_TAC [shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [],

(* 11 *)
Cases_on `r` THEN
`validItl ag itl` by METIS_TAC [validStates_def] THEN
`!e'.MEM e' itl ==>
         (e' = item s' (l',[])) \/ ~ ?l r2 r1. e' = item l (r1,e::r2)` by METIS_TAC [shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [],


(* 12 *)



])
*)



val rdres1 = store_thm ("rdres1",
	``!lhs rhs g.MEM (rule lhs rhs) (rules g) ==> rderives g [NTS lhs] rhs``,
	SRW_TAC [] [rderives_def] THEN MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`,`rhs`,`lhs`]
	THEN SRW_TAC [] []);

val rderives_append = store_thm ("rderives_append", 
``!nt r.rderives g [NTS nt] r ==> !sfx.EVERY isTmnlSym sfx ==> 
!pfx.rderives g (pfx++[NTS nt]++sfx) (pfx++r++sfx)``,
SRW_TAC [] [rderives_def] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq] THEN SRW_TAC [] [] THEN
MAP_EVERY Q.EXISTS_TAC [`pfx`,`sfx`,`rhs`,`lhs`]  THEN
METIS_TAC [])

val rderives_same_append_left = store_thm ("rderives_same_append_left",
	``!g u v.rderives g u v ==> !x.rderives g (x++u) (x++v)``,
	SRW_TAC [] [rderives_def] THEN MAP_EVERY Q.EXISTS_TAC [`x++s1`,`s2`,`rhs`,`lhs`]
	THEN SRW_TAC [] [])

val rtc_rderives_same_append_left = store_thm ("rtc_rderives_same_append_left",
``!u v.RTC (rderives g) u v ==> !x. RTC (rderives g) (x++u) (x++v)``,
	HO_MATCH_MP_TAC relationTheory.RTC_INDUCT THEN 
	METIS_TAC [RTC_RULES,rderives_same_append_left])

val language_not_empty = store_thm ("language_not_empty",
``!g.gaw g (NTS (startSym g))  ==> ~(language g = {})``,
SRW_TAC [] [] THEN
Cases_on `g` THEN 
FULL_SIMP_TAC (srw_ss()) [startSym_def, gaw_def, EXTENSION] THEN 
SRW_TAC [] [language_def] THEN
METIS_TAC [startSym_def])

val inNonTerminals = store_thm ("inNonTerminals", 
``!l r g.MEM (rule l r) (rules g) ==> (!nt. (MEM (NTS nt) r) ==> (NTS nt) IN nonTerminals g)``,
SRW_TAC [] [] THEN
`?r1 r2.r = r1++[NTS nt]++r2` by METIS_TAC [rgr_r9eq] THEN
SRW_TAC [] [slemma1_4] THEN
METIS_TAC [slemma1_4])

val gawAllSyms = store_thm ("gawAllSyms",
``!e l.MEM e l ==> (l=SET_TO_LIST (allSyms g)) ==> 
(!nt. nt IN nonTerminals g ==>
     ?w. RTC (derives g) [nt] w /\ EVERY isTmnlSym w) ==>
gaw g e``,
Induct_on `l` THEN SRW_TAC [] [] THEN
Cases_on `e` THENL[
METIS_TAC [term_syms_gen_words, EVERY_DEF, isTmnlSym_def],

`FINITE (LIST_TO_SET (rules g))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`(NTS s) IN (nonTerminals g UNION terminals g)`  by METIS_TAC [SET_TO_LIST_IN_MEM, finiteAllSyms, allSyms_def, MEM] THEN
FULL_SIMP_TAC (srw_ss()) [allSyms_def, gaw_def] THEN
Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [terminals_def] THEN
SRW_TAC [] [] THEN
METIS_TAC [isTmnlSym_def, isNonTmnlSym_def, rt],

METIS_TAC [term_syms_gen_words, EVERY_DEF, isTmnlSym_def],

`FINITE (LIST_TO_SET (rules g))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`(NTS s) IN (nonTerminals g UNION terminals g)`  by METIS_TAC [SET_TO_LIST_IN_MEM, finiteAllSyms, allSyms_def, MEM] THEN
FULL_SIMP_TAC (srw_ss()) [allSyms_def, gaw_def] THEN
Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [terminals_def] THEN
SRW_TAC [] [] THEN
METIS_TAC [isTmnlSym_def, isNonTmnlSym_def, rt]])


val ruleRhsInAllSyms = store_thm ("ruleRhsInAllSyms",
``!lhs rhs.MEM (rule lhs rhs) (rules g) ==> (!e.MEM e rhs ==> e IN (allSyms g))``,
SRW_TAC [] [allSyms_def] THEN
Cases_on `e` THEN 
METIS_TAC [slemma1_4, slemma1_4Tmnls, rgr_r9eq])

val gaw_rhs = store_thm ("gaw_rhs",
``!lhs rhs.MEM (rule lhs rhs) (rules g) ==>
(!nt.nt IN nonTerminals g ==> ?w. RTC (derives g) [nt] w /\ EVERY isTmnlSym w) ==> 
EVERY (gaw g) rhs``,
Induct_on `rhs` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[

Cases_on `h` THEN 
METIS_TAC [term_syms_gen_words, EVERY_DEF, isTmnlSym_def, slemma1_4, APPEND, gaw_def],

`!e.MEM e (h::rhs) ==> e IN (allSyms g)` by METIS_TAC [ruleRhsInAllSyms] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`!e.MEM e rhs ==> e IN allSyms g` by METIS_TAC [] THEN
`FINITE (LIST_TO_SET (rules g))` by METIS_TAC [FINITE_LIST_TO_SET] THEN
`FINITE (allSyms g)` by METIS_TAC [finiteAllSyms] THEN
`!e. e IN allSyms g = MEM e (SET_TO_LIST (allSyms g))` by METIS_TAC [MEM_SET_TO_LIST] THEN
`!e. MEM e rhs ==> gaw g e` by METIS_TAC [gawAllSyms] THEN
METIS_TAC [EVERY_MEM]])



val gaw_rderives_single = store_thm ("gaw_rderives_single", 
``!a b.(gaw g) a ==> rderives g [a] b ==> 
(!nt.nt IN (nonTerminals g) ==> gaw g nt) ==> EVERY (gaw g) b``,
Induct_on `b` THEN SRW_TAC [] [gaw_def, rderives_def, lreseq] THENL[
Cases_on `h` THENL[  
METIS_TAC [RTC_RULES, isTmnlSym_def, EVERY_DEF],
`!nt.MEM (NTS nt) (NTS s::b) ==> (NTS nt) IN nonTerminals g` by METIS_TAC [inNonTerminals] THEN
FULL_SIMP_TAC (srw_ss()) []],
`gaw g (NTS lhs)` by METIS_TAC [gaw_def] THEN
`EVERY (gaw g) (h::b)` by METIS_TAC [gaw_rhs] THEN
FULL_SIMP_TAC (srw_ss()) []])

val gaw_rderives = store_thm ("gaw_rderives", 
``!a b.EVERY (gaw g) a ==> rderives g a b ==> 
(!nt.nt IN (nonTerminals g) ==> gaw g nt) ==> EVERY (gaw g) b``,
SRW_TAC [] [gaw_def, rderives_def] THEN
`(NTS lhs) IN nonTerminals g` by METIS_TAC [slemma1_4] THEN
FULL_SIMP_TAC (srw_ss()) [EVERY_APPEND, gaw_def] THEN
METIS_TAC [gaw_rderives_single, gaw_def, rdres1])


val gaw_rtc_rderives = store_thm("gaw_rtc_rderives",
``!a b.RTC (rderives g) a b ==> EVERY (gaw g) a ==> 
(!nt.nt IN (nonTerminals g) ==> gaw g nt) ==> EVERY (gaw g) b``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [] THEN
`EVERY (gaw g) a'` by METIS_TAC [gaw_rderives] THEN
METIS_TAC [])

val gaw_l1 = store_thm ("gaw_l1",
``!pfx sfx.RTC (rderives g) [NTS (startSym g)] (pfx ++ r1 ++ [NTS nt] ++ r2 ++ sfx) ==> 
(!nt.nt IN (nonTerminals g) ==> gaw g nt) ==>
?w.RTC (rderives g) (r2++sfx) w /\ EVERY isTmnlSym w``,
SRW_TAC [] [] THEN
`(NTS (startSym g)) IN (nonTerminals g)` by METIS_TAC [slemma1_4] THEN
`gaw g (NTS (startSym g))` by METIS_TAC [] THEN
`EVERY (gaw g) (pfx ++ r1 ++ [NTS nt] ++ r2 ++ sfx)` by METIS_TAC [EVERY_DEF, gaw_rtc_rderives] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`EVERY (gaw g) (r2++sfx)` by FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [EVERY_DEF, EVERY_APPEND, gaw_def, sub_result, derivesImpRderives, rderivesImpDerives])


val validItemNts = store_thm ("validItemNts",
``!g p r.validItem g p (item l (r1,NTS nt::r2)) ==> 
(!nt.nt IN (nonTerminals g) ==> gaw g nt) ==>
MEM (rule nt r) (rules g) ==> validItem g p (item nt ([],r))``,
SRW_TAC [] [validItem] THEN
`(NTS nt)  IN (nonTerminals ( g))` by METIS_TAC [slemma1_4] THEN
`~(language g = {})` by METIS_TAC [language_not_empty, slemma1_4] THEN
`gaw g (NTS nt)` by METIS_TAC [language_def, gaw_def, slemma1_4] THEN
FULL_SIMP_TAC (srw_ss()) [gaw_def] THEN
`RTC (rderives g) [NTS nt] w` by METIS_TAC [derivesImpRderives] THEN
Cases_on `([NTS nt] = w)` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
`?sf.RTC (rderives g) [NTS nt] sf /\ rderives g sf w` by METIS_TAC [RTC_CASES2] THEN

Cases_on `EVERY isTmnlSym (r2++sfx)` THENL[
Q.EXISTS_TAC `r2++sfx` THEN SRW_TAC [] [] THENL[
METIS_TAC [RTC_RULES_RIGHT1, RTC_RULES, rdres1, APPEND, APPEND_ASSOC],
`rderives g [NTS nt] r` by METIS_TAC [rdres1] THEN
METIS_TAC [rderives_append, APPEND_ASSOC]],

(* ~EVERY isTmnlSym (r2 ++ sfx) *)
`gaw g (NTS (startSym ( g))) ` by METIS_TAC [gaw_def, slemma1_4] THEN
`RTC (rderives ( g)) [NTS (startSym ( g))] (pfx ++ r1 ++ [NTS nt]++r2 ++ sfx)` by METIS_TAC [RTC_RULES_RIGHT1, APPEND, APPEND_ASSOC] THEN
`gaw ( g) (NTS (startSym g))` by METIS_TAC [] THEN

`?w.RTC (rderives g) (r2++sfx) w /\ EVERY isTmnlSym w` by 
METIS_TAC [APPEND_ASSOC, APPEND, gaw_l1, gaw_def] THEN

`RTC (rderives ( g)) (pfx++r1++[NTS nt]++r2++sfx) (pfx++r1++[NTS nt]++w')` by 
METIS_TAC [rtc_rderives_same_append_left, APPEND_ASSOC] THEN
 Cases_on `((pfx ++ r1 ++ [NTS nt] ++ r2 ++ sfx) = (pfx ++ r1 ++ [NTS nt] ++ w'))` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
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
METIS_TAC [RTC_RTC, rderives_append, rdres1, APPEND_ASSOC]]])


val getItems_mem = store_thm ("getItems_mem",
``!e l s'.MEM e (getItems l s') ==> ?r.(e=item s' ([],r)) /\ MEM (rule s' r) l``,
Induct_on `l` THEN SRW_TAC [] [getItems_def] THEN
Cases_on `h` THEN METIS_TAC [getItems_def, MEM])

val validItem_getItems = store_thm ("validItem_getItems",
``!g p s' t.validItem g p (item s (q,NTS s'::t)) ==> 
(!nt.nt IN (nonTerminals g) ==> gaw g nt) ==>
EVERY (validItem g p) (getItems (rules g) s')``,
Induct_on `rules g` THEN SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [getItems_def, validItem] THEN METIS_TAC [EVERY_DEF, getItems_def],
`!e.MEM e (getItems (rules g) s') ==> ?r.(e=item s' ([],r)) /\ MEM (rule s' r) (rules g)` by METIS_TAC [getItems_mem] THEN
SRW_TAC [] [EVERY_MEM] THEN
RES_TAC  THEN
SRW_TAC [] [] THEN
METIS_TAC [validItemNts]])



val validItem_iclosure1 = store_thm ("validItem_iclosure1", 
``!g itl l.EVERY (validItem g l) itl ==> 
(!nt.nt IN (nonTerminals g) ==> gaw g nt) ==>
EVERY (validItem g l) (iclosure1 g itl)``,
Induct_on `itl` THEN SRW_TAC [] [iclosure1_def, validItem] THEN
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1_def, validItem] THENL[
METIS_TAC [RTC_RULES],
Cases_on `h` THEN SRW_TAC [] [iclosure1_def] THENL[
SRW_TAC [] [validItem] THEN METIS_TAC [],
`validItem g (pfx++q) (item s (q,NTS s'::t))` by METIS_TAC [validItem, APPEND_ASSOC] THEN
METIS_TAC [validItem_getItems],
`validItem g (pfx++q) (item s (q,NTS s'::t))` by METIS_TAC [validItem, APPEND_ASSOC] THEN
METIS_TAC [validItem_getItems]]])



val validItem_delete = store_thm ("validItem_delete",
``!t h.EVERY (validItem g l) t ==> EVERY (validItem g l) (delete h t)``,
Induct_on `t` THEN SRW_TAC [] [delete_def, validItem])


val validItem_rmDupes = store_thm ("validItem_rmDupes", 
``!itl g l.EVERY (validItem g l)  itl ==> EVERY (validItem g l) (rmDupes itl)``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes, validItem] THEN
METIS_TAC [validItem_delete])


val validItem_iclosure = store_thm ("validItem_iclosure",
``!g itl l.EVERY (validItem g l)  itl ==> 
(!nt.nt IN (nonTerminals g) ==> gaw g nt) ==>
EVERY (validItem g l)  (iclosure g itl)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, validItem, LET_THM] THEN
`EVERY (validItem g l) (v2::v3)` by FULL_SIMP_TAC (srw_ss()) [] THEN
`EVERY (validItem g l) (rmDupes (v2::v3))` by METIS_TAC [validItem_rmDupes, validItem_iclosure1, APPEND, EVERY_APPEND] THEN
`EVERY (validItem g l) (iclosure1 g (rmDupes (v2::v3)))` 
by METIS_TAC [validItem_rmDupes, validItem_iclosure1, APPEND, EVERY_APPEND] THEN
`EVERY (validItem g l) (rmDupes (iclosure1 g (rmDupes (v2::v3))))` 
by METIS_TAC [validItem_rmDupes, validItem_iclosure1, APPEND, EVERY_APPEND] THEN
METIS_TAC [])



val fstRhsNil_delete = store_thm ("fstRhsNil_delete",
``!t h.EVERY NULL (MAP itemFstRhs t) ==> EVERY NULL (MAP itemFstRhs (delete h t))``,
Induct_on `t` THEN SRW_TAC [] [delete_def])


val fstRhsNil_rmDupes = store_thm ("fstRhsNil_rmDupes", 
``!itl.EVERY NULL (MAP itemFstRhs itl) ==> EVERY NULL (MAP itemFstRhs (rmDupes itl))``,
HO_MATCH_MP_TAC rmDupes_ind THEN SRW_TAC [] [rmDupes] THEN
METIS_TAC [APPEND, fstRhsNil_delete])

val every_map_itemFstRhs = store_thm ("every_map_itemFstRhs",
``!l.EVERY NULL (MAP itemFstRhs l) = (!e.MEM e l ==> (itemFstRhs e = []))``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e` THEN Cases_on `p` THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def, NULL_EQ_NIL])


val fstRhsNil_getItems = store_thm ("fstRhsNil_getItems",
``!l.EVERY NULL (MAP itemFstRhs (getItems l s'))``,
Induct_on `l` THEN SRW_TAC [] [getItems_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [getItems_def] THEN
Cases_on `s=s'` THEN FULL_SIMP_TAC (srw_ss()) [getItems_def, itemFstRhs_def])


val fstRhsNil_iclosure1 = store_thm ("fstRhsNil_iclosure1",
``!g l.EVERY NULL (MAP itemFstRhs l) ==> EVERY NULL (MAP itemFstRhs (iclosure1 g l))``,
Induct_on `l` THEN SRW_TAC [] [iclosure1_def] THEN
Cases_on `h` THEN Cases_on `p` THEN 
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def] THEN
`q=[]` by METIS_TAC [NULL_EQ_NIL] THEN
SRW_TAC [] [] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1_def, itemFstRhs_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [iclosure1_def, itemFstRhs_def] THEN
METIS_TAC [fstRhsNil_getItems])

val fstRhsNil_iclosure = store_thm ("fstRhsNil_iclosure",
``!g l.EVERY NULL (MAP itemFstRhs l) ==> MEM e (iclosure g l) ==> (itemFstRhs e=[])``,
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
METIS_TAC [NULL_EQ_NIL, NOT_CONS_NIL]])



val fstRhsNil_initProds2Items = store_thm ("fstRhsNil_initProds2Items",
``!l r1 r2. MEM (item l (r1,r2)) (initProds2Items s x) ==> (r1=[])``,
Induct_on `x` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [initProds2Items_def] THEN
Cases_on `h` THEN Cases_on `r2` THEN 
FULL_SIMP_TAC (srw_ss()) [initProds2Items_def] THEN
Cases_on `s=s'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [])




val initItems_fstRhs_nil = store_thm ("initItems_fstRhs_nil", 
``!l r1 r2.MEM (item l (r1,r2)) (initItems ag (rules ag)) ==> (r1=[])``,
SRW_TAC [] [initItems_def, initProds2Items_def] THEN
`!l r1 r2.MEM (item l (r1,r2)) (initProds2Items (startSym ag) (rules ag)) ==> (r1 = [])` by 
METIS_TAC [fstRhsNil_initProds2Items] THEN
`EVERY NULL (MAP itemFstRhs (initProds2Items (startSym ag) (rules ag)))` by (FULL_SIMP_TAC (srw_ss()) [every_map_itemFstRhs] THEN
SRW_TAC [] [] THEN Cases_on `e` THEN Cases_on `p` THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def] THEN METIS_TAC []) THEN
`itemFstRhs (item l (r1,r2)) = []` by METIS_TAC [fstRhsNil_iclosure] THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def])


val completeItem_sndRhs_nil = store_thm ("completeItem_sndRhs_nil",
``!l r1 r2.MEM (item l (r1,r2)) (FILTER completeItem x) ==> (r2=[]) ``,
Induct_on `x` THEN SRW_TAC [] [completeItem] THENL[
Cases_on `r2` THEN FULL_SIMP_TAC (srw_ss()) [completeItem],
METIS_TAC [],
METIS_TAC []])


val initProds_compItem_nil = store_thm ("initProds_compItem_nil", 
``!l r1 r2.MEM (item l (r1, r2)) (FILTER completeItem (initItems ag (rules ag))) ==> ((r1=[]) /\ (r2=[]))``,
SRW_TAC [] [] THENL[
METIS_TAC [MEM_FILTER, initItems_fstRhs_nil],
METIS_TAC [completeItem_sndRhs_nil]])

val rderives_has_tmnl = store_thm ("rderives_has_tmnl",
``!x x'.rderives g x x' ==> MEM (TS h) x ==> MEM (TS h) x'``,
SRW_TAC [] [rderives_def] THEN
FULL_SIMP_TAC (srw_ss()) [])


val rtc_rderives_has_tmnl = store_thm ("rtc_rderives_has_tmnl",
``!x y.RTC (rderives g) x y ==> MEM (TS h) x ==> MEM (TS h) y``,
HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [] [] THEN
METIS_TAC [rderives_has_tmnl])


val auggr_not_rd_nts = store_thm ("auggr_not_rd_nts",
``!g st eof N.(auggr g st eof = SOME ag) ==> ~(N=st) ==> 
~ (RTC (rderives ag) [NTS (startSym ag)] [NTS N])``,
SRW_TAC [] [Once RTC_CASES1] THENL[
METIS_TAC [auggr_startSym],
FULL_SIMP_TAC (srw_ss()) [auggr_def, LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g)` THEN 
Cases_on `~(TS eof IN terminalsML g)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def, startSym_def] THEN
Cases_on `~rderives (G (rule st [NTS (startSym g); TS eof]::rules g) st) [NTS st] u` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq, rules_def] THENL[
`MEM (TS eof) [NTS (startSym g); TS eof]` by SRW_TAC [] [] THEN
Cases_on `RTC (rderives (G (rule st [NTS (startSym g); TS eof]::rules g) st))
       [NTS (startSym g); TS eof] [NTS N]` THENL[
`MEM (TS eof) [NTS N]` by METIS_TAC [rtc_rderives_has_tmnl] THEN
FULL_SIMP_TAC (srw_ss()) [],
FULL_SIMP_TAC (srw_ss()) []],
METIS_TAC [slemma1_4, nonTerminalsEq]]])


val auggr_eq_start_rule = store_thm ("auggr_eq_start_rule",
``!g st eof N r1 h.(auggr g st eof = SOME ag) ==> 
(MEM (rule st (r1 ++ [h])) (rules ag)) ==> 
((r1=[NTS (startSym g)]) /\ (h=TS eof))``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [auggr_def, LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g)` THEN 
Cases_on `~(TS eof IN terminalsML g)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THENL[
Cases_on `r1` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
Cases_on `t` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def],
METIS_TAC [slemma1_4, nonTerminalsEq],
Cases_on `r1` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
Cases_on `t` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def],
METIS_TAC [slemma1_4, nonTerminalsEq]])



val stateSym_stl_len1 = store_thm ("stateSym_stl_len1",
``!stl.(MAP FST (MAP FST stl) = [NTS nt]) ==>
(FST (FST (HD stl)) = NTS nt)``,
Induct_on `stl` THEN SRW_TAC [] [])

val auggrStartRule = store_thm ("auggrStartRule", 
``!g st eof h.(auggr g st eof = SOME ag) 
  ==> MEM (rule (startSym ag) h) (rules ag)
  ==> (h=[NTS (startSym g);TS eof])``,
SRW_TAC [] [auggr_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def] THEN
METIS_TAC [slemma1_4, nonTerminalsEq])


val auggrNotStInRtcRderives = store_thm ("auggrNotStInRtcRderives",
``!u v.RTC (rderives ag) u v ==> (u=[NTS (startSym g); TS eof]) ==> 
(auggr g st eof = SOME ag) ==> ~(MEM (NTS (startSym ag)) v)``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [auggr_def, LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g) /\ ~(TS eof IN terminalsML g)` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [nonTerminalsEq, slemma1_4, startSym_def],
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def, rules_def] THEN
METIS_TAC [slemma1_4, nonTerminalsEq, startSym_def, rgr_r9eq]])


val auggrStRtcDerivesSt = store_thm ("auggrStRtcDerivesSt",
``!u v.RTC (rderives ag) u v ==> (u=[NTS (startSym ag)]) ==> 
  (auggr g st eof = SOME ag) ==> ((v=[NTS (startSym ag)]) \/ ~(MEM (NTS (startSym ag)) v))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN
SRW_TAC [] [] THEN
`u'=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [auggrNotStInRtcRderives])


val auggrRtcRderivesPfxSfxNil = store_thm ("auggrRtcRderivesPfxSfxNil",
``!e pfx sfx.(auggr g st eof = SOME ag) ==>
RTC (rderives ag) [NTS (startSym ag)] (pfx++[NTS (startSym ag)]++sfx) ==> 
(pfx=[]) /\ (sfx=[])``,
SRW_TAC [] [] THEN
`(pfx ++ [NTS (startSym ag)] ++ sfx = [NTS (startSym ag)]) \/ 
~(MEM (NTS (startSym ag)) (pfx ++ [NTS (startSym ag)] ++ sfx))` by METIS_TAC [auggrStRtcDerivesSt] THEN
FULL_SIMP_TAC (srw_ss()) [lreseq])


val lastElemEq = store_thm ("lastElemEq",
``!l l' e e'.(l++[e] = l'++[e']) ==> (e=e')``,
Induct_on `l` THEN Induct_on `l'` THEN SRW_TAC [] [])

val lastListBdown = store_thm ("lastListBdown",
``!l e.~(l=[]) ==> (LAST l = e) ==> ?pfx.(l=pfx++[e])``,
Induct_on `l` THEN SRW_TAC [] [LAST_DEF] THEN
METIS_TAC [APPEND])


val rtcRderivesLastTmnl = store_thm ("rtcRderivesLastTmnl",
``!u v.RTC (rderives g) u v ==> (u=(pfx++[TS ts])) ==> ?pfx'.(v=pfx'++[TS ts])``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
`[NTS lhs] = [TS ts]` by METIS_TAC [lastElemEq] THEN
FULL_SIMP_TAC (srw_ss()) [],

`LAST (s1 ++ [NTS lhs] ++ h::t) = TS ts` by METIS_TAC [last_elem] THEN
`LAST (h::t) = TS ts` by METIS_TAC [last_append, NOT_CONS_NIL] THEN
`LAST v' = TS ts` by METIS_TAC [last_append, NOT_CONS_NIL] THEN
`~(v'=[])` by SRW_TAC [] [] THEN
METIS_TAC [lastListBdown]])

val lastEof = store_thm ("lastEof",
``!g st eof.(auggr g st eof = SOME ag) ==> 
  !l.RTC (rderives ag) [NTS (startSym ag)] (pfx++[NTS N]++sfx) ==> ~(N=startSym ag)
  ==> ?pfx'.(sfx = pfx'++[TS eof])``,
SRW_TAC [] [auggr_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [startSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [Once RTC_CASES1, lreseq, rderives_def] THEN
FULL_SIMP_TAC (srw_ss()) [rules_def] THENL[
SRW_TAC [] [] THEN
`?pfx'.(pfx ++ [NTS N] ++ sfx)=pfx'++[TS eof]` by METIS_TAC [rtcRderivesLastTmnl, APPEND] THEN
Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
`NTS N = TS eof` by METIS_TAC [last_elem] THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC [lastListBdown, NOT_CONS_NIL, last_append, last_elem]],
METIS_TAC [slemma1_4, nonTerminalsEq]])

val listEq = store_thm ("listEq",
``!l l1.(l = l1 ++ l) =  (l1=[])``,
SRW_TAC [] [EQ_IMP_THM] THEN
Cases_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH t = LENGTH (t' ++ h::t)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
DECIDE_TAC)

val auggrRtcRderivesStartRule = store_thm ("auggrRtcRderivesStartRule",
``!u v.RTC (rderives ag) u v ==> (u=[NTS (startSym ag)])  ==> 
      (auggr g st eof = SOME ag) ==>  
     ~(v=[NTS (startSym ag)]) ==> RTC (rderives ag)  [NTS (startSym g); TS eof] v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`!h.MEM (rule (startSym ag) h) (rules ag) ==>
         (h = [NTS (startSym g); TS eof])` by METIS_TAC [auggrStartRule] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN
SRW_TAC [] [] THEN
RES_TAC THEN
FULL_SIMP_TAC (srw_ss()) [])

val auggrDerivesNotNil = store_thm ("auggrDerivesNotNil",
``!g st eof.
            (auggr g st eof = SOME ag) ==>
            !l.
              RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
              ~(N = startSym ag) ==> ~(sfx=[])``,
SRW_TAC [] [] THEN
`?pfx'. sfx = pfx' ++ [TS eof]` by METIS_TAC [lastEof] THEN
FULL_SIMP_TAC (srw_ss()) [])

val mem_reduce = store_thm ("mem_reduce",
``!e itl N.e IN followSet ag (NTS N) ==> MEM (item N (h,[])) itl ==> isTmnlSym e ==>
    MEM (rule N h) (reduce ag itl (sym2Str e))``,
Induct_on `itl` THEN SRW_TAC [] [] THEN
SRW_TAC [] [reduce_def] THEN
Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [sym2Str_def, isTmnlSym_def, followSetEq] THEN
`reduce ag (h'::itl) s = reduce ag [h'] s ++ reduce ag itl s` by METIS_TAC [reduce_append, APPEND] THEN
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [] [] THEN
RES_TAC THEN
METIS_TAC [sym2Str_def])

val slrCompItemsEq = store_thm ("slrCompItemsEq",
``!m ag N h itl.(SOME m = slr ag) ==> MEM (item N (h,[])) itl 
                ==> (e IN followSet ag (NTS N)) ==> isTmnlSym e ==>
                (!j.
                MEM j itl /\ completeItem j /\
                e IN followSet ag (NTS (itemLhs j)) ==>
                (j = item N (h,[])))``,
SRW_TAC [] [slr_def, LET_THM] THEN
Cases_on `j=item N (h,[])` THEN
SRW_TAC [] [] THEN
`MEM (rule N h) (reduce ag itl (sym2Str e))` by METIS_TAC [mem_reduce] THEN
Cases_on `j` THEN 
Cases_on `p` THEN Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [completeItem, itemLhs_def] THEN
`MEM (rule s q) (reduce ag itl (sym2Str e))` by METIS_TAC [mem_reduce] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`itl`, `e`] ASSUME_TAC) THEN
Cases_on `sgoto ag itl e` THEN Cases_on `reduce ag itl (sym2Str e)` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN 
REPEAT 
(FULL_SIMP_TAC (srw_ss()) [] THEN 
Cases_on `t` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`rule N h = rule s q` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) []) THEN
REPEAT 
(Cases_on `t'` THEN
FULL_SIMP_TAC (srw_ss()) []))


val followSetMem = store_thm ("followSetMem", 
``!u v.RTC (derives g) u v ==> (u=[NTS N]) ==> (v=(pfx++[NTS N']++[TS ts]++sfx)) 
    ==> ((TS ts) IN followSet g (NTS N'))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THENL[

`LENGTH [NTS N] = LENGTH (pfx ++ [NTS N'] ++ [TS ts] ++ sfx)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (arith_ss) [],

FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq, followSet_def] THEN
Q.EXISTS_TAC `u'` THEN
SRW_TAC [] [] THENL[
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN
METIS_TAC [],

METIS_TAC []]])

val auggrExistsMemInit = store_thm ("auggrExistsMemInit",
``(auggr g s eof = SOME ag) ==> 
      MEM (item (startSym ag) ([],[NTS (startSym g);TS eof])) (initProds2Items (startSym ag) (rules ag))``,
SRW_TAC [] [auggr_def, LET_THM, startSym_def, rules_def, initProds2Items_def] THEN
SRW_TAC [] [startSym_def, rules_def, initProds2Items_def])

val rderivesHdTmnl = store_thm ("rderivesHdTmnl",
``rderives g u u' ==> isTmnlSym (HD u) ==> (HD u' = HD u)``,
SRW_TAC [] [rderives_def] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def])

val derivesHdTmnl = store_thm ("derivesHdTmnl",
``derives g u u' ==> isTmnlSym (HD u) ==> (HD u' = HD u)``,
SRW_TAC [] [derives_def] THEN
Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def])

val iclosure1_append = store_thm ("iclosure1_append",
``!l1 l2.iclosure1 g (l1 ++ l2) = iclosure1 g l1 ++ iclosure1 g l2``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [iclosure1_def] THEN
Cases_on `h'` THEN Cases_on `p` THEN Cases_on `r` 
THENL[
      SRW_TAC [] [iclosure1_def],

      Cases_on `h'` THEN SRW_TAC [] [iclosure1_def] THEN
      METIS_TAC [APPEND, APPEND_ASSOC, APPEND_NIL]
      ]
)

val stl_mem  = store_thm ("stl_mem",
``!s.FINITE s ==> (s=set l) ==> MEM e (SET_TO_LIST (set l)) ==> MEM e l``,
HO_MATCH_MP_TAC FINITE_INDUCT THEN SRW_TAC [] [])

val getItems_append = store_thm ("getItems_append",
``!l1 l2.getItems (l1++l2) N  = getItems l1 N ++ getItems l2 N``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [getItems_def] THEN
Cases_on `h'` THEN SRW_TAC [] [getItems_def])


val iclosureNt = store_thm ("iclosureNt",
``!ag l.MEM (item lhs ([],NTS N::r2)) (iclosure ag l) ==> 
 !rhs.MEM (rule N rhs) (rules ag) ==>
MEM (item N ([],rhs)) (iclosure ag l)``,
HO_MATCH_MP_TAC iclosure_ind THEN SRW_TAC [] [iclosure, LET_THM] THEN
`(item lhs ([],NTS N::r2)) IN set (rmDupes (iclosure1 ag (rmDupes (v2::v3))))` by 
FULL_SIMP_TAC (srw_ss()) [] THEN
`(item lhs ([],NTS N::r2)) IN set (rmDupes (v2::v3))` by METIS_TAC [] THEN
`MEM (item lhs ([],NTS N::r2)) (SET_TO_LIST (set (rmDupes (v2::v3))))` by 
METIS_TAC [FINITE_LIST_TO_SET, MEM_SET_TO_LIST, SET_TO_LIST_IN_MEM] THEN
`MEM (item lhs ([],NTS N::r2)) (rmDupes (v2::v3))` by METIS_TAC [stl_mem, FINITE_LIST_TO_SET] THEN
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, iclosure1_append] THEN
`rmDupes (iclosure1 ag (rmDupes (v2::v3))) = rmDupes (iclosure1 ag (r1'' ++ [item lhs ([],NTS N::r2)] ++ r2'''))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [iclosure1_append, iclosure1_def] THEN
`getItems (rules ag) N  = getItems (r1 ++ [rule N rhs] ++ r2') N` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [getItems_append, getItems_def] THEN
METIS_TAC [APPEND_ASSOC, rgr_r9eq, APPEND, rmd_r2])


val initClosure = store_thm ("initClosure",
``!l lhs r2.MEM (item lhs ([],NTS N::r2)) l ==> (l=(initItems ag (rules ag))) ==> 
 !rhs.MEM (rule N rhs) (rules ag) ==>
MEM (item N ([],rhs)) l``,
SRW_TAC [] [initItems_def] THEN
FULL_SIMP_TAC (srw_ss()) [initItems_def] THEN
METIS_TAC [iclosureNt])


val rtcImpInClosure = store_thm ("rtcImpInClosure",
``!u u'.RTC (rderives ag) u u' ==> (u=[NTS (startSym ag)]) ==> !v.derives ag u' v ==>
       (auggr g s eof = SOME ag) ==> (LENGTH v < LENGTH u' ==> isTmnlSym (HD u')) ==>
        (?lhs r2.
      MEM (item lhs ([],HD v::r2))
        (initItems ag (rules ag)))``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN SRW_TAC [] [RTC_RULES] THENL[

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
FULL_SIMP_TAC (srw_ss()) [] THENL[
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
`derives ag (NTS lhs'::(t ++ [NTS lhs] ++ s2))  ((TS s''::t')++(t ++ [NTS lhs] ++ s2))` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`LENGTH (s1 ++ rhs ++ s2') = LENGTH (TS s''::(t' ++ t ++ [NTS lhs] ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t' + LENGTH t + 1 + LENGTH s2) < SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`(TS s''::(t' ++ t ++ [NTS lhs] ++ s2))`] MP_TAC) THEN
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
`derives ag (NTS lhs'::(t ++ [NTS lhs] ++ s2)) (TS s''::t''++(t ++ [NTS lhs] ++ s2))` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
`LENGTH (s1 ++ rhs ++ s2') = LENGTH (TS s''::(t'' ++ t ++ [NTS lhs] ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~( SUC (LENGTH t'' + LENGTH t + 1 + LENGTH s2) < SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`TS s''::(t'' ++ t ++ [NTS lhs] ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
METIS_TAC []],

`~(LENGTH v < LENGTH u'')` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `rhs` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
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

`derives ag (NTS lhs::s2) ((NTS s'::t)++s2)` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS s'::(t ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t + LENGTH s2) < 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS s'::(t ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
METIS_TAC [],

`derives ag (NTS lhs::s2) ((NTS s'::t)++s2)` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS s'::(t ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t + LENGTH s2) < 1 + LENGTH s2)` by DECIDE_TAC THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS s'::(t ++ s2)`] MP_TAC) THEN
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

`derives ag  (NTS s'::(t ++ [NTS lhs] ++ s2)) (NTS s'::(t++s2))` by METIS_TAC [res1, derives_same_append_right, derives_same_append_left, APPEND_NIL, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS s'::(t' ++ [NTS lhs'] ++ s2')`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS s'::(t' ++ [NTS lhs'] ++ s2'))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t' + 1 + LENGTH s2') <
             SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC [],

`MEM (NTS lhs')  (t ++ s2)` by METIS_TAC [MEM_APPEND, rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[

`?pfx sfx.t=pfx++[NTS lhs']++sfx` by METIS_TAC [rgr_r9eq] THEN
SRW_TAC [] [] THEN
`derives ag (NTS s'::(pfx ++ [NTS lhs'] ++ sfx ++ [NTS lhs] ++ s2)) (NTS s'::(pfx ++ h::t'' ++ sfx)++ [NTS lhs] ++ s2)` by 
METIS_TAC [res1, derives_same_append_left, derives_same_append_right, APPEND, APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [` NTS s'::(pfx ++ h::t'' ++ sfx ++ [NTS lhs] ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS s'::(pfx ++ h::t'' ++ sfx ++ [NTS lhs] ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
` ~(SUC
 (LENGTH pfx + SUC (LENGTH t'') + LENGTH sfx + 1 +
                LENGTH s2) <
             SUC (LENGTH pfx + 1 + LENGTH sfx) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC [],

`?pfx sfx.s2=pfx++[NTS lhs']++sfx` by METIS_TAC [rgr_r9eq] THEN
SRW_TAC [] [] THEN
`derives ag (NTS s'::(t ++ [NTS lhs] ++ (pfx ++ [NTS lhs'] ++ sfx))) (NTS s'::(t ++ [NTS lhs] ++ (pfx ++ h::t'' ++ sfx)))` by 
METIS_TAC [res1, derives_same_append_left, derives_same_append_right, APPEND, APPEND_ASSOC] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS s'::(t ++ [NTS lhs] ++ pfx ++ h::t'' ++ sfx)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2) = LENGTH (NTS s'::(t ++ [NTS lhs] ++ pfx ++ h::t'' ++ sfx))` by METIS_TAC [] THEN
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


`derives ag (NTS s'::(t ++ [NTS lhs] ++ s2)) (NTS s'::(t ++ (h'::t') ++ s2))` by METIS_TAC [res1, derives_same_append_right, derives_same_append_left, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS s'::(t ++ h'::t' ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS s'::(t ++ h'::t' ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t + SUC (LENGTH t') + LENGTH s2) <
             SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC [],

`derives ag (NTS s'::(t ++ [NTS lhs] ++ s2)) (NTS s'::(t ++ (h'::t') ++ s2))` by METIS_TAC [res1, derives_same_append_right, derives_same_append_left, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`NTS s'::(t ++ h'::t' ++ s2)`] MP_TAC) THEN
SRW_TAC [] [] THEN
`LENGTH (s1 ++ rhs ++ s2'') = LENGTH (NTS s'::(t ++ h'::t' ++ s2))` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(SUC (LENGTH t + SUC (LENGTH t') + LENGTH s2) <
             SUC (LENGTH t) + 1 + LENGTH s2)` by DECIDE_TAC THEN
METIS_TAC []]]]]]])


val rdImpDg = store_thm ("rdImpDg",
``!u v.rderives g u v ==> derives g u v``,
SRW_TAC [] [derives_def, rderives_def] THEN
METIS_TAC [])

val rtcRdImpDg = store_thm ("rtcRdImpDg",
``!u v.RTC (rderives g) u v ==> RTC (derives g) u v``,
HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN
METIS_TAC [RTC_RULES, rdImpDg])

val auggrLastEof = store_thm ("auggrLastEof",
``(auggr g st eof = SOME ag) ==> 
RTC (rderives ag) [NTS (startSym ag)] (h::pfx++[NTS N]++sfx) ==> ?pfx'. sfx = pfx' ++ [TS eof]``,
SRW_TAC [] [Once RTC_CASES2, derives_def] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `lhs=(startSym ag)` THEN SRW_TAC [] []
THENL[

 `(s1=[]) /\ (s2=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
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
 
 `?pfx'.s2=pfx'++[TS eof]` by METIS_TAC [lastEof] THEN
 Cases_on `sfx` THEN SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [] 
 THENL[
 `TS eof = NTS N` by METIS_TAC [last_elem, APPEND] THEN
 FULL_SIMP_TAC (srw_ss()) [],

 `LAST [TS eof] = LAST (h'::t)` by METIS_TAC [last_append, NOT_CONS_NIL, APPEND_ASSOC, APPEND] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 METIS_TAC [APPEND_NIL, APPEND_FRONT_LAST, NOT_CONS_NIL]
 ]])


val initItemsHdNt = store_thm ("initItemsHdNt",
	       ``!u v.RTC (rderives ag) u v ==> (u=[NTS (startSym ag)]) ==> !N rst.(v=(NTS N::rst)) ==>
   !rhs.MEM (rule N rhs) (rules ag) ==> (auggr g st eof = SOME ag) ==>
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
      METIS_TAC [initClosure]])


val len1 = store_thm ("len1",
``!l1 l1' rst rst'.(l1++rst = l1'++rst') ==> (LENGTH l1 = LENGTH l1') ==> (l1 = l1')``,
Induct_on `l1` THEN Induct_on `l1'` THEN SRW_TAC [] [] THEN
METIS_TAC [])
		

val len2 = store_thm ("len2",
``!l1 l1' rst rst'.(l1++rst = l1'++rst') ==> (LENGTH l1' < LENGTH l1) ==> ?pfx sfx.(l1=pfx++sfx) /\ (l1'=pfx)``,		
Induct_on `l1` THEN Induct_on `l1'` THEN SRW_TAC [] [] THEN
METIS_TAC [])

val len3 = store_thm ("len3",
``!l1 l1' rst rst'.(l1++rst = l1'++rst') ==> (LENGTH l1' > LENGTH l1) ==> ?pfx sfx.(l1'=pfx++sfx) /\ (l1=pfx)``,		
Induct_on `l1` THEN Induct_on `l1'` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (arith_ss) [] THEN
`LENGTH l1' > LENGTH l1` by FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [])


val listStartSame = store_thm ("listStartSame",
			       ``!l l1 l1'.((l++l1) = (l++l1')) ==> (l1=l1')``,
Induct_on `l` THEN SRW_TAC [] [])

val listCompLens = store_thm ("listCompLens",
``!t t' s2 N rst.(t' ++ s2 = t ++ [NTS N] ++ rst) ==> 
(t=t') \/ (?pfx sfx.(t'=t++[NTS N]++pfx) /\ (rst=pfx++sfx)) \/ (?pfx sfx.(t=pfx++sfx) /\ (t'=pfx))``,
SRW_TAC [] [] THEN
Cases_on `LENGTH  t = LENGTH t'`
THENL[
      METIS_TAC [len1, APPEND, APPEND_ASSOC],

      `(LENGTH t < LENGTH t') \/ (LENGTH t > LENGTH t')` by FULL_SIMP_TAC (arith_ss) []
      THENL[
	    `?pfx sfx.(t'=pfx++sfx) /\ (t=pfx)` by METIS_TAC [len2, APPEND, APPEND_ASSOC] THEN
	    SRW_TAC [] [] THEN
	    Cases_on `pfx` THEN SRW_TAC [] [] THEN
	    Cases_on `sfx` THEN FULL_SIMP_TAC (srw_ss()) [] 
	    THENL[
		  METIS_TAC [],
	    
		  `h'::t' ++ s2 = [NTS N] ++ rst` by METIS_TAC [listStartSame, APPEND, APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC [APPEND, APPEND_ASSOC]
		  ],


	    `?pfx sfx.(t=pfx++sfx) /\ (t'=pfx)` by METIS_TAC [len3, APPEND, APPEND_ASSOC] THEN
	    SRW_TAC [] []
	    ]])

	    


val initItemsNtInBtwn = store_thm ("initItemsNtInBtwn",
``!u v.RTC (rderives ag) u v ==> (u=[NTS (startSym ag)]) ==> !sl N rst.(v=sl++[NTS N]++rst) ==> ~(sl=[]) ==> EVERY isTmnlSym sl ==> 
(auggr g st eof = SOME ag)
 ==> ?lhs rhs.MEM (item lhs ([],HD (sl)::rhs)) (initItems ag (rules ag))``,
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
      `(t'=t) \/ (?pfx sfx.(t'=t++[NTS N]++pfx) /\ (rst=pfx++sfx)) \/ (?pfx sfx.(t=pfx++sfx) /\ (t'=pfx))` by METIS_TAC [listCompLens]
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
      `(t'=t) \/ (?pfx sfx.(t'=t++[NTS N]++pfx) /\ (rst=pfx++sfx)) \/ (?pfx sfx.(t=pfx++sfx) /\ (t'=pfx))` by METIS_TAC [listCompLens, APPEND, APPEND_ASSOC, APPEND_NIL]
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
      ])


val auggrStRtcRderivesNotNil = store_thm ("auggrStRtcRderivesNotNil",
``(auggr g st eof = SOME ag) ==> ~RTC (rderives ag) [NTS (startSym ag)] []``,
SRW_TAC [] [Once RTC_CASES1] THEN
Cases_on `~rderives ag [NTS (startSym ag)] u` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN
SRW_TAC [] [] THEN
`u=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
`MEM (TS eof)  [NTS (startSym g); TS eof]` by SRW_TAC [] [] THEN
Cases_on `RTC (rderives ag) [NTS (startSym g); TS eof] []` THEN SRW_TAC [] [] THEN
METIS_TAC [rgr_r9eq, MEM, MEM_APPEND, APPEND, rtc_rderives_has_tmnl])

val auggrRtcRderivesSt = store_thm ("auggrRtcRderivesSt",
``(auggr g st eof = SOME ag) ==> RTC (rderives ag) [NTS (startSym ag)] [NTS lhs] ==> (lhs=startSym ag)``,
SRW_TAC [] [Once RTC_CASES1] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def, lreseq] THEN
SRW_TAC [] [] THEN
`u=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
`MEM (TS eof)  [NTS (startSym g); TS eof]` by SRW_TAC [] [] THEN
`MEM (TS eof) [NTS lhs]` by METIS_TAC [rgr_r9eq, MEM, MEM_APPEND, APPEND, rtc_rderives_has_tmnl] THEN
FULL_SIMP_TAC (srw_ss()) [])

(*

lr1_inv holds initially

(*
1. !items in a state the symbol b4 the dot is the symbol on top of the stack at that time.
2. if an item belongs at the top of the stack then 
 - either that item is a completely new item (i.e.no stuff b4 dot)
 - or 

if end of a handle is at the top of the stack then for all the states ecompassed by the length of the handle, then
for each of the item at the top,
 - either that item is a completely new item (i.e.no stuff b4 dot)
 - or an item having a half read handle is present in the states upto length l
*)

*)

val lr1_inv_init = store_thm ("lr1_inv_init",
``!m g.(auggr g st eof = SOME ag) ==>
(!nt.nt IN (nonTerminals ag) ==> gaw ag nt) ==>
(SOME m=slr ag) ==> 
(sl IN language ag) ==>
lr1_inv (ag, [], [((NTS st), initItems ag (rules ag))], sl)``,

SRW_TAC [] [] THEN
`EVERY (validItem ag []) (initItems ag (rules ag))` by
(`gaw ag (NTS (startSym ag))` by METIS_TAC [slemma1_4] THEN
`~(language ag = {})` by METIS_TAC [language_not_empty] THEN
SRW_TAC [] [initItems_def] THEN
`EVERY (validItem ag []) (initProds2Items (startSym ag) (rules ag))` by METIS_TAC [validItem_initProds2Items] THEN
Cases_on `g` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`gaw ag (NTS (startSym ag))` by METIS_TAC [slemma1_4] THEN
METIS_TAC [validItem_iclosure, validItem_initProds2Items, stackSyms]) THEN


SRW_TAC [] [lr1_inv, stackSyms] 
THENL[
(* 3 subgoals *)

      (* 1 validStlItems [] (initItems ag (rules ag)) *)
      METIS_TAC [b4DotEmpty, nullFstRhs_validStlItems],


      (* 2 validStates ag [state (NTS st) (initItems ag (rules ag))] *)
      FULL_SIMP_TAC (srw_ss()) [validStates_def, initItems_def] THEN
      METIS_TAC [validItl_initProds2Items, validItl_iclosure],


      (* 3 handle *)
      FULL_SIMP_TAC (srw_ss()) [IS_PREFIX, handleg, isSuffix] THEN
      FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION] THEN 
      `?u.
      RTC (rderives ag) [NTS (startSym ag)] u /\ rderives ag u sl` by 
      METIS_TAC [RTC_CASES2, EVERY_DEF, EVERY_APPEND, sym_r1b, isTmnlSym_def, isNonTmnlSym_def, APPEND, derivesImpRderives] THEN
      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [] [] THEN
      MAP_EVERY Q.EXISTS_TAC [`s1`,`rhs`,`lhs`,`s2`] THEN 
      SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [listEq] THEN
      SRW_TAC [] [] 
      THENL[
	    (*6 subgoals*)

	    FULL_SIMP_TAC (srw_ss()) [IS_PREFIX, handleg, isSuffix] THEN
	    SRW_TAC [] [followSet_def] THEN
	    `((NTS lhs::s2) = [NTS (startSym ag)]) \/ ~MEM (NTS (startSym ag)) (NTS lhs::s2)` by METIS_TAC [auggrStRtcDerivesSt] THEN
	    FULL_SIMP_TAC (srw_ss()) [] 
	    THENL[
		  METIS_TAC [auggrStartRule, NOT_CONS_NIL],

		  `~(NTS lhs::s2 = [NTS (startSym ag)])` by FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
		  `RTC (rderives ag) [NTS (startSym g); TS eof] (NTS lhs::s2)` by METIS_TAC [auggrRtcRderivesStartRule] THEN
		  `RTC (derives ag) [NTS (startSym ag)] (NTS lhs::s2)` by METIS_TAC [rtcRdImpDg] THEN
		  `?pfx'. s2 = pfx' ++ [TS eof]` by METIS_TAC [APPEND_NIL, APPEND, lastEof] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [auggr_def, LET_THM] THEN
		  Cases_on `~(NTS st IN nonTerminalsML g) /\ ~(TS eof IN terminalsML g)` THEN FULL_SIMP_TAC (srw_ss()) [] 
		  THENL[
			`MEM (rule st [NTS (startSym g); TS eof]) (rules ag)` by METIS_TAC [rules_def, MEM] THEN
			Cases_on `pfx'` THEN FULL_SIMP_TAC (srw_ss()) [] 
			THENL[
			      Q.EXISTS_TAC `[NTS (startSym g); TS eof]` THEN
			      SRW_TAC [] [rules_def, ruleRhs_def] THEN
			      FULL_SIMP_TAC (srw_ss()) [rules_def, startSym_def] THEN
			      METIS_TAC [APPEND, APPEND_NIL, rtcRdImpDg],

			      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
			      Q.EXISTS_TAC `[NTS (startSym g); TS eof]` THEN
			      SRW_TAC [] [rules_def, ruleRhs_def] THEN
			      FULL_SIMP_TAC (srw_ss()) [rules_def, startSym_def] THEN
			      METIS_TAC [APPEND_NIL, APPEND, APPEND_ASSOC, rtcRdImpDg]
			      ],

			FULL_SIMP_TAC (srw_ss()) [],

			FULL_SIMP_TAC (srw_ss()) []
			]
		  ],


	    FULL_SIMP_TAC (srw_ss()) [IS_PREFIX, handleg, isSuffix] THEN
	    `((NTS lhs::s2) = [NTS (startSym ag)]) \/ ~MEM (NTS (startSym ag)) (NTS lhs::s2)` by METIS_TAC [auggrStRtcDerivesSt] THEN
	    FULL_SIMP_TAC (srw_ss()) [] 
	    THENL[
		  METIS_TAC [auggrStartRule, NOT_CONS_NIL],

		  `~(s2=[])` by METIS_TAC [auggrDerivesNotNil, APPEND_NIL] THEN
		  Cases_on `s2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
		  `RTC (derives ag) [NTS (startSym ag)] (NTS lhs::TS s::t)` by METIS_TAC [rtcRdImpDg] THEN
		  `(TS s) IN followSet ag (NTS lhs)` by METIS_TAC [followSetMem, APPEND_NIL, APPEND, APPEND_ASSOC] THEN
		  METIS_TAC [slrCompItemsEq, isTmnlSym_def]
		  ],

	    FULL_SIMP_TAC (srw_ss()) [IS_PREFIX, handleg, isSuffix] THEN
	    Cases_on `rhs` THEN FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
	    `~(s1++h::t++s2=[])` by SRW_TAC [] [] THEN
	    `isTmnlSym (HD (s1 ++ h::t ++ s2))` by (Cases_on `s1` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
	    `LENGTH (s1 ++ (h::t) ++ s2) < LENGTH (s1 ++ [NTS lhs] ++ s2) ==> isTmnlSym (HD (s1 ++ [NTS lhs] ++ s2))` by SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (arith_ss) [] THEN
	    METIS_TAC [IS_PREFIX, rev_nil, rtcImpInClosure, HD, EVERY_DEF, EVERY_APPEND, derives_same_append_left, derives_same_append_right, res1],

	    Cases_on `s1` THEN SRW_TAC [] [] THEN
	    Cases_on `rhs` THEN SRW_TAC [] [] THEN
	    Cases_on `s2` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] 
	    THENL[
		  (* 8 subgoals *)
		  METIS_TAC [auggrStRtcRderivesNotNil, derivesImpRderives, EVERY_DEF],


		  METIS_TAC [initItemsHdNt],

		  `lhs=startSym ag` by METIS_TAC [auggrRtcRderivesSt] THEN
		  SRW_TAC [] [] THEN
		  `h::t=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

		  `derives ag (NTS lhs::h'::t') (h::t++h'::t')` by METIS_TAC [res1, derives_same_append_right, APPEND] THEN
		  `(LENGTH (h::t++h'::t') < LENGTH (NTS lhs::h'::t') ==> isTmnlSym (HD (NTS lhs::h'::t')))` by (SRW_TAC [] [] THEN
														FULL_SIMP_TAC (arith_ss) []) THEN
		      `?lhsx r2. MEM (item lhsx ([],HD (h::t++h'::t')::r2)) (initItems ag (rules ag))` by METIS_TAC [rtcImpInClosure] THEN
		      MAP_EVERY Q.EXISTS_TAC [`lhsx`, `[]`, `r2`] THEN SRW_TAC [] [] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      METIS_TAC [IS_PREFIX],

		      `derives ag (h::(t ++ [NTS lhs])) (h::t)` by METIS_TAC [APPEND_NIL, res1, derives_same_append_left, APPEND] THEN
		      `(LENGTH (h::t) < LENGTH (h::(t ++ [NTS lhs]))) ==> isTmnlSym (HD (h::(t ++ [NTS lhs])))` by (SRW_TAC [] [] THEN
												    FULL_SIMP_TAC (arith_ss) []) THEN
			  `?lhsx r2. MEM (item lhsx ([],HD (h::t)::r2)) (initItems ag (rules ag))` by METIS_TAC [rtcImpInClosure] THEN
			  MAP_EVERY Q.EXISTS_TAC [`lhsx`, `[]`, `r2`] THEN SRW_TAC [] [] THEN
			  FULL_SIMP_TAC (srw_ss()) [] THEN
			  METIS_TAC [IS_PREFIX],

			  `derives ag (h::(t ++ [NTS lhs] ++ h'::t')) (h::(t ++ h'::t'))` by 
			  METIS_TAC [derives_same_append_left, derives_same_append_right, res1, APPEND, APPEND_NIL] THEN
			  `LENGTH (h::(t ++ h'::t')) < LENGTH (h::(t ++ [NTS lhs] ++ h'::t')) ==> isTmnlSym (HD (h::(t ++ [NTS lhs] ++ h'::t')))` by 
			      (SRW_TAC [] [] THEN
			       FULL_SIMP_TAC (arith_ss) []) THEN
			  `?lhsx r2. MEM (item lhsx ([],HD (h::(t ++ h'::t'))::r2)) (initItems ag (rules ag))` by METIS_TAC [rtcImpInClosure] THEN
			  MAP_EVERY Q.EXISTS_TAC [`lhsx`, `[]`, `r2`] THEN SRW_TAC [] [] THEN
			  FULL_SIMP_TAC (srw_ss()) [] THEN
			  METIS_TAC [IS_PREFIX],

			  `?pfx'.[]=pfx'++[TS eof]` by METIS_TAC [APPEND, APPEND_ASSOC, NOT_CONS_NIL, auggrLastEof] THEN
			  FULL_SIMP_TAC (srw_ss()) [],

			  `derives ag (h::(t ++ [NTS lhs] ++ h''::t'')) (h::(t ++ h'::t' ++ h''::t''))` by 
			  METIS_TAC [res1, derives_same_append_right, derives_same_append_left, APPEND] THEN
			  `LENGTH (h::(t ++ h'::t' ++ h''::t'')) < LENGTH (h::(t ++ [NTS lhs] ++ h''::t'')) ==> isTmnlSym (HD (h::(t ++ [NTS lhs] ++ h''::t'')))` by 
			      (SRW_TAC [] [] THEN
			       FULL_SIMP_TAC (arith_ss) []) THEN
                         `?lhsx r2. MEM (item lhsx ([],HD (h::(t ++ h'::t' ++ h''::t''))::r2)) (initItems ag (rules ag))` by METIS_TAC [rtcImpInClosure] THEN
			 MAP_EVERY Q.EXISTS_TAC [`lhsx`, `[]`, `r2`] THEN SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 METIS_TAC [IS_PREFIX]
			 ],


	    Cases_on `s1` THEN SRW_TAC [] [] THEN
	    Cases_on `rhs` THEN SRW_TAC [] [] 
	    THENL[
		  `derives ag (h::t ++ [NTS lhs] ++ s2) (h::t ++ s2)` by 
		  METIS_TAC [derives_same_append_right, res1, APPEND, derives_same_append_left, APPEND_NIL] THEN
		  `LENGTH (h::t ++ s2) < LENGTH (h::t ++ [NTS lhs] ++ s2) ==> isTmnlSym (HD (h::t ++ [NTS lhs] ++ s2))` by (SRW_TAC [] [] THEN
															    FULL_SIMP_TAC (srw_ss()) [] THEN
															    FULL_SIMP_TAC (arith_ss) []) THEN
		  `?lhs r2. MEM (item lhs ([],HD (h::t ++ s2)::r2)) (initItems ag (rules ag))` by METIS_TAC [rtcImpInClosure] THEN
		   MAP_EVERY Q.EXISTS_TAC [`lhs'`, `[]`, `r2`] THEN SRW_TAC [] [] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [IS_PREFIX],

		   ` ?lhsx rhs.MEM (item lhsx ([],h::rhs)) (initItems ag (rules ag))` by METIS_TAC [initItemsNtInBtwn, HD, NOT_CONS_NIL] THEN
		   MAP_EVERY Q.EXISTS_TAC [`lhsx`, `[]`, `rhs`] THEN SRW_TAC [] [] THEN
		   METIS_TAC [IS_PREFIX]
		   ],


	    Cases_on `s1` THEN SRW_TAC [] [] THEN
	    Cases_on `rhs` THEN SRW_TAC [] [] 
	    THENL[
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `MEM (item lhs ([],h::t)) (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt] THEN
		  MAP_EVERY Q.EXISTS_TAC [`lhs`, `[]`, `t`] THEN SRW_TAC [] [] THEN
		  METIS_TAC [IS_PREFIX],
		  
		   `?lhsx rhs.MEM (item lhsx ([],h::rhs)) (initItems ag (rules ag))` by METIS_TAC [initItemsNtInBtwn, HD, NOT_CONS_NIL] THEN
		   MAP_EVERY Q.EXISTS_TAC [`lhsx`, `[]`, `rhs`] THEN SRW_TAC [] [] THEN
		   METIS_TAC [IS_PREFIX]
		   ]
	    ]])
								 



val vsisLen = store_thm ("vsisLen",
``!l1 l2.validStlItemsStack l1 l2 ==> (LENGTH l2 = LENGTH l1 + 1)``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems] THEN
Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems] THEN
Cases_on `l1` THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems] THEN
DECIDE_TAC)


val validStlItems_pop = mk_thm([],
``!l1 l2 n.validStlItemsStack l1 l2 ==> ~(l1=[]) ==>
(pop l2 n = e::el) ==> ~(l2=[]) ==>
validStlItemsStack (pop l1 n) (e::el)``)
(*
SRW_TAC [] [] THEN
`LENGTH l2 = LENGTH l1 + 1` by METIS_TAC [vsisLen] THEN
Induct_on `l1` THEN Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] []
Induct_on `l'` THEN SRW_TAC [] [validStlItemsStack, validStlItems, pop_def] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [itemFstRhs_def, validStlItems] THEN

FULL_SIMP_TAC (srw_ss()) [pop_def] THEN
Cases_on `LENGTH l' = 0` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [pop0, validStlItemsStack, validStlItems, itemFstRhs_def] THEN
`LENGTH t`


*)

val rules2ItemsMemType = store_thm ("rules2ItemsMemType",
``!l.MEM e (rules2Items l) ==> ?lhs r. e = item lhs ([],r)``,
Induct_on `l` THEN SRW_TAC [] [rules2Items_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [rules2Items_def])


val iclosureMemNotMemList = store_thm ("iclosureMemNotMemList",
``!g l.MEM e (iclosure g l) ==> ~MEM e l ==>  ?lhs r. (e = item lhs ([],r))``,
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
 ])


val sgotoMemType = store_thm ("sgotoMemType",
``!e l itl.MEM e l ==> (l=(sgoto g itl h)) ==> (?lhs r.(e=item lhs ([],r)) \/ ?lhs r1 r2.(e=item lhs (r1++[h],r2)))``,
Induct_on `itl` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, moveDot_def, iclosure] THEN
Cases_on `MEM e (moveDot (h'::itl) h)` THEN
METIS_TAC [mdMem, iclosureMemNotMemList])


val iclosureMemRhsFstNil = store_thm ("iclosureMemRhsFstNil",
	      ``!g l.~MEM (item lhs (r1 ++ [h],r2)) l ==> ~(MEM (item lhs (r1 ++ [h],r2)) (iclosure g l))``,
    SRW_TAC [] [] THEN
    Cases_on `~MEM (item lhs (r1 ++ [h],r2)) (iclosure g l)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    `?lhs' r. (item lhs (r1 ++ [h],r2)) = item lhs' ([],r)` by METIS_TAC [iclosureMemNotMemList] THEN
    FULL_SIMP_TAC (srw_ss()) [])
	      
				    ]

val sgotoMemItlType = store_thm ("sgotoMemItlType",
``!itl l.MEM (item lhs (r1++[h],r2)) l ==>  (l=(sgoto g itl h)) ==> MEM (item lhs (r1,[h]++r2)) itl``,
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
	    `?l r1' r2'.
           ((item lhs (r1 ++ [h],r2)) = item l (r1' ++ [h],r2')) /\ MEM (item l (r1',h::r2')) itl` by METIS_TAC [mdMem] THEN
	    FULL_SIMP_TAC (srw_ss()) [],
	    
	    METIS_TAC [iclosureMemRhsFstNil]
	    ]])


val validStlItems_sgoto_gen = mk_thm([],
``!l itl s el l' x''.validStlItemsStack l ((s, itl)::el) ==> (l'=(sgoto g itl (NTS s'))) ==>
validStlItems  (((NTS s', (sgoto g itl (NTS s'))),x'')::l) l'``)
(*

*)


val mdMem = store_thm ("mdMem",
``!e itl sym.MEM e (moveDot itl sym) ==>  ?l r1 r2.(e=item l (r1++[sym],r2)) /\ (MEM (item l (r1,sym::r2)) itl)``,
Induct_on `itl` THEN SRW_TAC [] [moveDot_def] THEN
`moveDot (h::itl) sym = moveDot [h] sym ++ moveDot itl sym` by METIS_TAC [md_append, APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `h` THEN Cases_on `p` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [moveDot_def] THEN
Cases_on `h=sym` THEN FULL_SIMP_TAC (srw_ss()) [],
METIS_TAC []])


val validStlItems_goto = mk_thm ([],
``!g itl itl' sym t.(getState (sgoto g, reduce g) itl sym = GOTO itl') ==>
 validStlItems t itl ==>
validStlItems (((sym,itl'), Leaf (TM (tmnlSym sym)))::t) itl'``)
(*
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto g itl sym` THEN Cases_on `reduce g itl (sym2Str sym)` THEN FULL_SIMP_TAC (srw_ss()) [] 
 THENL[
 Cases_on `LENGTH t'=0` THEN FULL_SIMP_TAC (srw_ss()) [],
 
 `itl'=h::t'` by METIS_TAC [] THEN
 SRW_TAC [] [validStlItems] 
 THENL[
 `?lhs r.
           (h = item lhs ([],r)) \/ ?lhs r1 r2. h = item lhs (r1 ++ [sym],r2)` by METIS_TAC [sgotoMem, MEM]

 SRW_TAC [] [isSuffix, stackSyms, itemFstRhs_def, IS_PREFIX]

`MEM (item lhs' (r1,[sym]++r2)) itl` by SRW_TAC [] []
 FULL_SIMP_TAC (srw_ss()) [validStlItems, rgr_r9eq, validStlItems_append]
SRW_TAC [] []
  FULL_SIMP_TAC (srw_ss()) [validStlItems, rgr_r9eq, validStlItems_append, itemFstRhs_def, isSuffix, stackSyms, REVERSE_APPEND, IS_PREFIX]

 Cases_on `itemEqRuleList (h::t') (h'::t'')` THEN FULL_SIMP_TAC (srw_ss()) []
 ]


*)


(*
lr1 components hold after one parse step
validStates ag (state s itl::csl) = parse_csl_validStates
CAN I ASSUME HERE that stl is not empty since it is not a start state???
*)

val parse_validStlItemsStack = store_thm("parse_validStlItemsStack",
``!m g.validStlItemsStack stl csl ==> (m=slr g) ==>
~NULL csl ==> (* preserved by parse_csl_not_nil *)
(LENGTH csl = LENGTH stl + 1) ==> (* another invariant *)
EVERY (\x.~(x=[])) (MAP SND csl) ==> (* prove this as an invariant!!!!! *)
~(stl=[]) ==>
(parse m (sl, stl, csl) = SOME (sl',stl',csl')) ==> validStlItems stl' (SND (HD csl'))``,

SRW_TAC [] [] THEN
`?x y.csl = x::y` by METIS_TAC [list_mem2, NULL_EQ_NIL] THEN
SRW_TAC [] [] THEN
Cases_on `x` THEN
`~NULL csl'` by METIS_TAC [parse_csl_not_nil] THEN
`?x' y'.csl' = x'::y'` by (Induct_on `csl'` THEN SRW_TAC [] []) THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN 
Cases_on `slr g ` THEN  Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN Cases_on `getState x r h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[

(* doReduce x ([h],h'::t,state s l::y) r = SOME (sl',stl',x'::y') *)

FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym h` THEN Cases_on `addRule (h'::t) r'` THEN 
Cases_on `pop ((q, r)::y) (LENGTH (ruleRhs r')) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `r'` THEN 
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [ADD1] THEN
`x=(sgoto g, reduce g)` by METIS_TAC [sgoto_exp] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`?e el.(pop ((q, (h''::t'))::y) (LENGTH l)) = e::el` by METIS_TAC [list_nchotomy] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
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
Cases_on `pop ((q, r)::y) (LENGTH (ruleRhs r')) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `r'` THEN 
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [ADD1] THEN
`x=(sgoto g, reduce g)` by METIS_TAC [sgoto_exp] THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`?e el.(pop ((q, (h'::t'))::y) (LENGTH l)) = e::el` by METIS_TAC [list_nchotomy] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
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
FULL_SIMP_TAC (srw_ss()) [validStlItems, isSuffix, stackSyms, REVERSE_APPEND] THEN
Cases_on `q'` THEN Cases_on `h''` THEN
Cases_on `r'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [push_def] THEN
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [validStlItemsStack, validStlItems] THEN
FULL_SIMP_TAC (srw_ss()) [push_def,validStlItemsStack] THEN
SRW_TAC [] [] THEN
`x=(sgoto g, reduce g)` by METIS_TAC [sgoto_exp] THEN
SRW_TAC [] [] THEN
METIS_TAC [sgoto_exp, validStlItems_goto, APPEND, APPEND_ASSOC, validStlItems]])


val validItem_moveDot = store_thm ("validItem_moveDot",
``!itl.EVERY (validItem ag p) itl ==>
EVERY (validItem ag (p++[h])) (moveDot itl h)``,
Induct_on `itl` THEN SRW_TAC [] [moveDot_def] THEN
Cases_on `h'` THEN Cases_on `p'` THEN
Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [moveDot_def]  THEN
Cases_on `h'=h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
SRW_TAC [] [] THEN
METIS_TAC [APPEND, APPEND_ASSOC])

(* 
``!m g.(auggr g st eof = SOME ag) ==>
(m=slr ag) ==>
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
validItemStack ag stl ==>
(MAP FST stl = FRONT (state s itl::csl)) ==>
((parse m (sl, stl, (state s itl::csl)) = SOME (sl',stl',csl'))) ==>
EVERY (validItem ag (stackSyms stl')) (stateItl (FST (HD stl')))``


SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
Cases_on `slr ag` THEN FULL_SIMP_TAC (srw_ss()) []  THEN Cases_on `sl` THEN  FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `getState x itl h ` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN  Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[

(* reduce with one symbol *)
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `isNonTmnlSym h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [stateItl_def, stackSyms] THEN
Cases_on `r` THEN  FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def, stateSym_def],

(* reduce with more than one symbol *)


(* shift *)

Cases_on `isNonTmnlSym h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [stackSyms] THEN
Cases_on `s'` THEN SRW_TAC [] [stateSym_def, stateItl_def] THEN
`x= (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto ag itl h` THEN Cases_on `reduce ag itl (sym2Str h)` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `LENGTH t` THEN FULL_SIMP_TAC (srw_ss()) [],

SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, stackSyms] THEN
`EVERY (validItem ag ((REVERSE (MAP stateSym (MAP FST stl)))++[h])) (moveDot itl h)` 
by METIS_TAC [validItem_moveDot] THEN
METIS_TAC [validItem_iclosure, EVERY_DEF],

Cases_on `itemEqRuleList (h'::t) (h''::t')` THEN FULL_SIMP_TAC (srw_ss()) []]

*)


val getState_reduce_not_NA = store_thm ("getState_reduce_not_NA", 
``!N r1 itl h ag. (slr ag = SOME (sgoto ag, reduce ag)) ==> MEM (item N (r1,[])) itl ==>
 h IN followSet ag (NTS N) ==> isTmnlSym h ==>
(!j.
             MEM j itl /\ completeItem j /\
             h IN followSet ag (NTS (itemLhs j)) ==>
             (j = item N (r1,[])))
==> ~(getState (sgoto ag,reduce ag) itl h = NA)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [slr_def, LET_THM] THEN
Cases_on `?itl' sym.
               case sgoto ag itl' sym of
                  [] ->
                    (case reduce ag itl' (sym2Str sym) of
                        [] -> F
                     || [v12] -> F
                     || v12::v16::v17 -> T)
               || v8::v9 ->
                    case reduce ag itl' (sym2Str sym) of
                       [] -> F
                    || [v20] -> T
                    || v20::v26::v27 -> T` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto ag itl h` THEN Cases_on `reduce ag itl (sym2Str h)` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [reduce_mem_followSet, NOT_CONS_NIL],

Cases_on `LENGTH t = 0` THEN SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`itl`, `h`] MP_TAC) THEN
Cases_on `t` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [],

Cases_on `itemEqRuleList (h'::t) (h''::t')` THEN SRW_TAC [] [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`itl`, `h`] MP_TAC) THEN
Cases_on `t'` THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) []])


val getState_shift_not_NA = store_thm ("getState_shift_not_NA",
``!g N r1 h' t itl.(SOME (sgoto g, reduce g) = slr g) ==>
MEM (item N (r1,h'::t)) itl ==> ~(getState (sgoto g, reduce g) itl h' = NA)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto g itl h'` THEN Cases_on `reduce g itl (sym2Str h')` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [sgoto_mem, NOT_CONS_NIL, APPEND, MEM, rgr_r9eq],
METIS_TAC [sgoto_mem, NOT_CONS_NIL, APPEND, MEM, rgr_r9eq],
Cases_on `itemEqRuleList (h::t') (h''::t'')` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [slr_def, LET_THM] THEN
Cases_on `?itl' sym.
               case sgoto g itl' sym of
                  [] ->
                    (case reduce g itl' (sym2Str sym) of
                        [] -> F
                     || [v12] -> F
                     || v12::v16::v17 -> T)
               || v8::v9 ->
                    case reduce g itl' (sym2Str sym) of
                       [] -> F
                    || [v20] -> T
                    || v20::v26::v27 -> T` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`itl`, `h'`] MP_TAC) THEN
Cases_on `t''` THEN SRW_TAC [][]])



val validStkSymTree_stateSym_eq_ptree2Sym = store_thm ("validStkSymTree_stateSym_eq_ptree2Sym", 
``!stl.validStkSymTree stl ==> ((MAP FST (MAP FST stl)) = (MAP (ptree2Sym o SND) stl))``,
Induct_on `stl` THEN SRW_TAC [] [] THEN
Cases_on `h` THEN Cases_on `q` THEN Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [ptree2Sym_def, validStkSymTree_def])


val addRule_SOME = store_thm ("addRule_SOME",
``!pfx l stl.(stackSyms stl = pfx++l) ==> validStkSymTree stl ==> ?x.(addRule stl (rule N l) = SOME x)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [buildTree_def, LET_THM, stackSyms, addRule_def] THEN
`((MAP FST (MAP FST stl)) = (MAP (ptree2Sym o SND) stl))` by METIS_TAC [validStkSymTree_stateSym_eq_ptree2Sym] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`(MAP (ptree2Sym o SND) stl) = REVERSE l ++ REVERSE pfx` by METIS_TAC [REVERSE_APPEND, REVERSE_REVERSE] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH l + LENGTH pfx >= LENGTH l` by DECIDE_TAC THEN
`LENGTH (REVERSE l) + LENGTH (REVERSE pfx) >= LENGTH (REVERSE l)` by DECIDE_TAC THEN
`LENGTH (REVERSE l ++ REVERSE pfx) >= (LENGTH (REVERSE l))` by FULL_SIMP_TAC (srw_ss()) [] THEN
`?x.((take (LENGTH (REVERSE l)) (REVERSE l ++ REVERSE pfx)) = SOME x)` by METIS_TAC [take_valid] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l` THEN SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
FULL_SIMP_TAC (srw_ss()) [take_def, take10] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [],
SRW_TAC [] [] THEN FULL_SIMP_TAC (srw_ss()) [] THEN FULL_SIMP_TAC (arith_ss) [] THEN
`~((LENGTH (REVERSE t) + 1) = 0)` by DECIDE_TAC THEN
`LENGTH (REVERSE t ++ [h]) = (LENGTH (REVERSE t) + 1)` by FULL_SIMP_TAC (arith_ss) [rev_nil, LENGTH, LENGTH_APPEND] THEN
`take (LENGTH (REVERSE t) + 1) (REVERSE t ++ [h] ++ REVERSE pfx) = SOME (REVERSE t ++ [h])` by METIS_TAC [takenthm] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (MAP SND stl) = LENGTH (x ++ REVERSE pfx)` by METIS_TAC [LENGTH_MAP] THEN
`LENGTH (MAP SND stl) >= LENGTH x` by FULL_SIMP_TAC (arith_ss) [LENGTH_APPEND] THEN
SRW_TAC [] [] THEN
`?x.take (LENGTH (REVERSE t ++[h])) (MAP SND stl) = SOME x` by METIS_TAC [take_valid] THEN
FULL_SIMP_TAC (srw_ss()) []])


val pop_not_empty = store_thm ("pop_not_empty",
``!l n.(LENGTH l > n) ==> ~(pop l n = [])``,
Induct_on `l` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (arith_ss) [] THEN 
SRW_TAC [] [pop_def] THEN
`LENGTH l > n-1` by FULL_SIMP_TAC (arith_ss) [] THEN
METIS_TAC [])


val getState_shift_not_NA2 = mk_thm ([],
``!g N h h' t itl.(SOME (sgoto g, reduce g) = slr g) ==>
MEM (item N (h,[])) itl ==> 
h' IN followSet g (NTS N) ==> isTmnlSym h' ==>
	   (!j.MEM j itl /\ completeItem j /\
             h' IN followSet g (NTS (itemLhs j)) ==>
             (j = item N (h,[]))) ==>
~(getState (sgoto g, reduce g) itl h' = NA)``)
(*
(* itl here shouldn't have duplicates!! *)
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto g itl h'` THEN Cases_on `reduce g itl (sym2Str h')` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [reduce_mem_followSet],
SRW_TAC [] [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def]





Cases_on `?itl' sym.
               case sgoto g itl' sym of
                  [] ->
                    (case reduce g itl' (sym2Str sym) of
                        [] -> F
                     || [v12] -> F
                     || v12::v16::v17 -> T)
               || v8::v9 ->
                    case reduce g itl' (sym2Str sym) of
                       [] -> F
                    || [v20] -> T
                    || v20::v26::v27 -> T` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`itl`, `h'`] MP_TAC) THEN
Cases_on `t''` THEN SRW_TAC [][]])
*)


(* lr1_inv ensures that machine takes a step *)

val rderivesNotNil = store_thm ("rderivesNotNil", 
``!l l' g.rderives g l l' ==> ~(l=[])``,
SRW_TAC [] [rderives_def] THEN
Cases_on `s1` THEN SRW_TAC [] [])



val validStatesAuggrRule = store_thm ("validStatesAuggrRule", 
``(auggr g st eof = SOME ag) ==> MEM (item l' (r1,TS eof::r2)) itl
==> validStates ag ((s,itl)::csl) ==> 
(l'=startSym ag) /\ (r1=[NTS (startSym g)]) /\ (r2=[])``,
SRW_TAC [] [] THEN
`validItl ag [item l' (r1,TS eof::r2)]` by METIS_TAC [validStates_def, validStates_append, rgr_r9eq, validItl_append] THEN
FULL_SIMP_TAC (srw_ss()) [validItl_def, auggr_def, startSym_def, LET_THM] THEN
Cases_on `~(NTS st IN nonTerminalsML g) /\ ~(TS eof IN terminalsML g)` THEN
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
METIS_TAC [APPEND, slemma1_4Tmnls, terminalsEq, APPEND_NIL, APPEND_ASSOC]])

val mapFstHd = store_thm ("mapFstHd",
``!l.~(l=[]) ==> (FST (FST (HD l)) = HD (MAP FST (MAP FST l)))``,
Induct_on `l` THEN SRW_TAC [] [])

val listEndNt = store_thm ("listEndNt",
``!l l' sfx.(l ++ [NTS N] = l' ++ sfx) ==> EVERY isTmnlSym sfx ==> (sfx=[])``,
Induct_on `sfx` THEN SRW_TAC [] [] THEN
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
`(FRONT (TS s'::t) ++ [LAST (TS s'::t)]) = (TS s'::t)` by  METIS_TAC [APPEND_FRONT_LAST, NOT_CONS_NIL] THEN
`EVERY isTmnlSym  (FRONT (TS s'::t) ++ [NTS N])` by METIS_TAC [EVERY_DEF, EVERY_APPEND, isTmnlSym_def] THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def])


val funcCompNegEq = store_thm ("funcCompNegEq",
``!l.EVERY ($~ o $~ o isTmnlSym) l ==> EVERY isTmnlSym l``,
Induct_on `l` THEN SRW_TAC [] [])


METIS_TAC [EVERY_DEF, APPEND_NIL, APPEND_ASSOC]
*)

(* 24 goals with the new inv, inp in the condn itself, the proof below still works but have to repeat some parts of the THENL
to cover all the 24 goals! *)
val mac_step = store_thm ("mac_step",
``!m g.(auggr g st eof = SOME ag) ==>
~(sl=[]) ==>
EVERY isTmnlSym sl ==> 
(SOME m=slr ag) ==> 
(validStkSymTree stl) ==> (* prop1thm preserves this as an invariant *)
(LENGTH ((s, itl)::csl) = LENGTH stl + 1) ==> (* prove this as an invariant , ensures pop in reduce goes ok *)
~(FST (FST (HD stl)) = NTS (startSym g)) ==> 
~(FST (FST (HD stl)) = TS eof) ==>
validStates ag ((s, itl)::csl) ==>
lr1_inv (ag, stl, ((s, itl)::csl), sl) ==>
?sl' stl' csl'.((parse (SOME m) (sl, stl, ((s, itl)::csl)) = SOME (sl',stl',csl')))``,

SRW_TAC [] [] THEN
`m = (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM, viablePfx, handleg, sforms_def, lr1_inv] THEN
`?h t.sl=h::t` by (Induct_on `sl` THEN SRW_TAC [] []) THEN
SRW_TAC [] [] THEN
`slr ag = SOME (sgoto ag,reduce ag)` by METIS_TAC [] THEN 
ONCE_ASM_REWRITE_TAC [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isSuffix h (stackSyms stl) /\ MEM (item N (h,[])) itl /\ (sfx=h'::t)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN SRW_TAC [] [] THEN
Cases_on `getState (sgoto ag, reduce ag) itl h'` THEN SRW_TAC [] [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[

(* 1 doReduce (sgoto ag,reduce ag) ([h],stl,state s itl::csl) r =
 SOME (sl',stl',csl') / MEM (item N (h,[])) itl *)
`validItem ag (stackSyms stl) (item N (h,[]))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
Cases_on `r` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s' (l,[])) itl`  by METIS_TAC [getState_mem_itl, validStates_def] THEN
`h' IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
`(item s' (l,[])) = (item N (h,[]))` by METIS_TAC [completeItem, itemLhs_def] THEN
SRW_TAC [] [] THEN
SRW_TAC [] [doReduce_def, LET_THM] THENL[
METIS_TAC [sym_r1b],

FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`LENGTH stl = LENGTH (stackSyms stl)` by METIS_TAC [stackSyms_len] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN

`LENGTH ((s, itl)::csl) > LENGTH h` by FULL_SIMP_TAC (arith_ss) [LENGTH, LENGTH_APPEND, APPEND] THEN
`~(pop ((s, itl)::csl) (LENGTH h) = [])` by METIS_TAC [pop_not_empty] THEN
SRW_TAC [] [] THEN
`?x.addRule stl (rule N h) = SOME x` by METIS_TAC [addRule_SOME] THEN
SRW_TAC [] []],

(* 2 getState (sgoto ag,reduce ag) itl h' = GOTO s' ==> F  / MEM (item N (h,[])) itl *)
`validItem ag (stackSyms stl) (item N (h,[]))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
METIS_TAC [sym_r1b, validStates_def, shiftReduceGoto],

(* 3 getState (sgoto ag,reduce ag) itl h' = NA  / MEM (item N (h,[])) itl *)
`validItem ag (stackSyms stl) (item N (h,[]))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
METIS_TAC [getState_shift_not_NA2, sgoto_exp],

(* 4 doReduce (sgoto ag,reduce ag) (h'::h''::t',stl,state s itl::csl) r =
    SOME (sl',stl',csl') / MEM (item N (h,[])) itl *)
`validItem ag (stackSyms stl) (item N (h,[]))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
Cases_on `r` THEN SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s' (l,[])) itl`  by METIS_TAC [getState_mem_itl, validStates_def] THEN
`h' IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
`(item s' (l,[])) = (item N (h,[]))` by METIS_TAC [completeItem, itemLhs_def] THEN
SRW_TAC [] [] THEN
SRW_TAC [] [doReduce_def, LET_THM] THENL[
METIS_TAC [sym_r1b],

FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`LENGTH stl = LENGTH (stackSyms stl)` by METIS_TAC [stackSyms_len] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN

`LENGTH ((s, itl)::csl) > LENGTH h` by FULL_SIMP_TAC (arith_ss) [LENGTH, LENGTH_APPEND, APPEND] THEN
`~(pop ((s, itl)::csl) (LENGTH h) = [])` by METIS_TAC [pop_not_empty] THEN
SRW_TAC [] [] THEN
`?x.addRule stl (rule N h) = SOME x` by METIS_TAC [addRule_SOME] THEN
SRW_TAC [] []],

(* 5 getState (sgoto ag,reduce ag) itl h' = GOTO l ==> F  / MEM (item N (h,[])) itl *)
`validItem ag (stackSyms stl) (item N (h,[]))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
METIS_TAC [sym_r1b, validStates_def, shiftReduceGoto],

(* 6 getState (sgoto ag,reduce ag) itl h' = NA / MEM (item N (h,[])) itl *)
`validItem ag (stackSyms stl) (item N (h,[]))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
METIS_TAC [getState_shift_not_NA2, sgoto_exp],

(* ---For MEM (item l (r1,h'::r2)) itl ------------------------------------ *)

(* 1 doReduce (sgoto ag,reduce ag) ([h],stl,state s itl::csl) r =
 SOME (sl',stl',csl') / MEM (item l' (r1,h'::r2)) itl *)
`validItem ag (stackSyms stl) (item l (r1,h'::r2))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
Cases_on `r` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s' (l',[])) itl`  by METIS_TAC [getState_mem_itl, validStates_def] THEN
`h' IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
SRW_TAC [] [doReduce_def, LET_THM] THENL[
METIS_TAC [sym_r1b],

FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`LENGTH stl = LENGTH (stackSyms stl)` by METIS_TAC [stackSyms_len] THEN
SRW_TAC [] [] THEN
Cases_on `addRule stl (rule s' l')` THEN 
Cases_on `pop ((s,itl)::csl) (LENGTH l') = []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`!e. MEM e itl ==>
(e = item s' (l',[])) \/ ~ ?l'' r2 r1. e = item l'' (r1,h'::r2)` by METIS_TAC [validStates_def, shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []],

(* 2 getState (sgoto ag,reduce ag) itl h' = GOTO l ==> F / MEM (item l' (r1,h'::r2)) itl *)
Cases_on `N=startSym ag` THEN SRW_TAC [] [] THENL[
`(h=[NTS (startSym g);TS eof])` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
`(pfx=[]) /\ (sfx=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`h'=TS eof` by METIS_TAC [APPEND, lastElemEq] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isSuffix] THEN
Cases_on `stackSyms stl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
`REVERSE (REVERSE (MAP FST (MAP FST stl))) = REVERSE [NTS (startSym g)]` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [],

`?pfx'.sfx = pfx'++[TS eof]` by METIS_TAC [lastEof] THEN
`h'=TS eof` by METIS_TAC [APPEND_ASSOC, lastElemEq, lastEof, NOT_CONS_NIL, APPEND] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isSuffix] THEN
`validItem ag (pfx ++ h ++ pfx') (item l' (r1,TS eof::r2))` by METIS_TAC [EVERY_DEF, rgr_r9eq, EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
`(l'=startSym ag) /\ (r1=[NTS (startSym g)]) /\ (r2=[])` by METIS_TAC [validStatesAuggrRule] THEN
SRW_TAC [] [] THEN
`pfx'=[]` by METIS_TAC [listEndNt] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
`(MAP FST (MAP FST stl)) = REVERSE h ++ REVERSE pfx` by METIS_TAC [REVERSE_REVERSE, REVERSE_APPEND] THEN
`REVERSE h ++ REVERSE pfx = REVERSE [NTS (startSym g)] ++ REVERSE pfx''` by METIS_TAC [REVERSE_REVERSE, REVERSE_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(stl=[])` by (Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
METIS_TAC [mapFstHd, HD]],

(* 3 getState (sgoto ag,reduce ag) itl h' = NA / MEM (item l (r1,h'::r2)) itl  *)
`validItem ag (stackSyms stl) (item l (r1,h'::r2))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
METIS_TAC [getState_shift_not_NA, sgoto_exp],


(* 4 doReduce (sgoto ag,reduce ag) (h'::h''::t',stl, (s, itl)::csl) r =
    SOME (sl',stl',csl') / MEM (item l (r1,h'::r2)) itl *)
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s' (l',[])) itl`  by METIS_TAC [getState_mem_itl, validStates_def] THEN
`h' IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
SRW_TAC [] [doReduce_def, LET_THM] THENL[
METIS_TAC [sym_r1b],

FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`LENGTH stl = LENGTH (stackSyms stl)` by METIS_TAC [stackSyms_len] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule stl (rule s' l')` THEN
Cases_on `pop ((s,itl)::csl) (LENGTH l') = []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`!e. MEM e itl ==>
(e = item s' (l',[])) \/ ~ ?l'' r2 r1. e = item l'' (r1,h'::r2)` by METIS_TAC [validStates_def, shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []],

(* 5 getState (sgoto ag,reduce ag) itl h' = GOTO l ==> F / MEM (item l' (r1,h'::r2)) itl *)
METIS_TAC [sym_r1b, validStates_def, shiftReduceGoto],


(* 6 getState (sgoto ag,reduce ag) itl h' = NA / MEM (item l' (r1,h'::r2)) itl *)
METIS_TAC [getState_shift_not_NA, sgoto_exp],

(* 7 getState (sgoto ag,reduce ag) itl h' = REDUCE r / MEM (item l (r1,h'::r2)) itl *)
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s' (l',[])) itl`  by METIS_TAC [getState_mem_itl, validStates_def] THEN
`h' IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
SRW_TAC [] [doReduce_def, LET_THM] THENL[
METIS_TAC [sym_r1b],

FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`LENGTH stl = LENGTH (stackSyms stl)` by METIS_TAC [stackSyms_len] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule stl (rule s' l')` THEN
Cases_on `pop ((s,itl)::csl) (LENGTH l') = []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`!e. MEM e itl ==>
(e = item s' (l',[])) \/ ~ ?l'' r2 r1. e = item l'' (r1,h'::r2)` by METIS_TAC [validStates_def, shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []],

(* 8 getState (sgoto ag,reduce ag) itl h' = GOTO l / MEM (item l' (r1,h'::r2)) itl *)
(* METIS_TAC [sym_r1b, validStates_def, shiftReduceGoto], *)
Cases_on `N=startSym ag` THEN SRW_TAC [] [] THENL[
`(h=[NTS (startSym g);TS eof])` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
`(pfx=[]) /\ (sfx=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`h'=TS eof` by METIS_TAC [APPEND, lastElemEq] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isSuffix] THEN
Cases_on `stackSyms stl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
`REVERSE (REVERSE (MAP FST (MAP FST stl))) = REVERSE [NTS (startSym g)]` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [],

`?pfx'.sfx = pfx'++[TS eof]` by METIS_TAC [lastEof] THEN
`h'=TS eof` by METIS_TAC [APPEND_ASSOC, lastElemEq, lastEof, NOT_CONS_NIL, APPEND] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isSuffix] THEN
`validItem ag (pfx ++ h ++ pfx') (item l' (r1,TS eof::r2))` by METIS_TAC [EVERY_DEF, rgr_r9eq, EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
`(l'=startSym ag) /\ (r1=[NTS (startSym g)]) /\ (r2=[])` by METIS_TAC [validStatesAuggrRule] THEN
SRW_TAC [] [] THEN
`pfx'=[]` by METIS_TAC [listEndNt] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
`(MAP FST (MAP FST stl)) = REVERSE h ++ REVERSE pfx` by METIS_TAC [REVERSE_REVERSE, REVERSE_APPEND] THEN
`REVERSE h ++ REVERSE pfx = REVERSE [NTS (startSym g)] ++ REVERSE pfx''` by METIS_TAC [REVERSE_REVERSE, REVERSE_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(stl=[])` by (Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
METIS_TAC [mapFstHd, HD]],

(* 9 getState (sgoto ag,reduce ag) itl h' = NA / MEM (item l' (r1,h'::r2)) itl *)
METIS_TAC [getState_shift_not_NA, sgoto_exp],


(* 10 doReduce (sgoto ag,reduce ag) (h'::h''::t',stl,(s,itl)::csl) r =
      SOME (sl',stl',csl') / MEM (item l' (r1,h'::r2)) itl *)
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s' (l',[])) itl`  by METIS_TAC [getState_mem_itl, validStates_def] THEN
`h' IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
SRW_TAC [] [doReduce_def, LET_THM] THENL[
METIS_TAC [sym_r1b],

FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`LENGTH stl = LENGTH (stackSyms stl)` by METIS_TAC [stackSyms_len] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule stl (rule s' l')` THEN
Cases_on `pop ((s,itl)::csl) (LENGTH l') = []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`!e. MEM e itl ==>
(e = item s' (l',[])) \/ ~ ?l'' r2 r1. e = item l'' (r1,h'::r2)` by METIS_TAC [validStates_def, shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []],


(* 11 getState (sgoto ag,reduce ag) itl h' = GOTO l *)
METIS_TAC [sym_r1b, validStates_def, shiftReduceGoto],

(* 12 getState (sgoto ag,reduce ag) itl h' = NA *)
METIS_TAC [getState_shift_not_NA, sgoto_exp],

(* 1 doReduce (sgoto ag,reduce ag) ([h],stl,state s itl::csl) r =
 SOME (sl',stl',csl') / MEM (item l' (r1,h'::r2)) itl *)
`validItem ag (stackSyms stl) (item l (r1,h'::r2))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
Cases_on `r` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s' (l',[])) itl`  by METIS_TAC [getState_mem_itl, validStates_def] THEN
`h' IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
SRW_TAC [] [doReduce_def, LET_THM] THENL[
METIS_TAC [sym_r1b],

FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`LENGTH stl = LENGTH (stackSyms stl)` by METIS_TAC [stackSyms_len] THEN
SRW_TAC [] [] THEN
Cases_on `addRule stl (rule s' l')` THEN 
Cases_on `pop ((s,itl)::csl) (LENGTH l') = []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`!e. MEM e itl ==>
(e = item s' (l',[])) \/ ~ ?l'' r2 r1. e = item l'' (r1,h'::r2)` by METIS_TAC [validStates_def, shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []],

(* 2 getState (sgoto ag,reduce ag) itl h' = GOTO l ==> F / MEM (item l' (r1,h'::r2)) itl *)
Cases_on `N=startSym ag` THEN SRW_TAC [] [] THENL[
`(h=[NTS (startSym g);TS eof])` by METIS_TAC [auggrStartRule] THEN
SRW_TAC [] [] THEN
`(pfx=[]) /\ (sfx=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`h'=TS eof` by METIS_TAC [APPEND, lastElemEq] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isSuffix] THEN
Cases_on `stackSyms stl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
`REVERSE (REVERSE (MAP FST (MAP FST stl))) = REVERSE [NTS (startSym g)]` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [],

`?pfx'.sfx = pfx'++[TS eof]` by METIS_TAC [lastEof] THEN
`h'=TS eof` by METIS_TAC [APPEND_ASSOC, lastElemEq, lastEof, NOT_CONS_NIL, APPEND] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [isSuffix] THEN
`validItem ag (pfx ++ h ++ pfx') (item l' (r1,TS eof::r2))` by METIS_TAC [EVERY_DEF, rgr_r9eq, EVERY_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
`(l'=startSym ag) /\ (r1=[NTS (startSym g)]) /\ (r2=[])` by METIS_TAC [validStatesAuggrRule] THEN
SRW_TAC [] [] THEN
`pfx'=[]` by METIS_TAC [listEndNt] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms] THEN
`(MAP FST (MAP FST stl)) = REVERSE h ++ REVERSE pfx` by METIS_TAC [REVERSE_REVERSE, REVERSE_APPEND] THEN
`REVERSE h ++ REVERSE pfx = REVERSE [NTS (startSym g)] ++ REVERSE pfx''` by METIS_TAC [REVERSE_REVERSE, REVERSE_APPEND] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`~(stl=[])` by (Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
METIS_TAC [mapFstHd, HD]],

(* 3 getState (sgoto ag,reduce ag) itl h' = NA / MEM (item l (r1,h'::r2)) itl  *)
`validItem ag (stackSyms stl) (item l (r1,h'::r2))` by (FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN
FULL_SIMP_TAC (srw_ss()) [validItem] THEN
METIS_TAC [getState_shift_not_NA, sgoto_exp],


(* 4 doReduce (sgoto ag,reduce ag) (h'::h''::t',stl, (s, itl)::csl) r =
    SOME (sl',stl',csl') / MEM (item l (r1,h'::r2)) itl *)
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`MEM (item s' (l',[])) itl`  by METIS_TAC [getState_mem_itl, validStates_def] THEN
`h' IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
SRW_TAC [] [doReduce_def, LET_THM] THENL[
METIS_TAC [sym_r1b],

FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`LENGTH stl = LENGTH (stackSyms stl)` by METIS_TAC [stackSyms_len] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule stl (rule s' l')` THEN
Cases_on `pop ((s,itl)::csl) (LENGTH l') = []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`!e. MEM e itl ==>
(e = item s' (l',[])) \/ ~ ?l'' r2 r1. e = item l'' (r1,h'::r2)` by METIS_TAC [validStates_def, shiftReduce] THEN
RES_TAC THEN FULL_SIMP_TAC (srw_ss()) []],

(* 5 getState (sgoto ag,reduce ag) itl h' = GOTO l ==> F / MEM (item l' (r1,h'::r2)) itl *)
METIS_TAC [sym_r1b, validStates_def, shiftReduceGoto],


(* 6 getState (sgoto ag,reduce ag) itl h' = NA / MEM (item l' (r1,h'::r2)) itl *)
METIS_TAC [getState_shift_not_NA, sgoto_exp]])