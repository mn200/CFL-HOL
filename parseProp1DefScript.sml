open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory pairTheory whileTheory

open regexpTheory grammarDefTheory boolLemmasTheory listLemmasTheory
parseTreeTheory parserDefTheory yaccDefTheory whileLemmasTheory

val _ = new_theory "parseProp1Def";

val stacklntmnls = Define `(stacklntmnls [] = []) /\
(stacklntmnls (((state sym itl),tree)::rst) = 
if isNonTmnlSym sym then (sym::stacklntmnls rst) else stacklntmnls rst)`

val stackltmnls = Define `(stackltmnls [] = []) /\
(stackltmnls (((state sym itl),tree)::rst) = 
if isTmnlSym sym then (sym::stackltmnls rst) else stackltmnls rst)`

val stacklsymtree = Define `(stacklsymtree [] = []) /\
(stacklsymtree (((state sym itl),tree)::rst) = 
     ((sym,tree)::stacklsymtree rst))`

(*The symbols and the trees corresponding to them are the same one. *)
val validStkSymTree = Define `(validStkSymTree [] = T) /\
(validStkSymTree (((state sym itl),tree)::rst) = (sym = ptree2Sym tree) /\ validStkSymTree rst)`

val prop1 = Define `prop1 g stl = 
validStkSymTree stl /\
(!s t.MEM (s,t) (stacklsymtree stl) ==> isNonTmnlSym s ==> validptree g t)`

val slst_append = store_thm ("slst_append", 
``!l1 l2.stacklsymtree (l1 ++ l2) = stacklsymtree l1 ++ stacklsymtree l2``,
Induct_on `l1` THEN SRW_TAC [] [stacklsymtree] THEN
Cases_on `h` THEN Cases_on `q` THEN SRW_TAC [] [stacklsymtree]
)

val slst_mem1 = store_thm ("slst_mem1", 
``!e l1 l2.MEM e (stacklsymtree l1) ==> MEM e (stacklsymtree (l1++l2))``,
Induct_on `l2` THEN
SRW_TAC [] [] THEN
METIS_TAC [slst_append, MEM_APPEND]
)

val slst_mem2 = store_thm ("slst_mem2", 
``!e.MEM e (stacklsymtree l2) ==> MEM e (stacklsymtree (l1++l2))``,
Induct_on `l1` THEN
SRW_TAC [] [] THEN
METIS_TAC [slst_append, MEM_APPEND, APPEND_ASSOC, APPEND]
)

val slst_mem3 = store_thm ("slst_mem3", 
``!e.MEM e (stacklsymtree (l1++l2)) ==> MEM e (stacklsymtree l1) \/ MEM e (stacklsymtree l2)``,
Induct_on `l1` THEN
SRW_TAC [] [] THEN
METIS_TAC [slst_append, MEM_APPEND, APPEND_ASSOC, APPEND])

val slst_mem4 = store_thm ("slst_mem4", 
``!l st pt.MEM (state sym itl, pt) l ==> (sym=ptree2Sym pt) ==> 
MEM  (sym, pt) (stacklsymtree l)``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [stacklsymtree] THEN
METIS_TAC [rgr_r9eq, slst_append, APPEND, CONS, APPEND_ASSOC])

val vst_append_distrib = store_thm ("vst_append_distrib",
``validStkSymTree (l1++l2) = validStkSymTree l1 /\ validStkSymTree l2``,
Induct_on `l1` THEN SRW_TAC [] [] THENL[
SRW_TAC [] [validStkSymTree],
Cases_on `h`  THEN Cases_on `q` THEN 
METIS_TAC [validStkSymTree]]
)

val prop1_append_distrib = store_thm ("prop1_append_distrib", 
``!l1 l2.prop1 g (l1++l2) = prop1 g l1 /\ prop1 g l2``,
SRW_TAC [] [prop1, EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [prop1] THEN 
METIS_TAC [slst_mem1, slst_mem2, slst_mem3, vst_append_distrib]
)


val prop1_r1 = store_thm ("prop1_r1", 
``!stl.prop1 g stl ==> (!l.?pfx sfx.(stl=pfx++l++sfx) ==> prop1 g l)``,
SRW_TAC [] [] THEN
Induct_on `stl` THEN
FULL_SIMP_TAC (srw_ss()) [prop1, stacklsymtree] THEN
METIS_TAC [prop1_append_distrib, CONS,APPEND, prop1]
)


val bdt_r0 = store_thm ("bdt_r0", 
``!p l.?x.(buildTree p l = SOME x) ==> ~(x=[])``,
Induct_on `p` THEN Induct_on `l` THEN FULL_SIMP_TAC (srw_ss()) [buildTree_def] THEN 
SRW_TAC [] [] THEN
METIS_TAC [NULL])




val bdt_r1 = store_thm ("bdt_r1",
``!l r g.
(buildTree p (REVERSE r) = SOME x) ==> (getSymbols x = REVERSE r)``,
SRW_TAC [] [buildTree_def] THEN
FULL_SIMP_TAC (srw_ss()) [Abbrev_def,LET_THM] THEN
Cases_on `take (LENGTH (REVERSE r)) (MAP (ptree2Sym o SND) p) = NONE` THEN
Cases_on `REVERSE r =
                THE (take (LENGTH (REVERSE r)) (MAP (ptree2Sym o SND) p))` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (MAP (ptree2Sym o SND) p) >= (LENGTH (REVERSE r))` by METIS_TAC [take_len] THEN
`REVERSE r = THE (take (LENGTH (REVERSE r)) (getSymbols (MAP SND p)))` by 
METIS_TAC [mapSymsptree] THEN
`take
  (LENGTH (THE
 (take (LENGTH (REVERSE r)) (MAP (ptree2Sym o SND) p))))
 (MAP SND p) = SOME x` by METIS_TAC [] THEN
`take (LENGTH (REVERSE r)) (MAP SND p) = SOME x` by METIS_TAC [] THEN
METIS_TAC [THE_DEF, take_getSyms]
)


val snd_elem = store_thm ("snd_elem", 
``!e p.MEM e (MAP SND p) ==> 
(?f.MEM (f,e) p)``,
Induct_on `p` THEN SRW_TAC [] [] THEN
Cases_on `h` THEN
METIS_TAC [SND])


val bdt_mem = store_thm ("bdt_mem", 
``(buildTree p l = SOME x) ==> 
(l=[]) \/ (!e.MEM e x ==> (?f.(MEM (f,e) p) ))``,
SRW_TAC [] [buildTree_def] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
Cases_on `take (LENGTH l) (MAP (ptree2Sym o SND) p) = NONE` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l = THE (take (LENGTH l) (MAP (ptree2Sym o SND) p))` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
` take (LENGTH (THE (take (LENGTH l) (MAP (ptree2Sym o SND) p))))
               (MAP SND p) = SOME x` by METIS_TAC [] THEN
`!e.MEM e x ==> MEM e (MAP SND p)` by METIS_TAC [option_r1, NOT_SOME_NONE, take_mem] THEN
`!e.MEM e (MAP SND p) ==> ?f.(MEM (f,e) p )` by METIS_TAC [snd_elem] THEN
SRW_TAC [] []
)




val bdt_nil = store_thm ("bdt_nil", 
``(buildTree p [] = SOME x') ==> (x'=[])``,
SRW_TAC [] [buildTree_def] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
Cases_on `take 0 (MAP (ptree2Sym o SND) p) = NONE` THEN
Cases_on `[] = THE (take 0 (MAP (ptree2Sym o SND) p))` THEN
FULL_SIMP_TAC (srw_ss()) [take_def] THEN
Induct_on `MAP SND p` THEN METIS_TAC [take1]
)


val addrule_r1 = store_thm ("addrule_r1",
``!p ru g.(MEM ru (rules g)) ==> prop1 g p ==> (addRule p ru = SOME x) ==> validptree g x``,
SRW_TAC [] [] THEN
Cases_on `ru` THEN
FULL_SIMP_TAC (srw_ss()) [addRule_def, LET_THM] THEN
Cases_on `buildTree p (REVERSE l) = NONE` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `(buildTree p (REVERSE l))` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`(getSymbols (THE (buildTree p (REVERSE l))) = REVERSE l)` by METIS_TAC [bdt_r1, THE_DEF] THEN
FULL_SIMP_TAC (srw_ss()) [prop1] THEN
Cases_on `(buildTree p (REVERSE l))` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [validptree] THEN
SRW_TAC [] [] THENL[
METIS_TAC [nonTmnlToStr_def, getSyms_rev, REVERSE_REVERSE],

`(l=[]) \/ (?f. (MEM (f,e) p))` 
by METIS_TAC [bdt_mem, rev_nil] THENL[
Cases_on `e`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [stacklsymtree, isNode_def, validptree, nonTmnlToStr_def, bdt_nil, getSymbols_def, MEM],

FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `f` THEN
`MEM (s',e) (stacklsymtree p)` by (SRW_TAC [] [] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [ptree2Sym_def, 
stacklsymtree, slst_append, rgr_r9eq] THENL[
METIS_TAC [isNode_def, nonTmnlToStr_def],
Cases_on `NTS (nonTmnlToStr n) = sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND_ASSOC, isNode_def, nonTmnlToStr_def]]) THEN

Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
METIS_TAC [isNode_def],
Cases_on `s'` THENL[

FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN 
SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [vst_append_distrib, validStkSymTree, ptree2Sym_def, validptree],
METIS_TAC [isNonTmnlSym_def]]]]])


val sgoto_nil = store_thm ("sgoto_nil",
``((sgoto g (item s' p::itl) (TS s) = []) ==> (sgoto g itl (TS s) = []))``,
SRW_TAC [] [sgoto_def] THEN
FULL_SIMP_TAC (srw_ss()) [nextState_def] THEN
Cases_on `p` THEN 
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [moveDot_def] THEN
Cases_on `h=TS s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [iclosure_nil,LENGTH_NIL, LENGTH, len_not_0]
)


val red_eq1 = store_thm ("red_eq1",
``~(TS sym IN followSetML g (NTS s)) ==>
(reduce g itl sym = reduce g (item s (q,[])::itl) sym)``,
SRW_TAC [] [reduce_def])


val red_eq2 = store_thm ("red_eq2",
``(TS sym IN followSetML g (NTS s)) ==>
((rule s q::reduce g itl sym) = reduce g (item s (q,[])::itl) sym)``,
SRW_TAC [] [reduce_def])

val reduce_append = store_thm ("reduce_append",
``reduce g (l1++l2) sym = reduce g l1 sym ++ reduce g l2 sym``,
Induct_on `l1` THEN Induct_on `l2` THEN SRW_TAC [] [reduce_def] THEN
Cases_on `h'` THEN Cases_on `p` THEN Cases_on `r` THEN
METIS_TAC [APPEND, CONS, reduce_def])


val reduce_mem = store_thm ("reduce_mem", 
``!sym itl out.(reduce g itl sym = out) ==> 
(!e.MEM e out ==> ?l r1.(e=rule l r1) /\ (MEM (item l (r1,[])) itl))``,
Induct_on `itl` THEN SRW_TAC [] [] THENL[
Cases_on `sym` THEN FULL_SIMP_TAC (srw_ss()) [reduce_def],
Cases_on `h` THEN Cases_on `p` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [doReduce_def, LET_THM, option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THENL[
Cases_on `(TS sym) IN (followSetML g (NTS s))` THENL[
`MEM e ((rule s q)::reduce g itl sym)` by METIS_TAC [red_eq2] THEN
`(e=rule s q) \/ (MEM e (reduce g itl sym))` by METIS_TAC [MEM] THENL[
Cases_on `e` THEN
METIS_TAC [reduce_def, red_eq1],
METIS_TAC [MEM]],
METIS_TAC [MEM , reduce_def]],
METIS_TAC [MEM , reduce_def]]])


val getstate_red = store_thm ("getstate_red", 
``!m itl sym g.(m = (sgoto g, reduce g)) ==> 
validItl g itl ==> (getState m itl sym = REDUCE r) ==> MEM r (rules g)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto g itl sym` THEN Cases_on `reduce g itl (sym2Str sym)` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `~(LENGTH t = 0)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `sym` THEN Induct_on `itl` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN `t=[]` by METIS_TAC [LENGTH_NIL] THEN
SRW_TAC [] [] THEN

`!e.MEM e [h] ==>
         ?l r1. (e = rule l r1) /\ MEM (item l (r1,[])) (h'::itl)` by METIS_TAC [reduce_mem] THEN
FULL_SIMP_TAC (srw_ss()) [reduce_mem,validItl_def, THE_DEF, APPEND, CONS, EVERY_DEF] THEN
`validItl g [h']` by METIS_TAC [APPEND, validItl_append] THEN
METIS_TAC [reduce_mem,validItl_def, APPEND, CONS, EVERY_DEF, MEM, validItl_append, rgr_r9eq, APPEND_NIL],

Cases_on `itemEqRuleList (h::t) (h'::t')` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`!e.MEM e (h'::t') ==>
         ?l r1. (e = rule l r1) /\ MEM (item l (r1,[])) itl` by METIS_TAC [reduce_mem]
THEN
FULL_SIMP_TAC (srw_ss()) [reduce_mem,validItl_def, THE_DEF, APPEND, CONS, EVERY_DEF] THEN
METIS_TAC [reduce_mem,validItl_def, APPEND, CONS, EVERY_DEF, MEM, validItl_append, rgr_r9eq, APPEND_NIL]]
)


val red_r1 = store_thm ("red_r1", 
``(doReduce m (sym::rst,stl,state s itl::csl) r = SOME (sl',stl',csl')) ==> 
?pfx sfx.(stl=pfx++sfx) /\ ?e.(stl'=[e]++sfx)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN  FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [popl]
)

val doReduce_vst = store_thm ("doReduce_vst",
``validStkSymTree stl ==> (doReduce m (sym::rst,stl,state s itl::csl) r = SOME (sl',stl',csl'))
==> validStkSymTree stl'``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [doReduce_def, LET_THM, option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN 
FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [],
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`stl' = (state (NTS (ruleLhs r))
             (FST m
                (stateItl
                   (HD (pop (state s itl::csl) (LENGTH (ruleRhs r)))))
                (NTS (ruleLhs r))),x)::pop stl (LENGTH (ruleRhs r))` by METIS_TAC [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
Cases_on `r` THEN 
FULL_SIMP_TAC (srw_ss()) [validStkSymTree, addRule_def, LET_THM] THEN
Cases_on `buildTree stl (REVERSE l)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`getSymbols x' = REVERSE l` by METIS_TAC [bdt_r1] THEN
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def] THEN
SRW_TAC [] [] THENL[
METIS_TAC [ptree2Sym_def, nonTmnlToStr_def],
METIS_TAC [popl,vst_append_distrib]]]
)

val list_pop = store_thm ("list_pop", 
``!l n.prop1 g l ==> prop1 g (pop l n)``,
SRW_TAC [] [] THEN
Q.ABBREV_TAC `x = pop l n` THEN
`(?pfx sfx.(l=pfx++sfx) /\ (sfx = x))` by METIS_TAC [popl] THEN
SRW_TAC [] [] THEN
METIS_TAC [prop1_append_distrib]
)

val getstate_r1 = store_thm ("getstate_r1", 
``!m itl sym.(getState m itl sym = GOTO (state s l)) ==> isTmnlSym sym ==> isTmnlSym s``,
SRW_TAC [] [] THEN
Cases_on `m` THEN 
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `q itl sym` THEN Cases_on `r itl (sym2Str sym)` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `LENGTH t` THEN FULL_SIMP_TAC (srw_ss()) [],
Cases_on `r itl (sym2Str sym) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
Cases_on `r itl (sym2Str sym) = []` THEN 
Cases_on `itemEqRuleList (h::t) (h'::t')`  THEN FULL_SIMP_TAC (srw_ss()) []]
)

val parse_csl_not_nil = store_thm ("parse_csl_not_nil",
``!m g.(m=slr g) ==> 
(parse m (sl, stl, (state s itl::csl)) = SOME (sl',stl',csl')) ==> ~(NULL csl')``,
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `getState m itl e` THEN
Cases_on `v1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD]  THEN
FULL_SIMP_TAC (srw_ss()) [slr_def, LET_THM] THEN 
Cases_on ` ?itl' sym.
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
                    || v20::v26::v27 -> T` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl r` THEN 
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`~(csl'=[])` by METIS_TAC [push_not_nil] THEN
METIS_TAC [list_l1],

FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl r` THEN 
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`~(csl'=[])` by METIS_TAC [push_not_nil] THEN
METIS_TAC [list_l1],


Cases_on `isNonTmnlSym e`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`~(csl'=[])` by METIS_TAC [push_not_nil] THEN
METIS_TAC [list_l1]])


val parse_csl_validStates = store_thm ("parse_csl_validStates",
``!m g.(m=slr g) ==> validStates g (state s itl::csl) 
==> (parse m (sl, stl, (state s itl::csl)) = SOME (sl',stl',csl')) ==> validStates g csl'``,
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `getState m itl e` THEN
Cases_on `v1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD]  THEN
FULL_SIMP_TAC (srw_ss()) [slr_def, LET_THM] THEN 
Cases_on ` ?itl' sym.
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
                    || v20::v26::v27 -> T` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[

FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl r` THEN 
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
`validStates   g        [(state (NTS (ruleLhs r))
               (FST m
                  (stateItl
                     (HD (pop (state s itl::csl) (LENGTH (ruleRhs r)))))
                  (NTS (ruleLhs r))))]` by (SRW_TAC [] [] THEN
SRW_TAC [] [validStates_def, validItl_def] THEN
`?h t.(pop (state s itl::csl) (LENGTH (ruleRhs r))) = h::t` by METIS_TAC [len_not_0, LENGTH_NIL] THEN
SRW_TAC [] [] THEN
`validStates g (h::t)` by METIS_TAC [validStates_pop, validStates_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def, stateItl_def] THEN
METIS_TAC [validItl_sgoto]) THEN
`csl' = push (pop (state s itl::csl) (LENGTH (ruleRhs r)))
            (state (NTS (ruleLhs r))
               (FST m
                  (stateItl
                     (HD (pop (state s itl::csl) (LENGTH (ruleRhs r)))))
                  (NTS (ruleLhs r))))` by METIS_TAC [] THEN SRW_TAC [] [push_def, validStates_def] THENL[
`?h t.(pop (state s itl::csl) (LENGTH (ruleRhs r))) = h::t` by METIS_TAC [len_not_0, LENGTH_NIL] THEN
SRW_TAC [] [] THEN
`validStates g (h::t)` by METIS_TAC [validStates_pop, validStates_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def, stateItl_def] THEN
METIS_TAC [validItl_sgoto],
METIS_TAC [validStates_pop, validStates_def]],

FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl r` THEN 
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
`validStates   g        [(state (NTS (ruleLhs r))
               (FST m
                  (stateItl
                     (HD (pop (state s itl::csl) (LENGTH (ruleRhs r)))))
                  (NTS (ruleLhs r))))]` by (SRW_TAC [] [] THEN
SRW_TAC [] [validStates_def, validItl_def] THEN
`?h t.(pop (state s itl::csl) (LENGTH (ruleRhs r))) = h::t` by METIS_TAC [len_not_0, LENGTH_NIL] THEN
SRW_TAC [] [] THEN
`validStates g (h::t)` by METIS_TAC [validStates_pop, validStates_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def, stateItl_def] THEN
METIS_TAC [validItl_sgoto]) THEN
`csl' = push (pop (state s itl::csl) (LENGTH (ruleRhs r)))
            (state (NTS (ruleLhs r))
               (FST m
                  (stateItl
                     (HD (pop (state s itl::csl) (LENGTH (ruleRhs r)))))
                  (NTS (ruleLhs r))))` by METIS_TAC [] THEN SRW_TAC [] [push_def, validStates_def] THENL[
`?h t.(pop (state s itl::csl) (LENGTH (ruleRhs r))) = h::t` by METIS_TAC [len_not_0, LENGTH_NIL] THEN
SRW_TAC [] [] THEN
`validStates g (h::t)` by METIS_TAC [validStates_pop, validStates_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def, stateItl_def] THEN
METIS_TAC [validItl_sgoto],
METIS_TAC [validStates_pop, validStates_def]],

Cases_on `isNonTmnlSym e` THEN 
`getState m itl e = getState (sgoto g, reduce g) itl e` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN 
Cases_on `sgoto g itl e` THEN Cases_on `reduce g itl (sym2Str e)` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[

Cases_on `LENGTH t'=0` THEN FULL_SIMP_TAC (srw_ss()) [],
`validItl g (h'::t')` by METIS_TAC [validItl_sgoto, validStates_def] THEN
METIS_TAC [validStates_def, push_def],
Cases_on `itemEqRuleList (h'::t') (h''::t'')` THEN FULL_SIMP_TAC (srw_ss()) []]])

(* 1.All the nonterminal symbols on top of the stack are the result of reduce operations *)
val prop1thm = store_thm ("prop1thm", 
``!m g.(m=slr g) ==> validStates g (state s itl::csl) ==> !stl.prop1 g stl
==> (parse m (sl, stl, (state s itl::csl)) = SOME (sl',stl',csl')) ==> (prop1 g stl')``,
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM, prop1] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `getState m itl e` THEN
Cases_on `v1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD]  THEN
FULL_SIMP_TAC (srw_ss()) [slr_def, LET_THM] THEN 
Cases_on ` ?itl' sym.
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
                    || v20::v26::v27 -> T` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
(* 8 subgoals *)
(* reduction action *)
(*1*) METIS_TAC [doReduce_vst],

(*2*) METIS_TAC [doReduce_vst],


(*3*)Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`m=(sgoto g, reduce g)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [getState_def, LET_THM, option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `sgoto g itl e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `(reduce g  itl (sym2Str e))` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `LENGTH t'` THEN SRW_TAC [] [],
Cases_on `e` THEN
SRW_TAC [] [validStkSymTree, ptree2Sym_def, tmnlSym_def, tmnlToStr_def] THEN
METIS_TAC [isNonTmnlSym_def],
Cases_on `itemEqRuleList (h'::t') (h''::t'')` THEN FULL_SIMP_TAC (srw_ss()) []],

(*4*)`?pfx sfx.(stl=pfx++sfx) /\ ?e.(stl'=[e]++sfx)` by METIS_TAC [red_r1] THEN
`prop1 g sfx` by METIS_TAC [prop1, prop1_append_distrib] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [doReduce_def, LET_THM, option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule (pfx ++ sfx) r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e'` THEN Cases_on `q` THEN
FULL_SIMP_TAC (srw_ss()) [stacklsymtree] THEN
METIS_TAC [prop1_append_distrib, prop1,getstate_red, addrule_r1, vst_append_distrib, validStates_def],

(*5*)`?pfx sfx.(stl=pfx++sfx) /\ ?e.(stl'=[e]++sfx)` by METIS_TAC [red_r1] THEN
`prop1 g sfx` by METIS_TAC [prop1, prop1_append_distrib] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [doReduce_def, LET_THM, option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule (pfx ++ sfx) r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop (state s itl::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e'` THEN Cases_on `q` THEN
FULL_SIMP_TAC (srw_ss()) [stacklsymtree] THEN
METIS_TAC [prop1_append_distrib, prop1,getstate_red, addrule_r1, vst_append_distrib, validStates_def],


(*6*)Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`m=(sgoto g, reduce g)` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [getState_def, LET_THM, option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `sgoto g itl e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `(reduce g itl (sym2Str e))` THEN FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `LENGTH t''` THEN FULL_SIMP_TAC (srw_ss()) [],

Cases_on `e` THEN
SRW_TAC [] [validStkSymTree, ptree2Sym_def, tmnlSym_def, tmnlToStr_def] THENL[
FULL_SIMP_TAC (srw_ss()) [stacklsymtree, slst_append] THEN
METIS_TAC [validptree],
METIS_TAC [isNonTmnlSym_def]],
Cases_on `itemEqRuleList (h'::t'') (h''::t''')` THEN FULL_SIMP_TAC (srw_ss()) []]])






val _ = export_theory ();