open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory pairTheory whileTheory

open symbolDefTheory grammarDefTheory boolLemmasTheory listLemmasTheory
parseTreeTheory yaccDefTheory whileLemmasTheory

val _ = new_theory "parseProp1Def";
val _ = diminish_srw_ss ["list EQ"];

val stacklntmnls = Define `(stacklntmnls [] = []) ∧
(stacklntmnls (((sym, itl),tree)::rst) = 
if isNonTmnlSym sym then (sym::stacklntmnls rst) else stacklntmnls rst)`;

val stackltmnls = Define `(stackltmnls [] = []) ∧
(stackltmnls (((sym, itl),tree)::rst) = 
if isTmnlSym sym then (sym::stackltmnls rst) else stackltmnls rst)`;

val stacklsymtree = Define `(stacklsymtree [] = []) ∧
(stacklsymtree (((sym, itl),tree)::rst) = 
     ((sym,tree)::stacklsymtree rst))`;

(*The symbols and the trees corresponding to them are the same one. *)
val validStkSymTree = Define 
`(validStkSymTree [] = T) ∧
(validStkSymTree (((sym, itl),tree)::rst) = 
(sym = ptree2Sym tree) ∧ validStkSymTree rst)`;

val validptree_inv = Define `validptree_inv g stl = 
validStkSymTree stl ∧
(∀s t.MEM (s,t) (stacklsymtree stl) ⇒ isNonTmnlSym s ⇒ validptree g t)`;

val slst_append = store_thm ("slst_append", 
``∀l1 l2.stacklsymtree (l1 ++ l2) = stacklsymtree l1 ++ stacklsymtree l2``,
Induct_on `l1` THEN SRW_TAC [] [stacklsymtree] THEN
Cases_on `h` THEN Cases_on `q` THEN SRW_TAC [] [stacklsymtree]
);

val slst_mem1 = store_thm ("slst_mem1", 
``∀e l1 l2.MEM e (stacklsymtree l1) ⇒ MEM e (stacklsymtree (l1++l2))``,
Induct_on `l2` THEN
SRW_TAC [] [] THEN
METIS_TAC [slst_append, MEM_APPEND]
);

val slst_mem2 = store_thm ("slst_mem2", 
``∀e.MEM e (stacklsymtree l2) ⇒ MEM e (stacklsymtree (l1++l2))``,
Induct_on `l1` THEN
SRW_TAC [] [] THEN
METIS_TAC [slst_append, MEM_APPEND, APPEND_ASSOC, APPEND]
);

val slst_mem3 = store_thm ("slst_mem3", 
``∀e.MEM e (stacklsymtree (l1++l2)) ⇒ MEM e (stacklsymtree l1) ∨ MEM e (stacklsymtree l2)``,
Induct_on `l1` THEN
SRW_TAC [] [] THEN
METIS_TAC [slst_append, MEM_APPEND, APPEND_ASSOC, APPEND]);

val slst_mem4 = store_thm ("slst_mem4", 
``∀l st pt.MEM ((sym, itl), pt) l ⇒ (sym=ptree2Sym pt) ⇒ 
MEM  (sym, pt) (stacklsymtree l)``,
Induct_on `l` THEN SRW_TAC [] [EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [stacklsymtree] THEN
METIS_TAC [rgr_r9eq, slst_append, APPEND, CONS, APPEND_ASSOC]);

val vst_append_distrib = store_thm ("vst_append_distrib",
``validStkSymTree (l1++l2) = validStkSymTree l1 ∧ validStkSymTree l2``,
Induct_on `l1` THEN SRW_TAC [] [] THENL[
SRW_TAC [] [validStkSymTree],
Cases_on `h`  THEN Cases_on `q` THEN 
METIS_TAC [validStkSymTree]]
);

val validptree_inv_append_distrib = store_thm ("validptree_inv_append_distrib", 
``∀l1 l2.validptree_inv g (l1++l2) = validptree_inv g l1 ∧ validptree_inv g l2``,
SRW_TAC [] [validptree_inv, EQ_IMP_THM] THEN
FULL_SIMP_TAC (srw_ss()) [validptree_inv] THEN 
METIS_TAC [slst_mem1, slst_mem2, slst_mem3, vst_append_distrib]
);


val validptree_inv_r1 = store_thm ("validptree_inv_r1", 
``∀stl.validptree_inv g stl ⇒ (∀l.∃pfx sfx.(stl=pfx++l++sfx) ⇒ validptree_inv g l)``,
SRW_TAC [] [] THEN
Induct_on `stl` THEN
FULL_SIMP_TAC (srw_ss()) [validptree_inv, stacklsymtree] THEN
METIS_TAC [validptree_inv_append_distrib, CONS,APPEND, validptree_inv]
);


val bdt_r0 = store_thm ("bdt_r0", 
``∀p l.∃x.(buildTree p l = SOME x) ⇒ ~(x=[])``,
Induct_on `p` THEN Induct_on `l` THEN FULL_SIMP_TAC (srw_ss()) [buildTree_def] THEN 
SRW_TAC [] [] THEN
METIS_TAC [NULL]);


val bdt_r1 = store_thm ("bdt_r1",
``∀l r g.
(buildTree p (REVERSE r) = SOME x) ⇒ (getSymbols x = REVERSE r)``,

SRW_TAC [] [buildTree_def] THEN
FULL_SIMP_TAC (srw_ss()) [Abbrev_def,LET_THM] THEN
Cases_on `take (LENGTH (REVERSE r)) (MAP (ptree2Sym o SND) p) = NONE` THEN
Cases_on `REVERSE r =
                THE (take (LENGTH (REVERSE r)) (MAP (ptree2Sym o SND) p))` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`LENGTH (MAP (ptree2Sym o SND) p) >= (LENGTH (REVERSE r))` 
			by METIS_TAC [take_len, option_CASES, LENGTH_REVERSE] THEN
`REVERSE r = THE (take (LENGTH (REVERSE r)) (getSymbols (MAP SND p)))` by 
METIS_TAC [mapSymsptree, LENGTH_REVERSE] THEN
`take
  (LENGTH (THE
 (take (LENGTH (REVERSE r)) (MAP (ptree2Sym o SND) p))))
 (MAP SND p) = SOME x` by METIS_TAC [LENGTH_REVERSE] THEN
`take (LENGTH (REVERSE r)) (MAP SND p) = SOME x` by METIS_TAC [LENGTH_REVERSE] THEN
METIS_TAC [THE_DEF, take_getSyms]
);


val snd_elem = store_thm ("snd_elem", 
``∀e p.MEM e (MAP SND p) ⇒ 
(∃f.MEM (f,e) p)``,
Induct_on `p` THEN SRW_TAC [] [] THEN
Cases_on `h` THEN
METIS_TAC [SND]);


val bdt_mem = store_thm ("bdt_mem", 
``(buildTree p l = SOME x) ⇒ 
(l=[]) ∨ (∀e.MEM e x ⇒ (∃f.(MEM (f,e) p) ))``,
SRW_TAC [] [buildTree_def] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
Cases_on `take (LENGTH l) (MAP (ptree2Sym o SND) p) = NONE` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l = THE (take (LENGTH l) (MAP (ptree2Sym o SND) p))` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
` take (LENGTH (THE (take (LENGTH l) (MAP (ptree2Sym o SND) p))))
               (MAP SND p) = SOME x` by METIS_TAC [] THEN
`∀e.MEM e x ⇒ MEM e (MAP SND p)` by METIS_TAC [option_r1, NOT_SOME_NONE, take_mem] THEN
`∀e.MEM e (MAP SND p) ⇒ ∃f.(MEM (f,e) p )` by METIS_TAC [snd_elem] THEN
SRW_TAC [] []
);


val bdt_nil = store_thm ("bdt_nil", 
``(buildTree p [] = SOME x') ⇒ (x'=[])``,
SRW_TAC [] [buildTree_def] THEN
FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
Cases_on `take 0 (MAP (ptree2Sym o SND) p) = NONE` THEN
Cases_on `[] = THE (take 0 (MAP (ptree2Sym o SND) p))` THEN
FULL_SIMP_TAC (srw_ss()) [take_def] THEN
Induct_on `MAP SND p` THEN METIS_TAC [take1]
);


val addrule_r1 = store_thm ("addrule_r1",
``∀p ru g.(MEM ru (rules g)) ⇒ validptree_inv g p ⇒ (addRule p ru = SOME x) ⇒ 
			    validptree g x``,

SRW_TAC [] [] THEN
Cases_on `ru` THEN
FULL_SIMP_TAC (srw_ss()) [addRule_def, LET_THM] THEN
Cases_on `buildTree p (REVERSE l) = NONE` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `(buildTree p (REVERSE l))` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`(getSymbols (THE (buildTree p (REVERSE l))) = REVERSE l)` 
			    by METIS_TAC [bdt_r1, THE_DEF] THEN
FULL_SIMP_TAC (srw_ss()) [validptree_inv] THEN
Cases_on `(buildTree p (REVERSE l))` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [validptree] THEN
SRW_TAC [] [] THEN1
METIS_TAC [getSyms_rev, REVERSE_REVERSE] THEN

`(l=[]) ∨ (∃f. (MEM (f,e) p))` 
by METIS_TAC [bdt_mem, rev_nil] THENL[
Cases_on `e`  THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [stacklsymtree, isNode_def, validptree,  bdt_nil, getSymbols_def, MEM],

FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `f` THEN
`MEM (q,e) (stacklsymtree p)` by (SRW_TAC [] [] THEN
Cases_on `e` THEN
FULL_SIMP_TAC (srw_ss()) [ptree2Sym_def, 
stacklsymtree, slst_append, rgr_r9eq] THENL[
METIS_TAC [isNode_def],
Cases_on `NTS n = sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [APPEND_ASSOC, isNode_def]]) THEN

Cases_on `e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1
METIS_TAC [isNode_def] THEN
Cases_on `q` THENL[

METIS_TAC [isNonTmnlSym_def],
FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN 
SRW_TAC [] [] THEN 
FULL_SIMP_TAC (srw_ss()) [vst_append_distrib, validStkSymTree, ptree2Sym_def, 
			  validptree]]]);


val sgoto_nil = store_thm ("sgoto_nil",
``((sgoto g (item s' p::itl) (TS s) = []) ⇒ (sgoto g itl (TS s) = []))``,
SRW_TAC [] [sgoto_def] THEN
FULL_SIMP_TAC (srw_ss()) [nextState_def] THEN
Cases_on `p` THEN 
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [moveDot_def] THEN
Cases_on `h=TS s` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [iclosure_nil,LENGTH_NIL, LENGTH, len_not_0]);



val red_r1 = store_thm ("red_r1", 
``(doReduce m (sym::rst,stl,(s, itl)::csl) r = SOME (sl',stl',csl')) ⇒ 
∃pfx sfx.(stl=pfx++sfx) ∧ ∃e.(stl'=[e]++sfx)``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN  FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `FST m (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
               (NTS (ruleLhs r)) =
             []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [popl]);


val doReduce_vst = store_thm ("doReduce_vst",
``validStkSymTree stl ⇒ 
(doReduce m (sym::rst,stl,(s, itl)::csl) r = SOME (sl',stl',csl'))
⇒ validStkSymTree stl'``,
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [doReduce_def, LET_THM, option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN 
FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [],
Cases_on `addRule stl r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `FST m (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
               (NTS (ruleLhs r)) =
             []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
`stl' = ((NTS (ruleLhs r),
            FST m (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
              (NTS (ruleLhs r))),x)::pop stl (LENGTH (ruleRhs r))` by METIS_TAC [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
Cases_on `r` THEN 
FULL_SIMP_TAC (srw_ss()) [validStkSymTree, addRule_def, LET_THM] THEN
Cases_on `buildTree stl (REVERSE l)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
`getSymbols x' = REVERSE l` by METIS_TAC [bdt_r1] THEN
FULL_SIMP_TAC (srw_ss()) [ruleLhs_def] THEN
SRW_TAC [] [] THENL[
METIS_TAC [ptree2Sym_def],
METIS_TAC [popl,vst_append_distrib]]]
);

val list_pop = store_thm ("list_pop", 
``∀l n.validptree_inv g l ⇒ validptree_inv g (pop l n)``,
SRW_TAC [] [] THEN
Q.ABBREV_TAC `x = pop l n` THEN
`(∃pfx sfx.(l=pfx++sfx) ∧ (sfx = x))` by METIS_TAC [popl] THEN
SRW_TAC [] [] THEN
METIS_TAC [validptree_inv_append_distrib]
);

(*
val getstate_r1 = store_thm ("getstate_r1", 
``∀m itl sym.(getState m itl sym = GOTO l) ⇒ isTmnlSym sym ⇒ isTmnlSym s``,
SRW_TAC [] [] THEN
Cases_on `m` THEN 
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `q itl sym` THEN Cases_on `r itl (symToStr sym)` THEN
FULL_SIMP_TAC (srw_ss()) [] THENL[
Cases_on `LENGTH t` THEN FULL_SIMP_TAC (srw_ss()) [],
Cases_on `r itl (symToStr sym) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [],
Cases_on `r itl (symToStr sym) = []` THEN 
Cases_on `itemEqRuleList (h::t) (h'::t')`  THEN FULL_SIMP_TAC (srw_ss()) []]
)
*)

val parse_csl_not_nil = store_thm ("parse_csl_not_nil",
``∀m g.(m=slrmac g) ⇒ 
(parse m (sl, stl, ((s, itl)::csl)) = SOME (sl',stl',csl'))
⇒ ~(NULL csl')``,

FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, 
 pairTheory.FORALL_PROD] THEN
Cases_on `getState m itl e` THEN
Cases_on `v1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD]  THEN
FULL_SIMP_TAC (srw_ss()) [slrmac_def, LET_THM] THEN 
Cases_on `∃pfx itl' sym.
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
      FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
      Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl r` THEN 
      Cases_on `FST m (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
               (NTS (ruleLhs r)) =
             []` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `~(csl'=[])` by METIS_TAC [push_not_nil] THEN
      METIS_TAC [list_l1]);


val sgoto_exp = store_thm ("sgoto_exp", 
``∀g.(slrmac g = SOME m) ⇒ (m= (sgoto g, reduce g))``,
SRW_TAC [] [slrmac_def, LET_THM]);



val parse_csl_validStates = store_thm ("parse_csl_validStates",
``∀m g.(m=slrmac g) ⇒ validStates g ((s, itl)::csl) 
⇒ (parse m (sl, stl, ((s, itl)::csl)) = SOME (sl',stl',csl'))
⇒ validStates g csl'``,

FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `getState m itl e` THEN
Cases_on `v1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD]  THEN
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
`SOME (sgoto g,reduce g) = SOME m` by METIS_TAC [NOT_SOME_NONE] THEN
SRW_TAC [][] THEN

((FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
Cases_on `isNonTmnlSym e` THEN Cases_on `addRule stl r` THEN 
Cases_on `sgoto g (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
               (NTS (ruleLhs r)) =
             []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
`validStates   g        [((NTS (ruleLhs r)),
               (sgoto g
                  (SND
                     (HD (pop ((s, itl)::csl) (LENGTH (ruleRhs r)))))
                  (NTS (ruleLhs r))))]` by (SRW_TAC [] [] THEN
SRW_TAC [] [validStates_def, validItl_def] THEN
`∃h t.(pop ((s, itl)::csl) (LENGTH (ruleRhs r))) = h::t` 
by METIS_TAC [len_not_0, LENGTH_NIL] THEN
SRW_TAC [] [] THEN
`validStates g (h::t)` by METIS_TAC [validStates_pop, validStates_def] THEN
Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
METIS_TAC [validItl_sgoto]) THEN
`csl' = push (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))
            (NTS (ruleLhs r),
             sgoto g (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
               (NTS (ruleLhs r)))` by METIS_TAC [] THEN SRW_TAC [] [push_def, validStates_def]
THENL[
      `∃h t.(pop ((s, itl)::csl) (LENGTH (ruleRhs r))) = h::t` by METIS_TAC [len_not_0, LENGTH_NIL] THEN
      SRW_TAC [] [] THEN
      `validStates g (h::t)` by METIS_TAC [validStates_pop, validStates_def] THEN
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [validStates_def] THEN
      METIS_TAC [validItl_sgoto],
      METIS_TAC [validStates_pop, validStates_def]]) ORELSE

(FULL_SIMP_TAC (srw_ss()) [push_def, validStates_def, getState_def,
LET_THM] THEN
Cases_on `sgoto g itl e` THEN 
Cases_on `reduce g itl (ts2str e)` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
(Cases_on `LENGTH t = 0` THEN FULL_SIMP_TAC (srw_ss()) []) THEN1
METIS_TAC [validItl_sgoto] THEN
Cases_on `itemEqRuleList (h::t) (h'::t')` THEN FULL_SIMP_TAC (srw_ss()) [])));


(* 1.All the nonterminal symbols on top of the stack are the result of reduce operations *)
val validptree_invthm = store_thm ("validptree_invthm", 
``∀m g.(m=slrmac g) ⇒ validStates g ((s, itl)::csl) ⇒ 
   ∀stl.validptree_inv g stl ⇒
   (parse m (sl, stl, ((s, itl)::csl)) = SOME (sl',stl',csl')) ⇒ 
   (validptree_inv g stl')``,

FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM, validptree_inv] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, 
				    pairTheory.FORALL_PROD] THEN
Cases_on `getState m itl e` THEN
Cases_on `v1` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [option_case_rwt, list_case_rwt, 
				    pairTheory.FORALL_PROD]  THEN
FULL_SIMP_TAC (srw_ss()) [slrmac_def, LET_THM] THEN1
(* 6 subgoals *)
(* reduction action *)
(*1*) METIS_TAC [doReduce_vst] THEN1

(*2*) METIS_TAC [doReduce_vst] THEN1


(*3*)
(Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [getState_def, LET_THM, 
				    option_case_rwt, list_case_rwt, 
				    pairTheory.FORALL_PROD] THEN
Cases_on `sgoto g itl e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `(reduce g  itl (ts2str e))` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
(Cases_on `e` THEN
SRW_TAC [] [validStkSymTree, ptree2Sym_def, tmnlSym_def,ts2str_def] THEN
METIS_TAC [isNonTmnlSym_def])) THENL[

(*4*)
`∃pfx sfx.(stl=pfx++sfx) ∧ ∃e.(stl'=[e]++sfx)` by METIS_TAC [red_r1] THEN
`validptree_inv g sfx` by METIS_TAC [validptree_inv, 
				     validptree_inv_append_distrib] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [doReduce_def, LET_THM, option_case_rwt, 
				    list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN

Cases_on `sgoto g (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
               (NTS (ruleLhs r)) =
             []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule (pfx ++ sfx) r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN 
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e'` THEN Cases_on `q` THEN
FULL_SIMP_TAC (srw_ss()) [stacklsymtree] THEN
SRW_TAC [][] THEN
`validptree_inv g (pfx++sfx)` by
(FULL_SIMP_TAC (srw_ss()) [validptree_inv] THEN
METIS_TAC [validptree_inv_append_distrib, validptree_inv]) THEN
METIS_TAC [validptree_inv_append_distrib, validptree_inv,getstate_red, 
	   addrule_r1, vst_append_distrib, validStates_def],

(*5*)`∃pfx sfx.(stl=pfx++sfx) ∧ ∃e.(stl'=[e]++sfx)` by METIS_TAC [red_r1] THEN
`validptree_inv g sfx` by METIS_TAC [validptree_inv, validptree_inv_append_distrib] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [doReduce_def, LET_THM, option_case_rwt, list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `sgoto g (SND (HD (pop ((s,itl)::csl) (LENGTH (ruleRhs r)))))
               (NTS (ruleLhs r)) =
             []` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `addRule (pfx ++ sfx) r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `pop ((s, itl)::csl) (LENGTH (ruleRhs r)) = []` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `e'` THEN Cases_on `q` THEN
FULL_SIMP_TAC (srw_ss()) [stacklsymtree] THEN
METIS_TAC [validptree_inv_append_distrib, validptree_inv,getstate_red, 
	   addrule_r1, vst_append_distrib, validStates_def],


(*6*)
Cases_on `isNonTmnlSym e` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [getState_def, LET_THM, option_case_rwt, 
				    list_case_rwt, pairTheory.FORALL_PROD] THEN
Cases_on `e` THEN
SRW_TAC [] [validStkSymTree, ptree2Sym_def, tmnlSym_def] THEN
(FULL_SIMP_TAC (srw_ss()) [stacklsymtree, slst_append] THEN
METIS_TAC [validptree])]);

val _ = export_theory ();