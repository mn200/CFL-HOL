open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory rich_listTheory
pairTheory

open symbolDefTheory grammarDefTheory boolLemmasTheory listLemmasTheory
setLemmasTheory whileLemmasTheory parseTreeTheory followSetDefTheory
yaccDefTheory parseProp1DefTheory parseProp2DefTheory
lrGrammarDefTheory validItemInvTheory macStepTheory

fun Store_thm(s,t,tac) = (store_thm(s,t,tac) before export_rewrites [s])


val _ = augment_srw_ss [rewrites [rich_listTheory.IS_PREFIX_NIL]]

val _ = new_theory "complDef"

val _ = diminish_srw_ss ["list EQ"];

val stackSyms_NIL = Store_thm(
  "stackSyms_NIL",
  ``stackSyms [] = []``,
  SRW_TAC [][stackSyms_def]);


Definition takesSteps_def:
  (takesSteps 0 f g s0 s ⇔ s0 = s) /\
  (takesSteps (SUC n) f g s0 s ⇔
    ¬g s0 ∧ ∃s'. f s0 = SOME s' ∧ takesSteps n f g s' s)
End
val takesSteps = takesSteps_def


val takesSteps_mwhile = store_thm(
  "takesSteps_mwhile",
``!n f g s0 s.takesSteps n f g s0 s /\ (g s) ==>
     (mwhile (\s. ~g s) f s0 =  SOME (SOME s))``,
Induct_on `n` THEN
SRW_TAC [][takesSteps] THEN
ONCE_REWRITE_TAC [mwhile_COND] THEN SRW_TAC [][]);

val getStateReduce = store_thm ("getStateReduce",
``!itl h rhs.
     (auggr g st eof = SOME ag) ==> (slrmac ag = SOME m) ==>
     validItl ag itl ==>
     (trans ag (initItems ag (rules ag),pfx) = SOME itl) ==>
     MEM (item lhs (rhs,([]:(α,β)symbol list))) itl ==>
     isTmnlSym h ==>
     h IN (followSet ag (NTS lhs))
   ==>
    (getState m itl h = REDUCE (rule lhs rhs))``,

SRW_TAC [] [] THEN
`m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM,slrmac_def] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`,`itl`,`h`] MP_TAC) THEN
SRW_TAC [][] THEN
Cases_on `sgoto ag itl h` THEN
Cases_on `reduce ag itl (ts2str h)` THEN FULL_SIMP_TAC (srw_ss()) []
 THENL[
       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
       FULL_SIMP_TAC (srw_ss()) [rgr_r9eq] THEN
       SRW_TAC [][]THEN
       FULL_SIMP_TAC (srw_ss()) [reduce_append,reduce_def] THEN
       Cases_on `h` THEN
       FULL_SIMP_TAC (srw_ss()) [ts2str_def,followSetEq,isNonTmnlSym_def,isTmnlSym_def] THEN
       Cases_on `TS t IN followSet ag (NTS lhs)` THEN
       FULL_SIMP_TAC (srw_ss()) [lreseq],

       METIS_TAC [reduce_not_mem],

       Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [],

       METIS_TAC [reduce_not_mem]
       ]);


val getStateGotoValidItl = store_thm ("getStateGotoValidItl",
``∀(itl :(α, β) state) (l :(α, β) state).
   (getState m itl ((TS s):(α,β) symbol) = GOTO l) ==>
   validItl ag itl ==>
   (auggr g st eof = SOME ag) ==> (slrmac ag = SOME m) ==>
   validItl ag l``,

SRW_TAC [][] THEN
`m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM, ts2str_def] THEN
Cases_on `sgoto (ag :(α, β) grammar) (itl :(α, β) state) (TS (s :β))` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `reduce ag itl s` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][]
THENL[
      Cases_on `t` THEN
      FULL_SIMP_TAC (srw_ss()) [],

      SRW_TAC [] [] THEN
      METIS_TAC [validItl_sgoto],

      BasicProvers.NORM_TAC (srw_ss()) []
      ]);


val reduce_not_nil = store_thm ("reduce_not_nil",
``!itl.isTmnlSym h ==>
  ~(reduce ag itl (ts2str h) = []) ==>
  ?N r1.MEM (item N (r1,[])) itl /\
     h IN followSet ag (NTS N)``,

Induct_on `itl` THEN SRW_TAC [] [reduce_def] THEN
Cases_on `h'` THEN
Cases_on `p` THEN
Cases_on `r` THEN
Cases_on `h` THEN
FULL_SIMP_TAC (srw_ss()) [reduce_def, ts2str_def, isTmnlSym_def]
THENL[
      Cases_on `TS t IN followG ag [] n`
      THENL[
	    METIS_TAC [followSetEq],

            Cases_on `TS t ∈ followSet ag (NTS n)` THEN
            FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [followSetEq]
	    ],

      METIS_TAC []
      ]);

val getStateGotoExists = store_thm ("getStateGotoExists",
``(slrmac ag = SOME m) ==>
  validItl ag itl ==>
  (trans ag (initItems ag (rules ag),pfx) = SOME itl) ==>
  isTmnlSym h ==>
  MEM (item N (r1,h::rst)) itl ==>
  ?l.getState m itl h = GOTO l``,
SRW_TAC [] [] THEN
`m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp]  THEN
FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
Cases_on `sgoto ag itl h` THEN
Cases_on `reduce ag itl (ts2str h)` THEN
SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, rgr_r9eq] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [md_append, moveDot_def] THEN
      METIS_TAC [MEM_APPEND, MEM, iclosure_nil],

      FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, rgr_r9eq] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [md_append, moveDot_def] THEN
      METIS_TAC [MEM_APPEND, MEM, iclosure_nil],

      FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def, rgr_r9eq] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [md_append, moveDot_def] THEN
      METIS_TAC [MEM_APPEND, MEM, iclosure_nil],

      FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
      FULL_SIMP_TAC (srw_ss()) [slrmac_def,LET_THM] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`pfx`,`itl`,`h`] MP_TAC) THEN
      SRW_TAC [][] THEN
      Cases_on `t'` THEN SRW_TAC [][],

      FULL_SIMP_TAC (srw_ss()) [reduce_def] THEN
      Cases_on `?N r1.MEM (item N (r1,[])) itl /\
                 h IN followSet ag (NTS N)`
      THENL[
	    METIS_TAC [rgr_r9eq, validItl_append, validItl_def, slrmacNotValid, APPEND_NIL],
	    METIS_TAC [reduce_not_nil, NOT_CONS_NIL]
	    ]
      ]
);


val takesStepsManyToOne1 = store_thm
("takesStepsManyToOne1",
``!n s0 s.takesSteps (SUC n) f g s0 s ==>
  ?s'.takesSteps n f g s0 s' /\ takesSteps (SUC 0) f g s' s``,
Induct_on `n` THEN SRW_TAC [] []THEN
FULL_SIMP_TAC (srw_ss()) [ADD1, takesSteps] THEN
`1=SUC 0` by DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [ADD1, takesSteps]);

val takesStepsManyToOne2 = store_thm
("takesStepsManyToOne2",
``!n s0 s s'.  takesSteps n f g s0 s' /\ takesSteps (SUC 0) f g s' s ==>
takesSteps (SUC n) f g s0 s``,
Induct_on `n` THEN SRW_TAC [] []THEN
`takesSteps (SUC 0) f g s' s` by FULL_SIMP_TAC (arith_ss) [] THEN
FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
METIS_TAC [takesStepsManyToOne1])

val takesStepsManyToOne = store_thm
("takesStepsManyToOne",
``!n s0 s.takesSteps (SUC n) f g s0 s =
  ?s'.takesSteps n f g s0 s' /\ takesSteps (SUC 0) f g s' s``,
METIS_TAC [takesStepsManyToOne1, takesStepsManyToOne2])

val takesStepsOneToMany1 = store_thm
("takesStepsOneToMany1",
``!n s0 s.takesSteps (SUC n) f g s0 s ==>
  ?s'.takesSteps (SUC 0) f g s0 s' /\ takesSteps n f g s' s``,
Induct_on `n` THEN SRW_TAC [] []THEN
FULL_SIMP_TAC (srw_ss()) [ADD1, takesSteps] THEN
`1=SUC 0` by DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [ADD1, takesSteps]);


val takesStepsOneToMany2 = store_thm
("takesStepsOneToMany2",
``!n s0 s s'.takesSteps (SUC 0) f g s0 s' /\ takesSteps n f g s' s
==> takesSteps (SUC n) f g s0 s``,
Induct_on `n` THEN SRW_TAC [] []THEN
FULL_SIMP_TAC (srw_ss()) [ADD1, takesSteps] THEN
`takesSteps (SUC 0) f g s0 s'` by FULL_SIMP_TAC (arith_ss) [] THEN
FULL_SIMP_TAC (srw_ss()) [takesSteps]);


val takesStepsOneToMany = store_thm
("takesStepsOneToMany",
``!n s0 s.takesSteps (SUC n) f g s0 s =
  ?s'.takesSteps (SUC 0) f g s0 s' /\ takesSteps n f g s' s``,
METIS_TAC [takesStepsOneToMany1, takesStepsOneToMany2]);


val takesStepsAdd = store_thm
("takesStepsAdd",
``!n n' s0 s' s''.takesSteps n f g s0 s' ==>
  takesSteps n' f g s' s'' ==>
  takesSteps (n+n') f g s0 s''``,
Induct_on `n'` THEN SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [takesSteps],

      Cases_on `n` THEN
      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      `takesSteps (SUC n'') f g s0 s'` by SRW_TAC [] [takesSteps] THEN
      `?sx.takesSteps (SUC 0) f g s0 sx /\ takesSteps n'' f g sx s'` by METIS_TAC [takesStepsOneToMany] THEN
      `takesSteps (SUC 0) f g s' s''''` by SRW_TAC [] [takesSteps] THEN
      `takesSteps (SUC n') f g s' s''` by  METIS_TAC [takesStepsOneToMany] THEN
      `takesSteps (SUC (SUC n'')) f g s0 s''''`
	  by METIS_TAC [takesStepsManyToOne] THEN
      `takesSteps ((SUC (SUC n'')) + n') f g s0 s''` by METIS_TAC [] THEN
      FULL_SIMP_TAC (arith_ss) [ADD1]
      ]);



val parseVldStkSymTree = store_thm(
"parseVldStkSymTree",
``!stl sl e csl.validStkSymTree stl ==>
(parse m (sl,stl,(e::csl)) = SOME (sl',stl',csl')) ==>
validStkSymTree stl'``,
Induct_on `stl` THEN SRW_TAC [] [validStkSymTree_def]
THENL[
      Cases_on `e` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t` THEN
      Cases_on `getState m r h` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    METIS_TAC [doReduce_vst, APPEND, validStkSymTree_def],

	    METIS_TAC [doReduce_vst, APPEND, validStkSymTree_def],

	    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def, push_def] THEN
	    METIS_TAC [validStkSymTree_def, ptree2Sym_def, tmnlSym_def,ts2str_def]
	    ],

      Cases_on `e` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t` THEN
      Cases_on `getState m r h'` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[

	    METIS_TAC [doReduce_vst, APPEND, validStkSymTree_def],

	    METIS_TAC [doReduce_vst, APPEND, validStkSymTree_def],

	    Cases_on `h'` THEN FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def, push_def] THEN
	    METIS_TAC [validStkSymTree_def, ptree2Sym_def, tmnlSym_def,ts2str_def]
	    ]
      ]);

val takesStepsValidStkSymTree = store_thm
("takesStepsValidStkSymTree",
``!n sl stl e csl.takesSteps n (parse m)
             (exitCond (eof,NTS (startSym g)))
             (sl,stl,e::csl)
             (sl',stl',csl') ==>
	     validStkSymTree stl ==>
	     (slrmac ag = SOME m) ==>
             validStkSymTree stl'``,
Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] [validStkSymTree_def] THEN
Cases_on `n` THEN
SRW_TAC [] []
THENL[

      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      METIS_TAC [parseVldStkSymTree],


      `takesSteps (SUC 0) (parse m) (exitCond (eof,NTS (startSym g)))
            (sl,stl,e::csl) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `validStkSymTree q'`
      THENL[
	    SRW_TAC [] []THEN
	    Cases_on `e` THEN
	    `~NULL r'` by METIS_TAC [parse_csl_not_nil]  THEN
	    Cases_on `r'` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `h` THEN SRW_TAC [] [] THEN
	    METIS_TAC [],

	    METIS_TAC [parseVldStkSymTree]
	    ]]);


val takesStepsValidStates = store_thm
("takesStepsValidStates",
``!n sl stl e csl.takesSteps n (parse m)
             (exitCond (eof,NTS (startSym g)))
             (sl,stl,e::csl)
             (sl',stl',csl') ==>
	     validStates ag (e::csl) ==>
	     (slrmac ag = SOME m) ==>
             validStates ag csl'``,
Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] [validStates_def] THEN
Cases_on `n` THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      Cases_on `e` THEN
      METIS_TAC [parse_csl_validStates],

      `takesSteps (SUC 0) (parse m) (exitCond (eof,NTS (startSym g)))
            (sl,stl,e::csl) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `validStates ag r'`
      THENL[
	    SRW_TAC [] [] THEN
	    Cases_on `e` THEN
	    `~NULL r'` by METIS_TAC [parse_csl_not_nil]  THEN
	    Cases_on `r'` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `h` THEN SRW_TAC [] [] THEN
	    METIS_TAC [],

	    Cases_on `e` THEN
	    METIS_TAC [parse_csl_validStates]
	    ]
      ]);


val doRedCslEqStl = store_thm(
"doRedCslEqStl",
``(doReduce m (h::sl,stl,MAP FST stl ++[e]) r' = SOME (sl',stl',csl')) ==>
      (getState m r h = REDUCE r') ==>
      (csl' = MAP FST stl' ++ [e])``,

Cases_on `stl` THEN
SRW_TAC [] []
THENL[

      Cases_on `e` THEN
      FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
      Cases_on `r'` THEN FULL_SIMP_TAC (srw_ss()) [ruleLhs_def, ruleRhs_def] THEN
      Cases_on `addRule ([] :(((α, γ) symbol # (α, β) state) # (α, β) ptree) list)
 (rule n l)` THEN
      FULL_SIMP_TAC (srw_ss()) [push_def]  THEN
      `csl' = (NTS n,FST m (SND (HD (pop [(q,r'')] (LENGTH l)))) (NTS n))::
              pop [(q,r'')] (LENGTH l)` by METIS_TAC [] THEN
      SRW_TAC [] [] THEN
      Cases_on `l` THEN SRW_TAC [] [pop_def] THEN
      FULL_SIMP_TAC (srw_ss()) [pop_def] THEN
      FULL_SIMP_TAC (arith_ss) [],


      Cases_on `h'` THEN Cases_on `q` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
      Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def] THEN
      Cases_on `addRule (((q',r'''),r'')::t) r'` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `FST m
                        (SND
                           (HD
                              (pop ((q',r''')::(MAP FST t ++ [e]))
                                 (LENGTH (ruleRhs r')))))
                        (NTS (ruleLhs r')) =
                      []` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `pop ((q',r''')::(MAP FST t ++ [e]))
                     (LENGTH (ruleRhs r')) = []` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `r'` THEN
      FULL_SIMP_TAC (srw_ss()) [ruleRhs_def, ruleLhs_def, LET_THM, push_def] THEN
      `csl' = (NTS n,
           FST m (SND (HD (pop ((q',r''')::(MAP FST t ++ [e])) (LENGTH l))))
             (NTS n))::pop ((q',r''')::(MAP FST t ++ [e])) (LENGTH l)` by METIS_TAC [] THEN
      SRW_TAC [] [] THEN
      `MAP FST (pop (((q',r'''),r'')::t) (LENGTH l)) ++ [e]
       = pop (MAP FST (((q',r'''),r'')::t)) (LENGTH l) ++ [e]`
	  by METIS_TAC [map_pop] THEN
      SRW_TAC [] []THEN
      `LENGTH (((q',r'''),r'')::t) >= LENGTH l` by METIS_TAC [addrule_len] THEN
      `((q',r''')::(MAP FST t ++ [e])) = ([(q',r''')]++MAP FST t) ++ [e]` by FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH ([((q',r'''),r'')]++t) >= LENGTH l`
	  by (FULL_SIMP_TAC (srw_ss()) [] THEN
	      FULL_SIMP_TAC (arith_ss) []) THEN
      `((q',r''')::MAP FST t) = ([(q',r''')]++MAP FST t)` by FULL_SIMP_TAC (srw_ss()) [] THEN
      `LENGTH ([(q',r''')] ++ MAP FST t) >= LENGTH l` by METIS_TAC [LENGTH_MAP, pairTheory.FST, MAP_APPEND, MAP] THEN
      METIS_TAC [popAdd]
      ]);

val parseCslStlEq = store_thm (
"parseCslStlEq",
``(parse m (sl,stl,MAP FST stl ++ [e])
   = SOME (sl',stl',csl')) ==>
    (csl' = MAP FST stl' ++ [e])``,

Cases_on `stl` THEN SRW_TAC  [] []
THENL[
      Cases_on `e` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t` THEN
      Cases_on `getState m r h` THEN FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    `[(q,r)] = MAP FST ([]:(((α,β)symbol#(α,β)state)#(α,β)ptree) list) ++
            [(q,r)]` by SRW_TAC [] [] THEN
	    METIS_TAC [doRedCslEqStl,APPEND],

	    `[(q,r)] = MAP FST ([]:(((α,β)symbol#(α,β)state)#(α,β)ptree) list) ++
            [(q,r)]` by SRW_TAC [] [] THEN
	    METIS_TAC [doRedCslEqStl,APPEND],

	    Cases_on `h` THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def, push_def] THEN
	    `csl' = [(TS t,l); (q,r)]` by METIS_TAC [] THEN
	    SRW_TAC [] []
	    ],


      Cases_on `h` THEN Cases_on `q` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t'` THEN
      Cases_on `getState m r' h` THEN FULL_SIMP_TAC (srw_ss()) []
      THENL[

	    `(q',r')::(MAP FST t ++ [e]) = (MAP FST (((q',r'),r)::t)) ++ [e]` by SRW_TAC [] [] THEN
	    METIS_TAC [doRedCslEqStl,APPEND],

	    `(q',r')::(MAP FST t ++ [e]) = (MAP FST (((q',r'),r)::t)) ++ [e]` by SRW_TAC [] [] THEN
	    METIS_TAC [doRedCslEqStl,APPEND],

	    Cases_on `h` THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def, push_def] THEN
	    `csl' = (TS t',l)::(q',r')::(MAP FST t ++ [e])` by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [tmnlSym_def] THEN
	    `stl' = ((TS t',l),Leaf t')::((q',r'),r)::t` by METIS_TAC [ts2str_def] THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    ]
      ]);


val takesStepsCslStlEq = store_thm(
"takesStepsCslStlEq",
``!n sl stl e csl.takesSteps n (parse m)
             (exitCond (eof,NTS (startSym g)))
             (sl,stl,MAP FST stl++[e])
             (sl',stl',csl') ==>
	     (csl' = MAP FST stl' ++ [e])``,
Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] []  THEN
Cases_on `n` THEN
SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      Cases_on `e` THEN
      METIS_TAC [parseCslStlEq],

      `takesSteps (SUC 0) (parse m) (exitCond (eof,NTS (startSym g)))
            (sl,stl,MAP FST stl++[e]) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `r'=MAP FST q'++[e]` THEN
      SRW_TAC [] [] THEN
      METIS_TAC [parseCslStlEq]
      ]);


val parseValidStlStack = store_thm
("parseValidStlStack",
``validStlItemsStack stl csl ==>
  (slrmac g = SOME m) ==>
  (csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
  (parse m (sl,stl,csl) = SOME (sl',stl',csl')) ==>
  validStlItemsStack stl' csl'``,

Cases_on `stl` THEN
SRW_TAC [] []
THENL[

      FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
      Q.ABBREV_TAC `inis = initItems ag (rules ag)` THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t` THEN
      Cases_on `getState m inis h` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
	    Cases_on `r` THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleRhs_def, ruleLhs_def] THEN
	    Cases_on `addRule ([]:((((α,β)symbol#(α,β)state)#(α,β)ptree) list)) (rule n l)` THEN
	    Cases_on `pop [(NTS st,inis)] (LENGTH l) = []` THEN
	    Cases_on `FST m (SND (HD (pop [(NTS st,inis)] (LENGTH l))))
                        (NTS n) =
                      []` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [pop_def] THEN
	    SRW_TAC [] [push_def] THEN
	    `m=(sgoto g, reduce g)`by METIS_TAC [sgoto_exp] THEN
	    SRW_TAC [] [validStlItemsStack_def, push_def] THEN
	    METIS_TAC [APPEND_NIL, validStlItems_sgoto_gen],

	    FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
	    Cases_on `r` THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleRhs_def, ruleLhs_def] THEN
	    Cases_on `addRule ([]:((((α,β)symbol#(α,β)state)#(α,β)ptree) list)) (rule n l)` THEN
	    Cases_on `pop [(NTS st,inis)] (LENGTH l) = []` THEN
	    Cases_on `FST m (SND (HD (pop [(NTS st,inis)] (LENGTH l))))
                        (NTS n) =
                      []` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [pop_def] THEN
	    SRW_TAC [] [push_def] THEN
	    `m=(sgoto g, reduce g)`by METIS_TAC [sgoto_exp] THEN
	    SRW_TAC [] [validStlItemsStack_def, push_def] THEN
	    METIS_TAC [APPEND_NIL, validStlItems_sgoto_gen],


	    SRW_TAC [] [push_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
	    METIS_TAC [validStlItems_goto, APPEND_NIL, sgoto_exp]
	    ],

      Cases_on `h` THEN Cases_on `q` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t'` THEN
      Cases_on `getState m r' h` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
	    Cases_on `r''` THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleRhs_def, ruleLhs_def] THEN
	    Cases_on `addRule (((q',r'),r)::t) (rule n l)` THEN
	    Cases_on `pop
                     ((q',r')::
                          (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
                     (LENGTH l) =
                   []` THEN
	    Cases_on `FST m
                        (SND
                           (HD
                              (pop
                                 ((q',r')::
                                      (MAP FST t ++
                                       [(NTS st,initItems ag (rules ag))]))
                                 (LENGTH l)))) (NTS n) =
                      []` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] [push_def] THEN
	    `m=(sgoto g, reduce g)`by METIS_TAC [sgoto_exp] THEN
	    SRW_TAC [] [validStlItemsStack_def, push_def] THEN
	    `LENGTH (((q',r'),r)::t) >= LENGTH l` by METIS_TAC [addrule_len] THEN
 	    `LENGTH l <= LENGTH (((q',r'),r)::t)` by DECIDE_TAC THEN
	    `validStlItemsStack (pop (((q',r'),r)::t) (LENGTH l))
				(pop ((q',r')::(MAP FST t ++ [(NTS st,initItems ag (rules ag))])) (LENGTH l))`
		by METIS_TAC [validStlItems_pop, NOT_CONS_NIL] THEN
	    Cases_on `l` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [pop_def, LENGTH]
            THENL[
		  SRW_TAC [] [] THEN
		  METIS_TAC [validStlItems_sgoto_gen],

		  Q.ABBREV_TAC `pped = pop (MAP FST t ++ [(NTS st,initItems ag (rules ag))]) (LENGTH t')` THEN
		  Cases_on `pped` THEN
		  SRW_TAC [] [] THEN
		  Cases_on `h''` THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC [validStlItems_sgoto_gen]
		  ],


	    FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM] THEN
	    Cases_on `r''` THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleRhs_def, ruleLhs_def] THEN
	    Cases_on `addRule (((q',r'),r)::t) (rule n l)` THEN
	    Cases_on `pop
                     ((q',r')::
                          (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
                     (LENGTH l) =
                   []` THEN
	    Cases_on `FST m
                        (SND
                           (HD
                              (pop
                                 ((q',r')::
                                      (MAP FST t ++
                                       [(NTS st,initItems ag (rules ag))]))
                                 (LENGTH l)))) (NTS n) =
                      []` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] [push_def] THEN
	    `m=(sgoto g, reduce g)`by METIS_TAC [sgoto_exp] THEN
	    SRW_TAC [] [validStlItemsStack_def, push_def] THEN
	    `LENGTH (((q',r'),r)::t) >= LENGTH l` by METIS_TAC [addrule_len] THEN
 	    `LENGTH l <= LENGTH (((q',r'),r)::t)` by DECIDE_TAC THEN
	    `validStlItemsStack (pop (((q',r'),r)::t) (LENGTH l))
				(pop ((q',r')::(MAP FST t ++ [(NTS st,initItems ag (rules ag))])) (LENGTH l))`
		by METIS_TAC [validStlItems_pop, NOT_CONS_NIL] THEN
	    Cases_on `l` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [pop_def, LENGTH]
            THENL[
		  SRW_TAC [] [] THEN
		  METIS_TAC [validStlItems_sgoto_gen],

		  Q.ABBREV_TAC `pped = pop (MAP FST t ++ [(NTS st,initItems ag (rules ag))]) (LENGTH t')` THEN
		  Cases_on `pped` THEN
		  SRW_TAC [] [] THEN
		  Cases_on `h''` THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC [validStlItems_sgoto_gen]
		  ],

	    SRW_TAC [] [push_def, validStlItemsStack_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
	    METIS_TAC [validStlItems_goto, sgoto_exp]
	    ]
      ]);


val takesStepsValidStlItems = store_thm
("takesStepsValidStlItems",
``!n sl stl csl.
             (csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
	     takesSteps n (parse m)
             (exitCond (eof,NTS (startSym g)))
             (sl,stl,csl)
             (sl',stl',csl') ==>
	     validStlItemsStack stl csl ==>
	     (slrmac ag = SOME m) ==>
             validStlItemsStack stl'  csl'``,

Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] [validStlItemsStack_def] THEN
Cases_on `n` THEN SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      METIS_TAC [parseValidStlStack],

      Q.ABBREV_TAC `csl=MAP FST stl ++ [(NTS st,initItems ag (rules ag))]` THEN
      `takesSteps (SUC 0) (parse m)
         (exitCond (eof,NTS (startSym g)))
         (sl,stl,csl) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `validStlItemsStack q' r'`
      THENL[
	    SRW_TAC [] [] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`q`, `q'`, `r'`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [takesStepsCslStlEq],

	    METIS_TAC [parseValidStlStack]
	    ]
      ]);



val svPop = store_thm
("svPop",
``!l1 l2 n.(stackValid ag l1 l2) ==>
  (LENGTH l1 >= n) ==>
  (stackValid ag (pop l1 n) (pop l2 n))``,
Induct_on `n` THEN SRW_TAC [] [pop_def,pop0] THEN
Cases_on `l1` THEN Cases_on `l2` THEN
FULL_SIMP_TAC (srw_ss()) [stackValid_def,pop_def,pop0] THEN
FULL_SIMP_TAC (arith_ss) []);


val parseValidItem = store_thm
("parseValidItem",
``!m g.
(slrmac ag = SOME m) ==>
(csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
stackValid ag stl csl  ==>
EVERY isTmnlSym sl ==>
(parse m (sl, stl, csl) = SOME (sl',stl',csl')) ==>
stackValid ag stl' csl'``,

 Cases_on `stl` THEN SRW_TAC [] []
 THENL[

      FULL_SIMP_TAC (srw_ss()) [parse_def, itemlist_def, LET_THM,stackValid_def] THEN
      Cases_on `sl` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Q.ABBREV_TAC `inis = initItems ag (rules ag)` THEN
      Cases_on `t` THEN
      Cases_on `getState m inis h` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[

	    Cases_on `r` THEN
	    FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, pop_def, push_def, ruleRhs_def, ruleLhs_def] THEN
	    Cases_on `addRule ([]:(((α,β)symbol#(α,β)state)#(α,β)ptree) list) (rule n l)` THEN
	    Cases_on `LENGTH l = 0` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `l` THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def,stackValid_def] THEN
	    SRW_TAC [] [EVERY_MEM,stackValid_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
	    Cases_on `e` THEN
	    Cases_on `p` THEN
	    `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
	    SRW_TAC  [] []THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `EVERY (validItem ag []) (iclosure ag inis)`
		by METIS_TAC [validItem_iclosure] THEN
	    FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
	    `EVERY (validItem ag [NTS n]) (moveDot inis (NTS n))`
		by METIS_TAC [validItem_moveDot, APPEND_NIL] THEN
	    METIS_TAC [rgr_r9eq, EVERY_APPEND, EVERY_DEF, validItem_iclosure],

	    Cases_on `r` THEN
	    FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, pop_def, push_def, ruleRhs_def, ruleLhs_def] THEN
	    Cases_on `addRule ([]:(((α,β)symbol#(α,β)state)#(α,β)ptree) list) (rule n l)` THEN
	    Cases_on `LENGTH l = 0` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `l` THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def,stackValid_def] THEN
	    SRW_TAC [] [EVERY_MEM,stackValid_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
	    Cases_on `e` THEN
	    Cases_on `p` THEN
	    `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
	    SRW_TAC  [] []THEN
	    `EVERY (validItem ag []) (iclosure ag inis)`
		by METIS_TAC [validItem_iclosure] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
	    `EVERY (validItem ag [NTS n]) (moveDot inis (NTS n))`
		by METIS_TAC [validItem_moveDot, APPEND_NIL] THEN
	    METIS_TAC [rgr_r9eq, EVERY_APPEND, EVERY_DEF, validItem_iclosure],

	    FULL_SIMP_TAC (srw_ss()) [push_def,stackValid_def,itemlist_def] THEN
	    SRW_TAC [] [] THEN
	    `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
	    FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
	    Cases_on `sgoto ag inis h` THEN
	    Cases_on `reduce ag inis (ts2str h)` THEN
	    FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  Cases_on `LENGTH t = 0`THEN
		  FULL_SIMP_TAC (srw_ss()) [],

		  SRW_TAC [] [stackValid_def,itemlist_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def,itemlist_def] THEN
		  `EVERY (validItem ag [h]) (moveDot inis h)`
		      by METIS_TAC [validItem_moveDot, APPEND_NIL] THEN
		  METIS_TAC [rgr_r9eq, EVERY_APPEND, EVERY_DEF, validItem_iclosure],


		  Cases_on `itemEqRuleList (h''::t) (h'''::t'')` THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  ]
	    ],

      Cases_on `h` THEN
      Cases_on `q` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) []THEN
      Cases_on `t'` THEN
      Cases_on `getState m r' h` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[

	    Cases_on `r''` THEN
	    FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, pop_def, push_def, ruleRhs_def, ruleLhs_def] THEN
	    Cases_on `addRule (((q',r'),r)::t) (rule n l)` THEN
	    Cases_on `LENGTH l = 0` THEN
	    FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  Cases_on `l` THEN
		  FULL_SIMP_TAC (srw_ss()) [itemlist_def,stackValid_def] THEN
		  SRW_TAC [] [EVERY_MEM,stackValid_def,itemlist_def] THEN
		  `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
		  METIS_TAC [validItem_moveDot, EVERY_MEM, validItem_iclosure],


		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  SRW_TAC [] [EVERY_MEM] THEN
		  `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
		  Q.ABBREV_TAC `pped=pop (MAP FST t ++ [(NTS st,initItems ag (rules ag))])
					  (LENGTH l - 1)` THEN
		  Cases_on `pped` THEN SRW_TAC [] [] THEN
		  Cases_on `h'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  Q.ABBREV_TAC `ppedSyms = stackSyms (pop t (LENGTH l - 1))` THEN
		  FULL_SIMP_TAC (srw_ss()) [stackValid_def,itemlist_def] THEN
		  `LENGTH (((q',r'),r)::t) >= LENGTH l` by METIS_TAC [addrule_len] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `LENGTH t >= LENGTH l - 1` by DECIDE_TAC THEN
		  `stackValid ag (pop t (LENGTH l - 1)) ((q,r'')::t')`
		      by METIS_TAC [svPop] THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC [validItem_moveDot, EVERY_MEM, validItem_iclosure,sv_1]
		  ],


	    Cases_on `r''` THEN
	    FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, pop_def, push_def, ruleRhs_def, ruleLhs_def] THEN
	    Cases_on `addRule (((q',r'),r)::t) (rule n l)` THEN
	    Cases_on `LENGTH l = 0` THEN
	    `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
	    FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  Cases_on `l` THEN
		  FULL_SIMP_TAC (srw_ss()) [itemlist_def,stackValid_def] THEN
		  SRW_TAC [] [EVERY_MEM,stackValid_def,itemlist_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
		  METIS_TAC [validItem_moveDot, EVERY_MEM, validItem_iclosure],


		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  SRW_TAC [] [EVERY_MEM] THEN
		  FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
		  Q.ABBREV_TAC `pped=pop (MAP FST t ++ [(NTS st,initItems ag (rules ag))])
					  (LENGTH l - 1)` THEN
		  Cases_on `pped` THEN SRW_TAC [] [] THEN
		  Cases_on `h''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
		  Q.ABBREV_TAC `ppedSyms = stackSyms (pop t (LENGTH l - 1))` THEN
		  FULL_SIMP_TAC (srw_ss()) [stackValid_def,itemlist_def] THEN
		  `LENGTH (((q',r'),r)::t) >= LENGTH l` by METIS_TAC [addrule_len] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `LENGTH t >= LENGTH l - 1` by DECIDE_TAC THEN
		  `stackValid ag (pop t (LENGTH l - 1)) ((q,r'')::t')`
		      by METIS_TAC [svPop] THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC [validItem_moveDot, EVERY_MEM, validItem_iclosure,sv_1]
		  ],

	    SRW_TAC [] [stackValid_def,itemlist_def,push_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [stackValid_def,itemlist_def] THEN
	    `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
	    FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
	    Cases_on `sgoto ag r' h` THEN
	    Cases_on `reduce ag r' (ts2str h)` THEN
	    FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  Cases_on `LENGTH t' = 0`THEN
		  FULL_SIMP_TAC (srw_ss()) [],

		  FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def,itemlist_def] THEN
		  `EVERY (validItem ag (stackSyms t ++ [q'] ++[h])) (moveDot r' h)`
		      by METIS_TAC [validItem_moveDot, APPEND_NIL] THEN
		  METIS_TAC [rgr_r9eq, EVERY_APPEND, EVERY_DEF, validItem_iclosure],


		  Cases_on `itemEqRuleList (h''::t') (h'''::t''')` THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  ]

	    ]]);


val parseTmnlSyms = store_thm
("parseTmnlSyms",
``!m g.
(csl = MAP FST stl ++ [e]) ==>
EVERY isTmnlSym sl ==>
(parse m (sl, stl, csl) = SOME (sl',stl',csl')) ==>
EVERY isTmnlSym sl'``,

Cases_on `stl`
THENL[
      Cases_on `e` THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
      Cases_on `t` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
      Cases_on `getState m r h` THEN FULL_SIMP_TAC (srw_ss()) []
      THENL[

 	    FULL_SIMP_TAC (srw_ss()) [doReduce_def,LET_THM] THEN
	    Cases_on `addRule ([]:((((α,β)symbol#(α,β)state)#(α,β)ptree)list)) r'` THEN
	    Cases_on `pop [(q,r)] (LENGTH (ruleRhs r'))` THEN
	    Cases_on `FST m
                          (SND (HD (pop [(q,r)] (LENGTH (ruleRhs r')))))
                          (NTS (ruleLhs r'))` THEN
	    Cases_on `r'` THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleLhs_def,ruleRhs_def] THEN
	    METIS_TAC [EVERY_DEF],

	    FULL_SIMP_TAC (srw_ss()) [doReduce_def,LET_THM] THEN
	    Cases_on `addRule ([]:((((α,β)symbol#(α,β)state)#(α,β)ptree)list)) r'` THEN
	    Cases_on `pop [(q,inis)] (LENGTH (ruleRhs r')) = []` THEN
	    Cases_on `FST m
                        (SND
                           (HD (pop [(q,r)] (LENGTH (ruleRhs r')))))
                        (NTS (ruleLhs r')) =
                      []` THEN
	    Cases_on `r'` THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleLhs_def,ruleRhs_def] THEN
	    METIS_TAC [EVERY_DEF],


	    METIS_TAC [EVERY_DEF]
	    ],



      Cases_on `h` THEN
      Cases_on `q` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
      SRW_TAC [][] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t'` THEN
      Cases_on `getState m r' h` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [doReduce_def,LET_THM] THEN
	    Cases_on `addRule (((q',r'),r)::t) r''` THEN
	    Cases_on `pop
                     ((q',r')::
                          (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
                     (LENGTH (ruleRhs r'')) =
                   []` THEN
	    Cases_on `FST m
                        (SND
                           (HD
                              (pop
                                 ((q',r')::
                                      (MAP FST t ++
                                       [(NTS st,initItems ag (rules ag))]))
                                 (LENGTH (ruleRhs r'')))))
                        (NTS (ruleLhs r'')) =
                      []` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [EVERY_DEF],

	    FULL_SIMP_TAC (srw_ss()) [doReduce_def,LET_THM] THEN
	    Cases_on `addRule (((q',r'),r)::t) r''` THEN
	    Cases_on `pop
                     ((q',r')::
                          (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
                     (LENGTH (ruleRhs r'')) =
                   []` THEN
	    Cases_on `FST m
                        (SND
                           (HD
                              (pop
                                 ((q',r')::
                                      (MAP FST t ++
                                       [(NTS st,initItems ag (rules ag))]))
                                 (LENGTH (ruleRhs r'')))))
                        (NTS (ruleLhs r'')) =
                      []` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [EVERY_DEF],


	    METIS_TAC [EVERY_DEF]
	    ]]);


val takesStepsTmnlSyms = store_thm
("takesStepsTmnlSyms",
``!n sl stl csl e.
             (csl = MAP FST stl ++ [e]) ==>
             takesSteps  n (parse m)
             (exitCond (eof,NTS (startSym g)))
             (sl,stl,csl)
             (sl',stl',csl') ==>
	     EVERY isTmnlSym sl ==>
	     EVERY isTmnlSym sl'``,
Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] [] THEN
Cases_on `n` THEN SRW_TAC [][]
THENL[

      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      METIS_TAC [parseTmnlSyms],

      Q.ABBREV_TAC `csl=(MAP FST stl ++ [e])` THEN
      `takesSteps (SUC 0) (parse m) (exitCond (eof,NTS (startSym g)))
            (sl,stl,csl) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `EVERY isTmnlSym q`
      THENL[
	    SRW_TAC [] [] THEN
	    METIS_TAC [takesStepsCslStlEq],

	    METIS_TAC [parseTmnlSyms]
	    ]
      ]);


val parseSlNotNil = store_thm
("parseSlNotNil",
``!m g.
(csl = MAP FST stl ++ [e]) ==>
~(sl=[]) ==>
(parse m (sl, stl, csl) = SOME (sl',stl',csl')) ==>
~(sl'=[])``,

Cases_on `stl` THEN
SRW_TAC [][]
THENL[
      Cases_on `e` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
      SRW_TAC [][] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `getState m r h` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[

	    FULL_SIMP_TAC (srw_ss()) [doReduce_def,LET_THM] THEN
	    Cases_on `addRule ([]:(((((α,β)symbol#(α,β)state)#(α,β)ptree)list))) r'` THEN
	    Cases_on `pop [(q,r)] (LENGTH (ruleRhs r')) = []` THEN
	    Cases_on `FST m
                        (SND
                           (HD (pop [(q,r)] (LENGTH (ruleRhs r')))))
                        (NTS (ruleLhs r')) =
                      []` THEN
	    Cases_on `r'` THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleLhs_def,ruleRhs_def] THEN
	    METIS_TAC [NOT_CONS_NIL],

	    FULL_SIMP_TAC (srw_ss()) [doReduce_def,LET_THM] THEN
	    Cases_on `addRule ([]:((((α,β)symbol#(α,β)state)#(α,β)ptree)list)) r'` THEN
	    Cases_on `pop [(q,r)] (LENGTH (ruleRhs r')) = []` THEN
	    Cases_on `FST m
                        (SND
                           (HD (pop [(q,r)] (LENGTH (ruleRhs r')))))
                        (NTS (ruleLhs r')) =
                      []` THEN
	    Cases_on `r'` THEN
	    FULL_SIMP_TAC (srw_ss()) [ruleLhs_def,ruleRhs_def] THEN
	    METIS_TAC [NOT_CONS_NIL],


	    METIS_TAC [NOT_CONS_NIL]
	    ],


      Cases_on `h` THEN
      Cases_on `q` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
      SRW_TAC [][] THEN
      Cases_on `sl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `t'` THEN
      Cases_on `getState m r' h` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    FULL_SIMP_TAC (srw_ss()) [doReduce_def,LET_THM] THEN
	    Cases_on `addRule (((q',r'),r)::t) r''` THEN
	    Cases_on `pop
                     ((q',r')::
                          (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
                     (LENGTH (ruleRhs r'')) =
                   []` THEN
	    Cases_on `FST m
                        (SND
                           (HD
                              (pop
                                 ((q',r')::
                                      (MAP FST t ++
                                       [(NTS st,initItems ag (rules ag))]))
                                 (LENGTH (ruleRhs r'')))))
                        (NTS (ruleLhs r'')) =
                      []` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [NOT_CONS_NIL],

	    FULL_SIMP_TAC (srw_ss()) [doReduce_def,LET_THM] THEN
	    Cases_on `addRule (((q',r'),r)::t) r''` THEN
	    Cases_on `pop
                     ((q',r')::
                          (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
                     (LENGTH (ruleRhs r'')) =
                   []` THEN
	    Cases_on `FST m
                        (SND
                           (HD
                              (pop
                                 ((q',r')::
                                      (MAP FST t ++
                                       [(NTS st,initItems ag (rules ag))]))
                                 (LENGTH (ruleRhs r'')))))
                        (NTS (ruleLhs r'')) =
                      []` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [NOT_CONS_NIL],


	    METIS_TAC [NOT_CONS_NIL]
	    ]]);



val takesStepsSlNotNil = store_thm
("takesStepsSlNotNil",
``!n sl stl csl e.
             (csl = MAP FST stl ++ [e]) ==>
             takesSteps n (parse m)
             (exitCond (eof,NTS (startSym g)))
             (sl,stl,csl)
             (sl',stl',csl') ==>
	     ~(sl=[]) ==>
             ~(sl'=[])``,
Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] [] THEN
Cases_on `n` THEN
SRW_TAC [][]
THENL[

      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      METIS_TAC [parseSlNotNil],

      Q.ABBREV_TAC `csl=(MAP FST stl ++ [e])` THEN
      `takesSteps (SUC 0) (parse m) (exitCond (eof,NTS (startSym g)))
            (sl,stl,csl) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `~(q=[])`
      THENL[
	    SRW_TAC [] [] THEN
	    METIS_TAC [takesStepsCslStlEq],

	    METIS_TAC [parseSlNotNil]
	    ]
      ]);


val takesStepsStackValid = store_thm
("takesStepsStackValid",
``!n sl stl csl.
             (csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
             takesSteps n (parse m)
             (exitCond (eof,NTS (startSym g)))
             (sl,stl,csl)
             (sl',stl',csl') ==>
	     (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
	     EVERY isTmnlSym sl ==>
	     (slrmac ag = SOME m) ==>
	     stackValid ag stl csl ==>
	     (slrmac ag = SOME m) ==>
             stackValid ag stl' csl'``,
Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] [] THEN
Cases_on `n` THEN SRW_TAC [][]
THENL[

      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      METIS_TAC [parseValidItem],

      Q.ABBREV_TAC `csl=(MAP FST stl ++ [(NTS st,initItems ag (rules ag))])` THEN
      `takesSteps (SUC 0) (parse m) (exitCond (eof,NTS (startSym g)))
            (sl,stl,csl) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `stackValid ag q' r'`
      THENL[
	    SRW_TAC [] [] THEN
	    METIS_TAC [takesStepsCslStlEq,takesStepsTmnlSyms],

	    METIS_TAC [parseValidItem]
	    ]
      ]);



val parseInvInit = store_thm
("parseInvInit",
``!m g sl st.
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
parseInv (ag, [], [((NTS st), initItems ag (rules ag))])``,
SRW_TAC [] [parseInv_def, validStkSymTree_def, itemlist_def]
THENL[
      FULL_SIMP_TAC (srw_ss()) [validStates_def, initItems_def] THEN
      METIS_TAC [validItl_initProds2Items, validItl_iclosure],


      SRW_TAC [] [initItems_def,stackValid_def,itemlist_def] THEN
      `EVERY (validItem ag []) (initProds2Items (startSym ag) (rules ag))`
	  by METIS_TAC [validItem_initProds2Items] THEN
      METIS_TAC [validItem_iclosure],


      FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
      METIS_TAC [b4DotEmpty, nullFstRhs_validStlItems]
      ]);

val parseParseInv = store_thm
("parseParseInv",
``(slrmac ag = SOME m) ==>
(auggr g st eof = SOME ag) ==>
EVERY isTmnlSym sl ==>
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
(csl=MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
parseInv (ag,stl,csl) ==>
(parse m (sl,stl,csl) = SOME (sl',stl',csl')) ==>
parseInv (ag,stl',csl')``,

      FULL_SIMP_TAC (srw_ss()) [parseInv_def] THEN
      SRW_TAC [] []
      THENL[

	    Cases_on `stl` THEN SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  METIS_TAC [parse_csl_validStates],

		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  Cases_on `h` THEN Cases_on `q` THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [parse_csl_validStates]
		  ],

      METIS_TAC [parseValidItem],

      METIS_TAC [parseValidStlStack],

      Cases_on `stl` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    METIS_TAC [parseVldStkSymTree],

	    FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
	    Cases_on `h` THEN Cases_on `q` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [parseVldStkSymTree]
	    ]
      ]);


val takesStepsParseInv = store_thm
("takesStepsParseInv",
``!n sl stl csl.
    (csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
    takesSteps n (parse m)
    (exitCond (eof,NTS (startSym g)))
    (sl,stl,csl)
    (sl',stl',csl') ==>
    EVERY isTmnlSym sl ==>
    parseInv (ag,stl,csl) ==>
    (auggr g st eof = SOME ag) ==>
    (!nt.nt IN nonTerminals ag ==> gaw ag nt) ==>
    (slrmac ag = SOME m) ==>
    parseInv (ag,stl',csl')``,
Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] [] THEN
Cases_on `n` THEN SRW_TAC [][]
THENL[
      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      METIS_TAC [parseParseInv],


      Q.ABBREV_TAC `csl=MAP FST stl ++ [(NTS st,initItems ag (rules ag))]` THEN
      `takesSteps (SUC 0) (parse m)
         (exitCond (eof,NTS (startSym g)))
         (sl,stl,csl) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `parseInv (ag,q',r')`
      THENL[
	    SRW_TAC [] [] THEN
	    METIS_TAC [takesStepsCslStlEq,takesStepsTmnlSyms],


	    METIS_TAC [parseParseInv,takesStepsTmnlSyms,takesStepsCslStlEq]
	    ]
      ]);

val takesStepsValidItemInv = store_thm
("takesStepsValidItemInv",
``!n sl stl csl.
             (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
             takesSteps n (parse m)
             (exitCond (eof,NTS (startSym g)))
             (sl,stl,csl)
             (sl',stl',csl') ==>
	     (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
	     EVERY isTmnlSym sl ==>
	     ~(sl=[]) ==>
             (slrmac ag = SOME m) ==>
             (auggr g st eof = SOME ag) ==>
	     parseInv (ag,stl,csl) ==>
	     validItemInv (ag, stl) ==>
	     validItemInv (ag,stl')``,
Induct_on `n` THEN SRW_TAC [] [takesSteps] THEN
SRW_TAC [] [] THEN
Cases_on `n` THEN SRW_TAC [][]
THENL[

      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      METIS_TAC [parseValidItemInv],

      Q.ABBREV_TAC `csl=(MAP FST stl ++ [(NTS st,initItems ag (rules ag))])` THEN
      `takesSteps (SUC 0) (parse m) (exitCond (eof,NTS (startSym g)))
            (sl,stl,csl) s'`by SRW_TAC [] [takesSteps] THEN
      Cases_on `s'` THEN Cases_on `r` THEN
      Q_TAC SUFF_TAC `validItemInv (ag,q')`
      THENL[
	    SRW_TAC [] [] THEN
	    METIS_TAC [takesStepsCslStlEq,takesStepsTmnlSyms,takesStepsParseInv,takesStepsSlNotNil],

	    METIS_TAC [parseValidItemInv]
	    ]
      ]);


val validItemInvGoto = store_thm
("validItemInvGoto",
``(slrmac ag = SOME m) ==>
(getState m r' (TS s) = GOTO l) ==>
parseInv (ag,((q',r'),r)::t,csli) ==>
validItemInv (ag,((q',r'),r)::t) ==>
(csli =
 (q',r')::(MAP FST t ++ [(NTS st,initItems ag (rules ag))])) ==>
validItemInv
   (ag,((TS s,l),Leaf (ts2str (TS s)))::((q',r'),r)::t)``,
cheat);
(*
SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [validItemInv_def, tmnlSym_def] THEN
 SRW_TAC [] [] THEN
 Cases_on `stk` THEN
 SRW_TAC [] [] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
 SRW_TAC [] [stackSyms_def, stkItl_def] THEN
 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
 FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM, ts2str_def] THEN
 Cases_on `sgoto ag r' (TS s) ` THEN
 Cases_on `reduce ag r' s` THEN
Cases_on `REVERSE t ++ [((q',r'),r)] ++ [((TS s,l),Leaf s)]` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN1
 (Cases_on `LENGTH t''=0` THEN
 FULL_SIMP_TAC (srw_ss()) [])
 THENL[

 SRW_TAC [][] THEN
 `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t ++ [((q',r'),r)]))) =
 SOME (stkItl (REVERSE (REVERSE t ++ [((q',r'),r)]))))`
 by METIS_TAC [IS_PREFIX_REFL,MEM,MEM_APPEND,nullNil] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
SRW_TAC [][] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`REVERSE t ++ [((q',r'),r)]`] MP_TAC) THEN
SRW_TAC [][] THEN
`REVERSE t ++ [((q',r'),r)] ++ [((TS s,h'::t''),Leaf s)] =
      h::t' ++ l` by METIS_TAC [APPEND] THEN
IMP_RES_TAC list_r6 THEN
SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

Cases_on `l1` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

`stackSyms (h::t') = stackSyms (REVERSE t ++ [((q',r'),r)])` by METIS_TAC [] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND, stkItl_def] THEN
`REVERSE (REVERSE (MAP FST (MAP FST t')) ++ [FST (FST h)]) =
      REVERSE (q'::REVERSE (MAP FST (MAP FST (REVERSE t))))` by METIS_TAC []
FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND, MAP_REVERSE, trans_snoc] THEN
Cases_on `trans ag
           (initItems ag (rules ag),REVERSE (MAP FST (MAP FST t)))` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `moveDot x q'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN


Q_TAC SUFF_TAC
`trans ag
(initItems ag (rules ag),[FST (FST h)] ++ REVERSE (MAP FST (MAP FST (REVERSE t'))))
= SOME (SND (FST (HD (REVERSE t' ++ [h]))))` THEN1
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [][trans_snoc]


 `~NULL (REVERSE t ++ [((q',r'),r)])` by METIS_TAC [popRevNotNil, REVERSE_APPEND, REVERSE, nullNil, MEM, MEM_APPEND] THEN


 `REVERSE ( h::t''') = REVERSE (REVERSE t ++ [((q',r'),r)] ++ [((TS s,h'::t''),Leaf s)])` by METIS_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [stackSyms_def, stkItl_def] THEN
 SRW_TAC [] [trans_snoc] THEN
 Cases_on `moveDot r' (TS s)` THEN
 SRW_TAC [] [] THEN1
 FULL_SIMP_TAC (srw_ss()) [iclosure,sgoto_def,nextState_def] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
 `REVERSE (REVERSE t' ++ [h]) =
 REVERSE (((TS s,h'::t''),Leaf  s)::((q',r'),r)::t)`
 by METIS_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
 `stackSyms (h::(t'++l)) =
 stackSyms (REVERSE t ++ [((q',r'),r)] ++ [((TS s,h'::t''),Leaf s)])`
 by METIS_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
`REVERSE (REVERSE (MAP FST (MAP FST l)) ++ REVERSE (MAP FST (MAP FST t')) ++
      [FST (FST h)]) =
 REVERSE (TS s::q'::REVERSE (MAP FST (MAP FST (REVERSE t))))`
by METIS_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND,map_rev] THEN
 SRW_TAC [] [trans_snoc] THEN
 FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def]


 `REVERSE (REVERSE (MAP FST (MAP FST t''')) ++ [FST (FST h)]) =
 REVERSE (TS s::q'::REVERSE (MAP FST (MAP FST (REVERSE t))))`
 by METIS_TAC [] THEN
 FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND,map_rev] THEN
 SRW_TAC [] [trans_snoc] THEN
 FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def]
 ]]],


 Cases_on `itemEqRuleList (h'::t'') (h''::t''')` THEN
 FULL_SIMP_TAC (srw_ss()) []
 ]);

*)

val validItemInvGotoInit = store_thm
("validItemInvGotoInit",
``(slrmac ag = SOME m) ==>
(getState m (itemlist csl) (TS s) = GOTO l) ==>
(csl = MAP FST t++[(NTS st,initItems ag (rules ag))]) ==>
parseInv (ag,t,csl) ==>
validItemInv (ag,t) ==>
validItemInv
   (ag,((TS s,l),Leaf (ts2str (TS s)))::t)``,
cheat);
(*
SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [validItemInv_def, tmnlSym_def] THEN
 SRW_TAC [] [] THEN
 Cases_on `stk` THEN
 SRW_TAC [] [] THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [IS_PREFIX] THEN
 SRW_TAC [] [stackSyms_def, stkItl_def] THEN
 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
 FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM, ts2str_def] THEN
 Cases_on `sgoto ag
               (itemlist (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
               (TS s) ` THEN
 Cases_on `reduce ag
                     (itemlist
                        (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
                     s` THEN
 FULL_SIMP_TAC (srw_ss()) []
 THENL[
       Cases_on `LENGTH t''=0` THEN
       FULL_SIMP_TAC (srw_ss()) [],

       Cases_on `t` THEN
       FULL_SIMP_TAC (srw_ss()) [itemlist_def]
       THENL[
	     SRW_TAC [][] THEN
	     FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
	     SRW_TAC [][trans_def] THEN
	     FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
	     Cases_on `moveDot (initItems ag (rules ag)) (TS s)`
	     THENL[
		   FULL_SIMP_TAC (srw_ss()) [iclosure],

		   FULL_SIMP_TAC (srw_ss()) []
		   ],


             Cases_on `REVERSE t''' ++ [h''] ++ [((TS s,l),Leaf s)]` THEN
             FULL_SIMP_TAC (srw_ss()) [] THEN
             SRW_TAC [][] THEN
	     `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t''' ++ [h'']))) =
             SOME (stkItl (REVERSE (REVERSE t''' ++ [h'']))))`
	     by METIS_TAC [IS_PREFIX_REFL,MEM,MEM_APPEND,nullNil] THEN
	     `IS_PREFIX (REVERSE t''' ++ [h'']) (h::t')
		      \/ IS_PREFIX (h::t') (REVERSE t''' ++ [h''])`
		 by METIS_TAC [IS_PREFIX_APPEND2]
		 THENL[
			RES_TAC THEN
			FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND,stkItl_def],

			`((REVERSE t''' ++ [h''])=h::t')
                         \/ ((REVERSE t''' ++ [h''] ++
                                      [((TS s,l),Leaf s)])=(h::t'))` by METIS_TAC [isPfx1]
			 THENL[
			       `REVERSE (h::t') = REVERSE (REVERSE t''' ++ [h''])`by METIS_TAC [] THEN
			       FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
			       RES_TAC THEN
			       FULL_SIMP_TAC (srw_ss()) [stkItl_def,stackSyms_def,REVERSE_APPEND],


			       `IS_PREFIX (REVERSE t''' ++ [h''])
				 (REVERSE t''' ++ [h''])` by METIS_TAC [IS_PREFIX_REFL] THEN
			       RES_TAC THEN
			       `~NULL (REVERSE t''' ++ [h''])` by METIS_TAC [popRevNotNil, REVERSE_APPEND, REVERSE, nullNil, MEM, MEM_APPEND] THEN
			       `REVERSE ( h::t') = REVERSE (REVERSE t''' ++ [h''] ++
						       [((TS s,l),Leaf s)])` by METIS_TAC [] THEN
			       FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
			       SRW_TAC [] [] THEN
			       FULL_SIMP_TAC (srw_ss()) [stackSyms_def, stkItl_def] THEN
			       SRW_TAC [] [trans_snoc] THEN
			       Cases_on `moveDot (SND (FST h'')) (TS s)` THEN
			       SRW_TAC [] []
			       THENL[
				     FULL_SIMP_TAC (srw_ss()) [iclosure,sgoto_def,nextState_def],

				     RES_TAC THEN
				     FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
				     `REVERSE (REVERSE t' ++ [h]) = REVERSE (((TS s,h'::t''),Leaf s)::h''::t''')`
				     by METIS_TAC [] THEN
				     FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
				     `stackSyms (h::t') =
			              stackSyms (REVERSE t''' ++ [h''] ++ [((TS s,h'::t''),Leaf s)])`
				     by METIS_TAC [] THEN
				     FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
				     `REVERSE (REVERSE (MAP FST (MAP FST t')) ++ [FST (FST h)]) =
				      REVERSE (TS s::FST (FST h'')::REVERSE (MAP FST (MAP FST (REVERSE t'''))))`
				     by METIS_TAC [] THEN
				     FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND,map_rev] THEN
				     SRW_TAC [] [trans_snoc] THEN
				     FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def]
				     ]
			       ]]],


			       Cases_on `itemEqRuleList (h'::t'') (h''::t''')` THEN
			       FULL_SIMP_TAC (srw_ss()) []]);


*)

val lem1 = store_thm ("lem1",
``!csli stli rhs pfx sfx N onstk ininp.
    (auggr g st eof = SOME ag) ==>
    RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
    (csli = (MAP FST stli++[(NTS st,initItems ag (rules ag))])) ==>
    MEM (rule N rhs) (rules ag) ==>
    ~(N=startSym ag) ==>
    EVERY isTmnlSym (pfx++rhs++sfx) ==>
    (slrmac ag = SOME m) ==>
    (rhs = onstk ++ ininp) ==>
    (stackSyms stli = pfx ++ onstk) ==>
    IS_PREFIX (pfx ++ rhs) (stackSyms stli) ==>
    (!nt. nt IN (nonTerminals ag) ==> gaw ag nt) ==>
    (LENGTH csli = LENGTH stli + 1) ==>
    parseInv (ag, stli, csli) ==>
    validItemInv (ag, stli)
  ==>
  ?i stl csl.
      takesSteps (LENGTH ininp) (parse m) (exitCond (eof,NTS (startSym g)))
                 (ininp ++ sfx,stli,csli)
                 (i,stl,csl) /\
      (stackSyms stl = pfx ++ rhs) /\ (i=sfx) /\
      (MEM (item N (rhs,[])) (itemlist csl))``,

Induct_on `ininp` THEN SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [takesSteps]
 THEN1
   (`validItem ag (stackSyms stli) (item N (onstk,[]))`
       by (SRW_TAC [] [validItem_def] THEN
           Q.EXISTS_TAC `sfx` THEN
           METIS_TAC [rdres1, rderives_append, APPEND_NIL]) THEN
    Cases_on `stli` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) []
    THENL[
	    METIS_TAC [itemlist_def,FST,SND,HD,initItemsHdNt],

	    FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
	    `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t ++ [h]))) =
              SOME (stkItl (REVERSE (REVERSE t ++ [h]))))`
		by METIS_TAC [nullNil, IS_PREFIX_REFL, rev_nil, validItemInv_def,MEM,MEM_APPEND] THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def, stkItl_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
	    METIS_TAC [transImpValidItem]
	    ]
    )
 THEN
 Cases_on `stli` THEN
 SRW_TAC [] [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [] [itemlist_def,exitCond_def]
 THEN1
   ((*stl=[]*)
    FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
    Cases_on `ininp++sfx` THEN
    Cases_on `getState m (initItems ag (rules ag)) h` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) []
    THENL[
	  METIS_TAC [lastEof,MEM,MEM_APPEND,APPEND_NIL],

	  METIS_TAC [lastEof,MEM,MEM_APPEND,APPEND_NIL],

	  METIS_TAC [lastEof,MEM,MEM_APPEND,APPEND_NIL],

	  `MEM (item N ([],h::ininp)) (initItems ag (rules ag))`
             by METIS_TAC [initItemsHdNt] THEN
	     Cases_on `r` THEN
	     `MEM (item n (l,[])) (initItems ag (rules ag))`
	        by METIS_TAC [parseInv_def,validStates_def,getState_mem_itl,sgoto_exp] THEN
	     `h  IN (followSet ag (NTS n))`
                by METIS_TAC [parseInv_def,validStates_def,getState_reduce_followSet,sgoto_exp] THEN
	     METIS_TAC [trans_def,slrmacNotValid,sgoto_exp],

          Cases_on `h` THEN
          FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,isTmnlSym_def] THEN
	  FIRST_X_ASSUM
            (Q.SPECL_THEN
	       [`[((TS t',l),Leaf t')]`,`[]`,`sfx`, `N`,`[TS t']`] MP_TAC) THEN
	  SRW_TAC [] [] THEN
	  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,IS_PREFIX] THEN
	  FULL_SIMP_TAC (srw_ss())
             [parseInv_def,validStates_def,validStlItemsStack_def,
              stackValid_def,itemlist_def,validStkSymTree_def] THEN
	  FULL_SIMP_TAC (srw_ss()) [ptree2Sym_def,tmnlSym_def] THEN
	  `validItl ag l` by METIS_TAC [getStateGotoValidItl] THEN
          IMP_RES_TAC sgoto_exp THEN
          SRW_TAC [][] THEN
          IMP_RES_TAC validStlItems_goto THEN
          FULL_SIMP_TAC (srw_ss()) [ts2str_def] THEN
	  `!csl t.
              (getState (sgoto ag,reduce ag) (itemlist csl) (TS t') = GOTO l) ==>
              (csl = MAP FST t ++ [(NTS st,initItems ag (rules ag))]) ==>
	      parseInv (ag,t,csl) ==>
              validItemInv (ag,t) ==> validItemInv (ag,((TS t',l),Leaf t')::t)`
                by METIS_TAC [validItemInvGotoInit, ts2str_def] THEN
	  FIRST_X_ASSUM (Q.SPECL_THEN [`[(NTS st,initItems ag (rules ag))]`,`[]`] MP_TAC) THEN
	  SRW_TAC [][] THEN
	  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
	  `validItemInv (ag,[((TS t',l),Leaf t')])`
	      by METIS_TAC [parseInvInit] THEN
	  `EVERY (validItem ag []) (iclosure ag (initItems ag (rules ag)))`
	      by METIS_TAC [validItem_iclosure] THEN
	  FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
	  Cases_on `sgoto ag (initItems ag (rules ag)) (TS t')` THEN
	  Cases_on `reduce ag (initItems ag (rules ag)) t'` THEN
	  FULL_SIMP_TAC (srw_ss()) [ts2str_def]
          THENL[
			Cases_on `t''` THEN
			FULL_SIMP_TAC (srw_ss()) [],

			FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			`EVERY (validItem ag [TS t']) (moveDot (initItems ag (rules ag)) (TS t'))`
			    by METIS_TAC [validItem_moveDot, APPEND_NIL] THEN
			`EVERY (validItem ag [TS t']) l`
			    by METIS_TAC [validItem_iclosure] THEN
			FULL_SIMP_TAC (srw_ss()) [push_def],

			Cases_on `itemEqRuleList (h::t'') (h''::t''')` THEN
			FULL_SIMP_TAC (srw_ss()) []
		],

	  `MEM (item N ([],h::ininp)) (initItems ag (rules ag))`
              by METIS_TAC [initItemsHdNt] THEN
	  METIS_TAC [getState_shift_not_NA,trans_def,sgoto_exp]
      ]
  )
 THEN
    (*~stl=[]*)
 `validItem ag (stackSyms (h'::t)) (item N (onstk,h::ininp))`
	by (SRW_TAC [] [validItem_def] THEN
 Q.EXISTS_TAC `sfx` THEN
 SRW_TAC [] [] THEN
 METIS_TAC [rdres1, rderives_append, EVERY_DEF, EVERY_APPEND, APPEND_ASSOC]) THEN
 `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE (h'::t)))) =
     SOME (stkItl (REVERSE (REVERSE (h'::t)))))`
    by METIS_TAC [nullNil, IS_PREFIX_REFL, rev_nil, validItemInv_def, NOT_CONS_NIL] THEN
 FULL_SIMP_TAC (srw_ss()) [itemlist_def, stkItl_def] THEN
 `MEM (item N (onstk,h::ininp)) (SND (FST h'))`
    by METIS_TAC [transImpValidItem] THEN
 Cases_on `h'` THEN
 Cases_on `q` THEN
 SRW_TAC [] [parse_def, LET_THM] THEN
 Cases_on `ininp++sfx` THEN
 Cases_on `getState m r' h` THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN
 SRW_TAC [] []
 >- (Cases_on `r''` THEN
     `(item N (onstk,[h])=item n (l,[])) \/
       ~?l' r2 r1. (item N (onstk,[h]) = item l' (r1,h::r2))`
          by METIS_TAC [parseInv_def, validStates_def, shiftReduce] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       METIS_TAC [APPEND])
 >- (Cases_on `N=startSym ag`THEN
     SRW_TAC [] [] THEN
     `?p.[]=p++[TS eof]`by METIS_TAC [lastEof, APPEND_NIL] THEN
     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [])
 >- METIS_TAC [sgoto_exp, APPEND, parseInv_def, validStates_def, APPEND_NIL,
               APPEND_ASSOC, getState_shift_not_NA]
 >- (Cases_on `r''` THEN
     `(item N (onstk,h::ininp)=item n (l,[])) \/
      ~?l' r2 r1. (item N (onstk,h::ininp) = item l' (r1,h::r2))`
	    by METIS_TAC [parseInv_def, validStates_def, shiftReduce] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [APPEND])
 >- (Cases_on `h` THEN
     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
     SRW_TAC [] [exitCond_def, push_def] THEN
     FIRST_X_ASSUM (Q.SPECL_THEN
	      [`((TS t'',l),Leaf t'')::((q',r'),r)::t`,
	       `pfx`, `sfx`, `N`,
	       `onstk++[TS t'']`] MP_TAC) THEN
     SRW_TAC [] [] THEN
     IMP_RES_TAC validItemInvGoto THEN
     FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
     SRW_TAC [] [] THEN
     `MEM (rule N (onstk ++ [TS t''] ++ ininp)) (rules ag)` by METIS_TAC [c1] THEN
     FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, IS_PREFIX_APPEND] THEN
     FULL_SIMP_TAC (srw_ss())
           [validStkSymTree_def, tmnlSym_def, ptree2Sym_def, parseInv_def] THEN
     SRW_TAC [] [] THEN
     FULL_SIMP_TAC (srw_ss()) [validStates_def, itemlist_def] THEN
     `validItl ag l` by METIS_TAC [getStateGotoValidItl] THEN
     FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
     `validStlItems (((TS t'',l),Leaf t'')::((ptree2Sym r,r'),r)::t) l`
	by METIS_TAC [validStlItems_goto,sgoto_exp, ts2str_def] THEN
     FULL_SIMP_TAC (srw_ss()) [tmnlSym_def, ptree2Sym_def,stackValid_def,itemlist_def] THEN
     `m = (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
     FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
     Cases_on `sgoto ag r' (TS t'')` THEN
     Cases_on `reduce ag r' t''` THEN
     FULL_SIMP_TAC (srw_ss()) [ts2str_def]
             >- (Cases_on `t'''` THEN FULL_SIMP_TAC (srw_ss()) [])

             >- (FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
		  `EVERY (validItem ag (stackSyms t ++ [ptree2Sym r]++[TS t'']))
					(moveDot r' (TS t''))`
		  by METIS_TAC [validItem_moveDot] THEN
		  `EVERY (validItem ag (stackSyms t ++ [ptree2Sym r]++[TS t'']))
					(iclosure ag (moveDot r' (TS t'')))`
		      by METIS_TAC [validItem_iclosure] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [validStates_def,stackValid_def] THEN
		  `~(MEM (TS eof) (onstk ++ TS t''::ininp))`
                   by METIS_TAC [auggrAllTmsRhs,EVERY_DEF,isTmnlSym_def,EVERY_APPEND] THEN
		  `~(t''=eof)` by FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [EVERY_DEF, APPEND, APPEND_ASSOC])

             >- (Cases_on `itemEqRuleList (h::t''') (h''::t'''')` THEN
		  FULL_SIMP_TAC (srw_ss()) [])
    )
 >- metis_tac [getState_shift_not_NA, sgoto_exp]
);



val lem2 = store_thm ("lem2",
``!csli stli rhs pfx sfx N onstk ininp.
(auggr g st eof = SOME ag) ==>
RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
(csli = (MAP FST stli++[(NTS st,initItems ag (rules ag))])) ==>
MEM (rule N rhs) (rules ag) ==>
~(N=startSym ag) ==>
EVERY isTmnlSym (pfx++rhs++sfx) ==>
(slrmac ag = SOME m) ==>
(pfx = onstk ++ ininp) ==>
(stackSyms stli = onstk) ==>
(!nt.nt IN (nonTerminals ag) ==> gaw ag nt) ==>
(LENGTH csli = LENGTH stli + 1) ==>
parseInv (ag, stli, csli) ==>
validItemInv (ag,stli) ==>
?i stl csl.
      takesSteps (LENGTH ininp) (parse m) (exitCond (eof,NTS (startSym g)))
        (ininp ++ rhs++ sfx,stli,csli) (i,stl,csl)
	   /\ (stackSyms stl = pfx) /\ (i=rhs++sfx)``,
cheat);
(*
Induct_on `ininp` THEN
SRW_TAC [] [takesSteps, exitCond_def] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      `(h::(pfx ++ [NTS N] ++ sfx) = (h::pfx) ++ [NTS N] ++ sfx)` by SRW_TAC [] [] THEN
      SRW_TAC [] [parse_def, LET_THM] THEN
      Cases_on `pfx++rhs++sfx` THEN SRW_TAC [] [] THEN
      Cases_on `getState m (initItems ag (rules ag)) h` THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
       THENL[
	     (* 6 *)

	     (* 1 *)
	     `?p.[]=p++[TS eof]` by METIS_TAC [APPEND_NIL, lastEof] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

	     (* 2 *)
	     `?p.[]=p++[TS eof]` by METIS_TAC [APPEND_NIL, lastEof] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

	     (* 3 *)
	     `?p.[]=p++[TS eof]` by METIS_TAC [APPEND_NIL, lastEof] THEN
	     Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

	     (* 4 *)
	     Cases_on `r` THEN
	     `h IN followSet ag (NTS n)` by METIS_TAC [getState_reduce_followSet, sgoto_exp, validStates_def, parseInv_def, parseInvInit] THEN
	     `MEM (item n (l,[])) (initItems ag (rules ag))` by METIS_TAC [validStates_def, getState_mem_itl, sgoto_exp, parseInvInit, parseInv_def] THEN
	     `validItl ag [item n (l,[])]` by METIS_TAC [validItl_append, validStates_def, rgr_r9eq, parseInvInit, parseInv_def] THEN
	     Cases_on `stackSyms stli` THEN
	     SRW_TAC [] [] THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   Cases_on `stli` THEN
		   FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
		   FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
		   Cases_on `ininp++rhs++sfx` THEN
		   SRW_TAC [][] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [][]
	           THENL[
			 `[h;NTS N] = [h]++[NTS N]`
			     by SRW_TAC [][] THEN
			 METIS_TAC [APPEND_NIL,lastEof,MEM,MEM_APPEND],

			 `(h::(ininp ++ [NTS N] ++ sfx)) =
              		   (h::ininp) ++ [NTS N] ++ sfx`
			     by SRW_TAC [][] THEN
			 `?lhs r1 r2.MEM (item lhs (r1,h::r2)) (initItems ag (rules ag))`
			     by METIS_TAC [initItemsNtInBtwn,HD,NOT_CONS_NIL,EVERY_DEF] THEN
			 METIS_TAC [slrmacNotValid,trans_def,sgoto_exp]
			 ],


		   Cases_on `stli` THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   Cases_on `h'''` THEN
		   Cases_on `q` THEN
		   SRW_TAC [] [parse_def, LET_THM] THEN
		   Cases_on `ininp++rhs++sfx` THEN
		   Cases_on `getState m r' h` THEN
		   SRW_TAC [] []
                   THENL[
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 SRW_TAC [] [] THEN
			 `(h''::(t' ++ [h] ++ [NTS N])) =
              		   ((h''::t' ++ [h]) ++ [NTS N])`
			     by SRW_TAC [] [] THEN
			 `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
			 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 SRW_TAC [] [] THEN
			 `(h''::(t' ++ [h] ++ [NTS N])) =
              		   ((h''::t' ++ [h]) ++ [NTS N])`
			     by SRW_TAC [] [] THEN
			 `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
			 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],


			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 SRW_TAC [] [] THEN
			 `(h''::(t' ++ [h] ++ [NTS N])) =
              		   ((h''::t' ++ [h]) ++ [NTS N])`
			     by SRW_TAC [] [] THEN
			 `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
			 Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

			 (*4*)
			 Cases_on `r''` THEN
			 FULL_SIMP_TAC (srw_ss()) [parseInv_def, validStates_def] THEN
			 `MEM (rule n' l') (rules ag)`
			 by METIS_TAC [getstate_red, sgoto_exp, ts2str_def] THEN
			 `h IN (followSet ag (NTS n'))` by METIS_TAC [getState_reduce_followSet, sgoto_exp] THEN
			 `(h''::(t' ++ h::ininp ++ [NTS N] ++ sfx))=
                          (h''::t' ++ h::ininp) ++ [NTS N] ++ sfx`
			     by SRW_TAC [][] THEN
			 `?itl.trans ag (initItems ag (rules ag), (h''::t' ++ h::ininp)) = SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
			 `?itl.trans ag (initItems ag (rules ag), h''::t') = SOME itl` by METIS_TAC [transAppend,APPEND_ASSOC] THEN
			 FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
			 `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t'' ++ [((q',r'),r)]))) =
			   SOME (stkItl (REVERSE (REVERSE t'' ++ [((q',r'),r)]))))`
			     by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			 FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,stkItl_def,transOutMem] THEN
			 `r'=itl'` by METIS_TAC [transOutMem,SOME_11] THEN
			 SRW_TAC [][] THEN
			 `h''::(t'++h::ininp) = h''::t' ++ h::ininp`
			     by SRW_TAC [][] THEN
			 METIS_TAC [slrmacTransConf,parseInv_def,validStates_def],

			 (*5*)
			 Cases_on `h` THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
			 SRW_TAC [] [] THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN
			    [`((TS t'''',l'),Leaf (ts2str (TS t'''')))::((q',r'),r)::t''`,
			     `rhs`, `sfx`, `N`] MP_TAC) THEN
			 SRW_TAC [] [ts2str_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
			 IMP_RES_TAC validItemInvGoto THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStkSymTree_def, tmnlSym_def, ptree2Sym_def, parseInv_def] THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStates_def, itemlist_def] THEN
			 `validItl ag l'` by METIS_TAC [getStateGotoValidItl] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
			 `validStlItems (((TS t'''',l'),Leaf (ts2str (TS t'''')))::((ptree2Sym r,r'),r)::t'') l'`
			     by METIS_TAC [validStlItems_goto,sgoto_exp, ts2str_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [tmnlSym_def, ptree2Sym_def,stackValid_def,itemlist_def] THEN
			 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
			 Cases_on `sgoto ag r' (TS t'''')` THEN
			 Cases_on `reduce ag r' t''''` THEN
			 FULL_SIMP_TAC (srw_ss()) [ts2str_def]
			 THENL[
			       Cases_on `LENGTH t'''''=0` THEN
			       FULL_SIMP_TAC (srw_ss()) [],

			       FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
			       `EVERY (validItem ag (stackSyms t'' ++ [ptree2Sym r]++[TS t''''])) (moveDot r' (TS t''''))`
				   by METIS_TAC [validItem_moveDot] THEN
			       `EVERY (validItem ag (stackSyms t'' ++ [ptree2Sym r]++[TS t''''])) (iclosure ag (moveDot r' (TS t'''')))`
				   by METIS_TAC [validItem_iclosure] THEN
			       SRW_TAC [] [push_def] THEN
			       METIS_TAC [EVERY_DEF, APPEND, APPEND_ASSOC,ts2str_def],

			       Cases_on `itemEqRuleList (h::t''''') (h''::t'''''')` THEN
			       FULL_SIMP_TAC (srw_ss()) []
			       ],

			 (*6*)
			 FULL_SIMP_TAC (srw_ss()) [parseInv_def, validStates_def] THEN
			 `(h''::(t' ++ h::ininp ++ [NTS N] ++ sfx))=
                          (h''::t' ++ h::ininp) ++ [NTS N] ++ sfx`
			     by SRW_TAC [][] THEN
			 `?itl.trans ag (initItems ag (rules ag), (h''::t' ++ h::ininp)) = SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
			 `?s.(trans ag (initItems ag (rules ag), h''::t') = SOME s)
                          /\ (trans ag (s,h::ininp) = SOME itl)`
			     by METIS_TAC [transAppend,APPEND_ASSOC,transOverAppend] THEN
			 FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
			 `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t'' ++ [((q',r'),r)]))) =
			   SOME (stkItl (REVERSE (REVERSE t'' ++ [((q',r'),r)]))))`
			     by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			 FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,stkItl_def,transOutMem] THEN
			 `r'=s` by METIS_TAC [transOutMem,SOME_11] THEN
			 SRW_TAC [][] THEN
			 `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
			 FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
			 Cases_on `moveDot r' h` THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 Cases_on `sgoto ag r' h` THEN
			 Cases_on `reduce ag r' (ts2str h)` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [iclosure_mem,MEM],

			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [iclosure_mem,MEM,ts2str_def],

			       Cases_on `itemEqRuleList (h'''''::t''''') (h''''''::t'''''')`THEN
			       FULL_SIMP_TAC (srw_ss()) [slrmac_def,LET_THM] THEN
			       FIRST_X_ASSUM (Q.SPECL_THEN
						  [`REVERSE (MAP FST (MAP FST t'')) ++ [q']`,`r'`,`h`] MP_TAC) THEN
			       SRW_TAC [][] THEN
			       Cases_on `t''''''` THEN SRW_TAC [][]
			       ]
			 ]],


		   (* GOTO l *)
	     Cases_on `stli` THEN
	     FULL_SIMP_TAC (srw_ss()) []
		   THENL[

			 FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
			 Cases_on `ininp++rhs++sfx` THEN
			 Cases_on `h` THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,isNonTmnlSym_def] THEN
			 SRW_TAC [][] THEN
			 FULL_SIMP_TAC (srw_ss()) []
                         THENL[
			       `[TS t';NTS N] = [TS t']++[NTS N]`
			       by SRW_TAC [][] THEN
			       METIS_TAC [APPEND_NIL,MEM,MEM_APPEND,lastEof],

			       SRW_TAC [] [push_def,tmnlSym_def,ptree2Sym_def] THEN
			       FIRST_X_ASSUM (Q.SPECL_THEN
						  [`[((TS t'',l),Leaf t'')]`,`rhs`,`sfx`, `N`] MP_TAC)   THEN
			       SRW_TAC [] [] THEN
			       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,IS_PREFIX] THEN
			       FULL_SIMP_TAC (srw_ss()) [parseInv_def,validStates_def,validStlItemsStack_def,stackValid_def,itemlist_def,validStkSymTree_def] THEN
			       FULL_SIMP_TAC (srw_ss()) [ptree2Sym_def,tmnlSym_def] THEN
			       `validItl ag l` by METIS_TAC [getStateGotoValidItl] THEN
			       `validStlItems [((TS t'',l),Leaf (ts2str (TS t'')))] l` by cheat
                               by METIS_TAC [validStlItems_goto,ptree2Sym_def,sgoto_exp, ts2str_def] THEN
			       `!csl t.(getState m (itemlist csl) (TS t'') = GOTO l) ==>
         					     (csl = MAP FST t ++ [(NTS st,initItems ag (rules ag))]) ==>
						     parseInv (ag,t,csl) ==>
						     validItemInv
						     (ag,t,MAP FST t ++ [(NTS st,initItems ag (rules ag))]) ==>
						     validItemInv
						     (ag,((TS t'',l),Leaf t'')::t,
						      (TS t'',l)::MAP FST t ++ [(NTS st,initItems ag (rules ag))])`
				   by METIS_TAC [validItemInvGotoInit, ts2str_def] THEN
			       FIRST_X_ASSUM (Q.SPECL_THEN [`[(NTS st,initItems ag (rules ag))]`,`[]`] MP_TAC) THEN
			       SRW_TAC [][] THEN
			       FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
			       `validItemInv
						     (ag,[((TS t'',l),Leaf t'')],
						      [(TS t'',l); (NTS st,initItems ag (rules ag))])`
				   by METIS_TAC [parseInvInit] THEN
			       `EVERY (validItem ag []) (iclosure ag (initItems ag (rules ag)))`
				   by METIS_TAC [validItem_iclosure] THEN
			       `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
			       FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
			       Cases_on `sgoto ag (initItems ag (rules ag)) (TS t'')` THEN
			       Cases_on `reduce ag (initItems ag (rules ag)) t''` THEN
			       FULL_SIMP_TAC (srw_ss()) [ts2str_def]
				THENL[
				      Cases_on `LENGTH t'''` THEN
				      FULL_SIMP_TAC (srw_ss()) [],


				      FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
				      `EVERY (validItem ag [TS s]) (moveDot (initItems ag (rules ag)) (TS t''))` by cheat
					  by METIS_TAC [validItem_moveDot, APPEND_NIL, ts2str_def] THEN
				      `EVERY (validItem ag [TS t'']) l` by cheat
					  by METIS_TAC [validItem_iclosure] THEN
				      FULL_SIMP_TAC (srw_ss()) [push_def] THEN
				      METIS_TAC [ptree2Sym_def,ts2str_def],

				      Cases_on `itemEqRuleList (h::t''') (h'''::t'''')` THEN
				      FULL_SIMP_TAC (srw_ss()) []
				      ]
			       ],

			 (*~stl=[]*)
			 `~(h=TS eof)` by METIS_TAC [auggrTmSymInBtwn,MEM,MEM_APPEND,APPEND,APPEND_ASSOC] THEN
			 SRW_TAC [][] THEN
			 Cases_on `h''` THEN
			 Cases_on `q` THEN
			 SRW_TAC [] [parse_def, LET_THM] THEN
			 Cases_on `ininp++rhs++sfx` THEN
			 Cases_on `getState m r' h` THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 SRW_TAC [][] THEN
			 FULL_SIMP_TAC (srw_ss()) []
		         THENL[

			       METIS_TAC [MEM,MEM_APPEND,lastEof,APPEND_NIL],

			       METIS_TAC [MEM,MEM_APPEND,lastEof,APPEND_NIL],

			       METIS_TAC [MEM,MEM_APPEND,lastEof,APPEND_NIL],

			       Cases_on `r''` THEN
			       FULL_SIMP_TAC (srw_ss()) [parseInv_def, validStates_def] THEN
			       `MEM (rule n l') (rules ag)`
				   by METIS_TAC [getstate_red, sgoto_exp] THEN
			       `h IN (followSet ag (NTS n))` by METIS_TAC [getState_reduce_followSet, sgoto_exp] THEN
			       FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
			       `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t' ++ [((q',r'),r)]))) =
				 SOME (stkItl (REVERSE (REVERSE t' ++ [((q',r'),r)]))))`
			       by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			       FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND] THEN
			       `?itl.(trans ag (initItems ag (rules ag),(REVERSE (MAP FST (MAP FST t')) ++ [q'] ++ h::ininp)) = SOME itl)`
			       by METIS_TAC [rtcRdImpTrans] THEN
			       `?s.(trans ag (initItems ag (rules ag), REVERSE (MAP FST (MAP FST t')) ++ [q']) = SOME s)
                                  /\ (trans ag (s,h::ininp) = SOME itl)`
				   by METIS_TAC [transAppend,APPEND_ASSOC,transOverAppend] THEN
			       `r'=s` by METIS_TAC [transOutMem,SOME_11] THEN
			       SRW_TAC [][] THEN
			       `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
			       FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
			       FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
			       Cases_on `moveDot r' h` THEN
			       FULL_SIMP_TAC (srw_ss()) [] THEN
			       Cases_on `sgoto ag r' h` THEN
			       Cases_on `reduce ag r' (ts2str h)` THEN
			       FULL_SIMP_TAC (srw_ss()) []
         		       THENL[
				     FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
				     METIS_TAC [iclosure_mem,MEM],

				     Cases_on `itemEqRuleList (h''''::t'''') (h'''''::t''''')`THEN
				     FULL_SIMP_TAC (srw_ss()) [slrmac_def,LET_THM] THEN
				     FIRST_X_ASSUM (Q.SPECL_THEN
							[`REVERSE (MAP FST (MAP FST t')) ++ [q']`,`r'`,`h`] MP_TAC) THEN
				     SRW_TAC [][] THEN
				     Cases_on `t'''''` THEN FULL_SIMP_TAC (srw_ss()) []
				     ],

			 Cases_on `h` THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
			 SRW_TAC [] [push_def] THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN
			    [`((TS t''',l'),Leaf t''')::((TS t''',r'),r)::t'`,
			     `rhs`, `sfx`, `N`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
			 `!q' r' r l t s csli.(slrmac ag = SOME m) ==>
                          (getState m r' (TS s) = GOTO l) ==>
                          parseInv (ag,((q',r'),r)::t,csli) ==>
			  validItemInv (ag,((q',r'),r)::t,csli) ==>
			  (csli =
			   (q',r')::(MAP FST t ++ [(NTS st,initItems ag (rules ag))])) ==>
			  validItemInv
			  (ag,((TS s,l),Leaf (s))::((q',r'),r)::t,
			   (TS s,l)::csli)`
			     by METIS_TAC [validItemInvGoto, ts2str_def] THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN [`TS t'''`,`r'`,`r`, `l'`,`t'`,`s`,`(TS s',r')::(MAP FST t' ++ [(NTS st,initItems ag (rules ag))])`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStkSymTree_def, tmnlSym_def, ptree2Sym_def, parseInv_def,stackValid_def,itemlist_def] THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStates_def, itemlist_def] THEN
			 `validItl ag l'` by METIS_TAC [getStateGotoValidItl] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [tmnlSym_def, ptree2Sym_def] THEN
			 `validStlItems (((TS t''',l'),Leaf t''')::((TS t''',r'),r)::t') l'`
			     by METIS_TAC [validStlItems_goto,sgoto_exp, ptree2Sym_def, tmnlSym_def, ts2str_def] THEN
			 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
			 Cases_on `sgoto ag r' (TS s)` THEN
			 Cases_on `reduce ag r' (s)` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       Cases_on `LENGTH t'''=0` THEN
			       FULL_SIMP_TAC (srw_ss()) [],


			       FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
			       `EVERY (validItem ag (stackSyms t' ++ [TS s']++[TS s])) (moveDot r' (TS s))`
				   by METIS_TAC [validItem_moveDot] THEN
			       `EVERY (validItem ag (stackSyms t' ++ [TS s']++[TS s])) (iclosure ag (moveDot r' (TS s)))`
				   by METIS_TAC [validItem_iclosure] THEN
			       METIS_TAC [APPEND, APPEND_ASSOC, isTmnlSym_def,ts2str_def],

			       Cases_on `itemEqRuleList (h::t''') (h'''::t'''')` THEN
			       FULL_SIMP_TAC (srw_ss()) []
			       ],


			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 Cases_on `sfx` THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[

			       `(stackSyms t' ++ [q'] ++ h::ininp ++ [NTS N]) =
			        (stackSyms t' ++ [q'] ++ h::ininp) ++ [NTS N] ` by SRW_TAC [][] THEN
			       `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
			       Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

			       `(stackSyms t' ++ [q'] ++ h::ininp ++ [NTS N] ++ h'''::t''') =
				(stackSyms t' ++ [q'] ++ h::ininp) ++ [NTS N] ++ h'''::t'''`
			       by SRW_TAC [][] THEN
			       `?itl.trans ag (initItems ag (rules ag),(stackSyms t' ++ [q'] ++ h::ininp)) = SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
			       FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
			       `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t' ++ [((q',r'),r)]))) =
				 SOME (stkItl (REVERSE (REVERSE t' ++ [((q',r'),r)]))))`
			       by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			       FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND] THEN
			       `?itl.(trans ag (initItems ag (rules ag),(REVERSE (MAP FST (MAP FST t')) ++ [q'] ++ h::ininp)) = SOME itl)`
				   by METIS_TAC [rtcRdImpTrans] THEN
			       `?s.(trans ag (initItems ag (rules ag), REVERSE (MAP FST (MAP FST t')) ++ [q']) = SOME s)
                                  /\ (trans ag (s,h::ininp) = SOME itl)`
				   by METIS_TAC [transAppend,APPEND_ASSOC,transOverAppend] THEN
			       `r'=s` by METIS_TAC [transOutMem,SOME_11] THEN
			       SRW_TAC [][] THEN
			       `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
			       FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
			       FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
			       Cases_on `moveDot r' h` THEN
			       FULL_SIMP_TAC (srw_ss()) [] THEN
			       Cases_on `sgoto ag r' h` THEN
			       Cases_on `reduce ag r' (ts2str h)` THEN
			       FULL_SIMP_TAC (srw_ss()) []
         		       THENL[
				     FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
				     METIS_TAC [iclosure_mem,MEM],

				     FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
				     METIS_TAC [iclosure_mem,MEM],

				     Cases_on `itemEqRuleList (h'''''::t''''') (h''''''::t'''''')`THEN
				     FULL_SIMP_TAC (srw_ss()) [slrmac_def,LET_THM] THEN
				     FIRST_X_ASSUM (Q.SPECL_THEN
							[`REVERSE (MAP FST (MAP FST t')) ++ [q']`,`r'`,`h`] MP_TAC) THEN
				     SRW_TAC [][] THEN
				     Cases_on `t''''''` THEN FULL_SIMP_TAC (srw_ss()) []
				     ]
			       ]

			 ]],

	     (*5*)
	     Cases_on `sfx` THEN
	     SRW_TAC [] [] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     SRW_TAC [] [] THEN
	     FULL_SIMP_TAC (srw_ss()) []
             THENL[
		   `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		   Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],

 		   `(stackSyms stli ++ h::ininp ++ [NTS N] ++ h''::t') =
	     (stackSyms stli ++ h::ininp) ++ [NTS N] ++ h''::t'`
		       by SRW_TAC [][] THEN
		   `?itl.trans ag (initItems ag (rules ag),(stackSyms stli ++ h::ininp)) = SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
		   Cases_on `stli` THEN SRW_TAC [][] THEN
		   FULL_SIMP_TAC (srw_ss()) []
                   THENL[
			 `(h::(ininp ++ [NTS N] ++ h''::t')) =
		          (h::ininp) ++ [NTS N] ++ h''::t'`
			     by SRW_TAC [][] THEN
			 `?l r1 r2.MEM (item l (r1,h::r2)) (initItems ag (rules ag))`
			     by METIS_TAC [initItemsNtInBtwn,HD,EVERY_DEF,NOT_CONS_NIL] THEN
			 METIS_TAC [getState_shift_not_NA,sgoto_exp,trans_def],


			 `~(h=TS eof)` by METIS_TAC [auggrTmSymInBtwn,APPEND,APPEND_ASSOC,MEM,MEM_APPEND] THEN
			 SRW_TAC [][] THEN
			 Cases_on `h'''` THEN Cases_on `q` THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
			 Cases_on `ininp++rhs++h''::t'` THEN
			 Cases_on `getState m r' h` THEN
			 SRW_TAC [][]
			 THENL[

			       `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t'' ++ [h''']))) =
				 SOME (stkItl (REVERSE (REVERSE t'' ++ [h''']))))`
				   by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			       FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND] THEN
			       `?itl.(trans ag (initItems ag (rules ag),(REVERSE (MAP FST (MAP FST t'')) ++ [FST (FST h''')] ++ h::ininp)) = SOME itl)`
				   by METIS_TAC [rtcRdImpTrans] THEN
			       `?s.(trans ag (initItems ag (rules ag), REVERSE (MAP FST (MAP FST t'')) ++ [FST (FST h''')]) = SOME s)
			 /\ (trans ag (s,h::ininp) = SOME itl)`
				   by METIS_TAC [transAppend,APPEND_ASSOC,transOverAppend],

			       `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t'' ++ [h''']))) =
				 SOME (stkItl (REVERSE (REVERSE t'' ++ [h''']))))`
				   by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			       FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND] THEN
			       `?itl.(trans ag (initItems ag (rules ag),(REVERSE (MAP FST (MAP FST t'')) ++ [FST (FST h''')] ++ h::ininp)) = SOME itl)`
				   by METIS_TAC [rtcRdImpTrans] THEN
			       `?s.(trans ag (initItems ag (rules ag), REVERSE (MAP FST (MAP FST t'')) ++ [FST (FST h''')]) = SOME s)
			 /\ (trans ag (s,h::ininp) = SOME itl)`
				   by METIS_TAC [transAppend,APPEND_ASSOC,transOverAppend],

			       `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t'' ++ [h''']))) =
				 SOME (stkItl (REVERSE (REVERSE t'' ++ [h''']))))`
				   by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			       FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND] THEN
			       `?itl.(trans ag (initItems ag (rules ag),(REVERSE (MAP FST (MAP FST t'')) ++ [FST (FST h''')] ++ h::ininp)) = SOME itl)`
				   by METIS_TAC [rtcRdImpTrans] THEN
			       `?s.(trans ag (initItems ag (rules ag), REVERSE (MAP FST (MAP FST t'')) ++ [FST (FST h''')]) = SOME s)
			 /\ (trans ag (s,h::ininp) = SOME itl)`
				   by METIS_TAC [transAppend,APPEND_ASSOC,transOverAppend],

			 (*4*)
			 Cases_on `r''` THEN
			 FULL_SIMP_TAC (srw_ss()) [parseInv_def, validStates_def] THEN
			 `MEM (rule s l) (rules ag)`
			 by METIS_TAC [getstate_red, sgoto_exp] THEN
			 `h IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, sgoto_exp] THEN
 			 FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
			 `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t'' ++ [((q',r'),r)]))) =
			   SOME (stkItl (REVERSE (REVERSE t'' ++ [((q',r'),r)]))))`
			     by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			 FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,stkItl_def,transOutMem] THEN
			 SRW_TAC [][] THEN
			 `?s.(trans ag (initItems ag (rules ag), REVERSE (MAP FST (MAP FST t'')) ++ [q']) = SOME s)
			     /\ (trans ag (s,h::ininp) = SOME itl)`
			     by METIS_TAC [transAppend,APPEND_ASSOC,transOverAppend] THEN
			 FULL_SIMP_TAC (srw_ss()) [transOutMem] THEN
			 METIS_TAC [slrmacTransConf,parseInv_def,validStates_def],

			 (*5*)
			 Cases_on `h` THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
 			 SRW_TAC [] [] THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN
			    [`((TS s,l),Leaf (s))::((TS s',r'),r)::t''`,
			     `rhs`, `TS s''::t'`, `N`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
			 IMP_RES_TAC validItemInvGoto THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStkSymTree_def, tmnlSym_def, ptree2Sym_def, parseInv_def] THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStates_def, itemlist_def] THEN
			 `validItl ag l` by METIS_TAC [getStateGotoValidItl] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
			 `validStlItems (((TS s,l),Leaf (s))::((TS s',r'),r)::t'') l `
			     by METIS_TAC [validStlItems_goto,sgoto_exp,ptree2Sym_def,tmnlSym_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [tmnlSym_def, ptree2Sym_def,stackValid_def,itemlist_def] THEN
			 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
			 Cases_on `sgoto ag r' (TS s)` THEN
			 Cases_on `reduce ag r' (s)` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       Cases_on `LENGTH t''''=0` THEN
			       FULL_SIMP_TAC (srw_ss()) [],


			       FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
			       `EVERY (validItem ag (stackSyms t'' ++ [TS s']++[TS s])) (moveDot r' (TS s))`
				   by METIS_TAC [validItem_moveDot] THEN
			       `EVERY (validItem ag (stackSyms t'' ++ [TS s']++[TS s])) (iclosure ag (moveDot r' (TS s)))`
				   by METIS_TAC [validItem_iclosure] THEN
			       SRW_TAC [] [push_def] THEN
			       METIS_TAC [EVERY_DEF, APPEND, APPEND_ASSOC,ts2str_def],

			       Cases_on `itemEqRuleList (h::t'''') (h''::t''''')` THEN
			       FULL_SIMP_TAC (srw_ss()) []
			       ],

			 (*6*)
			 FULL_SIMP_TAC (srw_ss()) [parseInv_def, validStates_def] THEN
			 `(stackSyms t'' ++ [q'] ++ h::ininp ++ [NTS N] ++ h''::t') =
                           ((stackSyms t'' ++ [q'] ++ h::ininp) ++ [NTS N] ++ h''::t')`
			     by SRW_TAC [][] THEN
			 `?itl.trans ag (initItems ag (rules ag), (stackSyms t'' ++ [q'] ++ h::ininp)) = SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
			 `?s.(trans ag (initItems ag (rules ag), stackSyms t''++[q']) = SOME s)
                          /\ (trans ag (s,h::ininp) = SOME itl)`
			     by METIS_TAC [transAppend,APPEND_ASSOC,transOverAppend] THEN
			 FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
			 `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t'' ++ [((q',r'),r)]))) =
			   SOME (stkItl (REVERSE (REVERSE t'' ++ [((q',r'),r)]))))`
			     by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
			 FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,stkItl_def,transOutMem] THEN
			 SRW_TAC [][] THEN
			 `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
			 FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
			 Cases_on `moveDot r' h` THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 Cases_on `sgoto ag r' h` THEN
			 Cases_on `reduce ag r' (ts2str h)` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [iclosure_mem,MEM],

			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [iclosure_mem,MEM],

			       Cases_on `itemEqRuleList (h'''''::t''''') (h''''''::t'''''')`THEN
			       FULL_SIMP_TAC (srw_ss()) [slrmac_def,LET_THM] THEN
			       FIRST_X_ASSUM (Q.SPECL_THEN
						  [`REVERSE (MAP FST (MAP FST t'')) ++ [q']`,`r'`,`h`] MP_TAC) THEN
			       SRW_TAC [][] THEN
			       Cases_on `t''''''` THEN SRW_TAC [][]
			       ]
			 ]

		   ]]]);

*)

val parseMacGuard = store_thm ("parseMacGuard",
``(slrmac ag = SOME m) ==>
(auggr g st eof = SOME ag) ==>
RTC (rderives ag) [NTS (startSym ag)]
      (h::(t ++ [NTS N] ++ sfx)) ==>
  MEM (rule N rhs) (rules ag) ==>
parseInv
(ag,stl,MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
takesSteps (SUC (LENGTH t)) (parse m)
       (exitCond (eof,NTS (startSym g)))
       (h::(t ++ rhs ++ sfx),[],
        [(NTS st,initItems ag (rules ag))])
       (rhs ++ sfx,stl,
        MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
~(N=startSym ag) ==>
(stackSyms stl = h::t) ==>
(~(stl = []) /\ (~(stackSyms stl = [NTS (startSym g)]) \/
            ~(HD (rhs ++ sfx) = TS eof)))``,

SRW_TAC [] [] THEN
Cases_on `stl` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `(~(h = NTS (startSym g)) ∨ ~(t = [])) ∨ ~(HD (rhs ++ sfx) = TS eof)` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `rhs` THEN
Cases_on `sfx` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN1
      (`!n sl stl csl e sl' stl' csl'.
         (csl = MAP FST stl ++ [e]) ==>
         takesSteps (SUC n) (parse m)
           (exitCond (eof,NTS (startSym g))) (sl,stl,csl)
           (sl',stl',csl') ==>
         ~(sl = []) ==>
         ~(sl' = [])` by METIS_TAC [takesStepsSlNotNil]THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH t`,`h::t`,`[]`,`[(NTS st,initItems ag (rules ag))]`,
			     `(NTS st,initItems ag (rules ag))`,
			     `[]`,`h'::t'`,
			     `FST h'::(MAP FST t' ++ [(NTS st,initItems ag (rules ag))])`] MP_TAC) THEN
      SRW_TAC [] []) THENL[

      SRW_TAC [] [] THEN
      `SUC 0 = 1` by DECIDE_TAC THEN
      `takesSteps (SUC 0) (parse m) (exitCond (eof,NTS (startSym g)))
            (NTS (startSym g)::TS eof::t'',[],
             [(NTS st,initItems ag (rules ag))])
            (TS eof::t'',h'::t',
             FST h'::(MAP FST t' ++ [(NTS st,initItems ag (rules ag))]))`
      by METIS_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [takesSteps] THEN
      FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
      `(NTS (startSym g)::NTS N::TS eof::t'')=
       [NTS (startSym g)]++[NTS N]++TS eof::t''`
      by METIS_TAC [APPEND,APPEND_ASSOC] THEN
      `?itl.trans ag (initItems ag (rules ag),[NTS (startSym g)]) = SOME itl` by METIS_TAC [rtcRdImpTrans] THEN
      `?pfx. ((NTS (startSym g)::NTS N::TS eof::t'') = pfx ++ [TS eof]) /\ ~MEM (TS eof) pfx`
	  by METIS_TAC [auggrStRtcRdEofGen,MEM] THEN
      SRW_TAC [] []THEN
      Cases_on `t''` THEN
      SRW_TAC [][]
      THENL[
	    `validItem ag [NTS (startSym g)]  (item N ([],[]))`
		by (SRW_TAC [][validItem_def] THEN
	    Q.EXISTS_TAC `[TS eof]` THEN
	    SRW_TAC [][] THEN
	    `[NTS (startSym g)]++[NTS N] = pfx`
		by METIS_TAC [APPEND_11,APPEND] THEN
	    `rderives ag ([NTS (startSym g)]++[NTS N]++[TS eof])
			       ([NTS (startSym g)]++[]++[TS eof])`
		by METIS_TAC [rdres1,rderives_append,isTmnlSym_def,EVERY_DEF] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC []) THEN
	    `MEM (item N ([],[])) itl` by METIS_TAC [transImpValidItem] THEN
	    `MEM (rule (startSym ag) [NTS (startSym g);TS eof]) (rules ag)`
		by METIS_TAC [auggrNewRuleMem] THEN
	    `validItem ag [NTS (startSym g)]  (item (startSym ag) ([NTS (startSym g)],[TS eof]))`
		by (SRW_TAC [][validItem_def] THEN
	    MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
	    SRW_TAC [][RTC_RULES] THEN
	    METIS_TAC [rdres1,rderives_append,isTmnlSym_def,EVERY_DEF,APPEND_NIL]) THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `MEM (item (startSym ag) ([NTS (startSym g)],[TS eof])) itl`
		by METIS_TAC [transImpValidItem] THEN
	    `(TS eof) IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
	    METIS_TAC [slrmacNotValid,isTmnlSym_def,sgoto_exp],

	    `(h::t) = FRONT (h::t) ++ [LAST (h::t)]`
	    by METIS_TAC [last_append,APPEND_FRONT_LAST,NOT_CONS_NIL] THEN
	    SRW_TAC [][] THEN
	    `LAST (NTS (startSym g)::NTS N::TS eof::h::t) = LAST (pfx ++ [TS eof])`
		by METIS_TAC [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `LAST (pfx++[TS eof]) = LAST [TS eof]` by METIS_TAC [last_append,NOT_CONS_NIL] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    `NTS (startSym g)::NTS N::TS eof::FRONT (h::t) ++ [TS eof] = pfx ++ [TS eof]`
		by METIS_TAC [APPEND,APPEND_ASSOC] THEN
	    `NTS (startSym g)::NTS N::TS eof::FRONT (h::t)=pfx`
		by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
	    METIS_TAC [MEM,MEM_APPEND]
	    ],

      `(h::(t ++ [NTS N])) = ((h::t) ++ [NTS N])` by SRW_TAC [] [] THEN
      `?p.[]=p++[TS eof]` by METIS_TAC [lastEof,APPEND_NIL] THEN
      Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [],


      SRW_TAC [] [] THEN
      METIS_TAC [auggrEofInRhs,APPEND,APPEND_NIL]
      ]);

val takesStepsBase = store_thm
("takesStepsBase",
``(auggr g st eof = SOME ag) ==>
  EVERY isTmnlSym (pfx++rhs++sfx) ==>
  RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
  MEM (rule N rhs) (rules ag) ==>
  (slrmac ag = SOME m) ==>
 (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
    ?n i stl csl.
      takesSteps n (parse m) (exitCond (eof,NTS (startSym g)))
        (pfx ++ rhs ++ sfx,[],[(NTS st,initItems ag (rules ag))])
        (i,stl,csl) /\ (stackSyms stl = pfx ++ rhs) /\
        MEM (item N (rhs,[])) (itemlist csl) /\ (i=sfx)``,

SRW_TAC [] [] THEN
`rderives ag (pfx++[NTS N]++sfx) (pfx++rhs++sfx)` by METIS_TAC [rdres1, rderives_same_append_left, rderives_append, APPEND_NIL] THEN
Cases_on `N=startSym ag` THEN1
   (SRW_TAC [] [] THEN
   `rhs = [NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
   FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]) THEN

   Cases_on `pfx` THEN
   SRW_TAC [] [] THEN
   FULL_SIMP_TAC (srw_ss()) [] THEN1

     (`!csli stli rhs pfx sfx N onstk ininp.
         (auggr g st eof = SOME ag) ==>
         RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
         (csli = MAP FST stli ++ [(NTS st,initItems ag (rules ag))]) ==>
         MEM (rule N rhs) (rules ag) ==>
         ~(N = startSym ag) ==>
         EVERY isTmnlSym (pfx ++ rhs ++ sfx) ==>
         (slrmac ag = SOME m) ==>
         (rhs = onstk ++ ininp) ==>
         (stackSyms stli = pfx ++ onstk) ==>
         IS_PREFIX (pfx ++ rhs) (stackSyms stli) ==>
         (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
         (LENGTH csli = LENGTH stli + 1) ==>
          parseInv (ag,stli,csli) ==>
         validItemInv (ag,stli) ==>
         ?i stl csl.
           takesSteps (LENGTH ininp) (parse m)
             (exitCond (eof,NTS (startSym g))) (ininp ++ sfx,stli,csli)
             (i,stl,csl) /\ (stackSyms stl = pfx ++ rhs) /\ (i = sfx) /\
           MEM (item N (rhs,[])) (itemlist csl)`
	 by METIS_TAC [lem1] THEN
     FIRST_X_ASSUM (Q.SPECL_THEN
	  [`[(NTS st,initItems ag (rules ag))]`,
	   `[]:(((α,β)symbol # (α,β)state)# (α,β)ptree) list`,
	   `rhs`,`[]`,`sfx`,`N`,`[]`,`rhs`] MP_TAC) THEN
     SRW_TAC [] [] THEN
     METIS_TAC [parseInvInit, validItemInvInit]) THEN

     `parseInv (ag,[],[(NTS st,initItems ag (rules ag))])`
     by METIS_TAC [parseInvInit] THEN
     `validItemInv
         ((ag :(α, β) grammar),
          ([] :(((α, β) symbol # (α, β) state) # (α, β) ptree) list))`
     by METIS_TAC [validItemInvInit] THEN
     IMP_RES_TAC lem2 THEN
     FIRST_X_ASSUM (Q.SPECL_THEN [`sfx`, `h::t`, `N`] MP_TAC) THEN
     SRW_TAC [][] THEN
     FIRST_X_ASSUM (Q.SPECL_THEN [`[]`, `rhs`] MP_TAC) THEN
     SRW_TAC [][] THEN
     FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
     `!csli stli rhs pfx sfx N onstk ininp.
         (auggr g st eof = SOME ag) ==>
         RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
         (csli = MAP FST stli ++ [(NTS st,initItems ag (rules ag))]) ==>
         MEM (rule N rhs) (rules ag) ==>
         ~(N = startSym ag) ==>
         EVERY isTmnlSym (pfx ++ rhs ++ sfx) ==>
         (slrmac ag = SOME m) ==>
         (rhs = onstk ++ ininp) ==>
         (stackSyms stli = pfx ++ onstk) ==>
         IS_PREFIX (pfx ++ rhs) (stackSyms stli) ==>
         (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
         (LENGTH csli = LENGTH stli + 1) ==>
          parseInv (ag,stli,csli) ==>
         validItemInv (ag,stli) ==>
         ?i stl csl.
           takesSteps (LENGTH ininp) (parse m)
             (exitCond (eof,NTS (startSym g))) (ininp ++ sfx,stli,csli)
             (i,stl,csl) /\ (stackSyms stl = pfx ++ rhs) /\ (i = sfx) /\
           MEM (item N (rhs,[])) (itemlist csl)`
	 by METIS_TAC [lem1] THEN
     `?stl csl.
             takesSteps (SUC (LENGTH t)) (parse m)
               (exitCond (eof,NTS (startSym g)))
               (h::(t ++ rhs ++ sfx),[],[(NTS st,initItems ag (rules ag))])
               (rhs++sfx,stl,csl) /\ (stackSyms stl = h::t)`
	 by METIS_TAC [parseInvInit, validItemInvInit] THEN
     FIRST_X_ASSUM (Q.SPECL_THEN
	  [`csl`,
	   `stl`,
	   `rhs`,`h::t`,`sfx`,`N`,`[]`,`rhs`] MP_TAC) THEN
     SRW_TAC [] [] THEN
     FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_REFL,IS_PREFIX_APPEND] THEN
     `(csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))])`
	 by METIS_TAC [takesStepsCslStlEq,MAP,APPEND_NIL] THEN
     FULL_SIMP_TAC (srw_ss()) [] THEN
     SRW_TAC [] [] THEN

`parseInv (ag,[],[(NTS st,initItems ag (rules ag))])`
    by METIS_TAC [parseInvInit] THEN
`validItemInv (ag,[])`
    by METIS_TAC [validItemInvInit] THEN
`!n sl stl csl stl' csl' sl'.
         (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
         takesSteps (SUC n) (parse m)
           (exitCond (eof,NTS (startSym g))) (sl,stl,csl)
           (sl',stl',csl') ==>
         EVERY isTmnlSym sl ==>
         parseInv (ag,stl,csl) ==>
         (auggr g st eof = SOME ag) ==>
         (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
         (slrmac ag = SOME m) ==>
         parseInv (ag,stl',csl')`
    by METIS_TAC [takesStepsParseInv] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH t`,`h::(t ++ rhs ++ sfx)`,
			     `[]`,`[(NTS st,initItems ag (rules ag))]`,
			     `stl`,`MAP FST stl++[(NTS st,initItems ag (rules ag))]`,
			     `rhs++sfx`]
			    MP_TAC) THEN
SRW_TAC [] [] THEN
`!n sl stl csl sl' stl' csl'.
         (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
         takesSteps (SUC n) (parse m)
           (exitCond (eof,NTS (startSym g))) (sl,stl,csl)
           (sl',stl',csl') ==>
         (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
         EVERY isTmnlSym sl ==>
         ~(sl = []) ==>
         (slrmac ag = SOME m) ==>
         (auggr g st eof = SOME ag) ==>
         parseInv (ag,stl,csl) ==>
         validItemInv (ag,stl) ==>
         validItemInv (ag,stl')`
    by METIS_TAC [takesStepsValidItemInv] THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`LENGTH t`,`h::(t ++ rhs ++ sfx)`,
			     `[]`,`[(NTS st,initItems ag (rules ag))]`,
			     `rhs++sfx`,`stl`,`MAP FST stl++[(NTS st,initItems ag (rules ag))]`]
			    MP_TAC) THEN
SRW_TAC [] [] THEN
IMP_RES_TAC parseMacGuard THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
METIS_TAC [takesStepsAdd, validItemInvInit]);

val validItemInvInit = store_thm
("validItemInvInit",
``!m g sl st.
validItemInv (ag, [])``,
SRW_TAC [] [validItemInv_def] THEN
FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
SRW_TAC [] [stackSyms_def, trans_def, FRONT_DEF, stkSymsCsl_def,
	    stkItl_def, initStateCsl_def] THEN
METIS_TAC [NULL]);


val _ = export_theory ();
