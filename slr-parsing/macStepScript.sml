open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory rich_listTheory
pairTheory

open regexpTheory grammarDefTheory boolLemmasTheory listLemmasTheory
setLemmasTheory whileLemmasTheory parseTreeTheory followSetDefTheory
yaccDefTheory parseProp1DefTheory parseProp2DefTheory
lrGrammarDefTheory validItemInvTheory

val _ = new_theory "macStep"

val sgotoMemItlExists = store_thm
("sgotoMemItlExists",
``!itl h.~(sgoto ag itl h = []) ==>
   ?l r1 r2.MEM (item l (r1,h::r2)) itl``,
Induct_on `itl` THEN 
SRW_TAC [][sgoto_def,nextState_def,iclosure,moveDot_def] THEN
Cases_on `moveDot (h::itl) h'`
THENL[
      FULL_SIMP_TAC (srw_ss()) [iclosure],
      
      `!e.MEM e (moveDot (h::itl) h') ==>
         ?l r1 r2.
           (e = item l (r1 ++ [h'],r2)) 
	   /\ MEM (item l (r1,h'::r2)) (h::itl)`
	  by METIS_TAC [mdMem] THEN      
      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [iclosure_mem,list_mem1,NOT_CONS_NIL]
      ])


val sgotoOverEof = store_thm ("sgotoOverEof",
``(auggr g st eof = SOME ag) ==>
(slrmac ag = SOME m) ==>
validItl ag itl ==>
(sgoto ag itl (TS eof) = h::t) ==>
MEM (item (startSym ag) ([NTS (startSym g)],[TS eof]))
   itl``,

SRW_TAC [][] THEN
Cases_on `?lhs r1 r2.MEM (item lhs (r1,[TS eof]++r2)) itl`
THENL[
      
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `validItl ag [item lhs (r1, TS eof::r2)]`
	  by METIS_TAC [rgr_r9eq,validItl_append] THEN
      FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
      `(lhs = startSym ag) /\ (r1 = [NTS (startSym g)]) /\ (r2 = [])` 
	  by METIS_TAC [auggrEofInRhs,APPEND,APPEND_ASSOC] THEN
      FULL_SIMP_TAC (srw_ss()) [],


      FULL_SIMP_TAC (srw_ss()) [] THEN
      METIS_TAC [sgotoMemItlExists,NOT_CONS_NIL]
      ])



val sv_1 = store_thm("sv_1",
``!p.stackValid ag p ((s,r)::rst) ==>
  EVERY (validItem ag (stackSyms p)) r``,
Induct_on `p` THEN 
SRW_TAC [] [stackValid_def, itemlist_def,stackSyms_def] THEN
Cases_on `rst` THEN
FULL_SIMP_TAC (srw_ss()) [stackValid_def, itemlist_def])


val slrmacReduceRulesEq = store_thm ("slrmacReduceRulesEq",
``!ag lh lhs' rhs rhs'.(slrmac ag = SOME m) ==>
(trans ag (initItems ag (rules ag),pfx) = SOME itl) ==>
MEM (item lhs (rhs,[])) itl  ==>
MEM (item lhs' (rhs',[])) itl ==>      
      (?h.isTmnlSym h /\ h IN followSet ag (NTS lhs) /\
       h IN followSet ag (NTS lhs')) ==>
      ((lhs=lhs') /\ (rhs=rhs'))``,

SRW_TAC [][] THEN
`(item lhs (rhs,[]))=(item lhs' (rhs',[]))`  
    by METIS_TAC [slrmacCompItemsEq,completeItem_def,itemLhs_def] THEN
FULL_SIMP_TAC (srw_ss()) []
)



val macStepDoRedExists = store_thm 
("macStepDoRedExists",
``(auggr g st eof = SOME ag) ==>
(slrmac ag = SOME m) ==>
EVERY isTmnlSym sl ==> 
(csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
 ~(ininp = []) ==> 
EVERY isTmnlSym (onstk++ininp) ==>
(sl=onstk++ininp) ==>
viablePfx ag (N,h) (stackSyms stl ++ ininp)
           (stackSyms stl) ==>
parseInv (ag, stl,csl) ==>
validItemInv (ag, stl, csl) ==>
(getState (sgoto ag,reduce ag) (itemlist csl) (HD ininp) 
 = REDUCE ru) ==>
?sl' stl' csl'.
(doReduce m (ininp,stl,csl) ru = SOME (sl',stl',csl')) /\
(stackSyms stl'= 
stackSyms (pop stl (LENGTH (ruleRhs ru))) ++ [NTS (ruleLhs ru)]) /\
(sl'=ininp)``,

SRW_TAC [] [] THEN
Cases_on `stl` THEN
Cases_on `ininp` THEN
SRW_TAC [] [] THEN
`slrmac ag = SOME (sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] 
THENL[

(*stl=[]*)
FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION] THEN
Cases_on `ru` THEN 
FULL_SIMP_TAC(srw_ss()) [stackSyms_def, itemlist_def] THEN
Q.ABBREV_TAC `r'=initItems ag (rules ag)` THEN
`MEM (item s (l,[])) r'` by METIS_TAC [getState_mem_itl, parseInv_def, validStates_def] THEN
`MEM (rule s l) (rules ag)` by METIS_TAC [getstate_red, validStates_def, parseInv_def] THEN
`h' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def, parseInv_def] THEN
Q.ABBREV_TAC `prestl = ([]:((symbol#state)#ptree)list)` THEN
FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv_def] THEN
`validStlItems prestl [(item s (l,[]))]` by METIS_TAC [rgr_r9eq, validStlItems_append,vsiImpvi] THEN
FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
`?p.stackSyms prestl = p++l` by METIS_TAC [isSuffix_APPEND] THEN
`?x.addRule prestl (rule s l) = SOME x` by METIS_TAC [addRule_SOME, parseInv_def] THEN
`LENGTH prestl >= LENGTH l` by METIS_TAC [isSuffix_LENGTH, stackSyms_len] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parseInv_def, itemlist_def,stackValid_def] THEN
`validItem ag (p++l) (item s (l,[]))`
    by METIS_TAC [EVERY_APPEND, rgr_r9eq, EVERY_DEF, SND, HD,sv_1] THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
FULL_SIMP_TAC (arith_ss) [stackSyms_def, viablePfx_def,handleg_def, IS_PREFIX, MAP, REVERSE] THEN
SRW_TAC [] [] THEN
`h'::t=sfx` by (SRW_TAC [] [] THEN
SPOSE_NOT_THEN ASSUME_TAC THEN
Cases_on `pfx++h` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [] THEN
Cases_on `pfx` THEN
Cases_on `h` THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] []
THENL[
      `MEM (item N ([],h'::t)) (initItems ag (rules ag))`
	  by METIS_TAC [initItemsHdNt] THEN
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
	  by METIS_TAC [trans_def] THEN
      METIS_TAC [slrmacNotValid, APPEND_NIL],

      `RTC (rderives ag) [NTS (startSym ag)]
         ((h'::t) ++ [NTS N] ++ sfx)` by FULL_SIMP_TAC (srw_ss()) [] THEN
      `?lhs rhs.
             MEM (item lhs ([],h'::rhs))
               (initItems ag (rules ag))` 
	  by METIS_TAC [initItemsNtInBtwn, NOT_CONS_NIL, HD, EVERY_DEF] THEN
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
	  by METIS_TAC [trans_def] THEN
      METIS_TAC [slrmacNotValid, APPEND_NIL],

      `RTC (rderives ag) [NTS (startSym ag)]
         ((h'::t) ++ [NTS N] ++ sfx)` by FULL_SIMP_TAC (srw_ss()) [] THEN
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
	  by METIS_TAC [trans_def] THEN
      `?lhs rhs.
             MEM (item lhs ([],h'::rhs))
               (initItems ag (rules ag))` 
	  by METIS_TAC [initItemsNtInBtwn, NOT_CONS_NIL, HD, EVERY_DEF, EVERY_APPEND] THEN
      METIS_TAC [slrmacNotValid, APPEND_NIL]
      ]) THEN
SRW_TAC [] [] THEN
`pfx++h=[]` by METIS_TAC [APPEND_11, APPEND_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [doReduce_def, LET_THM] THEN
Cases_on `h'` THEN 
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def, pop_def, ruleRhs_def, ruleLhs_def] THEN
SRW_TAC [] [] THEN
`MEM (item N ([],[])) (initItems ag (rules ag))`
by METIS_TAC [initItemsHdNt] THEN
`(TS s') IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
`trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
    by METIS_TAC [trans_def] THEN
`item s ([],[]) = item N ([],[])` by
METIS_TAC [slrmacCompItemsEq, completeItem_def, itemLhs_def, isTmnlSym_def] THEN
SRW_TAC [] [] THEN
`([NTS (startSym ag)]=(NTS N::TS s'::t)) \/
 ?u.RTC (rderives ag) [NTS (startSym ag)] u
 /\ rderives ag u (NTS N ::TS s'::t)`
by METIS_TAC [RTC_CASES2] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN
Cases_on `rhs` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] []
THENL[
      `MEM (item lhs ([],NTS N::t')) (initItems ag (rules ag))`
      by METIS_TAC [initItemsHdNt] THEN
      METIS_TAC [sgotoNotNil],

      Cases_on `t'` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
      THENL[	    
	    `(TS s') IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
	     Cases_on `lhs=startSym ag` THEN
	     SRW_TAC [][]
             THENL[
		   METIS_TAC [auggrStartRule,APPEND,NOT_CONS_NIL],

		   `(NTS N::NTS lhs::TS s'::t) =
	             [NTS N]++ [NTS lhs] ++ TS s'::t`
		       by METIS_TAC [APPEND,APPEND_ASSOC] THEN
		   `?itl.(trans ag (initItems ag (rules ag),[NTS N])
	            = SOME itl)` 
		       by METIS_TAC [rtcRdImpTrans,isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
		   FULL_SIMP_TAC (srw_ss()) [trans_def,sgoto_def,nextState_def] THEN
		   Cases_on `moveDot (initItems ag (rules ag)) (NTS N)` THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [iclosure_mem,MEM]
		   ],

	    `RTC (rderives ag) [NTS (startSym ag)]
             (([NTS N] ++[TS s']++t'')++[NTS lhs]++s2)` by FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `lhs=startSym ag` THEN
	     SRW_TAC [][]
             THENL[
		   METIS_TAC [auggrStartRule,APPEND,NOT_CONS_NIL],

		   `?itl.(trans ag (initItems ag (rules ag),[NTS N]++[TS s']++t'')
			  = SOME itl)` 
		       by METIS_TAC [rtcRdImpTrans,isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
		   FULL_SIMP_TAC (srw_ss()) [transAppend] THEN
		   FULL_SIMP_TAC (srw_ss()) [trans_def,sgoto_def,nextState_def] THEN
		   Cases_on `moveDot (initItems ag (rules ag)) (NTS N)` THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [iclosure_mem,MEM]
		   ]],


      Cases_on `t'` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
      THENL[

	     Cases_on `lhs=startSym ag` THEN
	     SRW_TAC [][]
             THENL[
		   `(TS s'::t'')=[NTS (startSym g);TS eof]` by METIS_TAC [auggrStartRule] THEN
		   FULL_SIMP_TAC (srw_ss()) [],

		   `(NTS N::NTS lhs::s2) =
	             [NTS N]++ [NTS lhs] ++ s2`
		       by METIS_TAC [APPEND,APPEND_ASSOC] THEN
		   `?itl.(trans ag (initItems ag (rules ag),[NTS N])
	            = SOME itl)` 
		       by METIS_TAC [rtcRdImpTrans,isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
		   FULL_SIMP_TAC (srw_ss()) [trans_def,sgoto_def,nextState_def] THEN
		   Cases_on `moveDot (initItems ag (rules ag)) (NTS N)` THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [iclosure_mem,MEM]
		   ],

	     Cases_on `lhs=startSym ag` THEN
	     SRW_TAC [][]
             THENL[
		   `(h'::t'')=[NTS (startSym g);TS eof]` by METIS_TAC [auggrStartRule] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   SRW_TAC [] [] THEN
		   FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

		   `(NTS N::TS s'::(t''' ++ [NTS lhs] ++ s2))=
        	     ((NTS N::TS s'::t''') ++ [NTS lhs] ++ s2)`
		       by METIS_TAC [APPEND,APPEND_ASSOC] THEN
		   `?itl.(trans ag (initItems ag (rules ag),NTS N::TS s'::t''')
	            = SOME itl)` 
		       by METIS_TAC [rtcRdImpTrans,isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
		   FULL_SIMP_TAC (srw_ss()) [trans_def,sgoto_def,nextState_def,transAppend] THEN
		   Cases_on `moveDot (initItems ag (rules ag)) (NTS N)` THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [iclosure_mem,MEM]
		   ]
		 ]
	    ],

(*~stl = []*)
Cases_on `h'` THEN
Cases_on `q` THEN
SRW_TAC [] []  THEN
FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv_def] THEN
Q.ABBREV_TAC `stkSyms = stackSyms t ++ [q']` THEN
Q.ABBREV_TAC `prestl = (((q',r'),r)::t)` THEN
Q.ABBREV_TAC `precsl = (q',r')::
                  (MAP FST t ++
                   [(NTS st,initItems ag (rules ag))])` THEN
FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION] THEN
Cases_on `ru` THEN 
`MEM (item s (l,[])) r'` by METIS_TAC [getState_mem_itl, parseInv_def, validStates_def] THEN
`MEM (rule s l) (rules ag)` by METIS_TAC [getstate_red, validStates_def, parseInv_def] THEN
`h'' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def, parseInv_def] THEN
`validStlItems prestl [(item s (l,[]))]` by METIS_TAC [rgr_r9eq, validStlItems_append,vsiImpvi] THEN
FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
`?p.stackSyms prestl = p++l` by METIS_TAC [isSuffix_APPEND] THEN
`?x.addRule prestl (rule s l) = SOME x` by METIS_TAC [addRule_SOME, parseInv_def] THEN
`LENGTH prestl >= LENGTH l` by METIS_TAC [isSuffix_LENGTH, stackSyms_len] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [parseInv_def, stackValid_def,itemlist_def] THEN
`validItem ag (p++l) (item s (l,[]))`
    by METIS_TAC [EVERY_APPEND, rgr_r9eq, EVERY_DEF, SND, HD,sv_1] THEN
`stkSyms = stackSyms (((q',r'),r)::t)`
    by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
`(s=startSym ag) \/
           ?lhs r1 r2. validItem ag 
         (stackSyms (pop (((q',r'),r)::t) (LENGTH l))) 
         (item lhs (r1,NTS s::r2))` 
	by METIS_TAC [validItemPopStk]
     THENL[
       SRW_TAC [] [] THEN
       METIS_TAC [auggrFsStNil],

       `IS_PREFIX (REVERSE (((q',r'),r)::t))
            (REVERSE (pop (((q',r'),r)::t) (LENGTH l)))`
	       by METIS_TAC [isPfxRevPopRefl] THEN
       Cases_on `pop (((q',r'),r)::t) (LENGTH l) = []`
       THENL[
         SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [stackSyms_def, validItem_def] THEN
	 SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [] THEN
	 `MEM (item lhs ([], NTS s::r2))
              (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt] THEN
	 UNABBREV_ALL_TAC THEN
	 FULL_SIMP_TAC (srw_ss()) [doReduce_def, ruleLhs_def, ruleRhs_def, LET_THM, push_def] THEN
	 Cases_on `h''` THEN
	 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN	 
	 Cases_on `pop
              ((q',r')::
                   (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
              (LENGTH l) = []` THEN
	     Cases_on `sgoto ag
                 (SND
                    (HD
                       (pop
                          ((q',r')::
                               (MAP FST t ++
                                [(NTS st,
                                  initItems ag (rules ag))]))
                          (LENGTH l)))) (NTS s) = []` THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   
		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

                   `pop  (MAP FST (((q',r'),r)::t)
                         ++ [(NTS st,initItems ag (rules ag))]) 
                       (LENGTH l) = 
                     [(NTS st,initItems ag (rules ag))]` 
		   by METIS_TAC [cslInit, addrule_len] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [sgotoNotNil]
		   ],


	     (* ~ pop stl = [] *)

	     `(trans ag (initItems ag (rules ag),
                 stackSyms (REVERSE (REVERSE 
                  (pop (((q',r'),r)::t) (LENGTH l))))) =
               SOME (stkItl (REVERSE (REVERSE (pop (((q',r'),r)::t)
                            (LENGTH l))))))`
	       by METIS_TAC [rev_nil, validItemInv_def, nullNil] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `MEM (item lhs (r1,NTS s::r2)) 
               (stkItl ((pop (((q',r'),r)::t) 
                        (LENGTH l))))`
		 by METIS_TAC [transImpValidItem] THEN	     
	     UNABBREV_ALL_TAC THEN
	     FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, ruleLhs_def, ruleRhs_def, push_def] THEN	     
	     Cases_on `h''` THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
	     Cases_on `pop
              ((q',r')::
                   (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
              (LENGTH l) = []` THEN
	     Cases_on `sgoto ag
                 (SND
                    (HD
                       (pop
                          ((q',r')::
                               (MAP FST t ++
                                [(NTS st,
                                  initItems ag (rules ag))]))
                          (LENGTH l)))) (NTS s) = []` THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   FULL_SIMP_TAC (srw_ss()) [stkItl_def] THEN
		   IMP_RES_TAC l1 THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   `sgoto ag (SND (FST (HD (pop (((q',r'),r)::t) 
                     (LENGTH l))))) (NTS s) = []` 
                     by METIS_TAC [] THEN
		   METIS_TAC [sgotoNotNil]
		   ]]]])


val macStepInvStlNotNil = 
store_thm ("macStepInvStlNotNil",
``!m g.(auggr g st eof = SOME ag) ==>
EVERY isTmnlSym sl ==> 
(SOME m=slrmac ag) ==> 
(csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
~(stl=[]) ==>
~(exitCond (eof,NTS (startSym g)) (ininp,stl,csl)) ==> 
 ~(ininp = []) ==> 
EVERY isTmnlSym (onstk++ininp) ==>
(sl=onstk++ininp) ==>
viablePfx ag (N,h) (stackSyms stl ++ ininp)
           (stackSyms stl) ==>
parseInv (ag, stl,csl) ==>
validItemInv (ag, stl, csl) ==>
?sl' stl' csl'.((parse (SOME m) (ininp, stl, csl) 
   = SOME (sl',stl',csl')))``,

SRW_TAC [] [] THEN
Cases_on `stl` THEN
SRW_TAC [] [] THEN
`slrmac ag = SOME (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN 
Cases_on `h'` THEN
Cases_on `q` THEN
FULL_SIMP_TAC (srw_ss()) [parse_def, LET_THM] THEN
FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION] THEN
Cases_on `ininp` THEN
SRW_TAC [] [] THEN
Cases_on `t'` THEN
Cases_on `getState (sgoto ag, reduce ag) r' h'` THEN SRW_TAC [] [] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [] 
THENL[
	
      FULL_SIMP_TAC (srw_ss()) [parseInv_def, itemlist_def,stackValid_def,validStlItemsStack_def] THEN
	Q.ABBREV_TAC `stkSyms = stackSyms t ++ [q']` THEN
	Q.ABBREV_TAC `prestl = (((q',r'),r)::t)` THEN
	Q.ABBREV_TAC `precsl = (q',r')::
                  (MAP FST t ++
                   [(NTS st,initItems ag (rules ag))])` THEN
    FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION, itemlist_def] THEN
    Cases_on `r''` THEN 
    `MEM (item s (l,[])) r'` by METIS_TAC [getState_mem_itl, validStates_def, parseInv_def] THEN
    `MEM (rule s l) (rules ag)` by METIS_TAC [getstate_red, validStates_def, parseInv_def] THEN
    `h' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
    FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv_def] THEN
    `validStlItems prestl [(item s (l,[]))]` by METIS_TAC [rgr_r9eq, validStlItems_append,vsiImpvi] THEN
    FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
    `?p.stackSyms prestl = p++l` by METIS_TAC [isSuffix_APPEND] THEN
    `?x.addRule prestl (rule s l) = SOME x` by METIS_TAC [addRule_SOME] THEN
    `LENGTH prestl >= LENGTH l` by METIS_TAC [isSuffix_LENGTH, stackSyms_len] THEN
    SRW_TAC [] [] THEN
    `validItem ag stkSyms (item s (l,[]))`
	by METIS_TAC [EVERY_APPEND, rgr_r9eq, EVERY_DEF] THEN
    `stkSyms = stackSyms (((q',r'),r)::t)`
	by FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
    `(s=startSym ag) \/
        ?lhs r1 r2. validItem ag 
         (stackSyms (pop (((q',r'),r)::t) (LENGTH l))) 
         (item lhs (r1,NTS s::r2))` 
	by METIS_TAC [validItemPopStk]
     THENL[
       SRW_TAC [] [] THEN
       METIS_TAC [auggrFsStNil],

       `IS_PREFIX (REVERSE (((q',r'),r)::t))
            (REVERSE (pop (((q',r'),r)::t) (LENGTH l)))`
	       by METIS_TAC [isPfxRevPopRefl] THEN
       Cases_on `pop (((q',r'),r)::t) (LENGTH l) = []`
       THENL[
         SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [stackSyms_def, validItem_def] THEN
	 SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [] THEN
	 `MEM (item lhs ([], NTS s::r2))
              (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt] THEN
	 UNABBREV_ALL_TAC THEN
	 FULL_SIMP_TAC (srw_ss()) [doReduce_def, ruleLhs_def, ruleRhs_def, LET_THM, push_def] THEN
	 Cases_on `h'` THEN
	 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN	 
	 Cases_on `pop
              ((q',r')::
                   (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
              (LENGTH l) = []` THEN
	     Cases_on `sgoto ag
                 (SND
                    (HD
                       (pop
                          ((q',r')::
                               (MAP FST t ++
                                [(NTS st,
                                  initItems ag (rules ag))]))
                          (LENGTH l)))) (NTS s) = []` THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   
		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

                   `pop  (MAP FST (((q',r'),r)::t)
                         ++ [(NTS st,initItems ag (rules ag))]) 
                       (LENGTH l) = 
                     [(NTS st,initItems ag (rules ag))]` 
		   by METIS_TAC [cslInit, addrule_len] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [sgotoNotNil]
		   ],


	     (* ~ pop stl = [] *)

	     `(trans ag (initItems ag (rules ag),
                 stackSyms (REVERSE (REVERSE 
                  (pop (((q',r'),r)::t) (LENGTH l))))) =
               SOME (stkItl (REVERSE (REVERSE (pop (((q',r'),r)::t)
                            (LENGTH l))))))`
	       by METIS_TAC [rev_nil, validItemInv_def, nullNil] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `MEM (item lhs (r1,NTS s::r2)) 
               (stkItl ((pop (((q',r'),r)::t) 
                        (LENGTH l))))`
		 by METIS_TAC [transImpValidItem] THEN	     
	     UNABBREV_ALL_TAC THEN
	     FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, ruleLhs_def, ruleRhs_def, push_def] THEN	     
	     Cases_on `h'` THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
	     Cases_on `pop
              ((q',r')::
                   (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
              (LENGTH l) = []` THEN
	     Cases_on `sgoto ag
                 (SND
                    (HD
                       (pop
                          ((q',r')::
                               (MAP FST t ++
                                [(NTS st,
                                  initItems ag (rules ag))]))
                          (LENGTH l)))) (NTS s) = []` THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   FULL_SIMP_TAC (srw_ss()) [stkItl_def] THEN
		   IMP_RES_TAC l1 THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   `sgoto ag (SND (FST (HD (pop (((q',r'),r)::t) 
                     (LENGTH l))))) (NTS s) = []` 
                     by METIS_TAC [] THEN
		   METIS_TAC [sgotoNotNil]
		   ]]],

      (* GOTO F *)
      FULL_SIMP_TAC (srw_ss()) [parseInv_def, itemlist_def,stackValid_def,validStlItemsStack_def] THEN
	Q.ABBREV_TAC `stkSyms = stackSyms t ++ [q']` THEN
	Q.ABBREV_TAC `prestl = (((q',r'),r)::t)` THEN
	Q.ABBREV_TAC `precsl = (q',r')::
                  (MAP FST t ++
                   [(NTS st,initItems ag (rules ag))])` THEN
	FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def] THEN
	FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
	Cases_on `sgoto ag r' h'` THEN
	Cases_on `reduce ag r' (sym2Str h')` THEN
	FULL_SIMP_TAC (srw_ss()) []
        THENL[
	      Cases_on `LENGTH t'=0` THEN
	      FULL_SIMP_TAC (srw_ss()) [],

	      SRW_TAC [] [] THEN
	      `pfx++h=stkSyms` by
	      (SPOSE_NOT_THEN ASSUME_TAC THEN
	      `?l. ~(l = []) /\ (stkSyms ++ l = pfx ++ h)`
		  by METIS_TAC [IS_PREFIX_APPEND, APPEND_NIL] THEN
	      `(?l1 l2.(l=l1++l2) /\
                (pfx=stkSyms ++l1) /\
                (h=l2)) \/
                (?h1 h2.(h=h1++h2) /\
                (stkSyms = pfx++h1) /\
                (l=h2)) \/
                ((stkSyms = pfx) /\ 
                (l=h))` by METIS_TAC [twoListAppEq] THEN
                SRW_TAC [] []
                THENL[
		      `[h']=l1++h++sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
		      Cases_on `l1` THEN Cases_on `h` THEN
		      Cases_on `sfx` THEN
		      SRW_TAC [] [] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      SRW_TAC [] [] THEN
		      FULL_SIMP_TAC (srw_ss()) []
	              THENL[
			    Cases_on `N=startSym ag` THEN
			    SRW_TAC [] []
                	    THENL[
				  `[h']=[NTS (startSym g); TS eof]`
				      by METIS_TAC [auggrStartRule] THEN
				  FULL_SIMP_TAC (srw_ss()) [],

				  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
				  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
				  ],

			    Cases_on `N=startSym ag` THEN
			    SRW_TAC [] []
                 	    THENL[
				  METIS_TAC [auggrStartRule, MEM, MEM_APPEND],
				  
				  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
				  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
				  ]
			    ],

		      `[h']=h2++sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
		      Cases_on`h2` THEN Cases_on `sfx` THEN
		      SRW_TAC [] [] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      SRW_TAC [] [] THEN      
		      Cases_on `N=startSym ag` THEN
		      SRW_TAC [] []
                      THENL[

			    `h1++[h]=[NTS (startSym g); TS eof]`
				by METIS_TAC [auggrStartRule] THEN
			    SRW_TAC [] [] THEN
			    Cases_on `h1` THEN
			    SRW_TAC [] [] THEN
			    FULL_SIMP_TAC (srw_ss()) [] THEN
			    Cases_on `t''` THEN
			    FULL_SIMP_TAC (srw_ss()) [] THEN
			    SRW_TAC [] [] THEN
			    `MEM (item (startSym ag) 
		            ([NTS (startSym g)],[TS eof])) r'`
				by METIS_TAC [sgotoOverEof,parseInv_def,validStates_def] THEN
			    FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv_def] THEN
			    `validStlItems prestl 
                             [item (startSym ag) 
		             ([NTS (startSym g)],[TS eof])]`
				by METIS_TAC [rgr_r9eq, validStlItems_append,vsiImpvi] THEN
			    UNABBREV_ALL_TAC THEN
			    FULL_SIMP_TAC (srw_ss()) [validStlItems_def,itemFstRhs_def, isSuffix_def, REVERSE_APPEND, stackSyms_def, IS_PREFIX],

			    `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
			    Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
			    ],

		      `[h']=h++sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
		      Cases_on `h` THEN Cases_on `sfx` THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      SRW_TAC [] [] THEN
		      Cases_on `N=startSym ag` THEN
		      SRW_TAC [] []
                      THENL[
			    `[h']=[NTS (startSym g); TS eof]`
				by METIS_TAC [auggrStartRule] THEN
			    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

			    `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
			    Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
			    ]]) THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [exitCond_def] 
              THENL[

		    FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
		    `validItem ag (REVERSE (MAP FST (MAP FST t)) 
					   ++ [NTS (startSym g)]) 
			     (item (startSym ag) 
				   ([NTS (startSym g)],[TS eof]))`
	                 by METIS_TAC [rgr_r9eq,EVERY_APPEND,EVERY_DEF] THEN
		    FULL_SIMP_TAC (srw_ss()) [validItem_def] THEN
		    `(sfx=[]) /\ (REVERSE (MAP FST (MAP FST t))=[])`
			by METIS_TAC [auggrRtcRderivesPfxSfxNil] THEN
		    Cases_on `t` THEN
		    FULL_SIMP_TAC (srw_ss()) [stackSyms_def],


		    UNABBREV_ALL_TAC THEN
		    SRW_TAC [][],

		    `sfx=[h']` by METIS_TAC[APPEND_11, APPEND_ASSOC] THEN
		    SRW_TAC [] [] THEN
		    `validItem ag (stackSyms prestl) (item N (h,[]))`
			by (SRW_TAC [] [validItem_def] THEN
			    MAP_EVERY Q.EXISTS_TAC [`pfx`, `[h']`] THEN
		      SRW_TAC [] [] 
		      THENL[
			    METIS_TAC [rdres1, rderives_append],
			    
			    UNABBREV_ALL_TAC THEN
			    FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND]
			    ]) THEN
		    `(trans ag
			    (initItems ag (rules ag),
			     stackSyms (REVERSE (REVERSE prestl))) =
			    SOME (stkItl (REVERSE (REVERSE prestl))))` 
			by METIS_TAC [parseInv_def, IS_PREFIX_REFL, NOT_CONS_NIL, rev_nil, nullNil, validItemInv_def] THEN
		    UNABBREV_ALL_TAC THEN
		    FULL_SIMP_TAC (srw_ss()) [stkItl_def] THEN
		    `MEM (item N (h,[])) r'` by METIS_TAC [transImpValidItem] THEN
		    `h' IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
		    METIS_TAC [mem_reduce, MEM, MEM_APPEND],

		    `sfx=[h']` by METIS_TAC[APPEND_11, APPEND_ASSOC] THEN
		    SRW_TAC [] [] THEN
		    `validItem ag (stackSyms prestl) (item N (h,[]))`
			by (SRW_TAC [] [validItem_def] THEN
			    MAP_EVERY Q.EXISTS_TAC [`pfx`, `[h']`] THEN
		      SRW_TAC [] [] 
		      THENL[
			    METIS_TAC [rdres1, rderives_append],
			    
			    UNABBREV_ALL_TAC THEN
			    FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND]
			    ]) THEN
		    `(trans ag
			    (initItems ag (rules ag),
			     stackSyms (REVERSE (REVERSE prestl))) =
			    SOME (stkItl (REVERSE (REVERSE prestl))))` 
			by METIS_TAC [parseInv_def, IS_PREFIX_REFL, NOT_CONS_NIL, rev_nil, nullNil, validItemInv_def] THEN
		    UNABBREV_ALL_TAC THEN
		    FULL_SIMP_TAC (srw_ss()) [stkItl_def] THEN
		    `MEM (item N (h,[])) r'` by METIS_TAC [transImpValidItem] THEN
		    `h' IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
		    METIS_TAC [mem_reduce, MEM, MEM_APPEND]],

	      Cases_on `itemEqRuleList (h''::t') (h'''::t'')` THEN
	      FULL_SIMP_TAC (srw_ss()) []
	      ],

	(* getstate = NA *)

	FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def, itemlist_def, parseInv_def,stackValid_def,validStlItemsStack_def] THEN
	FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
	`(?l1 l2.(l=l1++l2) /\
          (pfx=stackSyms t ++ [q']++l1) /\
          (h=l2)) \/
          (?h1 h2.(h=h1++h2) /\
          (stackSyms t ++ [q'] = pfx++h1) /\
          (l=h2)) \/
          ((stackSyms t ++ [q'] = pfx) /\ 
          (l=h))` by 
		  (SRW_TAC [] [] THEN
                   `?l1 l2.(pfx=stackSyms t ++[q'] ++l1) /\ (h=l2) /\
                    (l=l1++l2) \/
                    (h=l2++[q']++l) /\ (pfx=l1) /\
                   (stackSyms t = l1 ++ l2)` by METIS_TAC [list_r6] THEN
		   SRW_TAC [] [])
	THENL[

      SRW_TAC [] [] THEN
      `[h']=l1++h++sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      Cases_on `l1` THEN Cases_on `h` THEN
      Cases_on `sfx` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
      THENL[
	    `validItem ag (stackSyms t ++ [q']) (item N ([],[]))` by 
	    (SRW_TAC [] [validItem_def] THEN
	    MAP_EVERY Q.EXISTS_TAC [`[h]`] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [rdres1, rderives_append, EVERY_DEF, EVERY_APPEND, APPEND_NIL]) THEN
	    `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
            SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))`
	    by METIS_TAC [validItemInv_def, nullNil, rev_nil, NOT_CONS_NIL, IS_PREFIX_REFL] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
	    `MEM (item N ([],[])) r'` by METIS_TAC [transImpValidItem] THEN
	    `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      	    
	    METIS_TAC [getState_reduce_not_NA, slrmacCompItemsEq],

	    
	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  `[h']=[NTS (startSym g); TS eof]`
		  by METIS_TAC [auggrStartRule] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],

	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  METIS_TAC [auggrStartRule, MEM, MEM_APPEND],

		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ]
	    ],

      SRW_TAC [] [] THEN
      `validItem ag (stackSyms t ++ [q']) (item N (h1,h2))` by 
	    (SRW_TAC [] [validItem_def] THEN
	    MAP_EVERY Q.EXISTS_TAC [`sfx`] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [rdres1, rderives_append, EVERY_DEF, EVERY_APPEND, APPEND_NIL]) THEN
	    `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
            SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))`
	    by METIS_TAC [validItemInv_def, nullNil, rev_nil, NOT_CONS_NIL, IS_PREFIX_REFL] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
	    `MEM (item N (h1,h2)) r'` by METIS_TAC [transImpValidItem] THEN
	    `[h']=h2++sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	    Cases_on `h2` THEN
	    Cases_on `sfx` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] []
            THENL[
		  `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      	    
		  METIS_TAC [getState_reduce_not_NA, slrmacCompItemsEq],      

		  METIS_TAC [APPEND, getState_shift_not_NA]
		  ],


      SRW_TAC [] [] THEN
      `[h']=h++sfx` by METIS_TAC [APPEND_ASSOC, APPEND_11] THEN
      Cases_on `h` THEN Cases_on `sfx` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
      THENL[
	    `validItem ag (stackSyms t ++ [q']) (item N ([],[]))` by 
	    (SRW_TAC [] [validItem_def] THEN
	    MAP_EVERY Q.EXISTS_TAC [`[h]`] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [rdres1, rderives_append, EVERY_DEF, EVERY_APPEND, APPEND_NIL]) THEN
	    `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
            SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))`
	    by METIS_TAC [validItemInv_def, nullNil, rev_nil, NOT_CONS_NIL, IS_PREFIX_REFL] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
	    `MEM (item N ([],[])) r'` by METIS_TAC [transImpValidItem] THEN
	    `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      	    
	    METIS_TAC [getState_reduce_not_NA, slrmacCompItemsEq],

	    
	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  `[h']=[NTS (startSym g); TS eof]`
		  by METIS_TAC [auggrStartRule] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ]
	    ]],


	(*do reduce more than one *)
    FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION, itemlist_def, parseInv_def,stackValid_def,validStlItemsStack_def] THEN
    Cases_on `r''` THEN 
    `MEM (item s (l,[])) r'` by METIS_TAC [getState_mem_itl, validStates_def] THEN
    `MEM (rule s l) (rules ag)` by METIS_TAC [getstate_red, validStates_def] THEN
    `h' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN
    FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv_def] THEN
    `validStlItems (((q',r'),r)::t) [(item s (l,[]))]` by METIS_TAC [rgr_r9eq, validStlItems_append,vsiImpvi] THEN
    FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
    `stackSyms (((q',r'),r)::t) = (stackSyms t ++ [q'])` by FULL_SIMP_TAC (srw_ss()) [stackSyms_def, REVERSE_APPEND] THEN
    `?p.stackSyms (((q',r'),r)::t) = p++l` by METIS_TAC [isSuffix_APPEND] THEN
    `?x.addRule (((q',r'),r)::t) (rule s l) = SOME x` by METIS_TAC [addRule_SOME] THEN
    `LENGTH (((q',r'),r)::t) >= LENGTH l` by METIS_TAC [isSuffix_LENGTH, stackSyms_len] THEN
    SRW_TAC [] [] THEN
    `validItem ag (stackSyms (((q',r'),r)::t)) (item s (l,[]))`
	by METIS_TAC [EVERY_APPEND, rgr_r9eq, EVERY_DEF] THEN
    `(s=startSym ag) \/
        ?lhs r1 r2. validItem ag 
         (stackSyms (pop (((q',r'),r)::t) (LENGTH l))) 
         (item lhs (r1,NTS s::r2))` 
	by METIS_TAC [validItemPopStk]
     THENL[
       SRW_TAC [] [] THEN
       METIS_TAC [auggrFsStNil],

       `IS_PREFIX (REVERSE (((q',r'),r)::t))
            (REVERSE (pop (((q',r'),r)::t) (LENGTH l)))`
	       by METIS_TAC [isPfxRevPopRefl] THEN
       Cases_on `pop (((q',r'),r)::t) (LENGTH l) = []`
       THENL[
         SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [stackSyms_def, validItem_def] THEN
	 SRW_TAC [] [] THEN
	 FULL_SIMP_TAC (srw_ss()) [] THEN
	 `MEM (item lhs ([], NTS s::r2))
              (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt] THEN
	 FULL_SIMP_TAC (srw_ss()) [doReduce_def, ruleLhs_def, ruleRhs_def, LET_THM, push_def] THEN
	 Cases_on `h'` THEN
	 FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN	 
	 Cases_on `pop
              ((q',r')::
                   (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
              (LENGTH l) = []` THEN
	     Cases_on `sgoto ag
                 (SND
                    (HD
                       (pop
                          ((q',r')::
                               (MAP FST t ++
                                [(NTS st,
                                  initItems ag (rules ag))]))
                          (LENGTH l)))) (NTS s) = []` THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   
		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

                   `pop  (MAP FST (((q',r'),r)::t)
                         ++ [(NTS st,initItems ag (rules ag))]) 
                       (LENGTH l) = 
                     [(NTS st,initItems ag (rules ag))]` 
		   by METIS_TAC [cslInit, addrule_len] THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [sgotoNotNil]
		   ],


	     (* ~ pop stl = [] *)

	     `(trans ag (initItems ag (rules ag),
                 stackSyms (REVERSE (REVERSE 
                  (pop (((q',r'),r)::t) (LENGTH l))))) =
               SOME (stkItl (REVERSE (REVERSE (pop (((q',r'),r)::t)
                            (LENGTH l))))))`
	       by METIS_TAC [rev_nil, validItemInv_def, nullNil] THEN
	     FULL_SIMP_TAC (srw_ss()) [] THEN
	     `MEM (item lhs (r1,NTS s::r2)) 
               (stkItl ((pop (((q',r'),r)::t) 
                        (LENGTH l))))`
		 by METIS_TAC [transImpValidItem] THEN	     
	     FULL_SIMP_TAC (srw_ss()) [doReduce_def, LET_THM, ruleLhs_def, ruleRhs_def, push_def] THEN
	     Cases_on `h'` THEN
	     FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def, isTmnlSym_def] THEN
	     Cases_on `pop
              ((q',r')::
                   (MAP FST t ++ [(NTS st,initItems ag (rules ag))]))
              (LENGTH l) = []` THEN
	     Cases_on `sgoto ag
                 (SND
                    (HD
                       (pop
                          ((q',r')::
                               (MAP FST t ++
                                [(NTS st,
                                  initItems ag (rules ag))]))
                          (LENGTH l)))) (NTS s) = []` THEN
	     FULL_SIMP_TAC (srw_ss()) []
	     THENL[
		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   METIS_TAC [cslNotNil, APPEND, APPEND_ASSOC, addrule_len, LENGTH_MAP, LENGTH],

		   FULL_SIMP_TAC (srw_ss()) [stkItl_def] THEN
		   IMP_RES_TAC l1 THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   `sgoto ag (SND (FST (HD (pop (((q',r'),r)::t) 
                     (LENGTH l))))) (NTS s) = []` 
                     by METIS_TAC [] THEN
		   METIS_TAC [sgotoNotNil]
		   ]]],

    (*GOTO*)
    
    Cases_on `h` THEN 
    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def],


       (* NA - multiple input *)

 
    FULL_SIMP_TAC (srw_ss()) [stackTopSym_def, viablePfx_def, handleg_def, itemlist_def] THEN
    FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
`(?l1 l2.(l=l1++l2) /\
(pfx=stackSyms t ++ [q']++l1) /\
(h=l2)) \/
(?h1 h2.(h=h1++h2) /\
(stackSyms t ++ [q'] = pfx++h1) /\
 (l=h2)) \/
((stackSyms t ++ [q'] = pfx) /\ 
(l=h))` by 
(SRW_TAC [] [] THEN
`?l1 l2.(pfx=stackSyms t ++[q'] ++l1) /\ (h=l2) /\
 (l=l1++l2) \/
 (h=l2++[q']++l) /\ (pfx=l1) /\
 (stackSyms t = l1 ++ l2)` by METIS_TAC [list_r6] THEN
SRW_TAC [] []) THEN
SRW_TAC [] []
THENL[

      SRW_TAC [] [] THEN
      `h'::h''::t''=l1++h++sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      Cases_on `l1` THEN Cases_on `h` THEN
      Cases_on `sfx` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
      THENL[
	    (*1*)
	    `validItem ag (stackSyms t ++ [q']) (item N ([],[]))` by 
	    (SRW_TAC [] [validItem_def] THEN
	    MAP_EVERY Q.EXISTS_TAC [`h::h''::t''`] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [rdres1, rderives_append, EVERY_DEF, EVERY_APPEND, APPEND_NIL]) THEN
	    `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
            SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))`
	    by METIS_TAC [validItemInv_def, nullNil, rev_nil, NOT_CONS_NIL, IS_PREFIX_REFL] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
	    `MEM (item N ([],[])) r'` by METIS_TAC [transImpValidItem] THEN
	    `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      	    
	    METIS_TAC [getState_reduce_not_NA, slrmacCompItemsEq],

	    
	    (*2*)
	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  `h'::h''::t''=[NTS (startSym g); TS eof]`
		  by METIS_TAC [auggrStartRule] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],

	    (*3*)
	    SRW_TAC [] [] THEN
	    `validItem ag (stackSyms t ++ [q']) (item N ([],h'::t'))` by 
	    (SRW_TAC [] [validItem_def] THEN
	    MAP_EVERY Q.EXISTS_TAC [`h::t'''`] THEN
	    SRW_TAC [] [] THEN
	    METIS_TAC [rdres1, rderives_append, EVERY_DEF, EVERY_APPEND, APPEND_NIL]) THEN
	    `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
            SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))`
	    by METIS_TAC [validItemInv_def, nullNil, rev_nil, NOT_CONS_NIL, IS_PREFIX_REFL] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
	    `MEM (item N ([],h'::t')) r'` by METIS_TAC [transImpValidItem] THEN
	    METIS_TAC [APPEND, getState_shift_not_NA, APPEND_11, APPEND_ASSOC],

	    (*4*)
	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  METIS_TAC [auggrStartRule, MEM, MEM_APPEND],

		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],

	    (*5*)
	    `RTC (rderives ag) [NTS (startSym ag)]
            ((stackSyms t ++ [q'] ++ h'::t') ++ [NTS N] ++
             [h] ++ t''')` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	    `h IN (followSet ag (NTS N))` 
		by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [][]
            THENL[
		  METIS_TAC [auggrStartRule,APPEND,NOT_CONS_NIL],

		  `?itl.trans ag (initItems ag (rules ag),
				  (stackSyms t ++ [q'] ++ h'::t')) = SOME itl `
		      by METIS_TAC [rtcRdImpTrans,isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
		  `?itl.trans ag (initItems ag (rules ag),stackSyms t ++ [q'] ) = SOME itl` 
		      by METIS_TAC [transAppend,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN		  
		  `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t ++ [((q',r'),r)]))) =
		    SOME (stkItl (REVERSE (REVERSE t ++ [((q',r'),r)]))))`
		  by METIS_TAC [validItemInv_def,nullNil,rev_nil,MEM,MEM_APPEND,IS_PREFIX_REFL] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,stkItl_def,transOutMem] THEN
		  `?s.(trans ag (initItems ag (rules ag),
			    REVERSE (MAP FST (MAP FST t)) ++ [q']) = SOME s) /\
                    (trans ag (s,h'::t') = SOME itl)`
		  by METIS_TAC [transAppend,APPEND_ASSOC] THEN		  
		  FULL_SIMP_TAC (srw_ss()) [transOutMem] THEN
		  SRW_TAC [][] THEN
		  `?l r1 r2.MEM (item l (r1,h'::r2)) itl'`
		       by (SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
		  Cases_on `moveDot itl' h'` THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `?l r1 r2.
                     (h''' = item l (r1 ++ [h'],r2)) /\ MEM (item l (r1,h'::r2)) itl'`
		      by METIS_TAC [mdMem,MEM] THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC []) THEN
		  METIS_TAC [getState_shift_not_NA,sgoto_exp]		  
		  ],
	    


	    (*6*)
	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
	    THENL[
		  `h''''::t'''=[NTS (startSym g); TS eof]`
		      by METIS_TAC [auggrStartRule] THEN
		  `EVERY isTmnlSym (h''''::t''')` by METIS_TAC [EVERY_DEF, EVERY_APPEND] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],

	    (*7*)
	    `RTC (rderives ag) [NTS (startSym ag)]
            ((stackSyms t ++ [q'] ++ h'::t' ++ [NTS N]) ++
             [h] ++ t'''')` by METIS_TAC [APPEND, APPEND_ASSOC] THEN
	    `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      	    	    	    
	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [][]
            THENL[
		  `(h''''::t''')=[NTS (startSym g);TS eof]` by METIS_TAC [auggrStartRule] THEN
		  SRW_TAC [][] THEN
		  `EVERY isTmnlSym (t' ++ [NTS (startSym g); TS eof] ++ h::t'''')`
		      by METIS_TAC [EVERY_DEF,EVERY_APPEND,APPEND,isTmnlSym_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

		  `?itl.trans ag (initItems ag (rules ag),
				  (stackSyms t ++ [q'] ++ h'::t')) = SOME itl `
		      by METIS_TAC [rtcRdImpTrans,isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
		  `?itl.trans ag (initItems ag (rules ag),stackSyms t ++ [q'] ) = SOME itl` 
		      by METIS_TAC [transAppend,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN		  
		  `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE t ++ [((q',r'),r)]))) =
		    SOME (stkItl (REVERSE (REVERSE t ++ [((q',r'),r)]))))`
		  by METIS_TAC [validItemInv_def,nullNil,rev_nil,MEM,MEM_APPEND,IS_PREFIX_REFL] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,stkItl_def,transOutMem] THEN
		  `?s.(trans ag (initItems ag (rules ag),
			    REVERSE (MAP FST (MAP FST t)) ++ [q']) = SOME s) /\
                    (trans ag (s,h'::t') = SOME itl)`
		  by METIS_TAC [transAppend,APPEND_ASSOC] THEN		  
		  FULL_SIMP_TAC (srw_ss()) [transOutMem] THEN
		  SRW_TAC [][] THEN
		  `?l r1 r2.MEM (item l (r1,h'::r2)) itl'`
		       by (SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
		  Cases_on `moveDot itl' h'` THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `?l r1 r2.
                     (h''' = item l (r1 ++ [h'],r2)) /\ MEM (item l (r1,h'::r2)) itl'`
		      by METIS_TAC [mdMem,MEM] THEN
		  SRW_TAC [] [] THEN
		  METIS_TAC []) THEN
		  METIS_TAC [getState_shift_not_NA,sgoto_exp]		  
		  ]	    
	    ],


      `h'::h''::t'' = h2++sfx` 
	  by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
      Cases_on `h2` THEN 
      Cases_on `sfx` THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
      THENL[
	    `validItem ag (pfx ++ h1) (item N (h1,[]))`
		by (SRW_TAC [] [validItem_def] THEN
		    MAP_EVERY Q.EXISTS_TAC [`h::h''::t''`] THEN
		    SRW_TAC [] [] THEN
		    METIS_TAC [APPEND_NIL, rdres1, 
	                       rderives_append, 
                               EVERY_DEF, EVERY_APPEND]) THEN
	    `(trans ag
	      (initItems ag (rules ag),
	       stackSyms (REVERSE (REVERSE ((((q',r'),r)::t))))) =
	      SOME (stkItl (REVERSE (REVERSE ((((q',r'),r)::t))))))` 
		by METIS_TAC [IS_PREFIX_REFL, nullNil, rev_nil, NOT_CONS_NIL, validItemInv_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
	    `MEM (item N (h1,[])) r'` 
		by METIS_TAC [transImpValidItem] THEN
	    `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      	    	    	    		  
	    METIS_TAC [getState_reduce_not_NA, slrmacCompItemsEq],

	    Cases_on `N=startSym ag` THEN
	    SRW_TAC [] []
            THENL[
		  `(h1 ++ h::h''::t'')=[NTS (startSym g); TS eof]`
		      by METIS_TAC [auggrStartRule] THEN
		  SRW_TAC [] [] THEN
		  Cases_on `h1` THEN		 
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
		  SRW_TAC [] [] THEN
		  Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [],
		  
		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],

		  
	    `validItem ag (pfx ++ h1) (item N (h1,h::t'))`		
		by (SRW_TAC [] [validItem_def] THEN
		    MAP_EVERY Q.EXISTS_TAC [`h'''::t'''`] THEN
		    SRW_TAC [] [] THEN
		    `rderives ag [NTS N] (h1++h::t')` by METIS_TAC [rdres1] THEN
		    `rderives ag (pfx++[NTS N]++h'''::t''') 
		         (pfx++(h1++h::t')++h'''::t''')` by METIS_TAC [rderives_append, EVERY_DEF, EVERY_APPEND] THEN			  
		    FULL_SIMP_TAC (srw_ss()) []) THEN
	    `(trans ag
		    (initItems ag (rules ag),
		     stackSyms (REVERSE (REVERSE ((((q',r'),r)::t))))) =
		    SOME (stkItl (REVERSE (REVERSE ((((q',r'),r)::t))))))` 
		by METIS_TAC [IS_PREFIX_REFL, nullNil, rev_nil, NOT_CONS_NIL, validItemInv_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
	    `MEM (item N (h1,h::t')) r'` 
		by METIS_TAC [transImpValidItem] THEN
	    METIS_TAC [getState_shift_not_NA]
	    ],
	    
	    
	    `h'::h''::t''=h++sfx` by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
	    Cases_on `h` THEN Cases_on `sfx` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] []
            THENL[
		  
		  `validItem ag (stackSyms t ++ [q']) (item N ([],[]))`		
		      by (SRW_TAC [] [validItem_def] THEN
		  MAP_EVERY Q.EXISTS_TAC [`h::h''::t''`] THEN
		  SRW_TAC [] [] THEN
		  `rderives ag [NTS N] []` by METIS_TAC [rdres1] THEN
		  `rderives ag ((stackSyms t ++ [q'])++[NTS N]++(h::h''::t'')) 
         	    ((stackSyms t ++ [q'])++[]++(h::h''::t''))`
		      by METIS_TAC [rderives_append, EVERY_DEF, EVERY_APPEND] THEN			  
		  FULL_SIMP_TAC (srw_ss()) []) THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE ((((q',r'),r)::t))))) =
			  SOME (stkItl (REVERSE (REVERSE ((((q',r'),r)::t))))))` 
		      by METIS_TAC [IS_PREFIX_REFL, nullNil, rev_nil, NOT_CONS_NIL, validItemInv_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
		  `MEM (item N ([],[])) r'` 
		      by METIS_TAC [transImpValidItem] THEN
		  `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      	    	    	    		  
		  METIS_TAC [getState_reduce_not_NA, slrmacCompItemsEq],

		  Cases_on `N=startSym ag` THEN
		  SRW_TAC [] []
        	  THENL[
		  `(h'::h''::t'')=[NTS (startSym g); TS eof]`
		      by METIS_TAC [auggrStartRule] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

		  `?p.[]=p++[TS eof]` by METIS_TAC [lastEof, APPEND_NIL] THEN
		  Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) []
		  ],


		  `validItem ag (stackSyms t ++ [q']) 
				       (item N ([],h'::t'))`
		      by (SRW_TAC [] [validItem_def] THEN
			  MAP_EVERY Q.EXISTS_TAC [`h::t'''`] THEN
			  SRW_TAC [] [] THEN
			  METIS_TAC [rdres1, rderives_append, 
				     EVERY_DEF, EVERY_APPEND]) THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE ((((q',r'),r)::t))))) =
			  SOME (stkItl (REVERSE (REVERSE ((((q',r'),r)::t))))))` 
		      by METIS_TAC [IS_PREFIX_REFL, nullNil, rev_nil, NOT_CONS_NIL, validItemInv_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [stkItl_def, REVERSE_APPEND] THEN
		  `MEM (item N ([],h'::t')) r'` 
		      by METIS_TAC [transImpValidItem] THEN
		  METIS_TAC [getState_shift_not_NA]
		  ]
	    ]])



val macStepInvStlNil = 
store_thm ("macStepInvStlNil",
``!m g.(auggr g st eof = SOME ag) ==>
EVERY isTmnlSym sl ==> 
(SOME m=slrmac ag) ==> 
(csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
(LENGTH csl = LENGTH stl + 1) ==> (* prove this as an invariant , ensures pop in reduce goes ok *)
(stl=[]) ==>
~(ininp = []) ==>
EVERY isTmnlSym (onstk++ininp) ==>
(sl=onstk++ininp) ==>
viablePfx ag (N,h) (stackSyms stl ++ ininp)
           (stackSyms stl) ==>
parseInv (ag, stl,csl) ==>
validItemInv (ag, stl, csl) ==>
?sl' stl' csl'.((parse (SOME m) (ininp, stl, csl) 
   = SOME (sl',stl',csl')))``,

SRW_TAC [] [] THEN
`slrmac ag = SOME (sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms_def, parse_def, parseInv_def, LET_THM, itemlist_def,stackValid_def] THEN
Cases_on `ininp` THEN SRW_TAC [] [] THEN
Cases_on `t` THEN
Cases_on `getState (sgoto ag,reduce ag) (initItems ag (rules ag)) h'` THEN
SRW_TAC [] []
THENL[
      FULL_SIMP_TAC (srw_ss()) [language_def, EXTENSION] THEN
      Cases_on `r` THEN 
      FULL_SIMP_TAC(srw_ss()) [stackSyms_def, itemlist_def] THEN
      Q.ABBREV_TAC `r'=initItems ag (rules ag)` THEN
      `MEM (item s (l,[])) r'` by METIS_TAC [getState_mem_itl, parseInv_def, validStates_def] THEN
      `MEM (rule s l) (rules ag)` by METIS_TAC [getstate_red, validStates_def, parseInv_def] THEN
      `h' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def, parseInv_def] THEN
      Q.ABBREV_TAC `prestl = ([]:((symbol#state)#ptree)list)` THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv_def] THEN
      `validStlItems prestl [(item s (l,[]))]` by METIS_TAC [rgr_r9eq, validStlItems_append,vsiImpvi] THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
      `?p.stackSyms prestl = p++l` by METIS_TAC [isSuffix_APPEND] THEN
      `?x.addRule prestl (rule s l) = SOME x` by METIS_TAC [addRule_SOME, parseInv_def] THEN
      `LENGTH prestl >= LENGTH l` by METIS_TAC [isSuffix_LENGTH, stackSyms_len] THEN
      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [parseInv_def, itemlist_def] THEN
      `validItem ag [] (item s (l,[]))`
	  by METIS_TAC [EVERY_APPEND, rgr_r9eq, EVERY_DEF, SND, HD] THEN
      UNABBREV_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `l` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      FULL_SIMP_TAC (arith_ss) [stackSyms_def, viablePfx_def,handleg_def, IS_PREFIX, MAP, REVERSE] THEN
      SRW_TAC [] [] THEN
      `[h']=sfx` 
	  by (SRW_TAC [] [] THEN
	      SPOSE_NOT_THEN ASSUME_TAC THEN
	      Cases_on `pfx++h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] [] THEN
	      Cases_on `pfx` THEN
	      Cases_on `h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] []
              THENL[
		    Cases_on `N=startSym ag` THEN
		    SRW_TAC [] []
		    THENL[
			  `[h']=[NTS (startSym g);TS eof]`
			      by METIS_TAC [auggrStartRule] THEN
			  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def], 

			  `?p.[]=p++[TS eof]`
			  by METIS_TAC [lastEof, APPEND_NIL, APPEND] THEN
			  Cases_on `p` THEN
			  FULL_SIMP_TAC (srw_ss()) []
			  ],

		    Cases_on `N=startSym ag` THEN
		    SRW_TAC [][]
		    THENL[
			  METIS_TAC [MEM,MEM_APPEND,auggrStartRule],

			  `?p.[]=p++[TS eof]`
			  by METIS_TAC [lastEof, APPEND_NIL, APPEND] THEN
			  Cases_on `p` THEN
			  FULL_SIMP_TAC (srw_ss()) []			  
			  ]		    
		    ]) THEN
`trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
    by METIS_TAC [trans_def] THEN
SRW_TAC [] [] THEN
`pfx++h=[]` by METIS_TAC [APPEND_11, APPEND_NIL] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
SRW_TAC [] [doReduce_def, LET_THM] THEN
Cases_on `h'` THEN 
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def, pop_def, ruleRhs_def, ruleLhs_def] THEN
SRW_TAC [] [] THEN
`MEM (item N ([],[])) (initItems ag (rules ag))`
by METIS_TAC [initItemsHdNt] THEN
`(TS s') IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
`item s ([],[]) = item N ([],[])` by
METIS_TAC [slrmacCompItemsEq, completeItem_def, itemLhs_def, isTmnlSym_def] THEN
SRW_TAC [] [] THEN
`([NTS (startSym ag)]=[NTS N;TS s']) \/
 ?u.RTC (rderives ag) [NTS (startSym ag)] u
 /\ rderives ag u [NTS N ;TS s']`
by METIS_TAC [RTC_CASES2] THEN
SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
SRW_TAC [] [] THEN
Cases_on `s1` THEN
Cases_on `rhs` THEN
FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
SRW_TAC [] []
THENL[
      `MEM (item lhs ([],NTS N::t)) (initItems ag (rules ag))`
      by METIS_TAC [initItemsHdNt] THEN
      METIS_TAC [sgotoNotNil],

      Cases_on `t` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] []
      THENL[	    
	    `(TS s') IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
	     Cases_on `lhs=startSym ag` THEN
	     SRW_TAC [][]
             THENL[
		   METIS_TAC [auggrStartRule,APPEND,NOT_CONS_NIL],

		   `[NTS N; NTS lhs; TS s'] =
	             [NTS N]++ [NTS lhs] ++ [TS s']`
		       by METIS_TAC [APPEND,APPEND_ASSOC] THEN
		   `?itl.(trans ag (initItems ag (rules ag),[NTS N])
	            = SOME itl)` 
		       by METIS_TAC [rtcRdImpTrans,isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
		   FULL_SIMP_TAC (srw_ss()) [trans_def,sgoto_def,nextState_def] THEN
		   Cases_on `moveDot (initItems ag (rules ag)) (NTS N)` THEN
		   FULL_SIMP_TAC (srw_ss()) [] THEN
		   METIS_TAC [iclosure_mem,MEM]
		   ],

	    
	    Cases_on `lhs=startSym ag` THEN
	     SRW_TAC [][]
             THENL[
		   METIS_TAC [auggrStartRule,APPEND,NOT_CONS_NIL],

		   `[NTS N; TS s'; NTS lhs] = 
         	     [NTS N; TS s']++ [NTS lhs]`
		       by METIS_TAC [APPEND_ASSOC,APPEND] THEN
		   METIS_TAC [APPEND_NIL,APPEND_NIL,lastEof,MEM,MEM_APPEND]
		   ]
	     ],


      Cases_on `t` THEN SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]THEN
      Cases_on `lhs=startSym ag` THEN
      SRW_TAC [][]
      THENL[
	    `[TS s']=[NTS (startSym g);TS eof]`
	    by METIS_TAC [auggrStartRule] THEN
	    FULL_SIMP_TAC (srw_ss()) [],

	    `[NTS N;NTS lhs] = [NTS N]++[NTS lhs]`
		by SRW_TAC [][] THEN
	    METIS_TAC [APPEND_NIL,APPEND_NIL,lastEof,MEM,MEM_APPEND]
	    ]      
      ],


      (*GOTO*)
      FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def, itemlist_def] THEN
      `[h']=sfx`
	  by (SRW_TAC [] [] THEN
	      SPOSE_NOT_THEN ASSUME_TAC THEN
	      Cases_on `pfx++h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] [] THEN
	      Cases_on `pfx` THEN
	      Cases_on `h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] []
              THENL[
		    Cases_on `N=startSym ag` THEN
		    SRW_TAC [] []
		    THENL[
			  `[h']=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
			  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

			  `?p.[]=p++[TS eof]`
			  by METIS_TAC [lastEof, APPEND_NIL, APPEND] THEN
			  Cases_on `p` THEN
			  FULL_SIMP_TAC (srw_ss()) []
			  ],

		    Cases_on `N=startSym ag` THEN
		    SRW_TAC [] []
		    THENL[
			  METIS_TAC [auggrStartRule, MEM, MEM_APPEND],

			  `?p.[]=p++[TS eof]`
			  by METIS_TAC [lastEof, APPEND_NIL, APPEND] THEN
			  Cases_on `p` THEN
			  FULL_SIMP_TAC (srw_ss()) []
			  ]
		    ]) THEN
      SRW_TAC [] [] THEN
      `pfx++h=[]` by METIS_TAC [APPEND_11, APPEND_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `h' IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
      `MEM (item N ([],[])) (initItems ag (rules ag))`
      by METIS_TAC [initItemsHdNt, APPEND] THEN
      METIS_TAC [shiftReduceGoto, validStates_def],


      (*NA*)
      FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def, itemlist_def] THEN
      `[h']=sfx`
	  by (SRW_TAC [] [] THEN
	      SPOSE_NOT_THEN ASSUME_TAC THEN
	      Cases_on `pfx++h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] [] THEN
	      Cases_on `pfx` THEN
	      Cases_on `h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] []
              THENL[
		    Cases_on `N=startSym ag` THEN
		    SRW_TAC [] []
		    THENL[
			  `[h']=[NTS (startSym g); TS eof]` by METIS_TAC [auggrStartRule] THEN
			  FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],

			  `?p.[]=p++[TS eof]`
			  by METIS_TAC [lastEof, APPEND_NIL, APPEND] THEN
			  Cases_on `p` THEN
			  FULL_SIMP_TAC (srw_ss()) []
			  ],

		    Cases_on `N=startSym ag` THEN
		    SRW_TAC [] []
		    THENL[
			  METIS_TAC [auggrStartRule, MEM, MEM_APPEND],

			  `?p.[]=p++[TS eof]`
			  by METIS_TAC [lastEof, APPEND_NIL, APPEND] THEN
			  Cases_on `p` THEN
			  FULL_SIMP_TAC (srw_ss()) []
			  ]
		    ]) THEN
      SRW_TAC [] [] THEN      
      `pfx++h=[]` by METIS_TAC [APPEND_11, APPEND_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `h' IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
      `MEM (item N ([],[])) (initItems ag (rules ag))`
      by METIS_TAC [initItemsHdNt, APPEND] THEN
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
	  by METIS_TAC [trans_def] THEN
      METIS_TAC [getState_reduce_not_NA, validStates_def, slrmacCompItemsEq],      


      (*reduce - multiple ininp *)
      FULL_SIMP_TAC (srw_ss()) [viablePfx_def, handleg_def, itemlist_def] THEN
      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
	  by METIS_TAC [trans_def] THEN
      `h'::h''::t'=sfx`
	  by (SRW_TAC [] [] THEN
	      SPOSE_NOT_THEN ASSUME_TAC THEN
	      Cases_on `pfx++h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] [] THEN
	      Cases_on `pfx` THEN
	      Cases_on `h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] []
              THENL[
		    `MEM (item N ([],h'::t)) (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt] THEN
		    Cases_on `r` THEN
		    `MEM (item s (l,[])) (initItems ag (rules ag))`
			by METIS_TAC [getState_mem_itl, validStates_def] THEN
		    `validItl ag [item s (l,[])]` by METIS_TAC [validStates_def, validItl_append, rgr_r9eq] THEN
		    `validItl ag [item N ([],h'::t)]` by METIS_TAC [validStates_def, validItl_append, rgr_r9eq] THEN
		    FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
		    `h' IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def] THEN      		    
		    METIS_TAC [slrmacNotValid, APPEND_NIL],

		    `RTC (rderives ag) [NTS (startSym ag)] ((h'::t) ++ [NTS N] ++ sfx)` by FULL_SIMP_TAC (srw_ss()) [] THEN
		    `?lhs rhs.MEM (item lhs ([],h'::rhs)) (initItems ag (rules ag))` by METIS_TAC [initItemsNtInBtwn, NOT_CONS_NIL, HD, EVERY_DEF, EVERY_APPEND] THEN
		    `validItl ag [item lhs ([],h'::rhs)]` by METIS_TAC [validStates_def, validItl_append, rgr_r9eq] THEN
		    FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
		    Cases_on `r` THEN
		    `MEM (item s (l,[])) (initItems ag (rules ag))` by METIS_TAC [validStates_def, getState_mem_itl] THEN
		    `l=[]` by METIS_TAC [initItems_fstRhs_nil] THEN
		    SRW_TAC [] [] THEN
		    `( (item lhs ([],h'::rhs)) = item s ([],[])) \/ ~ ?l' r2 r1.  (item lhs ([],h'::rhs)) = item l' (r1,h'::r2)` by METIS_TAC [shiftReduce, NOT_CONS_NIL, validStates_def] THEN
		    FULL_SIMP_TAC (srw_ss()) [] THEN
		    METIS_TAC [],

		    `RTC (rderives ag) [NTS (startSym ag)] 
                     ((h'::t'') ++ [NTS N] ++ sfx)` by FULL_SIMP_TAC (srw_ss()) [] THEN
		    `?lhs rhs.MEM (item lhs ([],h'::rhs)) (initItems ag (rules ag))` by METIS_TAC [initItemsNtInBtwn, NOT_CONS_NIL, HD, EVERY_DEF, EVERY_APPEND] THEN
		    `validItl ag [item lhs ([],h'::rhs)]` by METIS_TAC [validStates_def, validItl_append, rgr_r9eq] THEN
		    FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
		    Cases_on `r` THEN
		    `MEM (item s (l,[])) (initItems ag (rules ag))` by METIS_TAC [validStates_def, getState_mem_itl] THEN
		    `l=[]` by METIS_TAC [initItems_fstRhs_nil] THEN
		    SRW_TAC [] [] THEN
		    `( (item lhs ([],h'::rhs)) = item s ([],[])) \/ ~ ?l' r2 r1.  (item lhs ([],h'::rhs)) = item l' (r1,h'::r2)` by METIS_TAC [shiftReduce, NOT_CONS_NIL, validStates_def] THEN
		    FULL_SIMP_TAC (srw_ss()) [] THEN
		    METIS_TAC []
		    ]) THEN		    
      SRW_TAC [] [] THEN
      `pfx++h=[]` by METIS_TAC [APPEND_11, APPEND_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      Cases_on `r` THEN
      `MEM (item s (l,[])) (initItems ag (rules ag))`
	  by METIS_TAC [getState_mem_itl, validStates_def] THEN
      `l=[]` by METIS_TAC [initItems_fstRhs_nil] THEN
      SRW_TAC [] [] THEN
      `validItem ag [] (item s ([],[]))`
	  by METIS_TAC [EVERY_DEF, EVERY_APPEND, rgr_r9eq] THEN
      FULL_SIMP_TAC (srw_ss()) [validItem_def, handleg_def] THEN
      SRW_TAC [] [doReduce_def, LET_THM] THEN
      Cases_on `h'` THEN 
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def, pop_def, ruleRhs_def, ruleLhs_def] THEN
      SRW_TAC [] [] THEN
      `MEM (item N ([],[])) (initItems ag (rules ag))`
	  by METIS_TAC [initItemsHdNt] THEN
`(TS s') IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
`(TS s') IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, validStates_def, isTmnlSym_def] THEN
`item s ([],[]) = item N ([],[])` by
METIS_TAC [slrmacCompItemsEq, completeItem_def, itemLhs_def, isTmnlSym_def] THEN
SRW_TAC [] [] THEN
      Q.ABBREV_TAC `prestl = ([]:((symbol#state)#ptree)list)` THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def,parseInv_def] THEN
      `validStlItems prestl [(item N ([],[]))]` by METIS_TAC [rgr_r9eq, validStlItems_append,vsiImpvi] THEN
      FULL_SIMP_TAC (srw_ss()) [validStlItems_def, itemFstRhs_def] THEN
      `?p.stackSyms prestl = p++[]` by METIS_TAC [isSuffix_APPEND] THEN
      `?x.addRule prestl (rule N []) = SOME x` by METIS_TAC [addRule_SOME, parseInv_def] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      UNABBREV_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
      SRW_TAC [] [] THEN
      `RTC (rderives ag) [NTS (startSym ag)] 
          ([NTS N]++[TS s']++(TS s''::t'))`
	  by FULL_SIMP_TAC (srw_ss()) [] THEN
      `([NTS N] ++ [TS s'] ++ TS s''::t') =
        ([NTS N] ++ ([TS s'] ++ TS s''::t'))`
	  by METIS_TAC [APPEND,APPEND_ASSOC] THEN
      Cases_on `N=startSym ag` THEN
      SRW_TAC [][]
      THENL[
	    METIS_TAC [auggrStartRule,NOT_CONS_NIL],


	    `?n.NRC (rderives ag) n [NTS (startSym ag)]
             ([NTS N] ++ [TS s'] ++ TS s''::t')` by METIS_TAC [RTC_NRC] THEN
	    Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    `0 < SUC n'`by DECIDE_TAC THEN
	    IMP_RES_TAC sublemma THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN
			       [`(startSym ag)`,`TS s'::TS s''::t'`,
				`[]`,`N`,`ag`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    `validItem ag [] (item nt' ([],NTS N::sfx2))`
		by (SRW_TAC [][validItem_def] THEN
	    Q.EXISTS_TAC `sfx1`  THEN
	    SRW_TAC [][] THEN
	    `rderives ag ([NTS nt']++sfx1)
		     ((NTS N::sfx2)++sfx1)`
		by METIS_TAC [rdres1,rderives_append,EVERY_APPEND,APPEND_NIL] THEN
	    METIS_TAC [NRC_RTC,APPEND_ASSOC,APPEND]) THEN
	    `MEM (item nt' ([],NTS N::sfx2)) (initItems ag (rules ag))`
	    by METIS_TAC [transImpValidItem] THEN
	    METIS_TAC [sgoto_mem,MEM]
	    ],


      Cases_on `h` THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def],

      `trans ag (initItems ag (rules ag),[]) = SOME (initItems ag (rules ag))`
	  by METIS_TAC [trans_def] THEN
      FULL_SIMP_TAC (srw_ss()) [itemlist_def, handleg_def, viablePfx_def] THEN
      FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_APPEND] THEN
      `h'::h''::t' = sfx`
      by (SPOSE_NOT_THEN ASSUME_TAC THEN
	      Cases_on `pfx++h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] [] THEN
	      Cases_on `pfx` THEN
	      Cases_on `h` THEN
	      SRW_TAC [] [] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      SRW_TAC [] []
              THENL[
		    `MEM (item N ([],h'::t)) (initItems ag (rules ag))` by METIS_TAC [initItemsHdNt] THEN
		    METIS_TAC [getState_shift_not_NA],

		    `RTC (rderives ag) [NTS (startSym ag)] 
                     ((h'::t) ++ [NTS N] ++ sfx)` by FULL_SIMP_TAC (srw_ss()) [] THEN
		    `?lhs rhs.MEM (item lhs ([],h'::rhs)) (initItems ag (rules ag))` by METIS_TAC [initItemsNtInBtwn, EVERY_DEF, EVERY_APPEND, NOT_CONS_NIL, HD] THEN
		    METIS_TAC [getState_shift_not_NA],

		    `RTC (rderives ag) [NTS (startSym ag)] 
                     ((h'::t'') ++ [NTS N] ++ sfx)` by FULL_SIMP_TAC (srw_ss()) [] THEN
		    `?lhs rhs.MEM (item lhs ([],h'::rhs)) (initItems ag (rules ag))` by METIS_TAC [initItemsNtInBtwn, EVERY_DEF, EVERY_APPEND, NOT_CONS_NIL, HD] THEN
		    METIS_TAC [getState_shift_not_NA]
		    ]) THEN
      SRW_TAC [] [] THEN
      `pfx++h=[]` by METIS_TAC [APPEND_11, APPEND_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [] [] THEN
      `MEM (item N ([],[])) (initItems ag (rules ag))`
	  by METIS_TAC [initItemsHdNt] THEN
      `h' IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN      
      METIS_TAC [getState_reduce_not_NA, slrmacCompItemsEq]
      ])



val macStepValidInv = 
store_thm ("macStepValidInv",
``!m g.(auggr g st eof = SOME ag) ==>
EVERY isTmnlSym sl ==> 
(SOME m=slrmac ag) ==> 
(csl = MAP FST stl ++ [(NTS st, initItems ag (rules ag))]) ==>
(LENGTH csl = LENGTH stl + 1) ==>
((stl=[]) \/ (~(stl=[]) /\ 
~(exitCond (eof,NTS (startSym g)) (ininp,stl,csl)))) ==> 
~(ininp = []) ==>
EVERY isTmnlSym (onstk++ininp) ==>
(sl=onstk++ininp) ==>
viablePfx ag (N,h) (stackSyms stl ++ ininp)
           (stackSyms stl) ==>
parseInv (ag, stl,csl) ==>
validItemInv (ag, stl, csl) ==>
?sl' stl' csl'.((parse (SOME m) (ininp, stl, csl) 
   = SOME (sl',stl',csl')))``,
METIS_TAC [macStepInvStlNil, macStepInvStlNotNil])

val _ = export_theory ();
