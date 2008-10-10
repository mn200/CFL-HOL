open HolKernel boolLib bossLib Parse BasicProvers Defn

open listTheory containerTheory pred_setTheory arithmeticTheory
relationTheory markerTheory boolSimps optionTheory rich_listTheory
pairTheory

open regexpTheory grammarDefTheory boolLemmasTheory listLemmasTheory
setLemmasTheory whileLemmasTheory parseTreeTheory followSetDefTheory
parserDefTheory yaccDefTheory parseProp1DefTheory parseProp2DefTheory
lrGrammarDefTheory validItemInvTheory macStepTheory complDefTheory


fun MAGIC (asl, w) = ACCEPT_TAC (mk_thm(asl,w)) (asl,w)

val _ = Globals.linewidth := 60


val stepDoRedInit = store_thm ("stepDoRedInit",
``(auggr g st eof = SOME ag) ==>
  (slr ag = SOME m) ==>
  (inis = initItems ag (rules ag)) ==>
  parseInv (ag,[],[(NTS st,inis)]) ==>
  MEM (item lhs ([],[])) inis ==>
 EVERY isTmnlSym (h::sfx) ==>
  RTC (rderives ag) [NTS (startSym ag)] ([NTS lhs]++(h::sfx)) ==>
  (getState m inis h = REDUCE r) ==>
  ?stl' csl'.
       (doReduce m (h::sfx,[],[(NTS st,inis)]) r =
                            SOME (h::sfx,stl',csl')) /\
      (stackSyms stl' = [NTS lhs])``,
SRW_TAC [][]THEN
Q.ABBREV_TAC `inis=initItems ag (rules ag)` THEN
Cases_on `r` THEN
FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
`MEM (item s (l,[])) inis`
    by METIS_TAC [getState_mem_itl,sgoto_exp,parseInv_def,validStates_def] THEN
`h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
`h IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet,parseInv_def,validStates_def,sgoto_exp] THEN
`validItl ag [(item lhs ([],[]))]` by METIS_TAC [parseInv_def,validStates_def,validItl_append,rgr_r9eq] THEN
`validItl ag [(item s (l,[]))]` by METIS_TAC [parseInv_def,validStates_def,validItl_append,rgr_r9eq] THEN
FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
`(s=lhs) /\ (l=[])` by METIS_TAC [completeItem_def,slrReduceRulesEq,trans_def] THEN
SRW_TAC [][] THEN
`!stl csl N h ininp onstk ru sl.
      (auggr g st eof = SOME ag) ==>
       (slr ag = SOME m) ==>
       EVERY isTmnlSym sl ==>
       (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
       ~(ininp = []) ==>
       EVERY isTmnlSym (onstk ++ ininp) ==>
       (sl = onstk ++ ininp) ==>
       viablePfx ag (N,h) (stackSyms stl ++ ininp) (stackSyms stl) ==>
       parseInv (ag,stl,csl) ==>
       validItemInv (ag,stl,csl) ==>
       (getState (sgoto ag,reduce ag) (itemlist csl) (HD ininp) =
        REDUCE ru) ==>
       ?sl' stl' csl'.
       (doReduce m (ininp,stl,csl) ru = SOME (sl',stl',csl')) /\
       (stackSyms stl'=
	stackSyms (pop stl (LENGTH (ruleRhs ru)))
       ++ [NTS (ruleLhs ru)]) /\ (sl'=ininp)`
    by METIS_TAC [macStepDoRedExists] THEN
FIRST_X_ASSUM (Q.SPECL_THEN
		     [`[]`,`[(NTS st,initItems ag (rules ag))]`,
		      `lhs`,`[]`,`h::sfx`,`[]`,`(rule lhs [])`,
		      `h::sfx`]
		     MP_TAC) THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [itemlist_def,pop_def] THEN
`viablePfx ag (lhs,[]) (h::sfx) []`
    by (SRW_TAC [][viablePfx_def] THEN
	SRW_TAC [][handleg_def] THEN
	MAP_EVERY Q.EXISTS_TAC [`[]`,`h::sfx`] THEN
	SRW_TAC [][IS_PREFIX]) THEN
METIS_TAC [validItemInvInit,sgoto_exp])


val stepDoRedGen = store_thm ("stepDoRedGen",
``(auggr g st eof = SOME ag) ==>
  (slr ag = SOME m) ==>
  (inis = initItems ag (rules ag)) ==>
  (stl = ((sym,sta:state),tr:ptree)::t) ==>
validItemInv
(ag,((sym,sta),tr)::t,
 (sym,sta)::
 (MAP FST t ++ [(NTS st,initItems ag (rules ag))])) ==>
(csl = (sym,sta)::MAP FST t ++ [(NTS st,inis)]) ==>
  parseInv (ag,stl,csl) ==>
  MEM (item lhs (stackSyms stl,[])) sta ==>
 EVERY isTmnlSym (h::sfx) ==>
  RTC (rderives ag) [NTS (startSym ag)] ([NTS lhs]++(h::sfx)) ==>
  (getState m sta h = REDUCE r) ==>
  ?stl' csl'.
       (doReduce m (h::sfx,stl,csl) r =
                            SOME (h::sfx,stl',csl')) /\
      (stackSyms stl' = stackSyms (pop stl (SUC (LENGTH t))) ++
				  [NTS lhs])``,
SRW_TAC [][] THEN
Cases_on `r` THEN
`MEM (item s (l,[])) sta` by METIS_TAC [getState_mem_itl,parseInv_def,validStates_def,sgoto_exp] THEN
`h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
`h IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet,parseInv_def,validStates_def,sgoto_exp] THEN
`(NTS lhs::h::sfx) = [NTS lhs]++h::sfx`
    by METIS_TAC [APPEND] THEN
Cases_on `lhs=startSym ag`THEN
SRW_TAC [][]
THENL[
      METIS_TAC [auggrRtcRderivesPfxSfxNil,NOT_CONS_NIL,APPEND_NIL],


      `?itl.trans ag (initItems ag (rules ag),[]) = SOME itl`
	  by METIS_TAC [rtcRdImpTrans,APPEND_NIL] THEN
      `validItl ag [item lhs (stackSyms t ++ [sym],[])]`
	  by METIS_TAC [parseInv_def,validStates_def,rgr_r9eq,validItl_append] THEN
      FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
      `MEM (item lhs ([],stackSyms t++[sym])) (initItems ag (rules ag))`
	  by METIS_TAC [initItemsHdNt] THEN
      `?s'. trans ag (initItems ag (rules ag),stackSyms t ++[sym]) = SOME s'`
	  by METIS_TAC [ruleRhsExistsImpTrans] THEN
      `?s.(trans ag (initItems ag (rules ag),stackSyms t) = SOME s) /\
          (trans ag (s,[sym]) = SOME s')`
	  by METIS_TAC [transOverAppend] THEN
      `REVERSE (((sym,sta),tr)::t) = (REVERSE t ++ [((sym,sta),tr)])`
	  by FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND] THEN
      `(trans ag
               (initItems ag (rules ag),
                stackSyms (REVERSE (REVERSE t ++ [((sym,sta),tr)]))) =
             SOME (stkItl (REVERSE (REVERSE t ++ [((sym,sta),tr)]))))`
	  by METIS_TAC [rev_nil,nullNil,IS_PREFIX_REFL,MEM,MEM_APPEND,validItemInv_def] THEN
      FULL_SIMP_TAC (srw_ss()) [REVERSE_APPEND,stackSyms_def,transOutMem,stkItl_def] THEN
      SRW_TAC [][] THEN
      `validItem ag ((REVERSE (MAP FST (MAP FST t)) ++ [sym]))
	  (item lhs
                (REVERSE (MAP FST (MAP FST t)) ++ [sym],[]))`
	  by (SRW_TAC [][validItem_def] THEN
	      MAP_EVERY Q.EXISTS_TAC [`[]`,`h::sfx`] THEN
	      SRW_TAC [][] THEN
	      `(NTS lhs::h::sfx)=([NTS lhs]++h::sfx)`
		  by METIS_TAC [APPEND] THEN
	      METIS_TAC [EVERY_DEF,rdres1,rderives_append,APPEND_NIL]) THEN
      `MEM (item lhs
                (REVERSE (MAP FST (MAP FST t)) ++ [sym],[])) s'`
	  by METIS_TAC [transImpValidItem] THEN
      `(item s (l,[]))=(item lhs ((REVERSE (MAP FST (MAP FST t))) ++ [sym],[]))`
	  by METIS_TAC [slrCompItemsEq,itemLhs_def,completeItem_def] THEN
      SRW_TAC [][] THEN
      `!stl csl N h ininp onstk ru sl.
      (auggr g st eof = SOME ag) ==>
       (slr ag = SOME m) ==>
       EVERY isTmnlSym sl ==>
       (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
       ~(ininp = []) ==>
       EVERY isTmnlSym (onstk ++ ininp) ==>
       (sl = onstk ++ ininp) ==>
       viablePfx ag (N,h) (stackSyms stl ++ ininp) (stackSyms stl) ==>
       parseInv (ag,stl,csl) ==>
       validItemInv (ag,stl,csl) ==>
       (getState (sgoto ag,reduce ag) (itemlist csl) (HD ininp) =
        REDUCE ru) ==>
       ?sl' stl' csl'.
       (doReduce m (ininp,stl,csl) ru = SOME (sl',stl',csl')) /\
       (stackSyms stl'=
	stackSyms (pop stl (LENGTH (ruleRhs ru)))
       ++ [NTS (ruleLhs ru)]) /\ (sl'=ininp)`
    by METIS_TAC [macStepDoRedExists] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN
		     [`((sym,s'),tr)::t`,
		      `(sym,s')::(MAP FST t++[(NTS st,initItems ag (rules ag))])`,
		      `lhs`,`(REVERSE (MAP FST (MAP FST t))) ++ [sym]`,
		      `h::sfx`,`[]`,
		      `(rule lhs ((REVERSE (MAP FST (MAP FST t))) ++ [sym]))`,
		      `h::sfx`]
		     MP_TAC) THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
      `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
      SRW_TAC [][]THEN
      `viablePfx ag (lhs,(REVERSE (MAP FST (MAP FST t))) ++ [sym])
			     ((REVERSE (MAP FST (MAP FST t))) ++ [sym] ++ h::sfx) ((REVERSE (MAP FST (MAP FST t))) ++ [sym])`
	  by (SRW_TAC [] [viablePfx_def,handleg_def] THEN
	      MAP_EVERY Q.EXISTS_TAC [`[]`,`h::sfx`] THEN
	      SRW_TAC [] [IS_PREFIX] THEN
	      FULL_SIMP_TAC (srw_ss()) [IS_PREFIX_REFL]) THEN
      `stackSyms (((sym,sta),tr)::t) = (REVERSE (MAP FST (MAP FST t)) ++ [sym])`
	  by FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
	  `stackSyms t = REVERSE (MAP FST (MAP FST t))`
	  by FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
      `LENGTH (stackSyms  t) + 1 = SUC (LENGTH (stackSyms t))` by DECIDE_TAC THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
      RES_TAC THEN
      METIS_TAC [stackSyms_len,sgoto_exp,LENGTH_MAP,LENGTH_REVERSE]])


val takesStepsReduce = store_thm
("takesStepsReduce",
``(auggr g st eof = SOME ag) ==>
  (slr ag = SOME m) ==>
  (stackSyms stl = s1++rhs) ==>
  parseInv (ag,stl,csl) ==>
  validItemInv (ag,stl,csl) ==>
   MEM (item lhs (rhs,[])) (itemlist csl) ==>
   RTC (rderives ag) [NTS (startSym ag)]
    (s1++[NTS lhs]++s2) ==>
   EVERY isTmnlSym s2 ==>
   ~(lhs=startSym ag) ==>
   (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
   ?stl' csl'.
   takesSteps (SUC 0) (parse (SOME m))
   (exitCond (eof,NTS (startSym g)))
   (s2,stl,csl)
   (s2,stl',csl') /\
   (stackSyms stl'=stackSyms (pop stl (LENGTH rhs))++[NTS lhs]) /\
   (getState m (itemlist csl) (HD s2) = REDUCE (rule lhs rhs))``,

SRW_TAC [] [takesSteps_def] THEN
Q.ABBREV_TAC `csl=MAP FST stl ++ [(NTS st,initItems ag (rules ag))]` THEN
Q.ABBREV_TAC `pped = (pop stl (LENGTH rhs))` THEN
Cases_on `s1`
THENL[
  Cases_on `rhs`
  THENL[
    Cases_on `stl` THEN
    FULL_SIMP_TAC (srw_ss()) [pop_def]
    THENL[
      UNABBREV_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
      SRW_TAC [][] THEN
      Q.ABBREV_TAC `inis=initItems ag (rules ag)` THEN
      SRW_TAC [][parse_def,LET_THM] THEN
      Cases_on `s2` THEN SRW_TAC [] []
      THENL[
	METIS_TAC [auggrRtcRderivesSt],

	Cases_on `t` THEN
	Cases_on `getState m inis h` THEN
	FULL_SIMP_TAC (srw_ss()) []
	THENL[
	      `!inis st h sfx r.
	         (auggr g st eof = SOME ag) ==>
	       (slr ag = SOME m) ==>
	       (inis = initItems ag (rules ag)) ==>
	       parseInv (ag,[],[(NTS st,inis)]) ==>
	       MEM (item lhs ([],[])) inis ==>
	       EVERY isTmnlSym (h::sfx) ==>
	       RTC (rderives ag) [NTS (startSym ag)]
               ([NTS lhs] ++ h::sfx) ==>
	       (getState m inis h = REDUCE r) ==>
	       ?stl' csl'.
               (doReduce m (h::sfx,[],[(NTS st,inis)]) r =
		SOME (h::sfx,stl',csl')) /\
               (stackSyms stl' = [NTS lhs])`
		  by METIS_TAC [stepDoRedInit] THEN
	      FIRST_X_ASSUM (Q.SPECL_THEN
				 [`initItems ag (rules ag)`,
				  `startSym ag`,`h`,`[]`,`r`]
				 MP_TAC) THEN
	      SRW_TAC [][] THEN
	      FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
	      Cases_on `r` THEN
	      `validItl ag [item lhs ([],[])]`
		  by METIS_TAC [parseInv_def,validStates_def,rgr_r9eq,validItl_append] THEN
	      FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
	      `validItem ag [] (item lhs ([],[]))`
		  by (SRW_TAC [][validItem_def] THEN
		      Q.EXISTS_TAC `[h]` THEN
		      SRW_TAC [] [] THEN
		      METIS_TAC [APPEND,rdres1,APPEND_NIL,rderives_append,EVERY_DEF]) THEN
	      `h IN (followSet ag (NTS s))`
		  by METIS_TAC [getState_reduce_followSet,sgoto_exp,validStates_def,parseInv_def] THEN
	      `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
	      `MEM (item s (l,[])) inis`
		  by METIS_TAC [getState_mem_itl,parseInv_def,validStates_def,sgoto_exp] THEN
	      `l=[]` by METIS_TAC [initItems_fstRhs_nil] THEN
	      SRW_TAC [][] THEN
	      `item s ([],[]) = item lhs ([],[])`
		  by METIS_TAC [slrCompItemsEq,completeItem_def,itemLhs_def,trans_def] THEN
	      FULL_SIMP_TAC (srw_ss()) [] THEN
	      METIS_TAC [auggr_startSym,parseInvInit],


	  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
	  METIS_TAC [parseInv_def,validStates_def,shiftReduceGoto],

	  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
	  METIS_TAC [getState_reduce_not_NA,sgoto_exp,
		     slrCompItemsEq,trans_def],


	  Cases_on `r` THEN
	  `h IN (followSet ag (NTS s))`
	      by METIS_TAC [getState_reduce_followSet,sgoto_exp,validStates_def,parseInv_def] THEN
	  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
	  `MEM (item s (l,[])) inis`
	      by METIS_TAC [getState_mem_itl,parseInv_def,validStates_def,sgoto_exp] THEN
	  `l=[]` by METIS_TAC [initItems_fstRhs_nil] THEN
	  SRW_TAC [][] THEN
	  `item s ([],[]) = item lhs ([],[])`
	      by METIS_TAC [slrCompItemsEq,completeItem_def,itemLhs_def,trans_def] THEN
	  `(NTS lhs::h::h'::t')=[NTS lhs]++(h::h'::t')`
	      by METIS_TAC [APPEND,APPEND_ASSOC] THEN
	  SRW_TAC [] [exitCond_def] THEN
	  METIS_TAC [stepDoRedInit,EVERY_DEF,EVERY_APPEND],

	  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
	  METIS_TAC [parseInv_def,validStates_def,shiftReduceGoto],

	  `h IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
	  METIS_TAC [getState_reduce_not_NA,sgoto_exp,
		     slrCompItemsEq,trans_def]
	  ]],

      UNABBREV_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [stackSyms_def]
      ],


    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `s2` THEN SRW_TAC [] []
    THENL[
	  METIS_TAC [auggrRtcRderivesSt],


	    Cases_on `h'` THEN
	    Cases_on `q` THEN
	    UNABBREV_ALL_TAC THEN
	    FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
	    Cases_on `t''` THEN
	    Cases_on `getState m r' h''` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def]
            THENL[

		  `!inis stl sym sta tr t m h r csl sfx.
	    (auggr g st eof = SOME ag) ==>
	    (slr ag = SOME m) ==>
	    (inis = initItems ag (rules ag)) ==>
	    (stl = ((sym,sta),tr)::t) ==>
	    validItemInv
         (ag,((sym,sta),tr)::t,
          (sym,sta)::
              (MAP FST t ++
               [(NTS st,initItems ag (rules ag))])) ==>
       (csl = (sym,sta)::MAP FST t ++ [(NTS st,inis)]) ==>
       parseInv (ag,stl,csl) ==>
       MEM (item lhs (stackSyms stl,[])) sta ==>
       EVERY isTmnlSym (h::sfx) ==>
       RTC (rderives ag) [NTS (startSym ag)]
         ([NTS lhs] ++ h::sfx) ==>
       (getState m sta h = REDUCE r) ==>
       ?stl' csl'.
         (doReduce m (h::sfx,stl,csl) r =
          SOME (h::sfx,stl',csl')) /\
         (stackSyms stl' =
          stackSyms (pop stl (SUC (LENGTH t))) ++ [NTS lhs])` by METIS_TAC [stepDoRedGen] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN [`initItems ag (rules ag)`,`((q',r'),r)::t'`,`q'`,`r'`,
					       `r`,`t'`,`m`,`h''`,`r''`,`(q',r')::
				 (MAP FST t' ++
				      [(NTS st,initItems ag (rules ag))])`,`[]`
					       ]MP_TAC) THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  `LENGTH (REVERSE (MAP FST (MAP FST t')) ++ [q']) = LENGTH (h::t)`
		      by METIS_TAC [] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `LENGTH (REVERSE (MAP FST (MAP FST t'))) = LENGTH t`
		      by DECIDE_TAC THEN
		  FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
		  Cases_on `r''` THEN
		  `MEM (item s (l,[])) r'` by METIS_TAC [getState_mem_itl,sgoto_exp,parseInv_def,validStates_def] THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE (((q',r'),r)::t')))) =
			  SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t')))))`
		      by METIS_TAC [IS_PREFIX_REFL,nullNil,rev_nil,MEM,MEM_APPEND,validItemInv_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND] THEN
		  `h'' IN (followSet ag (NTS s))`
		      by METIS_TAC [getState_reduce_followSet,sgoto_exp,validStates_def,parseInv_def] THEN
		  `h'' IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  `(item s (l,[])) = (item lhs (h::t,[]))`
                      by METIS_TAC [slrCompItemsEq,completeItem_def,itemLhs_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `(REVERSE
			(MAP FST
			     (MAP FST (pop (((q',r'),r)::t') (SUC (LENGTH t'))))) =
			REVERSE
			    (MAP FST
				 (MAP FST (pop (((q',r'),r)::t') (SUC (LENGTH t))))))`
		      by METIS_TAC [LENGTH_MAP,rev_len] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  SPOSE_NOT_THEN ASSUME_TAC THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) []THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  `MEM (rule (startSym ag) [NTS (startSym g);TS eof])
							 (rules ag)` by METIS_TAC [auggrNewRuleMem] THEN
		  `validItem ag [NTS (startSym g)] (item (startSym ag) ([NTS (startSym g)],[TS eof]))`
			by (SRW_TAC [] [validItem_def] THEN
			    MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
			    SRW_TAC [][RTC_RULES] THEN
			    METIS_TAC [rdres1]) THEN
		  `MEM (item (startSym ag) ([NTS (startSym g)],[TS eof])) r'`
		      by METIS_TAC [transImpValidItem] THEN
		  `(TS eof) IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  METIS_TAC [slrNotValid,sgoto_exp,APPEND,isTmnlSym_def,APPEND_NIL],

		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  METIS_TAC [shiftReduceGoto,parseInv_def,validStates_def],

		  FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE t' ++ [((q',r'),r)]))) =
			  SOME (stkItl (REVERSE (REVERSE t' ++ [((q',r'),r)]))))`
		      by METIS_TAC [rev_nil,nullNil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
        	  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND,itemlist_def] THEN
		  `h'' IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
		  METIS_TAC [getState_reduce_not_NA,sgoto_exp,slrCompItemsEq],

		  `!inis stl sym sta tr t m h r csl sfx.
	    (auggr g st eof = SOME ag) ==>
	    (slr ag = SOME m) ==>
	    (inis = initItems ag (rules ag)) ==>
	    (stl = ((sym,sta),tr)::t) ==>
	    validItemInv
         (ag,((sym,sta),tr)::t,
          (sym,sta)::
              (MAP FST t ++
               [(NTS st,initItems ag (rules ag))])) ==>
       (csl = (sym,sta)::MAP FST t ++ [(NTS st,inis)]) ==>
       parseInv (ag,stl,csl) ==>
       MEM (item lhs (stackSyms stl,[])) sta ==>
       EVERY isTmnlSym (h::sfx) ==>
       RTC (rderives ag) [NTS (startSym ag)]
         ([NTS lhs] ++ h::sfx) ==>
       (getState m sta h = REDUCE r) ==>
       ?stl' csl'.
         (doReduce m (h::sfx,stl,csl) r =
          SOME (h::sfx,stl',csl')) /\
         (stackSyms stl' =
          stackSyms (pop stl (SUC (LENGTH t))) ++ [NTS lhs])` by METIS_TAC [stepDoRedGen] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN [`initItems ag (rules ag)`,`((q',r'),r)::t'`,`q'`,`r'`,
					       `r`,`t'`,`m`,`h''`,`r''`,`(q',r')::
				 (MAP FST t' ++
				      [(NTS st,initItems ag (rules ag))])`,`h'::t'''`
					       ]MP_TAC) THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  `LENGTH (REVERSE (MAP FST (MAP FST t')) ++ [q']) = LENGTH (h::t)`
		      by METIS_TAC [] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `LENGTH (REVERSE (MAP FST (MAP FST t'))) = LENGTH t`
		      by DECIDE_TAC THEN
		  SRW_TAC [][exitCond_def]
		  THENL[
			`(NTS lhs::h''::h'::t''') =
		          [NTS lhs]++[h'']++h'::t'''`
			    by METIS_TAC [APPEND,APPEND_ASSOC] THEN
			METIS_TAC [auggrTmSymInBtwn,NOT_CONS_NIL],

			METIS_TAC [LENGTH_MAP,rev_len],

			Cases_on `r''` THEN
			`(trans ag
				(initItems ag (rules ag),
				 stackSyms (REVERSE (REVERSE (((q',r'),r)::t')))) =
				SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t')))))`
			    by METIS_TAC [IS_PREFIX_REFL,nullNil,rev_nil,MEM,MEM_APPEND,validItemInv_def] THEN
			FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND] THEN
			`h'' IN (followSet ag (NTS s))`
		      by METIS_TAC [getState_reduce_followSet,sgoto_exp,validStates_def,parseInv_def] THEN
			`h'' IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
			`MEM (item s (l,[])) r'` by METIS_TAC [getState_mem_itl,sgoto_exp,parseInv_def,validStates_def] THEN
			`(item s (l,[])) = (item lhs (h::t,[]))`
			    by METIS_TAC [slrCompItemsEq,completeItem_def,itemLhs_def] THEN
			FULL_SIMP_TAC (srw_ss()) []
			],

		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  METIS_TAC [shiftReduceGoto,parseInv_def,validStates_def],

		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE t' ++ [((q',r'),r)]))) =
			  SOME (stkItl (REVERSE (REVERSE t' ++ [((q',r'),r)]))))`
		      by METIS_TAC [rev_nil,nullNil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
        	  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND,itemlist_def] THEN
		  METIS_TAC [getState_reduce_not_NA,sgoto_exp,slrCompItemsEq]
		  ]
	    ]],

    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `stl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `s2` THEN SRW_TAC [] []
    THENL[

	  `(h::(t ++ [NTS lhs] ++ []))=
	       ((h::t) ++ [NTS lhs] ++ [])` by METIS_TAC [APPEND_ASSOC,APPEND] THEN
	  METIS_TAC [lastEof,MEM,MEM_APPEND],


	  Cases_on `h'` THEN
	  Cases_on `q` THEN
	  UNABBREV_ALL_TAC THEN
	  FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM,ruleLhs_def,ruleRhs_def,push_def] THEN
	    Cases_on `t''` THEN
	    Cases_on `getState m r' h''` THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def]
            THENL[


		  `!stl csl N h ininp onstk ru sl.
            	    (auggr g st eof = SOME ag) ==>
		    (slr ag = SOME m) ==>
		    EVERY isTmnlSym sl ==>
		    (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
		    ~(ininp = []) ==>
		    EVERY isTmnlSym (onstk ++ ininp) ==>
		    (sl = onstk ++ ininp) ==>
		    viablePfx ag (N,h) (stackSyms stl ++ ininp) (stackSyms stl) ==>
		    parseInv (ag,stl,csl) ==>
		    validItemInv (ag,stl,csl) ==>
		    (getState (sgoto ag,reduce ag) (itemlist csl) (HD ininp) =
		     REDUCE ru) ==>
		    ?sl' stl' csl'.
		    (doReduce m (ininp,stl,csl) ru = SOME (sl',stl',csl'))
		    /\ (stackSyms stl'=
			stackSyms (pop stl (LENGTH (ruleRhs ru)))
				  ++ [NTS (ruleLhs ru)]) /\ (sl'=ininp)`
		      by METIS_TAC [macStepDoRedExists] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				     [`((q',r'),r)::t'`,
				      `(q',r')::(MAP FST t' ++
				      [(NTS st,initItems ag (rules ag))])`,
				      `lhs`,`rhs`,`[h'']`,`[]`,`r''`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
		  SRW_TAC [][] THEN
		  Cases_on `r''`THEN
		  `MEM (item s (l,[])) r'` by METIS_TAC [sgoto_exp,parseInv_def,validStates_def,getState_mem_itl] THEN
		  `h'' IN (followSet ag (NTS s))` by METIS_TAC [sgoto_exp,parseInv_def,validStates_def,getState_reduce_followSet] THEN
		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE t' ++ [((q',r'),r)]))) =
			  SOME (stkItl (REVERSE (REVERSE t' ++ [((q',r'),r)]))))`
		      by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [stkItl_def,stackSyms_def,itemlist_def,REVERSE_APPEND] THEN
		  `(item s (l,[]) = item lhs (rhs,[]))` by METIS_TAC [slrCompItemsEq,completeItem_def,itemLhs_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [ruleRhs_def,ruleLhs_def] THEN
		  SRW_TAC [][] THEN
		  `validItl ag [item lhs (l,[])]` by METIS_TAC [validItl_append,rgr_r9eq,parseInv_def,validStates_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
		  `viablePfx ag (lhs,l) (h::(t ++ l ++ [h'']))
			    (h::(t ++ l))`
		      by (SRW_TAC [][viablePfx_def,handleg_def] THEN
			  MAP_EVERY Q.EXISTS_TAC [`h::t`,`[h'']`] THEN
			  SRW_TAC [][IS_PREFIX_APPEND] THEN
			  METIS_TAC [APPEND_NIL]) THEN
		  FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
		  Cases_on `~(stackSyms t' ++ [q'] = [NTS (startSym g)])`
		  THENL[
			METIS_TAC [],

			FULL_SIMP_TAC (srw_ss()) [] THEN
			Cases_on `stackSyms t'` THEN
			FULL_SIMP_TAC (srw_ss()) [stackSyms_def]  THEN
			Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			SRW_TAC [][] THEN
			`MEM (rule (startSym ag) [NTS (startSym g);TS eof])
		        (rules ag)` by METIS_TAC [auggrNewRuleMem] THEN
			FULL_SIMP_TAC (srw_ss()) [pop_def,validItemInv_def] THEN
			`(trans ag
				(initItems ag (rules ag),
				 REVERSE (MAP FST (MAP FST (REVERSE [((NTS (startSym g),r'),r)])))) =
				SOME (SND (FST (HD (REVERSE [((NTS (startSym g),r'),r)])))))`
			    by METIS_TAC [IS_PREFIX_REFL,APPEND,NOT_CONS_NIL,nullNil] THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			`validItem ag [NTS (startSym g)] (item (startSym ag) ([NTS (startSym g)],[TS eof]))`
			by (SRW_TAC [] [validItem_def] THEN
			    MAP_EVERY Q.EXISTS_TAC [`[]`,`[]`] THEN
			    SRW_TAC [][RTC_RULES] THEN
			    METIS_TAC [rdres1]) THEN
			`MEM (item (startSym ag) ([NTS (startSym g)],[TS eof])) r'`
			by METIS_TAC [transImpValidItem] THEN
			`?p.[h'']=p++[TS eof]` by METIS_TAC [APPEND,lastEof,APPEND_NIL] THEN
			Cases_on `p` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
			SRW_TAC [][] THEN
			`(TS eof) IN (followSet ag (NTS lhs))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def] THEN
			METIS_TAC [slrNotValid,sgoto_exp,APPEND,isTmnlSym_def,APPEND_NIL]
			],

		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  METIS_TAC [shiftReduceGoto,parseInv_def,validStates_def],

		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE t' ++ [((q',r'),r)]))) =
			  SOME (stkItl (REVERSE (REVERSE t' ++ [((q',r'),r)]))))`
		      by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [stkItl_def,stackSyms_def,itemlist_def,REVERSE_APPEND] THEN
		  METIS_TAC [getState_reduce_not_NA,sgoto_exp,slrCompItemsEq],


		  `!stl csl N h ininp onstk ru sl.
            	    (auggr g st eof = SOME ag) ==>
		    (slr ag = SOME m) ==>
		    EVERY isTmnlSym sl ==>
		    (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
		    ~(ininp = []) ==>
		    EVERY isTmnlSym (onstk ++ ininp) ==>
		    (sl = onstk ++ ininp) ==>
		    viablePfx ag (N,h) (stackSyms stl ++ ininp) (stackSyms stl) ==>
		    parseInv (ag,stl,csl) ==>
		    validItemInv (ag,stl,csl) ==>
		    (getState (sgoto ag,reduce ag) (itemlist csl) (HD ininp) =
		     REDUCE ru) ==>
		    ?sl' stl' csl'.
		    (doReduce m (ininp,stl,csl) ru = SOME (sl',stl',csl'))
		    /\ (stackSyms stl'=
			stackSyms (pop stl (LENGTH (ruleRhs ru)))
				  ++ [NTS (ruleLhs ru)]) /\ (sl'=ininp)`
		      by METIS_TAC [macStepDoRedExists] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				     [`((q',r'),r)::t'`,
				      `(q',r')::(MAP FST t' ++
				      [(NTS st,initItems ag (rules ag))])`,
				      `lhs`,`rhs`,`h''::h'::t'''`,`[]`,`r''`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
		  SRW_TAC [][] THEN
		  Cases_on `r''`THEN
		  `MEM (item s (l,[])) r'` by METIS_TAC [sgoto_exp,parseInv_def,validStates_def,getState_mem_itl] THEN
		  `h'' IN (followSet ag (NTS s))` by METIS_TAC [sgoto_exp,parseInv_def,validStates_def,getState_reduce_followSet] THEN
		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE t' ++ [((q',r'),r)]))) =
			  SOME (stkItl (REVERSE (REVERSE t' ++ [((q',r'),r)]))))`
		      by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [stkItl_def,stackSyms_def,itemlist_def,REVERSE_APPEND] THEN
		  `(item s (l,[]) = item lhs (rhs,[]))` by METIS_TAC [slrCompItemsEq,completeItem_def,itemLhs_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [ruleRhs_def,ruleLhs_def] THEN
		  SRW_TAC [][] THEN
		  `validItl ag [item lhs (l,[])]` by METIS_TAC [validItl_append,rgr_r9eq,parseInv_def,validStates_def] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItl_def] THEN
		  `viablePfx ag (lhs,l) (h::(t ++ l ++ h''::h'::t'''))
			    (h::(t ++ l))`
		      by (SRW_TAC [][viablePfx_def,handleg_def] THEN
			  MAP_EVERY Q.EXISTS_TAC [`h::t`,`h''::h'::t'''`] THEN
			  SRW_TAC [][IS_PREFIX_APPEND] THEN
			  METIS_TAC [APPEND_NIL]) THEN
		  SRW_TAC [][exitCond_def] THEN
		  Cases_on `~(h'' = TS eof)`
		  THENL[
			METIS_TAC [],

			FULL_SIMP_TAC (srw_ss()) []THEN
			SRW_TAC [][] THEN
			`(h::(t++[NTS lhs]++TS eof::h'::t''')) =
		          (h::t++ [NTS lhs])++[TS eof]++(h'::t''')`
			    by METIS_TAC [APPEND,APPEND_ASSOC] THEN
			METIS_TAC [auggrTmSymInBtwn,NOT_CONS_NIL,isTmnlSym_def]
			],

		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  METIS_TAC [shiftReduceGoto,parseInv_def,validStates_def],

		  `(h'' IN (followSet ag (NTS lhs)))` by METIS_TAC [followSetMem,rtcRdImpDg, EVERY_APPEND, isTmnlSym_def, EVERY_DEF,APPEND,APPEND_ASSOC] THEN
		  FULL_SIMP_TAC (srw_ss()) [validItemInv_def] THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE t' ++ [((q',r'),r)]))) =
			  SOME (stkItl (REVERSE (REVERSE t' ++ [((q',r'),r)]))))`
		      by METIS_TAC [nullNil,rev_nil,IS_PREFIX_REFL,MEM,MEM_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [stkItl_def,stackSyms_def,itemlist_def,REVERSE_APPEND] THEN
		  METIS_TAC [getState_reduce_not_NA,sgoto_exp,slrCompItemsEq]
		  ]
	  ]])



val lem1Gen = store_thm ("lem1Gen",
``!csli stli rhs pfx sfx N onstk ininp.
(auggr g st eof = SOME ag) ==>
RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
(!nt.nt IN (nonTerminals ag) ==> gaw ag nt) ==>
(csli = (MAP FST stli++[(NTS st,initItems ag (rules ag))])) ==>
MEM (rule N rhs) (rules ag) ==>
(stackSyms stli = pfx++onstk) ==>
~(N=startSym ag) ==>
EVERY isTmnlSym (ininp++sfx) ==>
(slr ag = SOME m) ==>
(rhs = onstk ++ ininp) ==>
(csli = MAP FST stli ++ [(NTS st,initItems ag (rules ag))]) ==>
~(stli=[]) ==>
(!nt.nt IN (nonTerminals ag) ==> gaw ag nt) ==>
parseInv (ag, stli, csli) ==>
validItemInv (ag,stli,csli) ==>
?i stl csl.
      takesSteps (LENGTH ininp) (parse (SOME m))
      (exitCond (eof,NTS (startSym g)))
        (ininp++sfx,stli,csli) (i,stl,csl)
	   /\ (stackSyms stl = stackSyms stli ++ ininp)
	   /\ (i=sfx) /\ (MEM (item N (rhs,[])) (itemlist csl))
           /\ (getState m (itemlist csl) (HD sfx)
	       = REDUCE (rule N rhs))``,
Induct_on `ininp` THEN
FULL_SIMP_TAC (srw_ss()) [takesSteps_def]
THENL[

      SRW_TAC [] [] THEN
      `validItem ag (stackSyms stli) (item N (onstk,[]))`
	  by (SRW_TAC [] [validItem_def] THEN
		   Q.EXISTS_TAC `sfx` THEN
	      METIS_TAC [rdres1, rderives_append, APPEND_NIL]) THEN
      `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE stli))) =
          SOME (stkItl (REVERSE (REVERSE stli))))`
	  by METIS_TAC [nullNil, IS_PREFIX_REFL, rev_nil, validItemInv_def] THEN
      FULL_SIMP_TAC (srw_ss()) [itemlist_def, stkItl_def] THEN
      Cases_on `stli` THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    METIS_TAC [transImpValidItem],

	    Cases_on `h` THEN
	    Cases_on `q` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `MEM (item N (onstk,[])) r'`
		by METIS_TAC [transImpValidItem] THEN
	    `~(sfx=[])` by METIS_TAC [lastEof,APPEND_NIL,MEM,MEM_APPEND] THEN
	    Cases_on `sfx` THEN SRW_TAC [][] THEN
	    `h IN (followSet ag (NTS N))` by METIS_TAC [followSetMem, APPEND, APPEND_ASSOC, APPEND_NIL, rtcRdImpDg, isTmnlSym_def,EVERY_DEF] THEN
	    `m=(sgoto ag,reduce ag)`
		by METIS_TAC [sgoto_exp] THEN
	    FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
	    Cases_on `sgoto ag r' h` THEN
	    Cases_on `reduce ag r' (sym2Str h)` THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    THENL[
		  METIS_TAC [reduce_not_mem],

		  Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) []
		  THENL[
			FULL_SIMP_TAC (srw_ss()) [rgr_r9eq]THEN
			SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) [reduce_def,reduce_append] THEN
			Cases_on `h` THEN
			FULL_SIMP_TAC (srw_ss()) [sym2Str_def,followSetEq,isTmnlSym_def] THEN
			Cases_on `TS s IN followSet ag (NTS N)` THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			Cases_on `reduce ag r1' s` THEN
			Cases_on `reduce ag r2' s` THEN
			FULL_SIMP_TAC (srw_ss()) [],

			FULL_SIMP_TAC (srw_ss()) [slr_def,LET_THM]THEN
			FIRST_X_ASSUM (Q.SPECL_THEN
					   [`stackSyms t ++ [q']`,
					    `r'`,`h`] MP_TAC) THEN
			SRW_TAC [] []
			],

		  METIS_TAC [reduce_not_mem],


		  FULL_SIMP_TAC (srw_ss()) [slr_def,LET_THM]THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				     [`stackSyms t ++ [q']`,
				      `r'`,`h`] MP_TAC) THEN
		  SRW_TAC [] [] THEN
		  Cases_on `t'''` THEN FULL_SIMP_TAC (srw_ss()) []
		  ]
	    ],

      SRW_TAC [] [exitCond_def] THEN
      (FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
       SRW_TAC [][] THEN
      Cases_on `stli` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Cases_on `h'` THEN Cases_on `q` THEN
      FULL_SIMP_TAC (srw_ss()) [parse_def,LET_THM] THEN
      Q.ABBREV_TAC `csli = (q',r')::
                            (MAP FST t ++
                             [(NTS st,initItems ag (rules ag))])` THEN
      Cases_on `ininp++sfx` THEN
      Cases_on `getState m r' h` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) []
      THENL[
	    METIS_TAC [lastEof,APPEND_NIL,MEM,MEM_APPEND],
	    METIS_TAC [lastEof,APPEND_NIL,MEM,MEM_APPEND],
	    METIS_TAC [lastEof,APPEND_NIL,MEM,MEM_APPEND],


	    SRW_TAC [] [itemlist_def, exitCond_def] THEN
	    `validItem ag (stackSyms (((q',r'),r)::t))
                 (item N (onstk,h::ininp))`
		by (SRW_TAC [] [validItem_def] THEN
		    Q.EXISTS_TAC `sfx` THEN
		    SRW_TAC [] [stackSyms_def] THEN
		    METIS_TAC [rdres1, rderives_append, EVERY_DEF, EVERY_APPEND, APPEND_ASSOC]) THEN
	    `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
              SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))`
		by METIS_TAC [nullNil, IS_PREFIX_REFL, rev_nil, validItemInv_def, NOT_CONS_NIL] THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def, stkItl_def] THEN
	    `MEM (item N (onstk,h::ininp)) r'`
		by METIS_TAC [transImpValidItem] THEN
	    Cases_on `r''`  THEN
	    `(item N (onstk,h::ininp)=item s (l,[]))
            \/ ~ ?l' r2 r1. (item N (onstk,h::ininp) =
			     item l' (r1,h::r2))`
	    by METIS_TAC [parseInv_def, validStates_def, shiftReduce] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [APPEND],

	    Cases_on `h` THEN
	    FULL_SIMP_TAC (srw_ss()) [isNonTmnlSym_def,isTmnlSym_def,push_def] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN
	      [`((TS s,l),Leaf (TM (tmnlSym (TS s))))::((q',r'),r)::t`,
	       `pfx`, `sfx`, `N`,
	       `onstk++[TS s]`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    IMP_RES_TAC validItemInvGoto THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
	    SRW_TAC [] [] THEN
	    UNABBREV_ALL_TAC THEN
	    FULL_SIMP_TAC (srw_ss()) [parseInv_def,stackValid_def,validStates_def] THEN
	    FULL_SIMP_TAC (srw_ss()) [validStkSymTree_def, tmnlSym_def, ptree2Sym_def, tmnlToStr_def] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
	    `validItl ag l` by METIS_TAC [getStateGotoValidItl] THEN
	    FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
	    `validStlItems (((TS s,l),Leaf (TM s))::((ptree2Sym r,r'),r)::t) l`
		by METIS_TAC [validStlItems_goto,sgoto_exp,tmnlToStr_def,tmnlSym_def,ptree2Sym_def] THEN
	    `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
	    `(case sgoto ag r' (TS s) of
               [] ->
                 (case reduce ag r' (sym2Str (TS s)) of
                     [] -> NA
                  || y::ys ->
                       (if
                          LENGTH
                            (reduce ag r' (sym2Str (TS s))) =
                          1
                        then
                          REDUCE
                            (HD (reduce ag r' (sym2Str (TS s))))
                        else
                          NA))
            || x::xs ->
                 case reduce ag r' (sym2Str (TS s)) of
                    [] -> GOTO (sgoto ag r' (TS s))
                 || y'::ys' ->
                      (if itemEqRuleList (x::xs) (y'::ys') then
                         REDUCE
                           (HD (reduce ag r' (sym2Str (TS s))))
                       else
                         NA)) =
           GOTO l` by FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
	    Cases_on `sgoto ag r' (TS s)` THEN
	    Cases_on `reduce ag r' (sym2Str (TS s))` THEN
	    FULL_SIMP_TAC (srw_ss()) []
	    THENL[
		  Cases_on `LENGTH t''=0` THEN
		  FULL_SIMP_TAC (srw_ss()) [],


		  FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
		  `EVERY (validItem ag (stackSyms t ++ [ptree2Sym r] ++ [TS s]))
					(moveDot r' (TS s))`
		      by METIS_TAC [validItem_moveDot, APPEND_NIL] THEN
		  `EVERY (validItem ag (stackSyms t ++ [ptree2Sym r] ++ [TS s]))
			(iclosure ag (moveDot r' (TS s)))`
		      by METIS_TAC [validItem_iclosure] THEN
		  SRW_TAC [] [] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `~(s=eof)` by (SRW_TAC [][] THEN
		  SPOSE_NOT_THEN ASSUME_TAC THEN
		  SRW_TAC [][] THEN
		  METIS_TAC [auggrEofInRhs,MEM,MEM_APPEND,APPEND,APPEND_ASSOC]) THEN
		  `?stl csl.
			takesSteps (LENGTH ininp)
			(parse (SOME (sgoto ag,reduce ag)))
			(exitCond (eof,NTS (startSym g)))
			(h'::t',
			 ((TS s,h::t''),Leaf (TM s))::
			 ((ptree2Sym r,r'),r)::t,
			 (TS s,h::t'')::(ptree2Sym r,r')::
			 (MAP FST t ++
			      [(NTS st,initItems ag (rules ag))]))
			(sfx,stl,csl) /\
                        (stackSyms stl =
			 pfx ++ onstk ++ [TS s] ++ ininp) /\
                         MEM (item N (onstk ++ [TS s] ++ ininp,[]))
			 (SND (HD csl)) /\
                          (getState (sgoto ag,reduce ag) (SND (HD csl))
				    (HD sfx) =
				    REDUCE (rule N (onstk ++ [TS s] ++ ininp)))`
		      by METIS_TAC [EVERY_DEF, APPEND, APPEND_ASSOC] THEN
		  Q.EXISTS_TAC `stl` THEN
		  Q.EXISTS_TAC `csl` THEN
		  SRW_TAC [][] THEN
		  METIS_TAC [APPEND,APPEND_ASSOC],

		  Cases_on `itemEqRuleList (h::t'') (h''::t''')` THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  ],

	    `validItem ag (stackSyms (((q',r'),r)::t))
                 (item N (onstk,h::ininp))`
		by (SRW_TAC [] [validItem_def] THEN
		    Q.EXISTS_TAC `sfx` THEN
		    SRW_TAC [] [stackSyms_def] THEN
		    METIS_TAC [rdres1, rderives_append, EVERY_DEF, EVERY_APPEND, APPEND_ASSOC]) THEN
	    `(trans ag (initItems ag (rules ag),stackSyms (REVERSE (REVERSE (((q',r'),r)::t)))) =
              SOME (stkItl (REVERSE (REVERSE (((q',r'),r)::t)))))`
		by METIS_TAC [nullNil, IS_PREFIX_REFL, rev_nil, validItemInv_def, NOT_CONS_NIL] THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def, stkItl_def] THEN
	    `MEM (item N (onstk,h::ininp)) r'`
		by METIS_TAC [transImpValidItem] THEN
	    METIS_TAC [getState_shift_not_NA, sgoto_exp, APPEND_NIL]
	    ])
      ])



val lem2Gen = store_thm ("lem2Gen",
``!csli stli rhs pfx sfx N onstk ininp.
(auggr g st eof = SOME ag) ==>
RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
(csli = (MAP FST stli++[(NTS st,initItems ag (rules ag))])) ==>
MEM (rule N rhs) (rules ag) ==>
~(N=startSym ag) ==>
EVERY isTmnlSym (ininp++rhs++sfx) ==>
(slr ag = SOME m) ==>
(pfx = onstk ++ ininp) ==>
(stackSyms stli = onstk) ==>
(!nt.nt IN (nonTerminals ag) ==> gaw ag nt) ==>
(LENGTH csli = LENGTH stli + 1) ==>
parseInv (ag, stli, csli) ==>
validItemInv (ag,stli,csli) ==>
?i stl csl.
      takesSteps (LENGTH ininp) (parse (SOME m))
      (exitCond (eof,NTS (startSym g)))
        (ininp ++ rhs++ sfx,stli,csli) (i,stl,csl)
	   /\ (stackSyms stl = pfx) /\ (i=rhs++sfx)
	   /\  MEM (item N ([],rhs)) (itemlist csl)``,
Induct_on `ininp` THEN
SRW_TAC [] [takesSteps_def, exitCond_def]
THENL[
      Cases_on `stli` THEN
      FULL_SIMP_TAC (srw_ss()) [itemlist_def]
      THENL[
	    METIS_TAC [initItemsHdNt],

	    `(trans ag
              (initItems ag (rules ag),
               stackSyms (REVERSE (REVERSE (h::t)))) =
            SOME (stkItl (REVERSE (REVERSE (h::t)))))`
		by METIS_TAC [validItemInv_def,NOT_CONS_NIL,nullNil,IS_PREFIX_REFL,rev_nil] THEN
	    FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,stackSyms_def,REVERSE_APPEND] THEN
	    `validItem ag (REVERSE (MAP FST (MAP FST t)) ++ [FST (FST h)])
                          (item N ([],rhs))`
	    by (SRW_TAC [][validItem_def] THEN
		Q.EXISTS_TAC `sfx` THEN SRW_TAC [][] THEN
		METIS_TAC [rderives_def,rdres1,rderives_append]) THEN
	    METIS_TAC [transImpValidItem]
	    ],


      SRW_TAC [] [] THEN
      FULL_SIMP_TAC (srw_ss()) [takesSteps_def] THEN
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
	     `h IN followSet ag (NTS s)` by METIS_TAC [getState_reduce_followSet, sgoto_exp, validStates_def, parseInv_def, parseInvInit] THEN
	     `MEM (item s (l,[])) (initItems ag (rules ag))` by METIS_TAC [validStates_def, getState_mem_itl, sgoto_exp, parseInvInit, parseInv_def] THEN
	     `validItl ag [item s (l,[])]` by METIS_TAC [validItl_append, validStates_def, rgr_r9eq, parseInvInit, parseInv_def] THEN
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
			 METIS_TAC [slrNotValid,trans_def,sgoto_exp]
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
			 `MEM (rule s' l') (rules ag)`
			 by METIS_TAC [getstate_red, sgoto_exp] THEN
			 `h IN (followSet ag (NTS s'))` by METIS_TAC [getState_reduce_followSet, sgoto_exp] THEN
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
			 METIS_TAC [slrTransConf,parseInv_def,validStates_def],

			 (*5*)
			 Cases_on `h` THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
			 SRW_TAC [] [] THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN
			    [`((TS s',l'),Leaf (TM (tmnlSym (TS s'))))::((q',r'),r)::t''`,
			     `rhs`, `sfx`, `N`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
			 IMP_RES_TAC validItemInvGoto THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStkSymTree_def, tmnlSym_def, ptree2Sym_def, tmnlToStr_def, parseInv_def] THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStates_def, itemlist_def] THEN
			 `validItl ag l'` by METIS_TAC [getStateGotoValidItl] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
			 `validStlItems (((TS s',l'),Leaf (TM (tmnlSym (TS s'))))::((ptree2Sym r,r'),r)::t'') l'`
			     by METIS_TAC [validStlItems_goto,sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [tmnlSym_def, ptree2Sym_def, tmnlToStr_def,stackValid_def,itemlist_def] THEN
			 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
			 Cases_on `sgoto ag r' (TS s')` THEN
			 Cases_on `reduce ag r' (sym2Str (TS s'))` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       Cases_on `LENGTH t''''=0` THEN
			       FULL_SIMP_TAC (srw_ss()) [],


			       FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
			       `EVERY (validItem ag (stackSyms t'' ++ [ptree2Sym r]++[TS s'])) (moveDot r' (TS s'))`
				   by METIS_TAC [validItem_moveDot] THEN
			       `EVERY (validItem ag (stackSyms t'' ++ [ptree2Sym r]++[TS s'])) (iclosure ag (moveDot r' (TS s')))`
				   by METIS_TAC [validItem_iclosure] THEN
			       SRW_TAC [] [push_def]  THEN
			       Cases_on `~(s' = eof)`
			       THENL[
				     METIS_TAC [EVERY_DEF, APPEND, APPEND_ASSOC],

				     FULL_SIMP_TAC (srw_ss()) []THEN
				     SRW_TAC [][] THEN

				     `(h''::(t' ++ TS eof::ininp ++ [NTS N] ++ sfx))=
              		              (h''::t') ++ [TS eof] ++ (ininp ++ [NTS N] ++ sfx)`
					by METIS_TAC [APPEND,APPEND_ASSOC] THEN
				     METIS_TAC [auggrTmSymInBtwn,MEM,MEM_APPEND,isTmnlSym_def]
				     ],

			       Cases_on `itemEqRuleList (h::t'''') (h''''::t''''')` THEN
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
			 `r'=s'` by METIS_TAC [transOutMem,SOME_11] THEN
			 SRW_TAC [][] THEN
			 `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
			 FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
			 Cases_on `moveDot r' h` THEN
			 FULL_SIMP_TAC (srw_ss()) [] THEN
			 Cases_on `sgoto ag r' h` THEN
			 Cases_on `reduce ag r' (sym2Str h)` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [iclosure_mem,MEM],

			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [iclosure_mem,MEM],

			       Cases_on `itemEqRuleList (h'''''::t''''') (h''''''::t'''''')`THEN
			       FULL_SIMP_TAC (srw_ss()) [slr_def,LET_THM] THEN
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
			       `[TS s;NTS N] = [TS s]++[NTS N]`
			       by SRW_TAC [][] THEN
			       METIS_TAC [APPEND_NIL,MEM,MEM_APPEND,lastEof],

			       SRW_TAC [] [push_def,tmnlToStr_def,tmnlSym_def,ptree2Sym_def] THEN
			       FIRST_X_ASSUM (Q.SPECL_THEN
						  [`[((TS s,l),Leaf (TM s))]`,`rhs`,`sfx`, `N`] MP_TAC)   THEN
			       SRW_TAC [] [] THEN
			       FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def,IS_PREFIX] THEN
			       FULL_SIMP_TAC (srw_ss()) [parseInv_def,validStates_def,validStlItemsStack_def,stackValid_def,itemlist_def,validStkSymTree_def] THEN
			       FULL_SIMP_TAC (srw_ss()) [ptree2Sym_def,tmnlSym_def,tmnlToStr_def] THEN
			       `validItl ag l` by METIS_TAC [getStateGotoValidItl] THEN
			       `validStlItems [((TS s,l),Leaf (TM s))] l`
				   by METIS_TAC [validStlItems_goto,ptree2Sym_def,tmnlSym_def,tmnlToStr_def,sgoto_exp] THEN
			       `!csl t.(getState m (itemlist csl) (TS s) = GOTO l) ==>
         					     (csl = MAP FST t ++ [(NTS st,initItems ag (rules ag))]) ==>
						     parseInv (ag,t,csl) ==>
						     validItemInv
						     (ag,t,MAP FST t ++ [(NTS st,initItems ag (rules ag))]) ==>
						     validItemInv
						     (ag,((TS s,l),Leaf (TM (tmnlSym (TS s))))::t,
						      (TS s,l)::MAP FST t ++ [(NTS st,initItems ag (rules ag))])`
				   by METIS_TAC [validItemInvGotoInit] THEN
			       FIRST_X_ASSUM (Q.SPECL_THEN [`[(NTS st,initItems ag (rules ag))]`,`[]`] MP_TAC) THEN
			       SRW_TAC [][] THEN
			       FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
			       `validItemInv
						     (ag,[((TS s,l),Leaf (TM (tmnlSym (TS s))))],
						      [(TS s,l); (NTS st,initItems ag (rules ag))])`
				   by METIS_TAC [parseInvInit] THEN
			       `EVERY (validItem ag []) (iclosure ag (initItems ag (rules ag)))`
				   by METIS_TAC [validItem_iclosure] THEN
			       `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
			       FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
			       Cases_on `sgoto ag (initItems ag (rules ag)) (TS s)` THEN
			       Cases_on `reduce ag (initItems ag (rules ag)) (sym2Str (TS s))` THEN
			       FULL_SIMP_TAC (srw_ss()) []
				THENL[
				      Cases_on `LENGTH t''` THEN
				      FULL_SIMP_TAC (srw_ss()) [],


				      FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
				      `EVERY (validItem ag [TS s]) (moveDot (initItems ag (rules ag)) (TS s))`
					  by METIS_TAC [validItem_moveDot, APPEND_NIL] THEN
				      `EVERY (validItem ag [TS s]) l`
					  by METIS_TAC [validItem_iclosure] THEN
				      FULL_SIMP_TAC (srw_ss()) [push_def] THEN
				      METIS_TAC [tmnlSym_def,ptree2Sym_def,tmnlToStr_def],

				      Cases_on `itemEqRuleList (h::t'') (h'''::t''')` THEN
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
			       `MEM (rule s l') (rules ag)`
				   by METIS_TAC [getstate_red, sgoto_exp] THEN
			       `h IN (followSet ag (NTS s))` by METIS_TAC [getState_reduce_followSet, sgoto_exp] THEN
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
			       `r'=s'` by METIS_TAC [transOutMem,SOME_11] THEN
			       SRW_TAC [][] THEN
			       `m=(sgoto ag,reduce ag)` by METIS_TAC [sgoto_exp] THEN
			       FULL_SIMP_TAC (srw_ss()) [getState_def,LET_THM] THEN
			       FULL_SIMP_TAC (srw_ss()) [trans_def] THEN
			       Cases_on `moveDot r' h` THEN
			       FULL_SIMP_TAC (srw_ss()) [] THEN
			       Cases_on `sgoto ag r' h` THEN
			       Cases_on `reduce ag r' (sym2Str h)` THEN
			       FULL_SIMP_TAC (srw_ss()) []
         		       THENL[
				     FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
				     METIS_TAC [iclosure_mem,MEM],

				     Cases_on `itemEqRuleList (h''''::t'''') (h'''''::t''''')`THEN
				     FULL_SIMP_TAC (srw_ss()) [slr_def,LET_THM] THEN
				     FIRST_X_ASSUM (Q.SPECL_THEN
							[`REVERSE (MAP FST (MAP FST t')) ++ [q']`,`r'`,`h`] MP_TAC) THEN
				     SRW_TAC [][] THEN
				     Cases_on `t'''''` THEN FULL_SIMP_TAC (srw_ss()) []
				     ],

			 Cases_on `h` THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
			 SRW_TAC [] [push_def] THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN
			    [`((TS s,l'),Leaf (TM (tmnlSym (TS s))))::((q',r'),r)::t'`,
			     `rhs`, `sfx`, `N`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
			 `!q' r' r l t s csli.(slr ag = SOME m) ==>
                          (getState m r' (TS s) = GOTO l) ==>
                          parseInv (ag,((q',r'),r)::t,csli) ==>
			  validItemInv (ag,((q',r'),r)::t,csli) ==>
			  (csli =
			   (q',r')::(MAP FST t ++ [(NTS st,initItems ag (rules ag))])) ==>
			  validItemInv
			  (ag,((TS s,l),Leaf (TM (tmnlSym (TS s))))::((q',r'),r)::t,
			   (TS s,l)::csli)`
			     by METIS_TAC [validItemInvGoto] THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN [`q'`,`r'`,`r`, `l'`,`t'`,`s`,`(q',r')::(MAP FST t' ++ [(NTS st,initItems ag (rules ag))])`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStkSymTree_def, tmnlSym_def, ptree2Sym_def, tmnlToStr_def, parseInv_def,stackValid_def,itemlist_def] THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStates_def, itemlist_def] THEN
			 `validItl ag l'` by METIS_TAC [getStateGotoValidItl] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [tmnlSym_def, ptree2Sym_def, tmnlToStr_def] THEN
			 `validStlItems (((TS s,l'),Leaf (TM s))::((ptree2Sym r,r'),r)::t') l'`
			     by METIS_TAC [validStlItems_goto,sgoto_exp, ptree2Sym_def, tmnlToStr_def, tmnlSym_def] THEN
			 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
			 Cases_on `sgoto ag r' (TS s)` THEN
			 Cases_on `reduce ag r' (sym2Str (TS s))` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       Cases_on `LENGTH t'''=0` THEN
			       FULL_SIMP_TAC (srw_ss()) [],


			       FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
			       `EVERY (validItem ag (stackSyms t' ++ [ptree2Sym r ]++[TS s])) (moveDot r' (TS s))`
				   by METIS_TAC [validItem_moveDot] THEN
			       `EVERY (validItem ag (stackSyms t' ++ [ptree2Sym r]++[TS s])) (iclosure ag (moveDot r' (TS s)))`
				   by METIS_TAC [validItem_iclosure] THEN
			       SRW_TAC [][] THEN
			       FULL_SIMP_TAC (srw_ss()) [] THEN
			       FULL_SIMP_TAC (srw_ss()) [stackValid_def] THEN
			       `RTC (rderives ag) [NTS (startSym ag)]
						      (stackSyms t' ++ [ptree2Sym r] ++ [TS s] ++
								 ininp ++ [NTS N] ++ sfx)`
				   by METIS_TAC [APPEND,APPEND_ASSOC] THEN
			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [APPEND,APPEND_ASSOC,EVERY_DEF],

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
			       Cases_on `reduce ag r' (sym2Str h)` THEN
			       FULL_SIMP_TAC (srw_ss()) []
         		       THENL[
				     FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
				     METIS_TAC [iclosure_mem,MEM],

				     FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
				     METIS_TAC [iclosure_mem,MEM],

				     Cases_on `itemEqRuleList (h'''''::t''''') (h''''''::t'''''')`THEN
				     FULL_SIMP_TAC (srw_ss()) [slr_def,LET_THM] THEN
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
			 METIS_TAC [slrTransConf,parseInv_def,validStates_def],

			 (*5*)
			 Cases_on `h` THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def, isNonTmnlSym_def] THEN
 			 SRW_TAC [] [] THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN
			    [`((TS s,l),Leaf (TM (tmnlSym (TS s))))::((q',r'),r)::t''`,
			     `rhs`, `TS s'::t'`, `N`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
			 IMP_RES_TAC validItemInvGoto THEN
			 FIRST_X_ASSUM (Q.SPECL_THEN [`st`] MP_TAC) THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStkSymTree_def, tmnlSym_def, ptree2Sym_def, tmnlToStr_def, parseInv_def] THEN
			 SRW_TAC [] [] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStates_def, itemlist_def] THEN
			 `validItl ag l` by METIS_TAC [getStateGotoValidItl] THEN
			 FULL_SIMP_TAC (srw_ss()) [validStlItemsStack_def] THEN
			 `validStlItems (((TS s,l),Leaf (TM s))::((ptree2Sym r,r'),r)::t'') l`
			     by METIS_TAC [validStlItems_goto,sgoto_exp,ptree2Sym_def,tmnlToStr_def,tmnlSym_def] THEN
			 FULL_SIMP_TAC (srw_ss()) [tmnlSym_def, ptree2Sym_def, tmnlToStr_def,stackValid_def,itemlist_def] THEN
			 `m=(sgoto ag, reduce ag)` by METIS_TAC [sgoto_exp] THEN
			 FULL_SIMP_TAC (srw_ss()) [getState_def, LET_THM] THEN
			 Cases_on `sgoto ag r' (TS s)` THEN
			 Cases_on `reduce ag r' (sym2Str (TS s))` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       Cases_on `LENGTH t''''=0` THEN
			       FULL_SIMP_TAC (srw_ss()) [],


			       FULL_SIMP_TAC (srw_ss()) [sgoto_def, nextState_def] THEN
			       `EVERY (validItem ag (stackSyms t'' ++ [ptree2Sym r]++[TS s])) (moveDot r' (TS s))`
				   by METIS_TAC [validItem_moveDot] THEN
			       `EVERY (validItem ag (stackSyms t'' ++ [ptree2Sym r]++[TS s])) (iclosure ag (moveDot r' (TS s)))`
				   by METIS_TAC [validItem_iclosure] THEN
			       SRW_TAC [] [push_def] THEN
			       METIS_TAC [EVERY_DEF, APPEND, APPEND_ASSOC],

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
			 Cases_on `reduce ag r' (sym2Str h)` THEN
			 FULL_SIMP_TAC (srw_ss()) []
			 THENL[
			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [iclosure_mem,MEM],

			       FULL_SIMP_TAC (srw_ss()) [sgoto_def,nextState_def] THEN
			       METIS_TAC [iclosure_mem,MEM],

			       Cases_on `itemEqRuleList (h'''''::t''''') (h''''''::t'''''')`THEN
			       FULL_SIMP_TAC (srw_ss()) [slr_def,LET_THM] THEN
			       FIRST_X_ASSUM (Q.SPECL_THEN
						  [`REVERSE (MAP FST (MAP FST t'')) ++ [q']`,`r'`,`h`] MP_TAC) THEN
			       SRW_TAC [][] THEN
			       Cases_on `t''''''` THEN SRW_TAC [][]
			       ]
			 ]

		   ]]]])




val a1 = store_thm ("a1",
``(auggr g st eof = SOME ag) ==>
  RTC (rderives ag) [NTS (startSym ag)]
  (pfx++[NTS lhs]++s1++s2) ==>
  ~(lhs=startSym ag) ==>
  (HD (s1++s2)=TS eof) ==>
  ((s1=[TS eof]) /\ (s2=[])) \/ ((s2=[TS eof]) /\ (s1=[]))``,
SRW_TAC [] [] THEN
Cases_on `s1` THEN
Cases_on `s2` THEN
FULL_SIMP_TAC (srw_ss()) []
THENL[
      METIS_TAC [APPEND_NIL,lastEof,MEM,MEM_APPEND],

      SRW_TAC [][]THEN
      `MEM (TS eof) (pfx ++ [NTS lhs] ++ TS eof::t)`
	  by SRW_TAC [][] THEN
       `?p.((pfx ++ [NTS lhs] ++ TS eof::t)
           = p++[TS eof]) /\ ~MEM (TS eof) p`
	  by METIS_TAC [auggrStRtcRdEofGen] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `h::t'=FRONT (h::t') ++ [LAST (h::t')]`
      by METIS_TAC [APPEND_FRONT_LAST,NOT_CONS_NIL] THEN
      SRW_TAC [][] THEN
      `LAST (p++[TS eof]) = LAST [TS eof]`
	  by METIS_TAC [last_append,APPEND,NOT_CONS_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `pfx ++ [NTS lhs] ++ TS eof::FRONT (h::t') ++ [LAST (h::t')]
       = p ++ [TS eof]` by METIS_TAC [APPEND_ASSOC,APPEND] THEN
      METIS_TAC [APPEND_11,MEM,MEM_APPEND,lastElemEq],


      SRW_TAC [][]THEN
      `MEM (TS eof) (pfx ++ [NTS lhs] ++ TS eof::t)`
	  by SRW_TAC [][] THEN
      `?p.((pfx ++ [NTS lhs] ++ TS eof::t)
           = p++[TS eof]) /\ ~MEM (TS eof) p`
	  by METIS_TAC [auggrStRtcRdEofGen] THEN
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      `h::t'=FRONT (h::t') ++ [LAST (h::t')]`
      by METIS_TAC [APPEND_FRONT_LAST,NOT_CONS_NIL] THEN
      SRW_TAC [][] THEN
      `LAST (p++[TS eof]) = LAST [TS eof]`
	  by METIS_TAC [last_append,APPEND,NOT_CONS_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `pfx ++ [NTS lhs] ++ TS eof::FRONT (h::t') ++ [LAST (h::t')]
       = p ++ [TS eof]` by METIS_TAC [APPEND_ASSOC,APPEND] THEN
      METIS_TAC [APPEND_11,MEM,MEM_APPEND,lastElemEq],

      SRW_TAC [][]THEN
      `MEM (TS eof) (pfx ++ [NTS lhs] ++ TS eof::t++h'::t')`
	  by SRW_TAC [][] THEN
      `?p.((pfx ++ [NTS lhs] ++ TS eof::t++h'::t')
           = p++[TS eof]) /\ ~MEM (TS eof) p`
	  by METIS_TAC [auggrStRtcRdEofGen] THEN
      `h'::t'=FRONT (h'::t') ++ [LAST (h'::t')]`
      by METIS_TAC [APPEND_FRONT_LAST,NOT_CONS_NIL] THEN
      SRW_TAC [][] THEN
      `LAST (p++[TS eof]) = LAST [TS eof]`
	  by METIS_TAC [last_append,APPEND,NOT_CONS_NIL] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      `pfx ++ [NTS lhs] ++ TS eof::t++FRONT (h'::t') ++ [LAST (h'::t')]
       = p ++ [TS eof]` by METIS_TAC [APPEND_ASSOC,APPEND] THEN
      METIS_TAC [APPEND_11,MEM,MEM_APPEND,lastElemEq]
      ])





val subl1 = store_thm ("subl1",
``takesSteps n (parse (SOME m)) (exitCond (eof,NTS (startSym g)))
             (LAST ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl),[],
              [(NTS st,initItems ag (rules ag))]) (pfx' ++ sfx,stl,csl) ==>
 (stackSyms stl = s1 ++ rhs') ==>
MEM (item lhs (rhs',[])) (itemlist csl) ==>
~(N=startSym ag) ==>
EVERY isTmnlSym (LAST ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl)) ==>
MEM (rule N rhs) (rules ag) ==>
RTC (rderives ag) [NTS (startSym ag)]
             (s1 ++ [NTS lhs] ++ pfx' ++ sfx) ==>
MEM (rule lhs rhs') (rules ag) ==>
(pfx ++ rhs = s1 ++ [NTS lhs] ++ pfx') ==>
(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
(slr ag = SOME m) ==>
 (auggr g st eof = SOME ag) ==>
EVERY isTmnlSym (pfx'++sfx) ==>
rtc2list (rderives ag) ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl) ==>
RTC (rderives ag) [NTS (startSym ag)] (pfx ++ [NTS N] ++ sfx) ==>
?n stl csl.
      takesSteps n (parse (SOME m)) (exitCond (eof,NTS (startSym g)))
        (LAST ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl),[],
         [(NTS st,initItems ag (rules ag))]) (sfx,stl,csl) /\
      (stackSyms stl = s1 ++ [NTS lhs] ++ pfx') /\
      MEM (item N (rhs,[])) (itemlist csl)``,

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [exitCond_def] THEN
SRW_TAC [][] THEN
Cases_on `stl` THEN
FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
Cases_on `lhs=startSym ag`THEN
SRW_TAC [][]
      THENL[

	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `(pfx'++sfx=[])`
		by METIS_TAC [auggrRtcRderivesPfxSfxNil,APPEND_ASSOC,APPEND] THEN
	    FULL_SIMP_TAC (srw_ss()) []THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [lastEof,APPEND_NIL,MEM,MEM_APPEND],


	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `~(pfx'++sfx =[])` by METIS_TAC [MEM,MEM_APPEND,lastEof,APPEND,APPEND_NIL] THEN
	    Cases_on `pfx'++sfx`THEN
	    SRW_TAC [][] THEN
	    `trans ag (initItems ag (rules ag),[])
             = SOME (initItems ag (rules ag))`
		by METIS_TAC [trans_def] THEN
	    `MEM (item lhs ([],[])) (initItems ag (rules ag))`
		by METIS_TAC [initItemsHdNt] THEN
	    `(NTS lhs::h::t) = [] ++ [NTS lhs]++[h]++t`
		by METIS_TAC [APPEND,APPEND_ASSOC] THEN
	    `h IN (followSet ag (NTS lhs))`
		by METIS_TAC [followSetMem, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
	    `(getState m (initItems ag (rules ag)) h = REDUCE (rule lhs []))`
		by METIS_TAC [getStateReduce,parseInvInit,parseInv_def,validStates_def,EVERY_DEF,EVERY_APPEND] THEN
	    `!stl csl s1 s2 lhs rhs st.
              (auggr g st eof = SOME ag) ==>
              (slr ag = SOME m) ==>
	      (stackSyms stl = s1 ++ rhs) ==>
	      parseInv (ag,stl,csl) ==>
	      validItemInv (ag,stl,csl) ==>
	      MEM (item lhs (rhs,[])) (itemlist csl) ==>
	      RTC (rderives ag) [NTS (startSym ag)]
              (s1 ++ [NTS lhs] ++ s2) ==>
	      EVERY isTmnlSym s2 ==>
	      ~(lhs = startSym ag) ==>
	      (csl =
               MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
	      ?stl' csl'.
              takesSteps (SUC 0) (parse (SOME m))
              (exitCond (eof,NTS (startSym g))) (s2,stl,csl)
              (s2,stl',csl') /\
                (stackSyms stl' =
		 stackSyms (pop stl (LENGTH rhs)) ++ [NTS lhs])
		/\ (getState m (itemlist csl) (HD s2) =
		    REDUCE (rule lhs rhs))`
		by METIS_TAC [takesStepsReduce] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN
			       [`[]`,`[(NTS st,initItems ag (rules ag))]`,
				`[]`,`h::t`,`lhs`,`[]`,`startSym ag`] MP_TAC) THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
	    SRW_TAC [] [] THEN
	    `?stl' csl'.
             takesSteps 1 (parse (SOME m))
               (exitCond (eof,NTS (startSym g)))
               (h::t,[],
                [(NTS (startSym ag),initItems ag (rules ag))])
               (h::t,stl',csl') /\
             (stackSyms stl' =
              stackSyms (pop ([]:((symbol#state)#ptree)list) 0) ++ [NTS lhs])`
		by METIS_TAC [parseInvInit,auggr_startSym,EVERY_DEF,EVERY_APPEND,validItemInvInit] THEN
	    FULL_SIMP_TAC (srw_ss()) [pop_def] THEN
	    `!csli stli rhs pfx sfx N onstk ininp.
             (auggr g st eof = SOME ag) ==>
             RTC (rderives ag) [NTS (startSym ag)]
             (pfx ++ [NTS N] ++ sfx) ==>
             (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
             (csli =
              MAP FST stli ++
		  [(NTS st,initItems ag (rules ag))]) ==>
             MEM (rule N rhs) (rules ag) ==>
             (stackSyms stli = pfx ++ onstk) ==>
             ~(N = startSym ag) ==>
             EVERY isTmnlSym (ininp ++ sfx) ==>
             (slr ag = SOME m) ==>
             (rhs = onstk ++ ininp) ==>
             (csli =
              MAP FST stli ++
		  [(NTS st,initItems ag (rules ag))]) ==>
             ~(stli = []) ==>
             (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
             parseInv (ag,stli,csli) ==>
             validItemInv (ag,stli,csli) ==>
             ?i stl csl.
             takesSteps (LENGTH ininp) (parse (SOME m))
             (exitCond (eof,NTS (startSym g)))
             (ininp ++ sfx,stli,csli) (i,stl,csl) /\
             (stackSyms stl = stackSyms stli ++ ininp) /\
              (i = sfx) /\ MEM (item N (rhs,[])) (itemlist csl) /\
              (getState m (itemlist csl) (HD sfx) =
               REDUCE (rule N rhs))`
		by METIS_TAC [lem1Gen] THEN
	    `[(NTS (startSym ag),initItems ag (rules ag))] =
	     MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
		by SRW_TAC [][] THEN
	    `csl'=MAP FST stl'++[(NTS (startSym ag),initItems ag (rules ag))]`
		  by METIS_TAC [takesStepsCslStlEq] THEN
	    `EVERY isTmnlSym (h::t)` by METIS_TAC [EVERY_APPEND] THEN
	    `st=startSym ag` by METIS_TAC [auggr_startSym] THEN
	    SRW_TAC [][] THEN
	    `parseInv (ag,stl',MAP FST stl' ++
              [(NTS (startSym ag),initItems ag (rules ag))])`
		by METIS_TAC [takesStepsParseInv,parseInvInit] THEN
	    `validItemInv (ag,stl',MAP FST stl' ++
              [(NTS (startSym ag),initItems ag (rules ag))])`
		by METIS_TAC [takesStepsValidItemInv,NOT_CONS_NIL,parseInvInit,validItemInvInit] THEN
	    `~(stl'=[])` by (Cases_on `stl'` THEN
			     FULL_SIMP_TAC (srw_ss()) [stackSyms_def]) THEN
	    `pfx ++ rhs = [NTS lhs]++pfx'`
		by SRW_TAC [][] THEN
	    `(pfx = [NTS lhs]) /\ (rhs = pfx') \/
		(?s1' s2'.
		  (pfx = [NTS lhs] ++ s1') /\ (rhs = s2') /\
                  (pfx' = s1' ++ s2')) \/
		?s1 s2.
                  ([NTS lhs] = pfx ++ s1) /\ (pfx' = s2)
		   /\ (rhs = s1 ++ s2)`
	    by METIS_TAC [twoListAppEq]
	    THENL[
		  SRW_TAC [] [] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				 [`MAP FST stl'++[(NTS (startSym ag),initItems ag (rules ag))]`,
				  `stl'`,`pfx'`,`[NTS lhs]`,
				  `sfx`,`N`,`[]`,`pfx'`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  `csl = MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
		      by METIS_TAC [takesStepsCslStlEq] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,itemlist_def] THEN
		  METIS_TAC [takesStepsAdd],

		  SRW_TAC [][] THEN
		  `?stl'' csl''.
		      takesSteps 1 (parse (SOME m))
		      (exitCond (eof,NTS (startSym g)))
		      (h::t,[],
                       [(NTS (startSym ag),initItems ag (rules ag))])
		      (h::t,stl'',csl'') /\
         	      (stackSyms stl''  = [NTS lhs])` by METIS_TAC [takesStepsAdd,EVERY_DEF,parseInvInit,validItemInvInit] THEN
		  SRW_TAC [][] THEN
		  `!csli stli rhs pfx sfx N onstk ininp st.
		      (auggr g st eof = SOME ag) ==>
		      RTC (rderives ag) [NTS (startSym ag)]
		      (pfx ++ [NTS N] ++ sfx) ==>
		      (csli =
		       MAP FST stli ++
			   [(NTS st,initItems ag (rules ag))]) ==>
		      MEM (rule N rhs) (rules ag) ==>
		      ~(N = startSym ag) ==>
		      EVERY isTmnlSym (ininp ++ rhs ++ sfx) ==>
		      (slr ag = SOME m) ==>
		      (pfx = onstk ++ ininp) ==>
		      (stackSyms stli = onstk) ==>
		      (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
		      (LENGTH csli = LENGTH stli + 1) ==>
		      parseInv (ag,stli,csli) ==>
		      validItemInv (ag,stli,csli) ==>
		      ?i stl csl.
		      takesSteps (LENGTH ininp) (parse (SOME m))
		      (exitCond (eof,NTS (startSym g)))
		      (ininp ++ rhs ++ sfx,stli,csli) (i,stl,csl) /\
          	       (stackSyms stl = pfx) /\ (i = rhs ++ sfx)
                       /\ MEM (item N ([],rhs)) (itemlist csl)`
		      by METIS_TAC [lem2Gen] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				 [`csl''`,`stl''`,`rhs`,`[NTS lhs]++s1'`,`sfx`,
				  `N`,`[NTS lhs]`,`s1'`,`startSym ag`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  `[(NTS (startSym ag),initItems ag (rules ag))] = MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
		      by SRW_TAC [][] THEN
		  `parseInv (ag,stl'',csl'')` by METIS_TAC [takesStepsParseInv,parseInvInit,EVERY_DEF] THEN
		  `validItemInv (ag,stl'',csl'')`
		      by METIS_TAC [validItemInvInit,NOT_CONS_NIL,EVERY_DEF,takesStepsValidItemInv,parseInvInit,takesStepsCslStlEq] THEN
		  `csl''=MAP FST stl''++[(NTS (startSym ag),initItems ag (rules ag))]`
		      by METIS_TAC [takesStepsCslStlEq] THEN
		  SRW_TAC [][] THEN
		  `?stl csl'.
		   takesSteps (LENGTH s1') (parse (SOME m))
		   (exitCond (eof,NTS (startSym g)))
		   (h::t,stl'',
                    MAP FST stl'' ++
			[(NTS (startSym ag),initItems ag (rules ag))])
		   (rhs ++ sfx,stl,csl') /\
                    (stackSyms stl = NTS lhs::s1') /\
                   MEM (item N ([],rhs)) (itemlist csl')`
		      by METIS_TAC [] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				 [`MAP FST stl ++ [(NTS (startSym ag),initItems ag (rules ag))]`,
				  `stl`,`rhs`,`[NTS lhs]++s1'`,`sfx`,
				  `N`,`[]`,`rhs`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  `~(stl=[])` by (Cases_on `stl` THEN
				  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND]) THEN
		  `[(NTS (startSym ag),initItems ag (rules ag))] = MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
		      by SRW_TAC [][] THEN
		  `(csl' =
		    MAP FST stl ++
			[(NTS (startSym ag),initItems ag (rules ag))])` by METIS_TAC [takesStepsCslStlEq] THEN
		  SRW_TAC [][] THEN
		  `parseInv
		   (ag,stl,
		    MAP FST stl ++
			[(NTS (startSym ag),initItems ag (rules ag))])`
		      by METIS_TAC [takesStepsParseInv,EVERY_APPEND] THEN
		  `validItemInv
		   (ag,stl,
		    MAP FST stl ++
			[(NTS (startSym ag),initItems ag (rules ag))])`
		      by METIS_TAC [NOT_CONS_NIL,EVERY_DEF,takesStepsValidItemInv,parseInvInit,takesStepsCslStlEq] THEN
		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  `?stl''' csl''.
		   takesSteps (LENGTH rhs) (parse (SOME m))
		   (exitCond (eof,NTS (startSym g)))
		   (rhs ++ sfx,stl,
                    MAP FST stl ++
			[(NTS (startSym ag),initItems ag (rules ag))])
		   (sfx,stl''',csl'') /\
                    (stackSyms stl''' = NTS lhs::(s1' ++ rhs)) /\
                     MEM (item N (rhs,[])) (SND (HD csl'')) /\
                    (getState m (SND (HD csl'')) (HD sfx) =
                     REDUCE (rule N rhs))`
		      by METIS_TAC [EVERY_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  `[(NTS (startSym ag),initItems ag (rules ag))] =
            	    MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
		      by SRW_TAC [][] THEN
		  `csl=MAP FST ([]:(((symbol#state)#ptree)list))++[(NTS (startSym ag),initItems ag (rules ag))]`
		      by METIS_TAC [takesStepsCslStlEq] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  SRW_TAC [][] THEN
		  `takesSteps (n+1) (parse (SOME m))
			   (exitCond (eof,NTS (startSym g)))
			   (LAST ((h::t)::dtl),[],
			    [(NTS (startSym ag),initItems ag (rules ag))])
			   (h::t,stl'',
			    MAP FST stl'' ++
				[(NTS (startSym ag),initItems ag (rules ag))])`
		      by METIS_TAC [takesStepsAdd] THEN
		  METIS_TAC [takesStepsAdd],

		  SRW_TAC [][] THEN
		  Cases_on `pfx` THEN
		  Cases_on `s1` THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) []
		  THENL[
			SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			FIRST_X_ASSUM (Q.SPECL_THEN
					   [`stl'`,`[]`,
					    `sfx`,`N`,`[NTS lhs]`,`pfx'`]
					   MP_TAC) THEN
			SRW_TAC [][] THEN
			`[(NTS (startSym ag),initItems ag (rules ag))] =
                    	  MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
			    by SRW_TAC [][] THEN
			`csl = MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
			    by METIS_TAC [takesStepsCslStlEq] THEN
			FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,itemlist_def] THEN
			METIS_TAC [takesStepsAdd],


			SRW_TAC [][] THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			`NTS lhs::NTS N::sfx = [NTS lhs]++[NTS N]++sfx`
			    by METIS_TAC [APPEND,APPEND_ASSOC] THEN
			`?itl.trans ag (initItems ag (rules ag),[NTS lhs]) = SOME itl`
			by METIS_TAC [rtcRdImpTrans] THEN
			Cases_on `pfx'` THEN
			SRW_TAC [] []
                        THENL[
			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      FIRST_X_ASSUM (Q.SPECL_THEN
						 [`stl'`,`[NTS lhs]`,
						  `h::t`,`N`,`[]`,`[]`]
						 MP_TAC) THEN
			      SRW_TAC [][] THEN
			      `[(NTS (startSym ag),initItems ag (rules ag))] =
                        	MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
				  by SRW_TAC [][] THEN
			      `csl = MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
				  by METIS_TAC [takesStepsCslStlEq] THEN
			      FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,itemlist_def] THEN
			      METIS_TAC [takesStepsAdd],


			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      SRW_TAC [][] THEN
			      `validItem ag [NTS lhs] (item N ([],h::t'))`
			      by (SRW_TAC [] [validItem_def] THEN
				  Q.EXISTS_TAC `sfx` THEN
				  FULL_SIMP_TAC (srw_ss()) [] THEN
				  `rderives ag ([NTS lhs] ++ [NTS N]++sfx) ([NTS lhs]++(h::t')++sfx)`
				      by METIS_TAC [rdres1,rderives_append] THEN
				  METIS_TAC [APPEND,APPEND_ASSOC]) THEN
			      `MEM (item N ([],h::t')) itl`
			      by METIS_TAC [transImpValidItem] THEN
			      `?itl'.trans ag (itl,h::t') = SOME itl'`
				  by METIS_TAC [ruleRhsExistsImpTrans] THEN
			      `trans ag (initItems ag (rules ag),[NTS lhs]++h::t') =
				SOME itl'` by METIS_TAC [transSeq,initItems_def] THEN
			      `?stl'' csl''.
				     takesSteps 1 (parse (SOME m))
				     (exitCond (eof,NTS (startSym g)))
				     (h::(t' ++ sfx),[],
				      [(NTS (startSym ag),initItems ag (rules ag))])
                                      (h::(t' ++ sfx),stl'',csl'') /\
                                      (stackSyms stl'' = [NTS lhs])`
				  by METIS_TAC [parseInvInit,validItemInvInit,EVERY_APPEND] THEN
			      FIRST_X_ASSUM (Q.SPECL_THEN
						 [`stl''`,`[NTS lhs]`,
						  `sfx`,`N`,`[]`,`h::t'`]
						 MP_TAC) THEN
			      SRW_TAC [][] THEN
			      `~(stl''=[])` by (Cases_on `stl''` THEN FULL_SIMP_TAC (srw_ss()) [stackSyms_def]) THEN
			      `[(NTS (startSym ag),initItems ag (rules ag))] =
                    		MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
				  by SRW_TAC [][] THEN
			      `csl = MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
				  by METIS_TAC [takesStepsCslStlEq] THEN
			      `parseInv (ag,stl'',csl'')` by METIS_TAC [takesStepsParseInv,parseInvInit,EVERY_DEF] THEN
			      `validItemInv (ag,stl'',csl'')`
				  by METIS_TAC [validItemInvInit,NOT_CONS_NIL,EVERY_DEF,takesStepsValidItemInv,parseInvInit,takesStepsCslStlEq] THEN
			      `csl''=MAP FST stl''++[(NTS (startSym ag),initItems ag (rules ag))]`
				  by METIS_TAC [takesStepsCslStlEq] THEN
			      SRW_TAC [][] THEN
			      `?stl csl'.
					 takesSteps (SUC (LENGTH t')) (parse (SOME m))
					 (exitCond (eof,NTS (startSym g)))
					 (h::(t' ++ sfx),stl'',
					  MAP FST stl'' ++
					      [(NTS (startSym ag),initItems ag (rules ag))])
					 (sfx,stl,csl') /\
                                         (stackSyms stl = NTS lhs::h::t') /\
                                         MEM (item N (h::t',[])) (itemlist csl') /\
                                       (getState m (itemlist csl') (HD sfx) =
                                       REDUCE (rule N (h::t')))`
				  by METIS_TAC [] THEN
			      FULL_SIMP_TAC (srw_ss()) [] THEN
			      `takesSteps (n+1) (parse (SOME m))
					 (exitCond (eof,NTS (startSym g)))
					 (LAST ((h::(t'++sfx))::dtl),[],
					  [(NTS (startSym ag),initItems ag (rules ag))])
					 (h::(t'++sfx),stl'',
					  MAP FST stl'' ++
					      [(NTS (startSym ag),initItems ag (rules ag))])`
				  by METIS_TAC [takesStepsAdd] THEN
			      FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,itemlist_def] THEN
			      METIS_TAC [takesStepsAdd]
			      ]
			]
		  ],

	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `(pfx'++sfx=[])`
		by METIS_TAC [auggrRtcRderivesPfxSfxNil,APPEND_ASSOC,APPEND] THEN
	    FULL_SIMP_TAC (srw_ss()) []THEN
	    SRW_TAC [][] THEN
	    METIS_TAC [lastEof,APPEND_NIL,MEM,MEM_APPEND],


	    (*~stl=[]*)
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `~(pfx'++sfx =[])` by METIS_TAC [MEM,MEM_APPEND,lastEof,APPEND,APPEND_NIL] THEN
	    Cases_on `pfx'++sfx`THEN
	    SRW_TAC [][] THEN
	    `RTC (rderives ag) [NTS (startSym ag)]
	     (s1 ++ [NTS lhs] ++ [h'] ++ t')`
		by METIS_TAC [APPEND,APPEND_ASSOC] THEN
	    `h' IN (followSet ag (NTS lhs))`
		by METIS_TAC [followSetMem, rtcRdImpDg, isTmnlSym_def,EVERY_DEF,EVERY_APPEND] THEN
	    `st=startSym ag` by METIS_TAC [auggr_startSym] THEN
	    SRW_TAC [] [] THEN
	    `[(NTS (startSym ag),initItems ag (rules ag))] =
	     MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
		by SRW_TAC [][] THEN
	    `csl=MAP FST (h::t)++[(NTS (startSym ag),initItems ag (rules ag))]`
		  by METIS_TAC [takesStepsCslStlEq] THEN
	    `EVERY isTmnlSym (h'::t')` by METIS_TAC [EVERY_APPEND] THEN
	    `parseInv (ag,h::t,MAP FST (h::t) ++
              [(NTS (startSym ag),initItems ag (rules ag))])`
		by METIS_TAC [takesStepsParseInv,parseInvInit] THEN
	    Cases_on `~(LAST ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl)=[])`
            THENL[
		  `validItemInv (ag,h::t,MAP FST (h::t) ++
					     [(NTS (startSym ag),initItems ag (rules ag))])`
		      by METIS_TAC [takesStepsValidItemInv,NOT_CONS_NIL,parseInvInit,validItemInvInit,EVERY_DEF,EVERY_APPEND,takesStepsTmnlSyms] THEN
		  `(trans ag
			  (initItems ag (rules ag),
			   stackSyms (REVERSE (REVERSE (h::t)))) =
			  SOME (stkItl (REVERSE (REVERSE (h::t)))))`
		      by METIS_TAC [rev_nil,nullNil,NOT_CONS_NIL,IS_PREFIX_REFL,validItemInv_def] THEN
		  Cases_on `h` THEN Cases_on `q` THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,stkItl_def,REVERSE_APPEND,itemlist_def] THEN
		  `validItem ag (REVERSE (MAP FST (MAP FST t)) ++ [q']) (item lhs (rhs',[]))`
		      by (SRW_TAC [] [validItem_def] THEN
			  Q.EXISTS_TAC `pfx'++sfx` THEN
			  SRW_TAC [][] THEN
			  METIS_TAC [rdres1,EVERY_APPEND,rderives_append,APPEND_ASSOC]) THEN
		  `MEM (item lhs (rhs',[])) r'`
		      by METIS_TAC [transImpValidItem] THEN
	    `(getState m r' h' = REDUCE (rule lhs rhs'))`
		by METIS_TAC [getStateReduce,parseInvInit,parseInv_def,validStates_def,EVERY_DEF,EVERY_APPEND] THEN
	    `!stl csl s1 s2 lhs rhs st.
              (auggr g st eof = SOME ag) ==>
              (slr ag = SOME m) ==>
	      (stackSyms stl = s1 ++ rhs) ==>
	      parseInv (ag,stl,csl) ==>
	      validItemInv (ag,stl,csl) ==>
	      MEM (item lhs (rhs,[])) (itemlist csl) ==>
	      RTC (rderives ag) [NTS (startSym ag)]
              (s1 ++ [NTS lhs] ++ s2) ==>
	      EVERY isTmnlSym s2 ==>
	      ~(lhs = startSym ag) ==>
	      (csl =
               MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
	      ?stl' csl'.
              takesSteps (SUC 0) (parse (SOME m))
              (exitCond (eof,NTS (startSym g))) (s2,stl,csl)
              (s2,stl',csl') /\
                (stackSyms stl' =
		 stackSyms (pop stl (LENGTH rhs)) ++ [NTS lhs])
		/\ (getState m (itemlist csl) (HD s2) =
		    REDUCE (rule lhs rhs))`
		by METIS_TAC [takesStepsReduce] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN
			       [`((q',r'),r)::t`,`(q',r')::
			   (MAP FST t ++
				[(NTS (startSym ag),
				  initItems ag (rules ag))])`,
			   `s1`,`pfx'++sfx`,
			   `lhs`,`rhs'`,`startSym ag`] MP_TAC) THEN
	    FULL_SIMP_TAC (srw_ss()) [itemlist_def,stackSyms_def,REVERSE_APPEND] THEN
	    SRW_TAC [] [] THEN
	    `?stl' csl'.
             takesSteps 1 (parse (SOME m))
               (exitCond (eof,NTS (startSym g)))
               (h'::t',((q',r'),r)::t,
                (q',r')::
                    (MAP FST t ++
                     [(NTS (startSym ag),
                       initItems ag (rules ag))]))
               (h'::t',stl',csl') /\
             (REVERSE (MAP FST (MAP FST stl')) =
              REVERSE
                (MAP FST
                   (MAP FST
                      (pop (((q',r'),r)::t) (LENGTH rhs')))) ++
		[NTS lhs])` by METIS_TAC [] THEN
	    `!csli stli rhs pfx sfx N onstk ininp st.
             (auggr g st eof = SOME ag) ==>
             RTC (rderives ag) [NTS (startSym ag)]
             (pfx ++ [NTS N] ++ sfx) ==>
             (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
             (csli =
              MAP FST stli ++
		  [(NTS st,initItems ag (rules ag))]) ==>
             MEM (rule N rhs) (rules ag) ==>
             (stackSyms stli = pfx ++ onstk) ==>
             ~(N = startSym ag) ==>
             EVERY isTmnlSym (ininp ++ sfx) ==>
             (slr ag = SOME m) ==>
             (rhs = onstk ++ ininp) ==>
             (csli =
              MAP FST stli ++
		  [(NTS st,initItems ag (rules ag))]) ==>
             ~(stli = []) ==>
             (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
             parseInv (ag,stli,csli) ==>
             validItemInv (ag,stli,csli) ==>
             ?i stl csl.
             takesSteps (LENGTH ininp) (parse (SOME m))
             (exitCond (eof,NTS (startSym g)))
             (ininp ++ sfx,stli,csli) (i,stl,csl) /\
             (stackSyms stl = stackSyms stli ++ ininp) /\
              (i = sfx) /\ MEM (item N (rhs,[])) (itemlist csl) /\
              (getState m (itemlist csl) (HD sfx) =
               REDUCE (rule N rhs))`
		by METIS_TAC [lem1Gen] THEN
	    `[(NTS (startSym ag),initItems ag (rules ag))] =
	     MAP FST ([]:(((symbol#state)#ptree)list)) ++ [(NTS (startSym ag),initItems ag (rules ag))]`
		by SRW_TAC [][] THEN
	    `csl'=MAP FST stl'++[(NTS (startSym ag),initItems ag (rules ag))]`
		  by METIS_TAC [takesStepsCslStlEq] THEN
	    `EVERY isTmnlSym (h'::t')` by METIS_TAC [EVERY_APPEND] THEN
	    SRW_TAC [][] THEN
	    `MAP FST (((q',r'),r)::t) ++
		      [(NTS (startSym ag),initItems ag (rules ag))]
		      =
		      (q',r')::
		      (MAP FST t ++
			   [(NTS (startSym ag),
			     initItems ag (rules ag))])`
		by METIS_TAC [MAP,FST,APPEND_ASSOC,APPEND] THEN
	    `parseInv (ag,stl',MAP FST stl' ++
              [(NTS (startSym ag),initItems ag (rules ag))])`
		by METIS_TAC [takesStepsParseInv,parseInvInit,
			      EVERY_DEF,EVERY_APPEND,
			      takesStepsTmnlSyms] THEN
	    `validItemInv (ag,stl',MAP FST stl' ++
              [(NTS (startSym ag),initItems ag (rules ag))])`
		by METIS_TAC [takesStepsValidItemInv,NOT_CONS_NIL,
			      parseInvInit,validItemInvInit,
			      takesStepsTmnlSyms,takesStepsSlNotNil] THEN
	    `~(stl'=[])` by (Cases_on `stl'` THEN
			     FULL_SIMP_TAC (srw_ss()) [stackSyms_def]) THEN
	    `(s1 = pfx) \/
		  (?p s.
		    (pfx = s1 ++ [NTS lhs] ++ p)
		    /\ (pfx' = p ++ s)) \/
		  ?p s. (s1 = p ++ s) /\ (pfx = p)`
		by METIS_TAC [listCompLens] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) []
            THENL[
		  `rhs=[NTS lhs]++pfx'`
		      by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
		  SRW_TAC [][] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				 [`stl'`,`pfx`,
				  `sfx`,`N`,`[NTS lhs]`,`pfx'`,`startSym ag`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  `stackSyms (((q',r'),r)::t) = pfx++rhs'`
		      by FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  `stackSyms (pop (((q',r'),r)::t) (LENGTH rhs')) = pfx`
		      by METIS_TAC [stackSymsPop] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  METIS_TAC [takesStepsAdd],

		  SRW_TAC [][] THEN
		  `!csli stli rhs pfx sfx N onstk ininp st.
		      (auggr g st eof = SOME ag) ==>
		      RTC (rderives ag) [NTS (startSym ag)]
		      (pfx ++ [NTS N] ++ sfx) ==>
		      (csli =
		       MAP FST stli ++
			   [(NTS st,initItems ag (rules ag))]) ==>
		      MEM (rule N rhs) (rules ag) ==>
		      ~(N = startSym ag) ==>
		      EVERY isTmnlSym (ininp ++ rhs ++ sfx) ==>
		      (slr ag = SOME m) ==>
		      (pfx = onstk ++ ininp) ==>
		      (stackSyms stli = onstk) ==>
		      (!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
		      (LENGTH csli = LENGTH stli + 1) ==>
		      parseInv (ag,stli,csli) ==>
		      validItemInv (ag,stli,csli) ==>
		      ?i stl csl.
		      takesSteps (LENGTH ininp) (parse (SOME m))
		      (exitCond (eof,NTS (startSym g)))
		      (ininp ++ rhs ++ sfx,stli,csli) (i,stl,csl) /\
          	       (stackSyms stl = pfx) /\ (i = rhs ++ sfx)
                       /\ MEM (item N ([],rhs)) (itemlist csl)`
		      by METIS_TAC [lem2Gen] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				 [`MAP FST stl'++[(NTS (startSym ag),initItems ag (rules ag))]`,
				  `stl'`,`rhs`,`s1++[NTS lhs]++p`,`sfx`,
				  `N`,`s1++[NTS lhs]`,`p`,`startSym ag`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  `stackSyms (((q',r'),r)::t) = s1++rhs'`
		      by FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  `stackSyms (pop (((q',r'),r)::t) (LENGTH rhs')) = s1`
		      by METIS_TAC [stackSymsPop] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  `?stl csl.
                     takesSteps (LENGTH p) (parse (SOME m))
		     (exitCond (eof,NTS (startSym g)))
		     (h'::t',stl',
                      MAP FST stl' ++
			  [(NTS (startSym ag),initItems ag (rules ag))])
		     (rhs ++ sfx,stl,csl) /\
                     (REVERSE (MAP FST (MAP FST stl)) =
		      s1 ++ [NTS lhs] ++ p) /\
                      MEM (item N ([],rhs)) (SND (HD csl))`
		      by METIS_TAC [] THEN
		  `parseInv (ag,stl,csl)` by METIS_TAC [takesStepsParseInv,parseInvInit,EVERY_DEF] THEN
		  `validItemInv (ag,stl,csl)`
		      by METIS_TAC [validItemInvInit,NOT_CONS_NIL,EVERY_DEF,takesStepsValidItemInv,parseInvInit,takesStepsCslStlEq] THEN
		  `csl=MAP FST stl++[(NTS (startSym ag),initItems ag (rules ag))]`
		      by METIS_TAC [takesStepsCslStlEq] THEN
		  SRW_TAC [][] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				 [`stl`,`(REVERSE(MAP FST(MAP FST
                                  (pop (((q',r'),r)::t) (LENGTH rhs'))))) ++
						 [NTS lhs] ++ p`,`sfx`,
				 `N`,`[]`,`rhs`,`startSym ag`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  `~(stl=[])` by (Cases_on `stl` THEN
				  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND]) THEN
		  `?stl''' csl.
			   takesSteps (LENGTH rhs) (parse (SOME m))
			   (exitCond (eof,NTS (startSym g)))
			   (rhs ++ sfx,stl,
			    MAP FST stl ++
				[(NTS (startSym ag),initItems ag (rules ag))])
			   (sfx,stl''',csl) /\
                           (REVERSE (MAP FST (MAP FST stl''')) =
			    REVERSE
				(MAP FST
				     (MAP FST
                                 (pop (((q',r'),r)::t) (LENGTH rhs')))) ++
				[NTS lhs] ++ p ++ rhs) /\
                             MEM (item N (rhs,[])) (SND (HD csl)) /\
                           (getState m (SND (HD csl)) (HD sfx) =
			    REDUCE (rule N rhs))`
		      by METIS_TAC [] THEN
		  `MAP FST (((q',r'),r)::t) ++
		      [(NTS (startSym ag),initItems ag (rules ag))]
		      =
		      (q',r')::
		      (MAP FST t ++
			   [(NTS (startSym ag),
			     initItems ag (rules ag))])`
		      by METIS_TAC [MAP,FST,APPEND_ASSOC,APPEND] THEN
		  METIS_TAC [takesStepsAdd],


		  SRW_TAC [][] THEN
		  `rhs=s++[NTS lhs]++pfx'`
		      by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
		  SRW_TAC [][] THEN
		  `MAP FST (((q',r'),r)::t) ++
		      [(NTS (startSym ag),initItems ag (rules ag))]
		      =
		      (q',r')::
		      (MAP FST t ++
			   [(NTS (startSym ag),
			     initItems ag (rules ag))])`
		      by METIS_TAC [MAP,FST,APPEND_ASSOC,APPEND] THEN
		  `!stl csl s1 lhs rhs s2 st.
                    (auggr g st eof = SOME ag) ==>
		    (slr ag = SOME m) ==>
		    (stackSyms stl = s1 ++ rhs) ==>
		    parseInv (ag,stl,csl) ==>
		    validItemInv (ag,stl,csl) ==>
		    MEM (item lhs (rhs,[])) (itemlist csl) ==>
		    RTC (rderives ag) [NTS (startSym ag)]
		    (s1 ++ [NTS lhs] ++ s2) ==>
		    EVERY isTmnlSym s2 ==>
		    ~(lhs = startSym ag) ==>
		    (csl =
		     MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
		    ?stl' csl'.
		    takesSteps (SUC 0) (parse (SOME m))
		    (exitCond (eof,NTS (startSym g))) (s2,stl,csl)
		    (s2,stl',csl') /\
                     (stackSyms stl' =
		      stackSyms (pop stl (LENGTH rhs)) ++ [NTS lhs]) /\
                      (getState m (itemlist csl) (HD s2) =
		       REDUCE (rule lhs rhs))`
		      by METIS_TAC [takesStepsReduce] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				     [`(((q',r'),r)::t)`,`(q',r')::
				        (MAP FST t ++
				        [(NTS (startSym ag),initItems ag (rules ag))])`,
				      `p++s`,`lhs`,`rhs'`,`pfx'++sfx`,`startSym ag`]
				     MP_TAC) THEN
		  SRW_TAC [][] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND,itemlist_def] THEN
		  `?stl'' csl'.
		      takesSteps 1 (parse (SOME m))
		      (exitCond (eof,NTS (startSym g)))
		      (h'::t',((q',r'),r)::t,
                       (q',r')::
                       (MAP FST t ++
			 [(NTS (startSym ag),
			   initItems ag (rules ag))]))
		      (h'::t',stl'',csl') /\
                      (REVERSE (MAP FST (MAP FST stl'')) =
		       REVERSE
			   (MAP FST
				(MAP FST
                      (pop (((q',r'),r)::t) (LENGTH rhs')))) ++
			   [NTS lhs]) /\
                       (getState m r' h' = REDUCE (rule lhs rhs'))`
		      by METIS_TAC [] THEN
		  `MAP FST (((q',r'),r)::t) ++
		      [(NTS (startSym ag),initItems ag (rules ag))]
		      =
		      (q',r')::
		      (MAP FST t ++
			   [(NTS (startSym ag),
			     initItems ag (rules ag))])`
		      by METIS_TAC [MAP,FST,APPEND_ASSOC,APPEND] THEN
		  `parseInv (ag,stl''',csl')` by METIS_TAC [takesStepsParseInv,parseInvInit,EVERY_DEF] THEN
		  `validItemInv (ag,stl''',csl')`
		      by METIS_TAC [validItemInvInit,NOT_CONS_NIL,EVERY_DEF,takesStepsValidItemInv,parseInvInit,takesStepsCslStlEq] THEN
		  `csl'=MAP FST stl'''++[(NTS (startSym ag),initItems ag (rules ag))]`
		      by METIS_TAC [takesStepsCslStlEq] THEN
		  SRW_TAC [][] THEN
		  FIRST_X_ASSUM (Q.SPECL_THEN
				 [`stl'''`,`p`,
				  `sfx`,
				  `N`,`s++[NTS lhs]`,`pfx'`,
				  `startSym ag`] MP_TAC) THEN
		  SRW_TAC [][] THEN
		  `stackSyms (((q',r'),r)::t) = p++s++rhs'`
		      by FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  `stackSyms (pop (((q',r'),r)::t) (LENGTH rhs')) = p++s`
		      by METIS_TAC [stackSymsPop] THEN
		  FULL_SIMP_TAC (srw_ss()) [stackSyms_def,REVERSE_APPEND] THEN
		  FULL_SIMP_TAC (srw_ss()) [itemlist_def] THEN
		  `~(stl'''=[])` by (Cases_on `stl'''` THEN FULL_SIMP_TAC (srw_ss()) []) THEN
		  METIS_TAC [takesStepsAdd]
		  ],

		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  `RTC (rderives ag) [NTS (startSym ag)]
                        (s1 ++ rhs' ++ pfx' ++ sfx)`
		  by METIS_TAC [RTC_RULES_RIGHT1,rderives_append,
				rdres1,APPEND_ASSOC,EVERY_APPEND] THEN
		  `RTC (rderives ag)
			(HD ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl))
			(LAST ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl))`
		      by METIS_TAC [rtc2listRtcRdHdLast,NOT_CONS_NIL] THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  METIS_TAC [RTC_RTC,auggrStRtcRderivesNotNil]
		  ]])





val rtc2listTakesStepsSfx = store_thm
("rtc2listTakesStepsSfx",
``!e dtl pfx N rhs sfx.
(auggr g st eof = SOME ag) ==>
(pfx ++ rhs ++ sfx = e) ==>
rtc2list (rderives ag) (e :: dtl) ==>
EVERY isTmnlSym (LAST ((pfx ++ rhs ++ sfx) :: dtl)) ==>
~(N=startSym ag) ==>
MEM (rule N rhs) (rules ag) ==>
 (rsf ag (pfx ++ [NTS N] ++ sfx)) ==>
EVERY isTmnlSym sfx ==>
(slr ag = SOME m) ==>
(!nt.nt IN (nonTerminals ag) ==> gaw ag nt) ==>
?n i stl csl.
   takesSteps n (parse (SOME m))
                (exitCond (eof,(NTS (startSym g))))
                (LAST ((pfx ++ rhs ++ sfx)::dtl),[],
		 [(NTS st,initItems ag (rules ag))])
		(i,stl,csl) /\
   (stackSyms stl = pfx ++ rhs) /\
MEM (item N (rhs, [])) (itemlist csl) /\ (i=sfx)``,

Induct_on `dtl` THEN SRW_TAC [] [] THEN
FULL_SIMP_TAC (srw_ss()) [rsf_def, rtc2list_def]  THEN
SRW_TAC [] []
THENL[

      METIS_TAC [takesStepsBase, EVERY_APPEND],


      (* Induction case *)

      FULL_SIMP_TAC (srw_ss()) [rderives_def] THEN
      SRW_TAC [] [] THEN

      `(s1 = pfx++rhs) \/
        (?pfx' sfx'. (pfx++rhs = s1 ++ [NTS lhs] ++ pfx') /\ (s2 = pfx' ++ sfx')) \/
         ?pfx' sfx'. (s1 = pfx' ++ sfx') /\ (pfx++rhs = pfx')`
	  by METIS_TAC [listCompLens,APPEND_ASSOC]
	  THENL[


		`sfx=[NTS lhs]++s2` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
		SRW_TAC [] [] THEN
		FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],


		SRW_TAC [] [] THEN
		`(sfx'=sfx)` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
		SRW_TAC [] [] THEN
		`RTC (rderives ag) [NTS (startSym ag)] (pfx ++ rhs ++ sfx)`
		    by METIS_TAC [rdres1,rderives_append,RTC_RULES_RIGHT1] THEN
		FIRST_X_ASSUM (Q.SPECL_THEN [`s1`,`lhs`,`rhs'`,`pfx'++sfx`]
					    MP_TAC) THEN
		ASM_SIMP_TAC (srw_ss()) [] THEN
		Q.PAT_ASSUM `XX = YY` (ASSUME_TAC o SYM) THEN
		ASM_SIMP_TAC (srw_ss()) [] THEN
		STRIP_TAC THEN
		FULL_SIMP_TAC (srw_ss()) [] THEN
		Cases_on `lhs=startSym ag` THEN
		SRW_TAC [][]
	        THENL[

		      `RTC (rderives ag) [NTS (startSym ag)] (s1 ++ [NTS (startSym ag)] ++ pfx' ++ sfx)`
			  by METIS_TAC [] THEN
		      `(s1=[]) /\ (pfx'++sfx=[])` by METIS_TAC [auggrRtcRderivesPfxSfxNil,APPEND_ASSOC] THEN
		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      SRW_TAC [][]  THEN
		      METIS_TAC [APPEND_NIL,lastEof,MEM,MEM_APPEND],


		      FULL_SIMP_TAC (srw_ss()) [] THEN
		      `!n s1 rhs' pfx' sfx dtl stl csl lhs N.
			takesSteps n (parse (SOME m))
			(exitCond (eof,NTS (startSym g)))
			(LAST ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl),[],
			 [(NTS st,initItems ag (rules ag))])
			(pfx' ++ sfx,stl,csl) ==>
			(stackSyms stl = s1 ++ rhs') ==>
			MEM (item lhs (rhs',[])) (itemlist csl) ==>
			~(N = startSym ag) ==>
			EVERY isTmnlSym
			(LAST ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl)) ==>
			MEM (rule N rhs) (rules ag) ==>
			RTC (rderives ag) [NTS (startSym ag)]
			(s1 ++ [NTS lhs] ++ pfx' ++ sfx) ==>
			MEM (rule lhs rhs') (rules ag) ==>
			(pfx ++ rhs = s1 ++ [NTS lhs] ++ pfx') ==>
			(!nt. nt IN nonTerminals ag ==> gaw ag nt) ==>
			(slr ag = SOME m) ==>
			(auggr g st eof = SOME ag) ==>
			EVERY isTmnlSym (pfx' ++ sfx) ==>
			rtc2list (rderives ag)
			((s1 ++ rhs' ++ pfx' ++ sfx)::dtl) ==>
			RTC (rderives ag) [NTS (startSym ag)]
			(pfx ++ [NTS N] ++ sfx) ==>
			?n stl csl.
			takesSteps n (parse (SOME m))
			(exitCond (eof,NTS (startSym g)))
			(LAST ((s1 ++ rhs' ++ pfx' ++ sfx)::dtl),[],
			 [(NTS st,initItems ag (rules ag))]) (sfx,stl,csl)
                         /\ (stackSyms stl = s1 ++ [NTS lhs] ++ pfx')
			 /\ MEM (item N (rhs,[])) (itemlist csl)` by METIS_TAC [subl1] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN
			       [`n`,`s1`,`rhs'`,`pfx'`,`sfx`,`dtl`,`stl`,`csl`,`lhs`,`N`] MP_TAC) THEN
	    SRW_TAC [][]
	    ],

		SRW_TAC [][] THEN
		`sfx'++[NTS lhs]++s2=sfx` by METIS_TAC [APPEND_11,APPEND_ASSOC] THEN
		SRW_TAC [][] THEN
		FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def]
      ]])





val treeExists = store_thm ("treeExists",
``(auggr g st eof = SOME ag) ==>
sl IN language ag ==>
(slr ag = SOME m) ==>
(!nt.nt IN (nonTerminals ag) ==> gaw ag nt) ==>
(initState = (NTS st,initItems ag (rules ag))) ==>
?tree.(parser ag (SOME m) sl [] [initState]
          (TS eof) (NTS (startSym g)) = SOME (SOME tree))``,

SRW_TAC [][] THEN
`((rderives ag [NTS (startSym ag)] [NTS (startSym g);TS eof])
/\ ?dtl.
          rtc2list (rderives ag) (([NTS (startSym g);TS eof]) :: dtl)
	  /\ ((LAST (([NTS (startSym g);TS eof])::dtl)) = sl) /\
          MEM (rule (startSym ag) [NTS (startSym g);TS eof])
	  (rules ag))`
    by METIS_TAC [lang2rtc2list] THEN
FULL_SIMP_TAC (srw_ss()) [language_def,EXTENSION] THEN
`~(startSym g = startSym ag)` by METIS_TAC [auggrStNeqOSt] THEN
`rsf ag [NTS (startSym g); TS eof]`
    by (SRW_TAC [][rsf_def] THEN
	METIS_TAC [RTC_RULES]) THEN
`[NTS (startSym g); TS eof]=
		 []++[NTS (startSym g)]++[TS eof]`
    by METIS_TAC [APPEND_NIL,APPEND] THEN
IMP_RES_TAC rtc2listTakesStepsSfx THEN
Cases_on `dtl`
THENL[
      FULL_SIMP_TAC (srw_ss()) [language_def,EXTENSION] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def],


      (*~[]*)
      FULL_SIMP_TAC (srw_ss()) [rtc2list_def,rderives_def,lreseq] THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN
      Cases_on `s1` THEN
      SRW_TAC [][] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][]
      THENL[
	    FIRST_X_ASSUM (Q.SPECL_THEN [`[TS eof]`,`rhs`,`
					[]`,`t`] MP_TAC) THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`startSym g`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
	    `!s1 rhs lhs s2 stl csl.
              (auggr g st eof = SOME ag) ==>
	      (slr ag = SOME m) ==>
	      (stackSyms stl = s1 ++ rhs) ==>
	      parseInv (ag,stl,csl) ==>
	      validItemInv (ag,stl,csl) ==>
	      MEM (item lhs (rhs,[])) (itemlist csl) ==>
	      RTC (rderives ag) [NTS (startSym ag)] (s1 ++ [NTS lhs] ++ s2) ==>
	      EVERY isTmnlSym s2 ==>
	      ~(lhs = startSym ag) ==>
	      (csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))]) ==>
	      ?stl' csl'.
	      takesSteps (SUC 0) (parse (SOME m))
	      (exitCond (eof,NTS (startSym g))) (s2,stl,csl) (s2,stl',csl') /\
               (stackSyms stl' = stackSyms (pop stl (LENGTH rhs)) ++ [NTS lhs])`
		by METIS_TAC [takesStepsReduce] THEN
	    FIRST_X_ASSUM (Q.SPECL_THEN [`[]`,`stackSyms stl`,`startSym g`,
					 `[TS eof]`,`stl`,`csl`] MP_TAC) THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [isTmnlSym_def] THEN
	    `[(NTS st,initItems ag (rules ag))] = MAP FST ([]:((symbol#state)#ptree)list) ++
						      [(NTS st,initItems ag (rules ag))]`
		by SRW_TAC [][] THEN
	    `parseInv (ag,stl,csl)`
		by METIS_TAC [takesStepsParseInv,
			      takesStepsCslStlEq,isTmnlSym_def,EVERY_DEF,parseInvInit] THEN
	    `~(LAST ((stackSyms stl ++ [TS eof])::t)=[])`
		by METIS_TAC [auggrStRtcRderivesNotNil,derivesImpRderives] THEN
	    `validItemInv (ag,stl,csl)`
		by METIS_TAC [takesStepsParseInv,
			      takesStepsCslStlEq,isTmnlSym_def,
			      EVERY_DEF,parseInvInit,validItemInvInit,
			      takesStepsValidItemInv,takesStepsSlNotNil] THEN
	    `(csl = MAP FST stl ++ [(NTS st,initItems ag (rules ag))])`
		by METIS_TAC [takesStepsCslStlEq] THEN
	    FULL_SIMP_TAC (srw_ss()) [rsf_def] THEN
	    `?stl' csl'.
             takesSteps 1 (parse (SOME m))
               (exitCond (eof,NTS (startSym g)))
               ([TS eof],stl,
                MAP FST stl ++
                [(NTS st,initItems ag (rules ag))])
               ([TS eof],stl',csl') /\
             (stackSyms stl' =
              stackSyms (pop stl (LENGTH (stackSyms stl))) ++
              [NTS (startSym g)])` by METIS_TAC [] THEN
	    `(pop stl (LENGTH (stackSyms stl)) =[])`
		by METIS_TAC [popnthm,APPEND_NIL,stackSyms_len] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    `takesSteps (n+1)
	     (parse (SOME m)) (exitCond (eof,NTS (startSym g)))
	     (LAST ((stackSyms stl ++ [TS eof])::t),[],[(NTS st,initItems ag (rules ag))])
	     ([TS eof],stl',csl')` by METIS_TAC [takesStepsAdd] THEN
	    `(exitCond (eof,NTS (startSym g)))
	     ([TS eof],stl',csl')`
		by (SRW_TAC [] [exitCond_def] THEN
		    Cases_on `stl'` THEN
		    FULL_SIMP_TAC (srw_ss()) [stackSyms_APPEND,stackSyms_def,pop_def] THEN
		    Cases_on `t'` THEN
		    FULL_SIMP_TAC (srw_ss()) [stackSyms_def,exitCond_def]) THEN
	    `mwhile (\s. ~exitCond (eof,NTS (startSym g)) s)
             (parse (SOME m))
             (LAST ((stackSyms stl ++ [TS eof])::t),[],
              [(NTS st,initItems ag (rules ag))]) =
             SOME (SOME ([TS eof],stl',csl'))`
		by METIS_TAC [takesSteps_mwhile] THEN
	    FULL_SIMP_TAC (srw_ss()) [parser_def,LET_THM,tmnlSym_def] THEN
	    SRW_TAC [][] THEN
	    FULL_SIMP_TAC (srw_ss()) [stackSyms_def] THEN
            FULL_SIMP_TAC (srw_ss()) [] THEN
	    Q.ABBREV_TAC `inp = LAST
                ((REVERSE (MAP FST (MAP FST stl)) ++ [TS eof])::
                     t)` THEN
	    Q.ABBREV_TAC `start = [(NTS st,initItems ag (rules ag))]` THEN
	    SRW_TAC [] [parseExp] THEN
	    Cases_on `MAP FST (MAP FST stl')` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `REVERSE t'` THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    SRW_TAC [] [] THEN
	    FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on` stl'` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    Cases_on `t''` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
	    METIS_TAC [NOT_CONS_NIL,REVERSE,MAP,rev_nil],

      Cases_on `t'` THEN FULL_SIMP_TAC (srw_ss()) []
      ]])





val _ = export_theory()
